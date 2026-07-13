#!/usr/bin/env python3
# Replay archived manual proofs into kosaraju_rel_proof_manual.v, then apply the
# entailment template to remaining Abort split-goals, then iteratively revert
# any tactic that does not compile (so the file always builds green).
#
# Usage:  python3 replay_manual.py [proof_manual.v]
# Default target = examples/QCP_demos_LLM/kosaraju_rel_proof_manual.v (run from SeparationLogic/).
import re, os, sys, subprocess

REPO = "/home/user/src/tarjan-coq-2"
SL   = os.path.join(REPO, "SeparationLogic")
ARCHIVE = os.path.join(SL, "examples/QCP_demos_LLM", "kosaraju_rel_manual_proofs.txt")
DEFAULT = "examples/QCP_demos_LLM/kosaraju_rel_proof_manual.v"
FILE = sys.argv[1] if len(sys.argv) > 1 else DEFAULT
VO   = FILE.replace(".v", ".vo")
GLOB = FILE.replace(".v", ".glob")

TEMPLATE = ("pre_process; match goal with H : csr_wf1 _ _ _ _ _ |- _ => destruct H "
            "| H : csr_wf2 _ _ _ _ _ |- _ => destruct H | _ => idtac end; "
            "entailer!; try lia; try congruence; try assumption.")

def terminate(tac):
    """Ensure exactly one trailing '.', so `Proof. <tac> Qed.` is well-formed."""
    tac = tac.strip()
    return tac if tac.endswith('.') else tac + '.'

os.chdir(SL)

def parse_archive(path):
    arch = {}
    name = None
    buf = []
    with open(path) as f:
        for ln in f:
            raw = ln.rstrip("\n")
            s = raw.strip()
            if s.startswith("#"):
                continue
            m = re.match(r"^===\s+(\S+)\s+===$", s)
            if m:
                if name is not None:
                    arch[name] = " ".join(buf).strip()
                name = m.group(1)
                buf = []
            elif name is not None:
                buf.append(s)
        if name is not None:
            arch[name] = " ".join(buf).strip()
    # collapse internal whitespace
    return {k: re.sub(r"\s+", " ", v).strip() for k, v in arch.items()}

ARCH = parse_archive(ARCHIVE)

def fallback_body(name):
    # split-goals are introduced as `Proof. Abort.`, main VCs as `Proof. Admitted.`
    return "Proof. Abort.\n" if "split_goal" in name else "Proof. Admitted. \n"

def apply_policies(lines):
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^(Lemma\s+(proof_of_\w+)\s*:)", line)
        if m and i + 1 < len(lines) and lines[i+1].lstrip().startswith("Proof."):
            name = m.group(2)
            body = lines[i+1]
            if name in ARCH:
                tac = ARCH[name].strip()
                if tac == "Admitted":
                    new = "Proof. Admitted. \n"
                else:
                    new = f"Proof. {terminate(ARCH[name])} Qed.\n"
            elif "Abort" in body:
                new = f"Proof. {TEMPLATE} Qed.\n"
            elif "Admitted" in body:
                new = "Proof. Admitted. \n"
            else:
                new = body
            out.append(line)
            out.append(new)
            i += 2
        else:
            out.append(line)
            i += 1
    return out

def build():
    for p in (VO, GLOB):
        if os.path.exists(p):
            os.remove(p)
    r = subprocess.run(f"eval $(opam env) && make {VO}", shell=True,
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr

def lemma_name_above(lines, err_line):
    idx = min(err_line - 1, len(lines) - 1)
    while idx >= 0:
        m = re.match(r"^Lemma\s+(proof_of_\w+)\s*:", lines[idx])
        if m:
            return m.group(1)
        idx -= 1
    return None

def proof_line_index(lines, name):
    for i, l in enumerate(lines):
        if re.match(rf"^Lemma\s+{re.escape(name)}\s*:", l) and i + 1 < len(lines):
            return i + 1
    return None

# 1. apply archive + template
with open(FILE) as f:
    lines = f.readlines()
lines = apply_policies(lines)
with open(FILE, "w") as f:
    f.writelines(lines)

applied_archive = set(ARCH.keys())
reverted = []
archived_failures = []

# 2. iterate: revert non-compiling tactics
for _ in range(120):
    rc, out = build()
    if rc == 0:
        print("=== BUILD GREEN ===")
        break
    m = re.search(r"line (\d+), characters", out)
    if not m:
        print("=== no 'line N' in error, stopping ===")
        print(out[-2500:])
        break
    err_line = int(m.group(1))
    with open(FILE) as f:
        lines = f.readlines()
    name = lemma_name_above(lines, err_line)
    if name is None:
        print(f"=== no lemma above error at {err_line}, stopping ===")
        break
    pl = proof_line_index(lines, name)
    if pl is None:
        print(f"=== no Proof line for {name}, stopping ===")
        break
    cur = lines[pl]
    if ("Abort" in cur and "Qed" not in cur) or ("Admitted" in cur and "Qed" not in cur):
        # already fallback yet still error -> real problem elsewhere
        print(f"=== {name} already fallback but error at {err_line}, stopping ===")
        print(out[-2500:])
        break
    is_archived = name in ARCH
    lines[pl] = fallback_body(name)
    with open(FILE, "w") as f:
        f.writelines(lines)
    reverted.append(name)
    if is_archived:
        archived_failures.append(name)
        print(f"  !! ARCHIVE FAIL {name} -> reverted (needs re-proof)")
    else:
        print(f"  reverted {name} (template) -> fallback")

# 3. summary
print()
print(f"Archive entries: {len(ARCH)}; reverted (any): {len(reverted)}")
if archived_failures:
    print(f"!! Archived proofs that FAILED to compile ({len(archived_failures)}):")
    for n in archived_failures:
        print(f"     - {n}")
print()
print("=== final proof_manual.v status ===")
with open(FILE) as f:
    flines = f.read().splitlines()
for i, l in enumerate(flines):
    if l.startswith("Lemma proof_of_"):
        nm = l.split()[1]
        body = flines[i+1] if i+1 < len(flines) else ""
        tag = ("Qed  " if "Qed" in body else
               "ABORT" if "Abort" in body else
               "ADMIT" if "Admitted" in body else "???? ")
        print(f"  {tag} {nm}")
