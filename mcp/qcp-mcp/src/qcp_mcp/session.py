import subprocess
import threading
import queue
import time
import os
import shutil
import re
from dataclasses import dataclass, field
from typing import Optional
import logging

END_PROMPT = "(end)"
logger = logging.getLogger(__name__)
ANSI_ESCAPE_RE = re.compile(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")


def _load_mcp_bin() -> str:
    env_bin = os.getenv("QCP_MCP_BIN", "").strip()
    if env_bin:
        return env_bin

    config_path = os.getenv("QCP_MCP_CONFIG", os.path.join(os.path.dirname(__file__), "CONFIGURE")).strip()
    if not config_path:
        raise RuntimeError("QCP_MCP_CONFIG is empty and QCP_MCP_BIN is not set")

    try:
        with open(config_path, "r", encoding="utf-8") as f:
            for raw in f:
                line = raw.strip()
                if not line or line.startswith("#"):
                    continue
                if line.startswith("QCP_MCP_BIN=") or line.startswith("PATH="):
                    value = line.split("=", 1)[1].strip().strip('"').strip("'")
                    if value:
                        logger.debug("loaded MCP binary path from CONFIGURE: %s", config_path)
                        return value
    except OSError as e:
        raise RuntimeError(f"failed to open CONFIGURE file: {config_path}") from e

    raise RuntimeError(
        "QCP_MCP_BIN is not set, and CONFIGURE has neither QCP_MCP_BIN nor PATH"
    )


_MCP_BIN = _load_mcp_bin()
_STDBUF_BIN = shutil.which("stdbuf")
_USE_STDBUF = os.getenv("QCP_MCP_USE_STDBUF", "0").strip().lower() in {"1", "true", "yes", "on"}

if os.name == "posix" and _STDBUF_BIN and _USE_STDBUF:
    TOOL_CMD = [_STDBUF_BIN, "-i0", "-oL", "-eL", _MCP_BIN]
else:
    TOOL_CMD = [_MCP_BIN]

@dataclass
class Session:
    proc: subprocess.Popen
    output_q: queue.Queue = field(default_factory=queue.Queue)
    status: str = "idle"
    cursor: Optional[str] = None
    initial_output: str = ""

    def _drain_pending_output(self) -> None:
        while True:
            try:
                self.output_q.get_nowait()
            except queue.Empty:
                break

    def send(self, cmd: str, timeout=300.0) -> str:
        logger.debug("sending command to pid=%s: %s", self.proc.pid, cmd)
        if hasattr(self.proc, "stdin") and self.proc.stdin is not None:
            self.proc.stdin.write(cmd + "\n")
            self.proc.stdin.flush()
        else:
            self._drain_pending_output()
            self.proc.write(cmd + "\r\n")
        output = self._collect(timeout)
        logger.debug("command completed pid=%s output_chars=%d", self.proc.pid, len(output))
        return output

    def _collect(self, timeout=300.0) -> str:
        start = time.time()
        logger.debug("start collecting output pid=%s timeout=%.1fs", self.proc.pid, timeout)
        chunks = []
        buffer = ""
        idle_deadline = None
        is_pty = not (hasattr(self.proc, "stdin") and self.proc.stdin is not None)
        while True:
            elapsed = time.time() - start
            remaining = timeout - elapsed
            if remaining <= 0:
                logger.warning("collect timeout pid=%s after %.2fs", self.proc.pid, elapsed)
                break

            # Use short queue waits so we can react quickly to process exit
            # instead of blocking for the full user-provided timeout.
            wait_timeout = min(0.2, remaining)
            try:
                chunk = self.output_q.get(timeout=wait_timeout)
                if chunk is None:
                    logger.debug("received output EOF marker pid=%s", self.proc.pid)
                    break
                buffer += chunk
                if is_pty:
                    idle_deadline = time.time() + 2.0
                if END_PROMPT in buffer:
                    before_prompt, _, _ = buffer.rpartition(END_PROMPT)
                    cleaned = ANSI_ESCAPE_RE.sub("", before_prompt)
                    if cleaned:
                        chunks.append(cleaned)
                    logger.debug("received end prompt pid=%s", self.proc.pid)
                    break
                cleaned = ANSI_ESCAPE_RE.sub("", buffer)
                if cleaned:
                    chunks.append(cleaned)
                buffer = ""
            except queue.Empty:
                if is_pty and idle_deadline is not None and time.time() >= idle_deadline:
                    logger.debug("pty idle deadline reached pid=%s", self.proc.pid)
                    break
                if not self.is_alive() and self.output_q.empty():
                    logger.debug("process exited and output queue drained pid=%s", self.proc.pid)
                    break
        if buffer:
            cleaned = ANSI_ESCAPE_RE.sub("", buffer)
            if cleaned:
                chunks.append(cleaned)
        output = "".join(chunks).replace("\r\n", "\n").strip()
        logger.debug(
            "collect finished pid=%s chunks=%d elapsed=%.2fs",
            self.proc.pid,
            len(chunks),
            time.time() - start,
        )
        return output

    def kill(self):
        if self.is_alive():
            logger.info("killing qcp process pid=%s", self.proc.pid)
            if hasattr(self.proc, "kill"):
                self.proc.kill()
            elif hasattr(self.proc, "close"):
                self.proc.close(True)
            if hasattr(self.proc, "wait"):
                self.proc.wait()
            logger.debug("qcp process terminated pid=%s", self.proc.pid)
        else:
            logger.debug("kill called but process already exited pid=%s", self.proc.pid)

    def is_alive(self) -> bool:
        if hasattr(self.proc, "isalive"):
            alive = bool(self.proc.isalive())
        else:
            alive = self.proc.poll() is None
        logger.debug("is_alive pid=%s -> %s", self.proc.pid, alive)
        return alive
