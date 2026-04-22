import subprocess
import sys
import threading
import os
import shlex
import shutil
from typing import Optional, List
from .session import Session, TOOL_CMD
import logging


logger = logging.getLogger(__name__)

class SessionManager:
    def __init__(self):
        self._session: Optional[Session] = None
        self._lock = threading.Lock()
        self._tool_args: List[str] = []
        self._state = False

    def current(self) -> Session:
        with self._lock:
            if self._session is None or not self._session.is_alive():
                logger.info("current state: %s", self._state)
                if not self._is_initialized():
                    logger.debug("current session requested but no alive session")
                    raise RuntimeError("没有设定工具参数，无法启动会话，请先调用 load_target_file 工具")

                if not self._state:
                    raise RuntimeError("load_target_file 工具启动失败，请先排查启动错误")

                logger.info("current session requested but no alive session, restarting")
                self._session = self._spawn()
                return self._session
            logger.debug("returning current alive session")
            return self._session

    def restart(self) -> Session:
        with self._lock:
            logger.info("restarting qcp session")
            if self._session:
                logger.debug("killing previous session before restart")
                self._session.kill()
            self._session = self._spawn()
            logger.info("qcp session restarted successfully")
            return self._session

    def active(self) -> Optional[Session]:
        with self._lock:
            if self._session is None:
                logger.debug("active session requested but session is None")
                return None
            if not self._session.is_alive():
                logger.debug("active session requested but session is not alive")
                return None
            return self._session
        
    def set_args(self, args: List[str]) -> None:
        self._tool_args = args
        logger.debug("session args set: %s", args)
        
    def _is_initialized(self) -> bool:
        return self._tool_args != []

    def _spawn(self) -> Session:
        cmd = TOOL_CMD + self._tool_args
        script_bin = shutil.which("script") if os.name == "posix" else None
        if script_bin:
            # Run mcp behind a PTY so the lexer behaves interactively on stdin.
            if sys.platform == "darwin":
                cmd = [script_bin, "-q", "/dev/null"] + cmd 
            else:
                cmd_str = " ".join(shlex.quote(part) for part in cmd)
                cmd = [script_bin, "-qf", "-E", "never", "-c", cmd_str, "/dev/null"]
        logger.info("spawning qcp process: %s", cmd)
        try:
            proc = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )
        except Exception:
            logger.exception("failed to spawn qcp process")
            raise

        logger.debug("qcp process started pid=%s", proc.pid)
        sess = Session(proc=proc)
        threading.Thread(
            target=self._reader, args=(sess,), daemon=True
        ).start()
        logger.debug("reader thread started for pid=%s", proc.pid)
        sess.initial_output = sess._collect(timeout=300)
        self._state = proc.poll() is None
        logger.debug("session startup state pid=%s alive=%s", proc.pid, self._state)
        logger.debug("captured initial output pid=%s chars=%d", proc.pid, len(sess.initial_output))
        logger.debug("initial collect finished for pid=%s", proc.pid)
        return sess

    def _reader(self, sess: Session):
        logger.debug("reader loop entered pid=%s", sess.proc.pid)
        for line in sess.proc.stdout:
            logger.debug("reader line pid=%s: %r", sess.proc.pid, line.rstrip("\n"))
            sess.output_q.put(line)
        logger.debug("reader loop finished pid=%s", sess.proc.pid)
        sess.output_q.put(None)

manager = SessionManager()
