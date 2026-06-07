from mcp.server.fastmcp import FastMCP
from .session_manager import manager
import asyncio
import json
import logging
import os
import tempfile

DEFAULT_LOG_LEVEL = "DEBUG"


def _configure_logging() -> None:
    level_name = os.getenv("QCP_MCP_LOG_LEVEL", DEFAULT_LOG_LEVEL).upper()
    default_level = getattr(logging, DEFAULT_LOG_LEVEL, logging.DEBUG)
    level = getattr(logging, level_name, default_level)
    handlers = [logging.StreamHandler()]
    log_file = os.getenv("QCP_MCP_LOG_FILE", "").strip()
    if log_file:
        handlers.append(logging.FileHandler(log_file))
    logging.basicConfig(
        level=level,
        format="%(asctime)s %(levelname)s [%(name)s] %(message)s",
        handlers=handlers,
        force=True,
    )


logger = logging.getLogger(__name__)

mcp = FastMCP("qcp")


def _extract_latest_json_blob(raw: str) -> str:
    decoder = json.JSONDecoder()
    latest = None
    latest_end = -1
    for idx, ch in enumerate(raw):
        if ch != "{":
            continue
        try:
            _, end = decoder.raw_decode(raw[idx:])
        except json.JSONDecodeError:
            continue
        absolute_end = idx + end
        if absolute_end >= latest_end:
            latest = raw[idx:absolute_end]
            latest_end = absolute_end
    return latest or raw

@mcp.tool(
    name = "load_target_file",
)
async def initialize(file: str = "") -> str:
    """用于加载并启动目标 C 文件的在QCP工具中的符号执行会话。这是有状态流程的第一步，必须先调用本工具并获得正常启动信息，才能使后续的 step、check、symbolic 等操作在当前会话中生效。若正常启动，则会返回启动提示。若有报错，则会返回报错信息及行号。
    
    Args:
        file: C文件路径，需要绝对路径。 例如 "/home/user/project/test.c"
    """
    logger.info("load_target_file tool invoked: file=%s", file)
    goal_tmp = tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".v",
        prefix="qcp_goal_",
        delete=False,
    )
    goal_tmp_path = os.path.abspath(goal_tmp.name)
    goal_tmp.close()

    args = ["--input-file=" + file, "--goal-file=" + goal_tmp_path]
    logger.debug("setting qcp args: %s", args)
    manager.set_args(args)
    try:
        sess = await asyncio.to_thread(manager.restart)
        if os.name == "nt" and not sess.initial_output:
            # Warm up the Windows PTY-backed session so the first real tool
            # call does not get stuck behind the startup banner.
            try:
                await asyncio.to_thread(sess.send, "<check>1</check>", 10.0)
            except Exception:
                logger.debug("windows qcp warm-up command failed", exc_info=True)
        output = sess.initial_output
        logger.debug("load_target_file collected output chars=%d", len(output))
        return output
    except Exception:
        logger.exception("load_target_file tool failed: file=%s", file)
        raise

@mcp.tool()
async def step(steps: int = 1) -> str:
    """在当前会话的当前位置执行符号单步。返回值是执行结束后当前位置的符号执行状态，若验证失败，则在errormessage中返回错误信息。通常在断点处（即执行过 check 或 step 后的位置）使用，用于逐步执行并检查符号执行状态的变化。
    
    Args:
        steps: 可选参数，指定连续执行的步数，默认为1。
    """
    sess = await asyncio.to_thread(manager.current)
    raw = await asyncio.to_thread(sess.send, "<step>%d</step>" % steps)
    return _extract_latest_json_blob(raw)

@mcp.tool()
async def check(line: int) -> str:
    """检查当前会话在指定行号处的符号执行状态。返回值是指定行号位置的符号执行状态，若验证失败，则在errormessage中返回错误信息。通常在执行错误时使用，用于检查错误发生位置前几个位置的符号执行状态。
    
    Args:
        line: 需要检查的行号，整数类型。
    """
    sess = await asyncio.to_thread(manager.current)
    raw = await asyncio.to_thread(sess.send, "<check>%d</check>" % line)
    return _extract_latest_json_blob(raw)

@mcp.tool()
async def symbolic(line: int) -> str:
    """整体验证当前会话的C文件，并获得符号执行结果概览。若errormessage为空，则验证通过；否则验证失败，并返回错误信息。

    Args:
        line: 需要检查的行号，整数类型。通常为目标文件的最后一行，用于检查整个文件的符号执行结果。
    """
    sess = await asyncio.to_thread(manager.current)
    raw = await asyncio.to_thread(sess.send, "<symbolic>%d</symbolic>" % line)
    return _extract_latest_json_blob(raw)

@mcp.tool()
async def proof(function_name: str, witness_type: int, number: int) -> str:
    """将 Json 记录中某个函数指定类型的第 number 个 witness 目标打印到 --goal-file 指定文件中。

    Args:
        function_name: 目标函数名。
        witness_type: witness 类型，1-5 分别对应五类 witness。
        number: witness 序号（从1开始）。
    """
    sess = await asyncio.to_thread(manager.current)
    raw = await asyncio.to_thread(
        sess.send,
        "<proof> %s %d %d </proof>" % (function_name, witness_type, number),
    )
    return _extract_latest_json_blob(raw)

@mcp.tool()
async def close() -> str:
    """关闭当前会话，释放相关资源。调用后当前会话将不再可用，必须重新调用 load_target_file 来启动新会话。
    """
    sess = await asyncio.to_thread(manager.active)
    if sess is None:
        logger.info("close requested but no active session")
        return "no active session"
    await asyncio.to_thread(sess.send, "<end></end>")
    return "session closed"

def main():
    _configure_logging()
    logger.info("starting qcp-mcp server on stdio transport")
    mcp.run(transport="stdio")

if __name__ == "__main__":
    main()
