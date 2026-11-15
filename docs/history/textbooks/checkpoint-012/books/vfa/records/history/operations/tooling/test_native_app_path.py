#!/usr/bin/env python3
"""Exercise the actual libc boundary in fresh, directly executed processes."""

from __future__ import annotations

import ctypes
import errno
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def fixture(link: str) -> None:
    library = ctypes.CDLL(None, use_errno=True)
    readlink = library.readlink
    readlink.argtypes = (ctypes.c_char_p, ctypes.c_void_p, ctypes.c_size_t)
    readlink.restype = ctypes.c_ssize_t

    def invoke(path: str | None, size: int = 4096, null_buffer: bool = False):
        buffer = ctypes.create_string_buffer(b"!" * (max(size, 1) + 1))
        ctypes.set_errno(123)
        result = readlink(None if path is None else os.fsencode(path),
                          None if null_buffer else buffer, size)
        return {
            "return": result, "errno": ctypes.get_errno(),
            "bytes": buffer.raw[:max(result, 0)].hex(),
            "next_byte": buffer.raw[max(result, 0)] if result >= 0 else None,
        }

    own = f"/proc/{os.getpid()}/exe"
    print(json.dumps({
        "self": invoke("/proc/self/exe"), "pid": invoke(own),
        "truncated": invoke(own, 3), "zero_size": invoke(own, 0),
        "null_buffer": invoke(own, 1, True), "null_path": invoke(None),
        "ordinary": invoke(link), "near_match": invoke("/proc/self/exe-extra"),
        "nonexistent_pid": invoke("/proc/0/exe"),
    }))


def main() -> None:
    if sys.argv[1:2] == ["--fixture"]:
        fixture(sys.argv[2])
        return
    if len(sys.argv) != 3:
        raise SystemExit("Usage: test_native_app_path.py SHIM_ABSOLUTE_PATH TEMP_PARENT")
    shim = Path(sys.argv[1]).resolve(strict=True)
    parent = Path(sys.argv[2]).resolve(strict=True)
    executable = str(Path(sys.executable).resolve(strict=True))
    script = str(Path(__file__).resolve())
    records = {}
    with tempfile.TemporaryDirectory(prefix="app-path-test-", dir=parent) as tmp:
        link = Path(tmp) / "ordinary-link"
        link.symlink_to("ordinary-target")
        for mode in ("baseline", "matched", "mismatched", "unset"):
            env = dict(os.environ)
            env.pop("LD_PRELOAD", None)
            env.pop("CONALED_SELF_EXE", None)
            if mode != "baseline":
                env["LD_PRELOAD"] = str(shim)
            if mode in ("matched", "mismatched"):
                env["CONALED_SELF_EXE"] = executable if mode == "matched" else "/nonmatching-executable"
            command = [executable, "-B", script, "--fixture", str(link)]
            result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=20)
            if result.returncode:
                raise RuntimeError(f"{mode} fixture failed: {result.returncode}: {result.stderr}")
            records[mode] = json.loads(result.stdout)
        baseline, matched = records["baseline"], records["matched"]
        expected = os.fsencode(executable)
        for name in ("self", "pid"):
            assert matched[name] == {
                "return": len(expected), "errno": 123,
                "bytes": expected.hex(), "next_byte": ord("!"),
            }, (name, matched[name])
        assert matched["truncated"] == {
            "return": 3, "errno": 123, "bytes": expected[:3].hex(), "next_byte": ord("!"),
        }
        assert matched["zero_size"]["return"] == -1 and matched["zero_size"]["errno"] == errno.EINVAL
        assert matched["null_buffer"]["return"] == -1 and matched["null_buffer"]["errno"] == errno.EFAULT
        for name in ("ordinary", "near_match", "nonexistent_pid", "null_path"):
            assert matched[name] == baseline[name], (name, matched[name], baseline[name])
        assert bytes.fromhex(matched["ordinary"]["bytes"]) == b"ordinary-target"
        assert records["mismatched"] == baseline, records["mismatched"]
        assert records["unset"] == baseline, records["unset"]
    print(json.dumps({"passed": True, "executable": executable, "shim": str(shim), "results": records}, indent=2))


if __name__ == "__main__":
    main()
