"""Boundary checks for the native own-executable compatibility library.

Run through native_toolchain.py so this process has the reviewed preload.
The raw syscall is an independent comparison for unaffected paths/errors.
"""
import ctypes
import errno
import json
import os
from pathlib import Path
import sys

libc = ctypes.CDLL(None, use_errno=True)
libc.readlink.argtypes = [ctypes.c_char_p, ctypes.c_void_p, ctypes.c_size_t]
libc.readlink.restype = ctypes.c_ssize_t
libc.syscall.restype = ctypes.c_long
libc.getauxval.argtypes = [ctypes.c_ulong]
libc.getauxval.restype = ctypes.c_ulong
SYS_READLINK = 89  # Linux x86-64, the adapter's explicit platform contract.


def observe(path, capacity=4096, raw=False):
    buffer = ctypes.create_string_buffer(b"Z" * (capacity + 1), capacity + 1)
    ctypes.set_errno(errno.EDOM)
    if raw:
        count = libc.syscall(ctypes.c_long(SYS_READLINK), ctypes.c_char_p(os.fsencode(path)),
                             buffer, ctypes.c_size_t(capacity))
    else:
        count = libc.readlink(os.fsencode(path), buffer, capacity)
    error = ctypes.get_errno()
    return {"count": count, "errno": error,
            "bytes": buffer.raw[:max(0, count)].decode(),
            "guard_unchanged": buffer.raw[capacity:] == b"Z"}


root = Path(__file__).resolve().parent
fixtures = root / "readlink-fixtures"
fixtures.mkdir(exist_ok=False)
(fixtures / "target.txt").write_text("ordinary target\n")
(fixtures / "ordinary-link").symlink_to("target.txt")
executable = os.path.realpath(ctypes.string_at(libc.getauxval(31)).decode())
results = []
for path in (f"/proc/{os.getpid()}/exe", "/proc/self/exe"):
    raw = observe(path, raw=True)
    actual = observe(path)
    assert actual["count"] == len(os.fsencode(executable)) and actual["bytes"] == executable
    assert actual["guard_unchanged"]
    truncated = observe(path, capacity=3)
    assert truncated["count"] == 3 and truncated["bytes"] == executable[:3]
    assert truncated["guard_unchanged"]
    zero = observe(path, capacity=0)
    zero_raw = observe(path, capacity=0, raw=True)
    assert zero == zero_raw
    results.append({"case": "own-executable", "path": path, "raw": raw,
                    "actual": actual, "truncated": truncated, "zero": zero})
for path in (str(fixtures / "ordinary-link"), str(fixtures / "target.txt"),
             str(fixtures / "absent"), f"/proc/{os.getpid() + 1000000}/exe",
             "/proc/self/cwd"):
    expected = observe(path, raw=True)
    actual = observe(path)
    assert actual == expected, (path, expected, actual)
    results.append({"case": "passthrough", "path": path, "raw": expected, "actual": actual})
print(json.dumps({"outcome": "passed", "executable": executable, "cases": results}, indent=2))
