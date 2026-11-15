#!/usr/bin/env python3
"""Positive mmap boundary fixture; snapshots are diagnostics, not syscall tracing."""
import argparse
import ctypes
import errno
import json
import os
from pathlib import Path
import resource
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--fixture", type=Path, required=True)
    args = parser.parse_args()
    assert sys.platform == "linux" and ctypes.sizeof(ctypes.c_void_p) == 8
    assert ctypes.sizeof(ctypes.c_long) == ctypes.sizeof(ctypes.c_ulong) == 8
    assert os.sysconf("SC_PAGE_SIZE") == 4096
    resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
    resource.setrlimit(resource.RLIMIT_AS, (256 << 20, 256 << 20))
    resource.setrlimit(resource.RLIMIT_FSIZE, (64 << 10, 64 << 10))

    size = 4096
    private = 0x02
    noreplace = 0x100000
    failed = ctypes.c_void_p(-1).value
    libc = ctypes.CDLL(None, use_errno=True)
    mmap = libc.mmap
    mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int,
                     ctypes.c_int, ctypes.c_int, ctypes.c_long]
    mmap.restype = ctypes.c_void_p
    munmap = libc.munmap
    munmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
    munmap.restype = ctypes.c_int
    diagnostic = libc.conaled_mmap_random_snapshot
    diagnostic.argtypes = [ctypes.POINTER(ctypes.c_ulong), ctypes.c_size_t]
    diagnostic.restype = ctypes.c_int
    fields = ["version", "calls", "forwarded", "mmap_failures",
              "preferred_successes", "disabled", "identity_mismatches",
              "advice_attempts", "advised_bytes", "advice_successes",
              "advice_failures", "last_advice_errno"]

    def snapshot():
        words = (ctypes.c_ulong * 12)()
        assert diagnostic(words, 12) == 0, "snapshot API failed"
        result = dict(zip(fields, words))
        assert result["version"] == 1, "unexpected snapshot API version"
        return result

    args.fixture.mkdir(parents=True, exist_ok=True)
    path = args.fixture / "mapping.bin"
    fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR, 0o600)
    original = bytes(range(256)) * 16
    live = set()
    calls = []

    def map_call(label, address, flags):
        ctypes.set_errno(123)
        result = mmap(address, size, 3, flags, fd, 0)
        error = ctypes.get_errno()
        calls.append({"name": label, "address": address, "length": size,
                      "prot": 3, "flags": flags, "offset": 0,
                      "result": result, "errno": error})
        if result != failed:
            live.add(result)
        return result, error

    try:
        assert os.write(fd, original) == size, "short fixture write"
        os.close(fd)
        fd = -1
        fd = os.open(path, os.O_RDONLY)
        reserved, _ = map_call("reserve", None, private)
        assert reserved not in (None, failed), "ordinary file mmap failed"
        assert munmap(reserved, size) == 0, "reserve munmap failed"
        live.remove(reserved)
        before = snapshot()

        mapped, error = map_call("preferred", reserved, private | noreplace)
        assert mapped == reserved, "preferred mmap did not retain its address"
        assert error == 123, "successful mmap changed errno"
        assert ctypes.string_at(mapped, size) == original, "mapped bytes changed"
        after = snapshot()
        assert after["advice_attempts"] == before["advice_attempts"] + 1, \
            "expected one MADV_RANDOM advice attempt; none or unexpected count observed"
        assert after["advised_bytes"] == before["advised_bytes"] + size
        assert after["advice_successes"] == before["advice_successes"] + 1

        sentinel = b"PRIVATE-MAPPING-WRITE"
        ctypes.memmove(mapped, sentinel, len(sentinel))
        expected = sentinel + original[len(sentinel):]
        assert ctypes.string_at(mapped, size) == expected
        collision, error = map_call("collision", mapped, private | noreplace)
        assert collision == failed and error == errno.EEXIST, \
            "collision must return MAP_FAILED/EEXIST"
        collision_after = snapshot()
        assert collision_after["advice_attempts"] == after["advice_attempts"], \
            "failed collision unexpectedly received advice"
        assert ctypes.string_at(mapped, size) == expected, "collision changed mapped bytes"
        assert os.pread(fd, size, 0) == original, "private write changed backing file"
        report = {"passed": True, "fixture": str(path), "mmap_calls": calls,
                  "before": before, "after_preferred": after,
                  "after_collision": collision_after,
                  "snapshot_scope": "public diagnostics, not independent syscall tracing"}
    finally:
        cleanup = []
        for address in live:
            ctypes.set_errno(0)
            result = munmap(address, size)
            cleanup.append({"address": address, "returncode": result,
                            "errno": ctypes.get_errno()})
            assert result == 0, "final munmap failed"
        if fd >= 0:
            os.close(fd)
    report["cleanup"] = cleanup
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
