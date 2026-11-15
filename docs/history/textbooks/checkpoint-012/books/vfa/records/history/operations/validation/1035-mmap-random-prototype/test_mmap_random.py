#!/usr/bin/env python3
"""Small mmap boundary fixture; snapshots are diagnostics, not syscall tracing."""
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
    parser.add_argument("--expect-advice", choices=("success", "none", "failure"),
                        default="success")
    parser.add_argument("--passthrough", action="store_true")
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

    def check_advice(before, after, expected):
        deltas = {"advice_attempts": int(expected != "none"),
                  "advised_bytes": size if expected != "none" else 0,
                  "advice_successes": int(expected == "success"),
                  "advice_failures": int(expected == "failure")}
        for field, wanted in deltas.items():
            actual = after[field] - before[field]
            assert actual == wanted, f"{field}: expected delta {wanted}, got {actual}"
        if expected == "failure":
            assert after["last_advice_errno"] == errno.EAGAIN

    args.fixture.mkdir(parents=True, exist_ok=True)
    path = args.fixture / "mapping.bin"
    fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR, 0o600)
    original = bytes(range(256)) * 16
    live = set()
    calls = []
    shared_fd = -1

    def map_call(label, address, flags, prot=3, map_fd=None, offset=0, length=size):
        map_fd = fd if map_fd is None else map_fd
        ctypes.set_errno(123)
        result = mmap(address, length, prot, flags, map_fd, offset)
        error = ctypes.get_errno()
        calls.append({"name": label, "address": address, "length": length,
                      "prot": prot, "flags": flags, "fd": map_fd, "offset": offset,
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

        if args.passthrough:
            shared_fd = os.open(path, os.O_RDWR)
            # name, flags, protection, fd, offset, length, expected error, readable bytes
            cases = [
                ("ordinary", private, 3, fd, 0, size, 0, original),
                ("anonymous", private | noreplace | 0x20, 3, -1, 0, size, 0, bytes(size)),
                ("shared", 0x01 | noreplace, 3, shared_fd, 0, size, 0, original),
                ("readonly", private | noreplace, 1, fd, 0, size, 0, original),
                ("executable", private | noreplace, 5, fd, 0, size, 0, original),
                ("noreserve", private | noreplace | 0x4000, 3, fd, 0, size, 0, original),
                ("aligned_offset", private | noreplace, 3, fd, size, size, 0, None),
                ("unaligned_offset", private | noreplace, 3, fd, 1, size, errno.EINVAL, None),
                ("zero_length", private | noreplace, 3, fd, 0, 0, errno.EINVAL, None),
                ("invalid_fd", private | noreplace, 3, -1, 0, size, errno.EBADF, None),
            ]
            observations = []
            for index, (name, flags, prot, call_fd, offset, length, wanted_error, contents) in enumerate(cases):
                assert not live, "passthrough case started with a live mapping"
                if index:
                    reserved, _ = map_call("reserve_" + name, None, private)
                    assert reserved not in (None, failed), "ordinary reservation failed"
                    assert munmap(reserved, size) == 0, "reservation munmap failed"
                    live.remove(reserved)
                case_before = snapshot()
                mapped, error = map_call(name, reserved, flags, prot, call_fd, offset, length)
                case_after = snapshot()
                check_advice(case_before, case_after, "none")
                if wanted_error:
                    assert mapped == failed and error == wanted_error, \
                        f"{name}: expected MAP_FAILED/errno {wanted_error}, got {mapped}/{error}"
                elif name == "executable" and mapped == failed:
                    assert error in (errno.EPERM, errno.EACCES), \
                        f"unexpected executable-map error {error}"
                else:
                    assert mapped not in (None, failed) and error == 123, \
                        f"{name}: expected success/errno 123, got {mapped}/{error}"
                    if flags & noreplace:
                        assert mapped == reserved, f"{name}: preferred address changed"
                    if contents is not None:
                        assert ctypes.string_at(mapped, size) == contents, f"{name}: bytes changed"
                if mapped != failed:
                    assert munmap(mapped, size) == 0, f"{name}: munmap failed"
                    live.remove(mapped)
                observations.append({"name": name, "before": case_before, "after": case_after,
                                     "policy_denied": name == "executable" and mapped == failed})
            after = snapshot()
            check_advice(before, after, "none")
            assert os.pread(fd, size, 0) == original, "passthrough changed backing file"
            report = {"mode": "passthrough", "before": before, "after": after,
                      "cases": observations}
        else:
            mapped, error = map_call("preferred", reserved, private | noreplace)
            assert mapped == reserved, "preferred mmap did not retain its address"
            assert error == 123, "successful mmap changed errno"
            assert ctypes.string_at(mapped, size) == original, "mapped bytes changed"
            after = snapshot()
            check_advice(before, after, args.expect_advice)

            sentinel = b"PRIVATE-MAPPING-WRITE"
            ctypes.memmove(mapped, sentinel, len(sentinel))
            expected = sentinel + original[len(sentinel):]
            assert ctypes.string_at(mapped, size) == expected
            collision, error = map_call("collision", mapped, private | noreplace)
            assert collision == failed and error == errno.EEXIST, \
                "collision must return MAP_FAILED/EEXIST"
            collision_after = snapshot()
            check_advice(after, collision_after, "none")
            assert ctypes.string_at(mapped, size) == expected, "collision changed mapped bytes"
            assert os.pread(fd, size, 0) == original, "private write changed backing file"
            report = {"mode": "preferred", "expected_advice": args.expect_advice,
                      "before": before, "after_preferred": after,
                      "after_collision": collision_after}
        report.update({"passed": True, "fixture": str(path), "mmap_calls": calls,
                       "snapshot_scope": "public diagnostics, not independent syscall tracing"})
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
        if shared_fd >= 0:
            os.close(shared_fd)
    report["cleanup"] = cleanup
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
