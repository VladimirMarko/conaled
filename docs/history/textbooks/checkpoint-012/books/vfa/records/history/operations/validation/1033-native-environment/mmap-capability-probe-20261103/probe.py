#!/usr/bin/env python3
"""One bounded mmap capability observation; never invokes Lean or reads /proc."""

import ctypes
import errno
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
from datetime import datetime, timezone

TASK_DIR = Path(__file__).resolve().parent
WALL_LIMIT_SECONDS = 15
CPU_LIMIT_SECONDS = 5
ADDRESS_SPACE_LIMIT_BYTES = 256 * 1024 * 1024
FILE_SIZE_LIMIT_BYTES = 65536
MAX_PAGE_SIZE_BYTES = 65536
MAX_LIVE_MAPPINGS = 2


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def child():
    report = {
        "scope": "One-page file-mapping capability observation, not a Lean-loader diagnosis or production adapter.",
        "started_utc": utc_now(),
        "limits": {
            "outer_wall_seconds": WALL_LIMIT_SECONDS,
            "cpu_seconds": CPU_LIMIT_SECONDS,
            "address_space_bytes": ADDRESS_SPACE_LIMIT_BYTES,
            "maximum_single_output_file_bytes": FILE_SIZE_LIMIT_BYTES,
            "maximum_page_size_bytes": MAX_PAGE_SIZE_BYTES,
            "maximum_live_explicit_mappings": MAX_LIVE_MAPPINGS,
            "maximum_explicit_mapped_bytes": MAX_PAGE_SIZE_BYTES * MAX_LIVE_MAPPINGS,
            "attempts": "One ordinary file mapping, one preferred mapping, one collision attempt; one ordinary fallback only if preferred mapping fails.",
        },
        "pinned_source": {
            "url": "https://raw.githubusercontent.com/leanprover/lean4/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/library/module.cpp",
            "sha256": "9b85a9a7610e73f240282fe288ad81c8b160fc975caa80bd5b13ddacdd6012a8",
            "lines": "524-540",
        },
        "ld_preload_present": bool(os.environ.get("LD_PRELOAD")),
        "calls": [],
        "cleanup": [],
    }
    live = set()
    fd = None
    file_path = TASK_DIR / "one-page.bin"
    passed = False
    munmap_fn = None
    try:
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_LIMIT_SECONDS, CPU_LIMIT_SECONDS))
        resource.setrlimit(resource.RLIMIT_AS, (ADDRESS_SPACE_LIMIT_BYTES, ADDRESS_SPACE_LIMIT_BYTES))
        resource.setrlimit(resource.RLIMIT_FSIZE, (FILE_SIZE_LIMIT_BYTES, FILE_SIZE_LIMIT_BYTES))
        page_size = os.sysconf("SC_PAGE_SIZE")
        if sys.platform != "linux" or not (0 < page_size <= MAX_PAGE_SIZE_BYTES):
            raise RuntimeError("Probe requires Linux and a page size within the explicit bound")
        if ctypes.sizeof(ctypes.c_void_p) != 8 or ctypes.sizeof(ctypes.c_long) != 8:
            raise RuntimeError("This captured probe is restricted to the observed 64-bit Linux ABI")
        report["page_size_bytes"] = page_size
        report["pointer_bits"] = 8 * ctypes.sizeof(ctypes.c_void_p)
        pattern = b"conaled isolated MAP_FIXED_NOREPLACE capability probe\n"
        seed = (pattern * ((page_size + len(pattern) - 1) // len(pattern)))[:page_size]
        report["mapped_file"] = {
            "path": str(file_path), "planned_size_bytes": page_size,
            "sha256_before": hashlib.sha256(seed).hexdigest(),
            "mapping_descriptor_mode": "O_RDONLY",
        }
        # Exclusively create the only mapped file. Lean opens its input read-only;
        # close the creation descriptor and do the same for all mapping calls.
        with file_path.open("xb") as handle:
            handle.write(seed)
        fd = os.open(file_path, os.O_RDONLY)
        report["mapped_file"]["size_bytes"] = os.fstat(fd).st_size
        libc = ctypes.CDLL(None, use_errno=True)
        mmap_fn = libc.mmap
        mmap_fn.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int,
                            ctypes.c_int, ctypes.c_int, ctypes.c_long]
        mmap_fn.restype = ctypes.c_void_p
        munmap_fn = libc.munmap
        munmap_fn.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
        munmap_fn.restype = ctypes.c_int
        map_failed = ctypes.c_void_p(-1).value
        prot = 0x1 | 0x2  # PROT_READ | PROT_WRITE
        map_private = 0x02
        map_fixed_noreplace = 0x100000  # Exact pinned Linux loader constant.
        flags = map_private | map_fixed_noreplace
        report["constants"] = {
            "PROT_READ": 1, "PROT_WRITE": 2, "MAP_PRIVATE": map_private,
            "MAP_FIXED_NOREPLACE": map_fixed_noreplace,
            "preferred_and_collision_flags": flags,
            "offset": 0, "MAP_FAILED": hex(map_failed),
        }

        def map_once(label, address, call_flags):
            if len(live) >= MAX_LIVE_MAPPINGS:
                raise RuntimeError("Explicit mapping-count bound reached")
            ctypes.set_errno(0)
            raw = mmap_fn(ctypes.c_void_p(address), page_size, prot, call_flags, fd, 0)
            observed_errno = ctypes.get_errno()
            value = 0 if raw is None else int(raw)
            failed = value == map_failed
            report["calls"].append({
                "operation": label, "requested_address": hex(address),
                "returned_address": hex(value), "length": page_size,
                "prot": prot, "flags": call_flags, "offset": 0,
                "failed": failed, "errno": observed_errno,
                "errno_name": errno.errorcode.get(observed_errno),
            })
            if not failed:
                live.add(value)
            report["maximum_live_mappings_observed"] = max(
                report.get("maximum_live_mappings_observed", 0), len(live))
            return value, observed_errno, failed

        def unmap_once(address, label):
            ctypes.set_errno(0)
            rc = munmap_fn(ctypes.c_void_p(address), page_size)
            observed_errno = ctypes.get_errno()
            report["cleanup"].append({
                "operation": label, "address": hex(address), "length": page_size,
                "returncode": rc, "errno": observed_errno,
                "errno_name": errno.errorcode.get(observed_errno),
            })
            if rc == 0:
                live.discard(address)
            return rc

        ordinary, _, ordinary_failed = map_once("ordinary_file_map", 0, map_private)
        if ordinary_failed:
            raise RuntimeError("Ordinary file mapping failed; no flag conclusion")
        ordinary_contents_match = ctypes.string_at(ordinary, page_size) == seed
        if unmap_once(ordinary, "ordinary_unmap_before_preferred") != 0:
            raise RuntimeError("Ordinary unmap failed; no freshly-freed-address test")
        # No other mappings are requested between the unmap and preferred call.
        preferred, preferred_errno, preferred_failed = map_once(
            "preferred_file_map_after_unmap", ordinary, flags)
        preferred_exact = not preferred_failed and preferred == ordinary
        if preferred_failed:
            occupied, _, failed = map_once("ordinary_collision_baseline", 0, map_private)
            if failed:
                raise RuntimeError("Unable to establish collision baseline")
        else:
            occupied = preferred
        contents_before_private_write = ctypes.string_at(occupied, page_size)
        # A private sentinel distinguishes preserved memory from a replacement
        # mapping of the same underlying file. The file bytes must remain intact.
        ctypes.c_ubyte.from_address(occupied).value = seed[0] ^ 0xFF
        private_before = ctypes.string_at(occupied, page_size)
        collision, collision_errno, collision_failed = map_once(
            "collision_against_live_mapping", occupied, flags)
        private_after = ctypes.string_at(occupied, page_size)
        collision_refused = collision_failed and collision_errno == errno.EEXIST
        non_overwrite = private_after == private_before
        report["checks"] = {
            "ordinary_file_contents_match": ordinary_contents_match,
            "preferred_mapping_at_freshly_freed_address": preferred_exact,
            "preferred_errno": preferred_errno,
            "collision_baseline_contents_match": contents_before_private_write == seed,
            "collision_refused_with_EEXIST": collision_refused,
            "private_sentinel_and_full_page_preserved": non_overwrite,
        }
        passed = all((ordinary_contents_match, preferred_exact,
                      contents_before_private_write == seed,
                      collision_refused, non_overwrite))
    except BaseException as exc:
        report["exception"] = {"type": type(exc).__name__, "message": str(exc)}
    finally:
        if munmap_fn is not None:
            for address in list(live):
                try:
                    unmap_once(address, "final_cleanup")
                except BaseException as exc:
                    report["cleanup"].append({"exception": type(exc).__name__, "message": str(exc)})
        if fd is not None:
            os.close(fd)
        if file_path.exists() and "mapped_file" in report:
            data = file_path.read_bytes()
            report["mapped_file"]["sha256_after"] = hashlib.sha256(data).hexdigest()
            report["mapped_file"]["unchanged"] = (
                report["mapped_file"]["sha256_before"] == report["mapped_file"]["sha256_after"])
            passed = passed and report["mapped_file"]["unchanged"]
        report["all_explicit_mappings_unmapped"] = not live
        passed = passed and not live
        report["passed"] = passed
        report["finished_utc"] = utc_now()
        report["interpretation"] = (
            "Exact flag accepted at this freshly freed address and enforced on collision; close the unsupported-flag capability hypothesis for this probe. No actual Lean mapping success rate or per-module cause was measured."
            if passed else
            "Capability check did not satisfy every expected condition. No automatic extension, alternative flag, or per-Lean diagnosis follows."
        )
        print(json.dumps(report, indent=2), flush=True)
    return 0 if passed else 1


def parent():
    command = [sys.executable, "-B", str(Path(__file__).resolve()), "--child"]
    record = {
        "started_utc": utc_now(), "command": command, "cwd": str(TASK_DIR),
        "timeout_seconds": WALL_LIMIT_SECONDS,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "writes_confined_to": str(TASK_DIR),
    }
    start = time.monotonic()
    try:
        result = subprocess.run(command, cwd=TASK_DIR, capture_output=True,
                                text=True, timeout=WALL_LIMIT_SECONDS)
        record.update({"returncode": result.returncode, "outcome": "completed"})
        stdout, stderr = result.stdout, result.stderr
    except subprocess.TimeoutExpired as exc:
        # subprocess.run kills and reaps only this owned child on timeout.
        record.update({"returncode": None, "outcome": "timed_out"})
        stdout, stderr = exc.stdout or b"", exc.stderr or b""
        stdout = stdout.decode(errors="replace") if isinstance(stdout, bytes) else stdout
        stderr = stderr.decode(errors="replace") if isinstance(stderr, bytes) else stderr
    record.update({"wall_seconds": time.monotonic() - start, "finished_utc": utc_now()})
    with (TASK_DIR / "stdout.log").open("x") as handle:
        handle.write(stdout)
    with (TASK_DIR / "stderr.log").open("x") as handle:
        handle.write(stderr)
    try:
        record["observation"] = json.loads(stdout)
    except json.JSONDecodeError:
        record["observation"] = None
    with (TASK_DIR / "execution.json").open("x") as handle:
        json.dump(record, handle, indent=2)
        handle.write("\n")
    print(json.dumps(record, indent=2), flush=True)
    return record["returncode"] if record["returncode"] is not None else 124


if __name__ == "__main__":
    raise SystemExit(child() if sys.argv[1:] == ["--child"] else parent())
