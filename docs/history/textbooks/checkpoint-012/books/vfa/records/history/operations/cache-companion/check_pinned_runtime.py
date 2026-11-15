#!/usr/bin/env python3
"""One bounded real-helper smoke check on literal files, never project artifacts."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tempfile

from cache_companion import HELPER_SHA, PinnedLake


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    runtime = PinnedLake(args.repo)
    identity = runtime.identity(args.repo)
    with tempfile.TemporaryDirectory(prefix="literal-lake-hash-", dir=args.work_dir) as temporary:
        root = Path(temporary)
        first, second = root / "first.bin", root / "second.bin"
        first.write_bytes(b"conaled cache companion fixture A\n")
        second.write_bytes(b"conaled cache companion fixture B\n")
        hashes = runtime.hashes([first, second, first], root / "checker")
        assert len(hashes) == 3 and all(re.fullmatch(r"[0-9a-f]{16}", h) for h in hashes)
        assert hashes[0] == hashes[2] and hashes[0] != hashes[1]
        files = sorted(str(p.relative_to(root)) for p in root.rglob("*") if p.is_file())
        assert files == ["checker/lake-output-hashes.lean", "checker/paths.json", "first.bin", "second.bin"]
        result = {"status": "passed", "identity": identity, "helper_sha256": HELPER_SHA,
                  "literal_inputs": [{"size_bytes": p.stat().st_size,
                                      "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
                                     for p in (first, second)],
                  "hashes": hashes, "runtime_evidence": runtime.last_hash_evidence,
                  "generated_compiler_artifacts": [], "private_files_before_cleanup": files,
                  "scope": "One helper invocation on literal private files; no project cache copied or formal module built."}
    result["temporary_directory_removed"] = not root.exists()
    assert result["temporary_directory_removed"]
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
