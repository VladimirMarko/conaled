"""Recover only the pinned public reference; keep bodies outside deliverables."""
import datetime
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile
import urllib.error
import urllib.request

WORK = Path(__file__).resolve().parents[1]
TARGET = WORK.parent.parent / "reference"
REPORT = WORK / "validation/1037-source-recovery.json"
inventory = json.loads((WORK / "source/vfa-source-inventory.json").read_text())
expected = inventory["source"]["archive_sha256"]
record = {"started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "expected_archive_sha256": expected, "attempts": [], "passed": False,
          "reference_bodies_excluded_from_checkpoint": True}
urls = ["https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz",
        "https://softwarefoundations.cis.upenn.edu/vfa-current/vfa.tgz"]
try:
    data = None
    for url in urls:
        attempt = {"url": url}
        record["attempts"].append(attempt)
        try:
            with urllib.request.urlopen(url, timeout=30) as response:
                attempt["http_status"] = response.status
                attempt["final_url"] = response.url
                candidate = response.read(20_000_001)
            if len(candidate) > 20_000_000:
                raise ValueError("Reference exceeds bounded download size")
            attempt["size_bytes"] = len(candidate)
            attempt["sha256"] = hashlib.sha256(candidate).hexdigest()
            if attempt["sha256"] != expected:
                raise ValueError("Archive identity mismatch: no source migration authorized")
            data = candidate
            break
        except (urllib.error.URLError, TimeoutError) as exc:
            attempt["error_type"] = type(exc).__name__
            attempt["error"] = str(exc)
    if data is None:
        raise RuntimeError("Both official archive retrieval routes failed")
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
        members = archive.getmembers()
        if len(members) > 10000:
            raise ValueError("Unexpected member count")
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or ".." in path.parts or not (member.isfile() or member.isdir()):
                raise ValueError("Unsafe archive member")
        matches = []
        for chapter in inventory["chapters"]:
            selected = [m for m in members if m.isfile() and PurePosixPath(m.name).name == chapter["source_file"]]
            if len(selected) != 1:
                raise ValueError("Missing or ambiguous chapter: " + chapter["chapter"])
            body = archive.extractfile(selected[0]).read()
            digest = hashlib.sha256(body).hexdigest()
            if digest != chapter["sha256"] or len(body) != chapter["size_bytes"]:
                raise ValueError("Chapter identity mismatch: " + chapter["chapter"])
            matches.append({"chapter": chapter["chapter"], "member": selected[0].name,
                            "sha256": digest, "size_bytes": len(body)})
        TARGET.mkdir(parents=True, exist_ok=True)
        (TARGET / "vfa.tgz").write_bytes(data)
        archive.extractall(TARGET, filter="data")
    record.update(passed=True, archive=str(TARGET / "vfa.tgz"),
                  archive_sha256=expected, chapters=matches)
except Exception as exc:
    record.update(error_type=type(exc).__name__, error=str(exc))
finally:
    record["completed_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    REPORT.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2), flush=True)
raise SystemExit(0 if record["passed"] else 1)
