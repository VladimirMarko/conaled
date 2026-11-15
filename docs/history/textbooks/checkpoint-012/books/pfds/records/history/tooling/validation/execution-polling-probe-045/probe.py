"""Bounded noncompiler observation of execution-service polling behavior."""
from datetime import datetime, timezone
from pathlib import Path
import json
import sys
import time

directory = Path(sys.argv[1])
directory.mkdir(parents=True, exist_ok=False)
start = time.monotonic()

def now():
    return datetime.now(timezone.utc).isoformat()

def save(name, value):
    (directory / name).write_text(json.dumps(value, indent=2) + "\n")

save("started.json", {"time": now(), "duration_seconds": 300,
                      "kind": "noncompiler-timer", "acceptance": False})
while True:
    elapsed = time.monotonic() - start
    record = {"time": now(), "elapsed_seconds": elapsed, "acceptance": False}
    save("latest.json", record)
    print(json.dumps(record), flush=True)
    if elapsed >= 300:
        save("completed.json", record)
        break
    time.sleep(min(20, 300 - elapsed))
