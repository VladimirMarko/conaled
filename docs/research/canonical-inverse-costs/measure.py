"""Run one bounded Lean probe under `direnv exec . lake env python3`.

Linux fork/wait4 supplies per-child CPU time and peak RSS. CLOCK_BOOTTIME lets
us report a suspension gap separately. The harness exits nonzero for harness
failures; inspect exit_code and wall_timeout for the Lean verdict. When flock
wraps this script, lock waiting and shell setup precede the measured child.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import signal
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--wall", type=float, default=30)
    parser.add_argument("--depth", type=int, default=512)
    parser.add_argument("--heartbeats", type=int, default=200000)
    parser.add_argument("--sync", action="store_true")
    args = parser.parse_args()
    if args.wall <= 0 or args.depth <= 0 or args.heartbeats <= 0:
        parser.error("resource bounds must be positive")
    if Path(args.tag).name != args.tag or args.tag in (".", ".."):
        parser.error("tag must be a single filename component")

    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    source = args.source.resolve()
    command = ["lean", f"-DmaxRecDepth={args.depth}",
               f"-DmaxHeartbeats={args.heartbeats}"]
    if args.sync:
        command.append("-DElab.async=false")
    command.append(str(source))
    record = {
        "tag": args.tag,
        "source": str(source),
        "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "command": command,
        "start_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "load_before": os.getloadavg(),
        "cpu_count": os.cpu_count(),
        "wall_limit_s": args.wall,
        "async": "false" if args.sync else "default",
        "depth": args.depth,
        "heartbeats": args.heartbeats,
    }
    start = time.monotonic()
    boot_start = time.clock_gettime(time.CLOCK_BOOTTIME)
    pid = os.fork()
    if pid == 0:
        os.setsid()
        fd = os.open(output / (args.tag + ".log"),
                     os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        os.dup2(fd, 1)
        os.dup2(fd, 2)
        os.close(fd)
        os.execvp(command[0], command)

    expired = False
    try:
        while True:
            done, status, usage = os.wait4(pid, os.WNOHANG)
            if done:
                break
            if time.monotonic() - start >= args.wall:
                expired = True
                os.killpg(pid, signal.SIGKILL)
                _, status, usage = os.wait4(pid, 0)
                break
            time.sleep(0.05)
    except BaseException:
        # Interruption is a harness failure, not a measured Lean timeout.
        try:
            os.killpg(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        os.wait4(pid, 0)
        raise

    record.update(
        wall_s=time.monotonic() - start,
        boottime_s=time.clock_gettime(time.CLOCK_BOOTTIME) - boot_start,
        user_s=usage.ru_utime,
        system_s=usage.ru_stime,
        maxrss_kib=usage.ru_maxrss,
        wall_timeout=expired,
        exit_code=os.waitstatus_to_exitcode(status),
        load_after=os.getloadavg(),
    )
    record["suspension_delta_s"] = record["boottime_s"] - record["wall_s"]
    (output / (args.tag + ".json")).write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
