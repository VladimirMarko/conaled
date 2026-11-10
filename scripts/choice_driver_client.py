"""JSONL transport for the bounded Lean choice driver; no policy reimplementation."""
import json
import os
from pathlib import Path
import selectors
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMMAND = ["lake", "env", "lean", "--run", "scripts/choice-driver.lean"]


class Session:
    def __init__(self, implementation=None):
        env = os.environ.copy()
        if implementation is not None:
            env["CONALED_CHOICE_IMPLEMENTATION"] = implementation
        self.process = subprocess.Popen(COMMAND, cwd=ROOT, env=env, text=True,
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, bufsize=1)

    def raw(self, line):
        self.process.stdin.write(line + "\n")
        self.process.stdin.flush()
        with selectors.DefaultSelector() as ready:
            ready.register(self.process.stdout, selectors.EVENT_READ)
            if not ready.select(timeout=60):
                self.process.kill()
                raise TimeoutError("choice driver did not reply within 60 seconds")
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError(self.process.stderr.read())
        return json.loads(line)

    def request(self, value):
        return self.raw(json.dumps(value))

    def close(self):
        self.process.stdin.close()
        self.process.wait(timeout=30)
        errors = self.process.stderr.read()
        self.process.stdout.close()
        self.process.stderr.close()
        if self.process.returncode:
            raise RuntimeError((self.process.returncode, errors))

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()
