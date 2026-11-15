#!/usr/bin/env python3
"""Index frozen public files so Nix does not copy private build caches.

This creates a new empty Git repository and index, without project history.
It refuses a preexisting commit or remote. No source repository is fetched.
"""

import argparse
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("handoff", type=Path)
    args = parser.parse_args()
    root = args.handoff.resolve()
    manifest = json.loads((root / "public-manifest.json").read_text())
    if not (root / ".git").exists():
        subprocess.run(["git", "init", "--quiet", str(root)], check=True)
    commit = subprocess.run(["git", "rev-parse", "--verify", "HEAD"], cwd=root,
                            capture_output=True)
    remotes = subprocess.check_output(["git", "remote"], cwd=root).strip()
    if commit.returncode == 0 or remotes:
        raise ValueError("Expected new public-only Git index, no commits or remotes")
    subprocess.run(["git", "read-tree", "--empty"], cwd=root, check=True)
    subprocess.run(["git", "add", "--", "public-manifest.json", *manifest["files"]],
                   cwd=root, check=True)
    subprocess.run(["direnv", "allow", "."], cwd=root, check=True)
    print("Prepared public-only Git index; no commits or remotes")


if __name__ == "__main__":
    main()
