"""Shared integrated-source inventory for coverage, candidate identity and auditing.

Only filesystem layout is interpreted here. Lean owns source syntax and imports.
The command emits the mathematical module names as JSON for ProofAudit.lean.
Run from the project root, as for the public verification and audit commands.
"""

import json
from pathlib import Path


SOURCE_TREES = ("SquareKit", "Applications", "Examples")
INFRASTRUCTURE = frozenset({"ProofAudit"})


def inventory(root: Path) -> dict[str, Path]:
    sources = list(root.glob("*.lean"))
    for directory in SOURCE_TREES:
        sources.extend((root / directory).rglob("*.lean"))
    return {
        ".".join(path.relative_to(root).with_suffix("").parts): path
        for path in sorted(sources)
    }


if __name__ == "__main__":
    print(json.dumps(sorted(set(inventory(Path.cwd())) - INFRASTRUCTURE)))
