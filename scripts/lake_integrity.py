"""Conservative project-output consistency guard for the pinned Lake trace format.

This trusts trace provenance and a stable checkout. It does not authenticate
inputs, protect concurrent readers/writers, or inspect dependency caches.
"""

import json
from pathlib import Path
import re
import subprocess
import tempfile
import time
import tomllib


LIB_EXTENSIONS = ("olean", "olean.server", "olean.private", "ilean", "ir", "ir.sig")
IR_EXTENSIONS = ("c", "bc", "ltar")


def artifact_path(root, name, extension):
    directory = "ir" if extension in IR_EXTENSIONS else "lib/lean"
    return root / ".lake/build" / directory / (name.replace(".", "/") + "." + extension)


def validate_layout(root):
    # This adapter supports this repository's TOML layout, not arbitrary Lake
    # packages. Refuse changes that could silently move artifacts out of scope.
    if (root / "lakefile.lean").exists():
        raise RuntimeError("Integrity guard requires lakefile.toml (no lakefile.lean)")
    config = tomllib.loads((root / "lakefile.toml").read_text())
    defaults = {"buildDir": ".lake/build", "leanLibDir": "lib/lean", "irDir": "ir", "srcDir": "."}
    if any(config.get(key, value) != value for key, value in defaults.items()):
        raise RuntimeError("Integrity guard requires the standard project build/source directories")
    if config.get("enableArtifactCache", False) is not False:
        raise RuntimeError("Integrity guard requires project enableArtifactCache unset or false")
    for library in config.get("lean_lib", []):
        if library.get("srcDir", ".") != ".":
            raise RuntimeError("Integrity guard requires standard library source directories")


def expected_artifacts(root, name):
    trace = artifact_path(root, name, "trace")
    data = json.loads(trace.read_text())
    if not isinstance(data, dict) or data.get("schemaVersion") != "2025-09-10":
        raise ValueError("unsupported trace schema")
    outputs = data.get("outputs")
    if not isinstance(outputs, dict) or type(outputs.get("m")) is not bool:
        raise ValueError("missing output descriptions")
    if set(outputs) - {"m", "o", "i", "rs", "r", "c", "b", "l"}:
        raise ValueError("unknown output descriptions")
    parts = outputs.get("o")
    module = outputs["m"]
    if not isinstance(parts, list) or len(parts) != (3 if module else 1):
        raise ValueError("unsupported olean parts")
    descriptions = list(zip(("olean", "olean.server", "olean.private"), parts))
    descriptions += [("ilean", outputs.get("i")), ("c", outputs.get("c"))]
    for key, extension in (("rs", "ir.sig"), ("r", "ir"), ("b", "bc"), ("l", "ltar")):
        if key in outputs or (module and key in ("rs", "r")):
            descriptions.append((extension, outputs.get(key)))
    expected = []
    for extension, description in descriptions:
        if not isinstance(description, str) or not re.fullmatch(r"[0-9a-f]{16}\." + re.escape(extension), description):
            raise ValueError("unsupported artifact identity")
        path = artifact_path(root, name, extension)
        if not path.is_file():
            raise ValueError(f"missing {extension}")
        expected.append((path, description[:16]))
    return expected


def inspect_outputs(root, names, env):
    """Return modules needing rebuild; hashing errors stop the entire check."""
    bad = {}
    entries = []
    for name in names:
        try:
            artifacts = expected_artifacts(root, name)
        except (OSError, ValueError, TypeError) as error:
            bad[name] = str(error)
        else:
            entries.extend((name, path, expected) for path, expected in artifacts)
    if entries:
        with tempfile.TemporaryDirectory(prefix="conaled-output-hashes-") as directory:
            manifest = Path(directory) / "paths.json"
            manifest.write_text(json.dumps([str(path) for _, path, _ in entries]))
            result = subprocess.run(
                ["lean", "--run", str(root / "scripts/lake-output-hashes.lean"), str(manifest)],
                cwd=root, env=env, capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError("Integrity hashing failed:\n" + result.stdout + result.stderr)
        hashes = json.loads(result.stdout)
        if (not isinstance(hashes, list) or len(hashes) != len(entries)
                or any(not isinstance(h, str) or not re.fullmatch(r"[0-9a-f]{16}", h) for h in hashes)):
            raise RuntimeError("Integrity guard received invalid hash results")
        for (name, path, expected), actual in zip(entries, hashes):
            if actual != expected:
                bad.setdefault(name, f"output mismatch: {path.relative_to(root)}")
    return bad, len(entries)


def guard_outputs(root, names, env, *, repair):
    started = time.monotonic()
    validate_layout(root)
    bad, count = inspect_outputs(root, names, env)
    if bad and not repair:
        raise RuntimeError("Integrity guard rejected build outputs: " + "; ".join(
            f"{name}: {reason}" for name, reason in bad.items()))
    for name, reason in bad.items():
        print(f"Integrity guard: rebuilding {name} ({reason})", flush=True)
        # Paths come from the inventoried source module, never from trace data.
        # Remove archives too: Lake can otherwise unpack one after invalidation.
        for extension in (*LIB_EXTENSIONS, *IR_EXTENSIONS, "trace"):
            path = artifact_path(root, name, extension)
            path.unlink(missing_ok=True)
            path.with_name(path.name + ".hash").unlink(missing_ok=True)
    print(f"Integrity guard: hashed {count} artifacts; {len(bad)} modules "
          f"{'invalidated' if repair else 'inconsistent'} ({time.monotonic() - started:.2f}s).", flush=True)
