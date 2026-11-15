#!/usr/bin/env python3
"""Small synthetic checks only; never reads any real project build directory."""

import ast
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
HELPER = HERE / "1034-pre-guard-assess.py"
GUARD = ROOT / "conaled/scripts/lake_integrity.py"


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    ast.parse(HELPER.read_text())
    helper = load(HELPER, "assessment_fixture_helper")
    guard = load(GUARD, "assessment_fixture_guard")
    tests = []

    def checked(name, condition):
        if not condition:
            raise AssertionError(name)
        tests.append({"name": name, "result": "passed"})

    with tempfile.TemporaryDirectory(prefix="1034-assessment-fixture-", dir=HERE) as directory:
        fixture = Path(directory) / "candidate"
        copied = Path(directory) / "evidence"
        fixture.mkdir()
        copied.mkdir()

        def put(relative, value=b"fixture bytes\n"):
            path = fixture / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
            return path

        def family(module):
            stem = module.replace(".", "/")
            for extension in helper.LIB[:-1]:
                put(f"{helper.TREES[0]}/{stem}.{extension}")
            put(f"{helper.TREES[1]}/{stem}.c")
            outputs = {"m": True, "o": ["0" * 16 + "." + suffix for suffix in
                       ("olean", "olean.server", "olean.private")],
                       "i": "0" * 16 + ".ilean", "c": "0" * 16 + ".c",
                       "rs": "0" * 16 + ".ir.sig", "r": "0" * 16 + ".ir"}
            put(f"{helper.TREES[0]}/{stem}.trace",
                json.dumps({"schemaVersion": "2025-09-10", "outputs": outputs}).encode())
            put(f"{helper.TREES[1]}/{stem}.setup.json", b'{"fixture":true}\n')

        modules = {name: name.replace(".", "/") + ".lean" for name in helper.KNOWN}
        modules.update({"ProofAudit": "ProofAudit.lean", "Loose.Raw": "Loose/Raw.lean", "Foo.Bar": "Foo/Bar.lean"})
        for module in helper.KNOWN[:3]:
            family(module)
        family("ProofAudit")
        family("Old.Ghost")
        family("Foo.Bar")
        put(".lake/build/lib/lean/.Foo.olean")
        put(".lake/build/lib/lean/.olean")
        put(".lake/build/ir/ProofAudit.trace", b"misplaced trace")
        put(".lake/build/lib/lean/Foo.Bar.trace", b"noncanonical flat trace")
        put(".lake/build/lib/lean/Loose/Raw.olean")
        put(".lake/build/ir/Loose/Raw.bc.hash", b"sidecar with missing base")
        put(".lake/build/lib/lean/Loose/unknown.blob")
        put(".lake/build/ir/Applications/Resources/BoundedSummary.ltar", b"surplus")
        put(".lake/build/lib/lean/Applications/Resources/BoundedSummary.olean.private.hash")
        inventory = {}
        helper.scan(fixture, 1000, inventory)
        before = {path: (item, helper.sha(fixture / path) if item["kind"] == "file" else None)
                  for path, item in inventory.items()}
        observations, families, mapped = helper.classify(fixture, inventory, modules, guard)
        reasons = {(item["module"], item["observation"]) for item in observations}
        checked("module-prefix orphan retained", ("Old.Ghost", "module_absent_from_integrated_sources") in reasons)
        checked("ProofAudit not mislabeled an orphan", ("ProofAudit", "module_absent_from_integrated_sources") not in reasons)
        checked("untraced output retained", ("Loose.Raw", "member_without_regular_trace") in reasons)
        checked("orphan sidecar retained", ("Loose.Raw", "sidecar_without_regular_base_file") in reasons)
        checked("surplus artifact retained", (helper.KNOWN[0], "output_not_described_by_usable_trace") in reasons)
        checked("unrecognized file retained", (None, "unrecognized_file") in reasons)
        checked("empty and absolute-like module names remain raw unrecognized files", all(
            mapped[path] is None for path in (".lake/build/lib/lean/.Foo.olean", ".lake/build/lib/lean/.olean")))
        checked("noncanonical trace locations selected", all(
            (module, "member_at_noncanonical_path") in reasons for module in ("ProofAudit", "Foo.Bar")))
        checked("compound sidecar suffix maps correctly", helper.member(
            ".lake/build/lib/lean/Applications/Resources/BoundedSummary.olean.private.hash") ==
            (helper.KNOWN[0], "olean.private", True))
        checked("absent historical family has explicit missing members", all(
            path not in inventory for path in helper.family_paths(helper.KNOWN[3])))
        selected = set(helper.KNOWN) | set(families)
        selected_paths = [path for path, module in mapped.items() if module is None or module in selected]
        state = {"copies": [], "copied_bytes": 0}
        for relative in selected_paths:
            helper.copy_raw(fixture / relative, copied / relative, state, 1024 * 1024)
        checked("known consistent family setup captured", any(
            item["source"].endswith("Examples/BoundedSummary.setup.json") for item in state["copies"]))
        checked("raw source/copy digests agree", all(
            item["source_read_sha256"] == item["copy_sha256"] and not item["observed_changed"]
            for item in state["copies"]))
        after_inventory = {}
        helper.scan(fixture, 1000, after_inventory)
        after = {path: (item, helper.sha(fixture / path) if item["kind"] == "file" else None)
                 for path, item in after_inventory.items()}
        checked("synthetic source tree bytes and non-atime metadata unchanged", before == after)
        try:
            helper.scan(fixture, 2, {})
        except RuntimeError:
            tests.append({"name": "inventory budget fails explicitly", "result": "passed"})
        else:
            raise AssertionError("inventory budget did not fail")
        try:
            helper.copy_raw(fixture / selected_paths[0], copied / "budget-test",
                            {"copies": [], "copied_bytes": 0}, 1)
        except RuntimeError:
            tests.append({"name": "copy budget fails before oversized copy", "result": "passed"})
        else:
            raise AssertionError("copy budget did not fail")
        link = fixture / ".lake/build/ir/external-link"
        link.symlink_to(copied, target_is_directory=True)
        linked = {}
        helper.scan(fixture, 1000, linked)
        checked("directory symlink recorded without traversal", linked[
            ".lake/build/ir/external-link"]["kind"] == "symlink" and not any(
                path.startswith(".lake/build/ir/external-link/") for path in linked))
        try:
            helper.copy_raw(link, copied / "link-copy", {"copies": [], "copied_bytes": 0}, 1024)
        except RuntimeError:
            tests.append({"name": "symlink raw copy refused", "result": "passed"})
        else:
            raise AssertionError("symlink copy not refused")
        old_tmp = os.environ.get("TMPDIR")
        old_cached_tmp = tempfile.tempdir
        try:
            env = helper.assessment_environment(copied)
            with tempfile.TemporaryDirectory(prefix="guard-temp-fixture-") as temporary:
                checked("process and child temporary paths stay in evidence", Path(temporary).parent == copied / "tmp"
                        and env["TMPDIR"] == str(copied / "tmp"))
        finally:
            tempfile.tempdir = old_cached_tmp
            if old_tmp is None:
                os.environ.pop("TMPDIR", None)
            else:
                os.environ["TMPDIR"] = old_tmp
        approved_packages = Path(directory) / "shared/.lake/packages"
        approved_packages.mkdir(parents=True)
        local_packages = fixture / ".lake/packages"
        local_packages.mkdir()
        package_names = ("mathlib", "plausible", "LeanSearchClient", "importGraph",
                         "proofwidgets", "aesop", "Qq", "batteries", "Cli")
        manifest = {"packagesDir": ".lake/packages", "packages": [
            {"name": name, "type": "git", "rev": "0" * 40} for name in package_names]}
        for name in package_names:
            (approved_packages / name).mkdir()
            (local_packages / name).symlink_to(approved_packages / name, target_is_directory=True)
        bindings = helper.dependency_paths(fixture, approved_packages, manifest)
        checked("all nine exact shared dependency links allowed", set(bindings) == set(package_names)
                and all(item["resolved_path"] == str(approved_packages / name)
                        for name, item in bindings.items()))
        outside = Path(directory) / "wrong-shared-root/mathlib"
        outside.mkdir(parents=True)
        for target, description in (
                (outside, "dependency link outside approved root rejected"),
                (approved_packages / "plausible", "wrong same-root package target rejected")):
            link = local_packages / "mathlib"
            link.unlink()
            link.symlink_to(target, target_is_directory=True)
            try:
                helper.dependency_paths(fixture, approved_packages, manifest)
            except RuntimeError:
                tests.append({"name": description, "result": "passed"})
            else:
                raise AssertionError(description)
    timeout_version = subprocess.run(["/usr/bin/timeout", "--version"],
                                     capture_output=True, text=True, check=True).stdout
    bounded = subprocess.run(["/usr/bin/timeout", "--signal=TERM", "--kill-after=0.2s", "0.2s",
                              sys.executable, "-B", "-c", "import time; time.sleep(30)"],
                             capture_output=True, text=True, timeout=5)
    checked("owned synthetic timeout retains actual 124", bounded.returncode == 124)
    output = {"recorded_utc": datetime.now(timezone.utc).isoformat(), "kind": "synthetic_preparation_checks",
              "helper_sha256": helper.sha(HELPER), "guard_sha256": helper.sha(GUARD),
              "test_source_sha256": helper.sha(Path(__file__)), "python": sys.version,
              "timeout": {"path": "/usr/bin/timeout", "sha256": helper.sha(Path("/usr/bin/timeout")),
                          "version": timeout_version, "fixture_returncode": bounded.returncode},
              "tests": tests, "real_artifact_inspector_executed": False,
              "real_project_output_directories_accessed": False, "formal_acceptance": False,
              "scope_limit": "Fixture inventory/parser/copy/budgets/temp policy, exact shared dependency-link routing, and one owned timeout only; no Lean invocation, real dependency inspection, or end-to-end candidate assessment."}
    helper.save(HERE / "1034-pre-guard-helper-checks.json", output)
    print(json.dumps({"synthetic_checks": len(tests), "result": "passed", "formal_acceptance": False}))


if __name__ == "__main__":
    main()
