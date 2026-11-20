#!/usr/bin/env python3
"""Capture and verify the missing R2 runtime evidence; never run a whole proof check."""
import argparse
import ast
import datetime
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import struct
import subprocess
import sys
import time
import traceback

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

CANDIDATE = "99a2974c93e556088af814f033540eb36ba2d3a6"
TREE = "173003db476a73783a873897bb754ca941d2f9c8"
COMPILER_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
DIRECT = ["lake", "env", "lean", "--run", "scripts/ExtractSearchTree.lean"]
NATIVE = [".lake/build/bin/extract-searchtree"]
HARNESS = "scripts/test-extract-searchtree.py"
SELECTED_C = [
    "ExtractSearchTree", "Examples/ExtractedPrograms", "Examples/ExtractedTrees",
    "Examples/InsertionSorting", "Applications/Sorting/DecodedInsertion",
    "Applications/Sorting/SourceSelection", "Applications/Representations/SignedComparison",
    "Applications/Representations/DecodedBinomialQueue", "Applications/Search/OrderedMap/Basic",
    "Applications/Search/OrderedMap/Interface", "Applications/Search/OrderedMap/DecodedKeys",
    "Applications/Search/OrderedMap/DecodedKeysModels", "Applications/Search/OrderedMap/Enumeration",
    "Applications/Search/OrderedMap/Workload", "Applications/Trees/Observations",
    "Applications/Search/RedBlack/Basic", "Applications/Search/RedBlack/Models",
    "Applications/Search/RedBlack/Shape", "Applications/Search/RedBlack/Observations",
    "Applications/Search/BinomialQueue/Core", "Applications/Search/BinomialQueue/Contents",
    "Applications/Search/ListMaximumQueue",
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n").encode()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(encoded(value))


def load(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"duplicate metadata member {key}: {path}")
            result[key] = value
        return result
    return json.loads(path.read_bytes(), object_pairs_hook=unique,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def descriptor(path):
    info = path.lstat()
    mode = stat.S_IMODE(info.st_mode)
    if stat.S_ISLNK(info.st_mode):
        target = os.readlink(path)
        require(path.is_file(), f"unresolved or directory artifact symlink: {path}")
        return {"type": "symlink", "mode": mode, "target": target,
                "resolved": str(path.resolve()), "content": descriptor(path.resolve())}
    require(stat.S_ISREG(info.st_mode), f"not an ordinary file: {path}")
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    return {"type": "file", "mode": mode, "bytes": info.st_size, "sha256": digest}


def inventory(root):
    require(root.is_dir() and not root.is_symlink(), f"ordinary artifact root required: {root}")
    result = {}
    for folder, dirs, files in os.walk(root, followlinks=False):
        for name in list(dirs):
            p = Path(folder) / name
            if p.is_symlink():
                result[str(p.relative_to(root))] = descriptor(p)
                dirs.remove(name)
        for name in files:
            p = Path(folder) / name
            result[str(p.relative_to(root))] = descriptor(p)
    return dict(sorted(result.items()))


def probe(argv, cwd, env):
    result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, check=False)
    require(result.returncode == 0, f"identity probe failed {argv!r}: {result.stderr.decode(errors='replace')}")
    return result.stdout.decode().strip()


def git(repo, env, *args):
    return probe(["git", "-c", "gc.auto=0", "-c", "maintenance.auto=false",
                  "-c", "core.fsmonitor=false", "-C", str(repo), *args], repo, env)


def source_state(repo, env):
    def one(root, expected):
        require(git(root, env, "rev-parse", "HEAD") == expected, f"wrong source revision: {root}")
        require(not git(root, env, "status", "--porcelain=v1", "--untracked-files=all"),
                f"dirty source checkout: {root}")
        paths = git(root, env, "ls-files", "-z").split("\0")
        return {"commit": expected, "tree": git(root, env, "rev-parse", "HEAD^{tree}"),
                "files": {name: descriptor(root / name) for name in paths if name}}
    current = one(repo, CANDIDATE)
    require(current["tree"] == TREE, "R2 tree changed")
    manifest = load(repo / "lake-manifest.json")
    require(manifest["packagesDir"] == ".lake/packages", "unexpected packages directory")
    dependencies = {}
    for package in manifest["packages"]:
        require(package["type"] == "git" and not package.get("subDir"), "unsupported dependency layout")
        dependencies[package["name"]] = one(repo / ".lake/packages" / package["name"], package["rev"])
    require(len(dependencies) == 9, "R2 dependency count changed")
    compiler = probe(["lean", "--version"], repo, env)
    require("version 4.35.0," in compiler and COMPILER_COMMIT in compiler, "compiler pin mismatch")
    require((repo / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0", "toolchain pin mismatch")
    prefix = Path(probe(["lean", "--print-prefix"], repo, env)).resolve()
    return {"project": current, "dependencies": dependencies, "compiler": compiler,
            "toolchain_prefix": str(prefix), "validator": descriptor(Path(__file__).resolve()),
            "python_executable": str(Path(sys.executable).resolve()),
            "python_identity": descriptor(Path(sys.executable).resolve()), "python_version": sys.version}


def runtime_state(repo, env, linkage):
    sources = source_state(repo, env)
    roots = {"project": repo / ".lake/build"}
    for name in sources["dependencies"]:
        path = repo / ".lake/packages" / name / ".lake/build"
        if path.exists():
            roots["dependency/" + name] = path
    prefix = Path(sources["toolchain_prefix"])
    roots.update({"toolchain/bin": prefix / "bin", "toolchain/lib": prefix / "lib"})
    artifacts = {name: inventory(path) for name, path in roots.items()}
    dynamic = {path: descriptor(Path(path)) for path in linkage}
    return {"sources": sources, "artifacts": artifacts, "dynamic_libraries": dynamic}


def command(repo, out, label, argv, env, additions=None):
    folder = out / "commands"
    folder.mkdir(exist_ok=True)
    require(re.fullmatch(r"[a-zA-Z0-9_.-]+", label), "bad command label")
    record = {"command": argv, "cwd": str(repo), "environment_additions": additions or {}, "started_utc": utc()}
    save(folder / (label + ".started.json"), record)
    print(f"CONALED_RUNTIME_START stage={label} at={record['started_utc']}", flush=True)
    clock = time.monotonic()
    stdout, stderr = folder / (label + ".stdout"), folder / (label + ".stderr")
    with stdout.open("xb") as output, stderr.open("xb") as errors:
        result = subprocess.run(argv, cwd=repo, env=env | (additions or {}), stdout=output, stderr=errors, check=False)
    record.update(returncode=result.returncode, seconds=time.monotonic() - clock,
                  completed_utc=utc(), stdout=descriptor(stdout), stderr=descriptor(stderr))
    save(folder / (label + ".json"), record)
    print(f"CONALED_RUNTIME_EXIT stage={label} exit_code={result.returncode} seconds={record['seconds']:.6f}", flush=True)
    require(result.returncode == 0, f"{label} exited {result.returncode}; full streams retained")
    return record


class JNumber(str):
    pass


class JObject(list):
    pass


def replace_paths(data, mapping):
    for source, replacement in sorted(mapping.items(), key=lambda item: len(item[0]), reverse=True):
        data = data.replace(source.encode(), replacement.encode())
    return data


def semantic(data, mapping):
    """Preserve duplicate members, number lexemes, arrays and invalid timing mutations."""
    try:
        value = json.loads(data.decode("utf-8"), object_pairs_hook=JObject,
                           parse_int=JNumber, parse_float=JNumber, parse_constant=JNumber)
    except (ValueError, UnicodeError):
        return ["raw-bytes", replace_paths(data, mapping).hex()]

    def visit(node):
        if isinstance(node, JObject):
            fields = []
            for key, child in node:
                if key == "elapsedNs" and type(child) is JNumber and re.fullmatch(r"0|[1-9][0-9]*", child):
                    fields.append([key, ["nonnegative-integer-elapsedNs"]])
                else:
                    fields.append([key, visit(child)])
            return ["object", fields]
        if type(node) is list:
            return ["array", [visit(child) for child in node]]
        if type(node) is JNumber:
            return ["number", str(node)]
        if type(node) is str:
            return ["string", replace_paths(node.encode(), mapping).decode()]
        if type(node) is bool:
            return ["boolean", node]
        require(node is None, "unknown JSON value")
        return ["null"]
    return visit(value)


def invocation_records(out, mode, plan):
    expected_tests = plan["expected_tests"]
    folder = out / mode
    records, referenced = {}, set()
    for path in sorted(folder.glob("*.json")):
        meta = load(path)
        require(set(meta) == {"kind", "test", "invocation", "command", "arguments", "returncode",
                             "started_utc", "seconds", "stdout_file", "stdout_sha256", "stderr_file",
                             "stderr_sha256", "input_files"}, f"unexpected invocation metadata: {path}")
        key = (meta["test"], meta["invocation"])
        require(key not in records and type(key[1]) is int and key[1] > 0, "duplicate or bad invocation")
        require(meta["test"] in expected_tests, "unrecognized test invocation")
        require(type(meta["returncode"]) is int and type(meta["seconds"]) in (float, int)
                and math.isfinite(meta["seconds"]) and meta["seconds"] >= 0, "bad invocation outcome")
        require(datetime.datetime.fromisoformat(meta["started_utc"]).tzinfo is not None, "unqualified start time")
        prefix = DIRECT if mode == "direct" else NATIVE
        if meta["kind"] == "driver":
            require(meta["command"] == prefix + meta["arguments"], "incorrect driver launch argv")
        else:
            require(meta["kind"] == "observer" and len(meta["command"]) >= 3
                    and meta["command"][0] == plan["python_executable"]
                    and meta["command"][1] == "-B"
                    and meta["command"][2] in (HARNESS, plan["harness_path"])
                    and meta["command"][3:] == meta["arguments"],
                    "incorrect independent observer launch argv")
            require(Path(meta["command"][0]).is_absolute(), "observer Python must have an absolute identity")
        referenced.add(path.name)

        def retained(name, digest, length=None):
            require(type(name) is str and Path(name).name == name, "unsafe retained filename")
            p = folder / name
            require(p.is_file() and not p.is_symlink(), "missing or symlinked retained input/output")
            data = p.read_bytes()
            require(sha(data) == digest and (length is None or len(data) == length), "retained bytes changed")
            referenced.add(name)
            return data

        stdout = retained(meta["stdout_file"], meta["stdout_sha256"])
        stderr = retained(meta["stderr_file"], meta["stderr_sha256"])
        arguments = meta["arguments"]
        if meta["kind"] == "observer":
            require(len(arguments) == 2 and arguments[0] == "--check-receipt", "unexpected observer arguments")
            expected_inputs = [("--check-receipt", arguments[1])]
        else:
            expected_inputs = [(flag, arguments[index + 1]) for index, flag in enumerate(arguments[:-1])
                               if flag in ("--inserted-file", "--queries-file", "--keys-file")]
        require([(item["option"], item["path"]) for item in meta["input_files"]] == expected_inputs,
                "input identities do not cover exactly the invocation file arguments")
        inputs = []
        for item in meta["input_files"]:
            if item.get("missing") is True:
                require(set(item) == {"option", "path", "missing"}, "bad missing-input identity")
                data = None
            else:
                require(set(item) == {"option", "path", "bytes", "sha256", "retained_file"}, "bad input identity")
                data = retained(item["retained_file"], item["sha256"], item["bytes"])
            inputs.append((item, data))
        records[key] = (meta, stdout, stderr, inputs)
    require(set(p.name for p in folder.iterdir()) == referenced, f"unaccounted {mode} invocation artifacts")
    require({key[0] for key in records} == set(expected_tests), "test coverage differs from the complete source harness")
    for name in expected_tests:
        numbers = sorted(number for test, number in records if test == name)
        require(numbers == list(range(1, len(numbers) + 1)), "nonconsecutive invocation numbering")
    return records


def compare(out):
    plan = load(out / "plan.json")
    expected = plan["expected_tests"]
    direct, native = [invocation_records(out, mode, plan) for mode in ("direct", "standalone")]
    require(set(direct) == set(native), "launch modes have different invocation sets")
    pairs, reverse, parent_pairs, parent_reverse, exact_parent_bindings, evidence = {}, {}, {}, {}, set(), []
    for key in sorted(direct):
        left, right = direct[key], native[key]
        require(len(left[3]) == len(right[3]), "input-file lists differ")
        for (a, da), (b, db) in zip(left[3], right[3]):
            require(a["option"] == b["option"] and (da is None) == (db is None), "input roles or absence differ")
            pa, pb = a["path"], b["path"]
            require(pairs.get(pa, pb) == pb and reverse.get(pb, pa) == pa, "inconsistent paired fixture paths")
            pairs[pa], reverse[pb] = pb, pa
            parent_a, parent_b = str(Path(pa).parent), str(Path(pb).parent)
            require(parent_pairs.get((key[0], parent_a), parent_b) == parent_b
                    and parent_reverse.get((key[0], parent_b), parent_a) == parent_a,
                    "fixture parent mapping changed within the test")
            parent_pairs[key[0], parent_a], parent_reverse[key[0], parent_b] = parent_b, parent_a
            if da is not None and da == db:
                exact_parent_bindings.add((key[0], parent_a, parent_b))
                evidence.append({"test": key[0], "invocation": key[1], "option": a["option"],
                                 "left": pa, "right": pb, "bytes": len(da), "sha256": sha(da)})
            if left[0]["kind"] == "driver":
                require(da == db, "actual replay file bytes differ between launch modes")
    mappings = [{}, {}]
    for index, (pa, pb) in enumerate(sorted(pairs.items())):
        if pa != pb:
            require(Path(pa).is_absolute() and Path(pb).is_absolute() and Path(pa).name == Path(pb).name,
                    "differing paths are not paired temporary fixture names")
            mappings[0][pa] = mappings[1][pb] = f"@retained-fixture-{index:04d}/{Path(pa).name}"
    comparisons, missing = [], []
    for key in sorted(direct):
        left, right = direct[key], native[key]
        ma, mb = left[0], right[0]
        require(all(ma[field] == mb[field] for field in ("kind", "test", "invocation", "returncode")),
                f"invocation identity or exit differs: {key}")
        if ma["kind"] == "observer":
            require(ma["command"][:3] == mb["command"][:3], "observer interpreter/script identities differ")
        aa = [replace_paths(arg.encode(), mappings[0]).decode() for arg in ma["arguments"]]
        ab = [replace_paths(arg.encode(), mappings[1]).decode() for arg in mb["arguments"]]
        require(aa == ab, f"command arguments differ: {key}")
        for (a, da), (b, db) in zip(left[3], right[3]):
            if da is None:
                if a["path"] != b["path"]:
                    parents = (str(Path(a["path"]).parent), str(Path(b["path"]).parent))
                    require((key[0], *parents) in exact_parent_bindings,
                            f"missing-file path lacks a directory binding from actual identical fixture bytes: {key}")
                    missing.append({"test": key[0], "invocation": key[1], "left": a["path"],
                                    "right": b["path"], "parents": list(parents),
                                    "basis": "actual equal-byte earlier or sibling fixture from this same test"})
            elif ma["kind"] == "observer":
                require(semantic(da, mappings[0]) == semantic(db, mappings[1]), f"observer inputs differ: {key}")
        sa, sb = semantic(left[1], mappings[0]), semantic(right[1], mappings[1])
        require(sa == sb, f"complete stdout semantic output differs: {key}")
        ea, eb = replace_paths(left[2], mappings[0]), replace_paths(right[2], mappings[1])
        require(ea == eb, f"complete stderr differs: {key}")
        comparisons.append({"test": key[0], "invocation": key[1], "kind": ma["kind"],
                            "returncode": ma["returncode"], "stdout_semantic_sha256": sha(encoded(sa)),
                            "stderr_normalized_sha256": sha(ea)})
    return {"result": "passed", "tests_per_mode": len(expected), "invocations_per_mode": len(comparisons),
            "driver_invocations_per_mode": sum(item["kind"] == "driver" for item in comparisons),
            "observer_invocations_per_mode": sum(item["kind"] == "observer" for item in comparisons),
            "normalization": ["nonnegative integer elapsedNs values only; invalid timing mutations remain exact",
                              "explicit recorded paired input-file paths after full input comparison",
                              "absent fixture basenames only in directories bound by actual identical retained bytes from this test"],
            "equal_byte_directory_bindings": evidence, "absent_path_bindings": missing,
            "comparisons": comparisons}


def selected_generated(repo, out, env):
    generated = out / "generated"
    paths = [".lake/build/ir/" + name + ".c" for name in SELECTED_C]
    paths.append(".lake/packages/mathlib/.lake/build/ir/Mathlib/Data/List/Sort.c")
    historical = dict(re.findall(r"\| `([^`]+\.c)` \| [0-9]+ \| `([0-9a-f]{64})` \|",
                                 (repo / "docs/research/vfa-extract-runtime.md").read_text()))
    records = []
    for name in paths:
        path = repo / name
        require(path.is_file() and not path.is_symlink(), f"selected generated C is absent: {name}")
        destination = generated / name.removeprefix(".lake/")
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
        current = descriptor(path)
        require(sha(destination.read_bytes()) == current["sha256"], "generated C copy changed")
        records.append({"source": name, "retained": str(destination.relative_to(out)), "identity": current,
                        "historical_ctb91_sha256": historical.get(name),
                        "historical_hash_equal": historical.get(name) == current["sha256"] if name in historical else None})
    exe = repo / NATIVE[0]
    with exe.open("rb") as stream:
        header = stream.read(64)
    require(header[:6] == b"\x7fELF\x02\x01" and struct.unpack_from("<H", header, 18)[0] == 62,
            "standalone target is not a little-endian x86-64 native ELF")
    for label, argv in [("native-file", ["file", str(exe)]), ("native-header", ["readelf", "-h", str(exe)]),
                        ("native-dynamic", ["readelf", "-d", str(exe)]),
                        ("native-symbols", ["nm", "--defined-only", str(exe)]),
                        ("native-linkage", ["ldd", str(exe)])]:
        command(repo, out, label, argv, env)
    symbols = (out / "commands/native-symbols.stdout").read_text().splitlines()
    selected = sorted({line.split()[-1] for line in symbols if line.split() and
                       (re.search(r"SignedComparison_int64(Ltb|Leb)___boxed$", line.split()[-1])
                        or line.split()[-1] in ("l_BitVec_slt", "l_IO_lazyPure___redArg"))})
    require(selected, "no selected native comparator/thunk symbols found")
    for index, symbol in enumerate(selected):
        command(repo, out, f"native-disassembly-{index:02d}", ["objdump", "-d", "--disassemble=" + symbol, str(exe)], env)
    linkage_text = (out / "commands/native-linkage.stdout").read_text()
    require("not found" not in linkage_text, "unresolved native shared library")
    linkage = sorted(set(re.findall(r"(?:=>\s+|^\s*)(/[^\s()]+)", linkage_text, re.MULTILINE)))
    require(linkage, "native dynamic-library identity list is empty")
    result = {"selected_generated_c": records, "native_executable": descriptor(exe),
              "elf_header_hex": header.hex(), "native_selected_disassembly_symbols": selected,
              "dynamic_library_paths": linkage,
              "assessment": "Retained bytes and concrete disassembly for independent affected-code assessment; no compiler correctness or unchanged code semantics inferred from names/hashes."}
    save(out / "generated-identities.json", result)
    return linkage


def evidence_files(out):
    excluded = {"result.json", "readback.json", "evidence-manifest.json", "failure.json"}
    result = {}
    for path in sorted(out.rglob("*")):
        if path.is_file() and path.relative_to(out).as_posix() not in excluded:
            require(not path.is_symlink(), "symlink in retained evidence")
            result[str(path.relative_to(out))] = descriptor(path)
    return result


def run(repo, out, env):
    require(not list(out.iterdir()), "runtime output directory must be empty")
    before_source = source_state(repo, env)
    methods = []
    for node in ast.parse((repo / HARNESS).read_text()).body:
        if isinstance(node, ast.ClassDef) and node.name in ("ExtractRuntime", "BinomialRuntime"):
            methods.extend("__main__." + node.name + "." + child.name for child in node.body
                           if isinstance(child, ast.FunctionDef) and child.name.startswith("test_"))
    require(len(methods) == len(set(methods)) == 55, "the pinned complete harness is not 55 tests")
    save(out / "plan.json", {"candidate": CANDIDATE, "tree": TREE, "expected_tests": sorted(methods),
                            "harness_path": str(repo / HARNESS), "python_executable": sys.executable,
                            "direct_argv": DIRECT, "standalone_argv": NATIVE,
                            "host": {"platform": platform.platform(), "machine": platform.machine(),
                                     "uname": list(platform.uname()), "python": sys.version,
                                     "python_executable": sys.executable},
                            "whole_check": "Reused from separate successful exact-R2 CI; this script does not perform or forge a whole-library check."})
    shutil.copyfile(Path(__file__).resolve(), out / "validation-driver.py")
    build = command(repo, out, "standalone-build", ["lake", "--no-cache", "--rehash", "build", "extract-searchtree"], env)
    require(source_state(repo, env) == before_source, "source/dependency/compiler identities changed during target build")
    save(out / "build-source-readback.json", {"before_sha256": sha(encoded(before_source)),
                                             "after_sha256": sha(encoded(before_source)), "equal": True})
    linkage = selected_generated(repo, out, env)
    before = runtime_state(repo, env, linkage)
    save(out / "runtime-inputs-before.json", before)
    mode_results = {}
    temporary = out / "temporary-inputs"
    temporary.mkdir()
    for mode, argv in (("direct", DIRECT), ("standalone", NATIVE)):
        (out / mode).mkdir()
        additions = {"EXTRACT_TEST_LOG_DIR": str(out / mode), "EXTRACT_TEST_COMMAND_JSON": json.dumps(argv),
                     "TMPDIR": str(temporary)}
        record = command(repo, out, mode + "-full-harness", [sys.executable, "-B", HARNESS, "-v"], env, additions)
        stderr = (out / "commands" / (mode + "-full-harness.stderr")).read_text()
        require(re.search(r"^Ran 55 tests in [0-9.]+s$", stderr, re.MULTILINE)
                and re.search(r"^OK$", stderr, re.MULTILINE) and "skipped" not in stderr.lower(),
                f"{mode} did not report the complete 55-test success without skips")
        mode_results[mode] = {"tests": 55, "skipped": 0, "seconds": record["seconds"], "exit": 0}
    require(not list(temporary.iterdir()), "harness temporary fixture cleanup was incomplete")
    temporary.rmdir()
    after = runtime_state(repo, env, linkage)
    if after != before:
        save(out / "runtime-inputs-mismatch.json", after)
        raise ValueError("source, compiler, dependency or runtime artifact identities changed during observations")
    save(out / "runtime-inputs-after.json", {"identical": True, "before_sha256": sha(encoded(before)),
                                           "after_sha256": sha(encoded(after)), "checked_utc": utc()})
    comparison = compare(out)
    save(out / "comparison.json", comparison)
    manifest = evidence_files(out)
    save(out / "evidence-manifest.json", manifest)
    result = {"result": "passed", "candidate": CANDIDATE, "tree": TREE, "completed_utc": utc(),
              "standalone_build_seconds": build["seconds"], "modes": mode_results,
              "input_snapshot_sha256": sha(encoded(before)), "comparison_sha256": sha(encoded(comparison)),
              "evidence_manifest_sha256": sha(encoded(manifest)), "evidence_files": len(manifest),
              "generated_assessment": "Independent affected-code assessment remains a separate review input.",
              "whole_library_reexecuted": False}
    save(out / "result.json", result)
    print(json.dumps(result, sort_keys=True), flush=True)


def verify(repo, out, env):
    require(not (out / "failure.json").exists(), "capture recorded an actual failure; no successful readback is available")
    result = load(out / "result.json")
    require(result["result"] == "passed" and result["candidate"] == CANDIDATE and result["tree"] == TREE,
            "no successful exact-R2 runtime record")
    manifest = load(out / "evidence-manifest.json")
    require(sha(encoded(manifest)) == result["evidence_manifest_sha256"], "evidence manifest identity changed")
    require(evidence_files(out) == manifest, "retained runtime evidence bytes or inventory changed")
    before = load(out / "runtime-inputs-before.json")
    require(sha(encoded(before)) == result["input_snapshot_sha256"], "input snapshot identity changed")
    linkage = load(out / "generated-identities.json")["dynamic_library_paths"]
    require(runtime_state(repo, env, linkage) == before, "nonrepairing source/artifact readback differs")
    comparison = compare(out)
    require(comparison == load(out / "comparison.json") and sha(encoded(comparison)) == result["comparison_sha256"],
            "retained semantic comparison differs")
    readback = {"result": "passed", "candidate": CANDIDATE, "tree": TREE, "verified_utc": utc(),
                "runtime_result_sha256": sha((out / "result.json").read_bytes()),
                "input_snapshot_sha256": result["input_snapshot_sha256"],
                "evidence_manifest_sha256": result["evidence_manifest_sha256"],
                "comparison_sha256": result["comparison_sha256"], "commands_rerun": [],
                "identity_probes_only": "Git status/revision, compiler version/prefix, byte hashing; no build, harness, driver workload or proof audit."}
    save(out / "readback.json", readback)
    print(json.dumps(readback, sort_keys=True), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("run", "verify", "compare"))
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--candidate", default=CANDIDATE)
    args = parser.parse_args()
    require(args.candidate == CANDIDATE, "this validation method is pinned to reviewed R2")
    out = args.out.resolve()
    require(out.is_dir() and not out.is_symlink(), "ordinary existing output directory required")
    if args.operation == "compare":
        print(json.dumps(compare(out), sort_keys=True))
        return
    require(args.repo is not None, "--repo required")
    repo = args.repo.resolve()
    require(not out.is_relative_to(repo), "keep evidence outside the candidate checkout")
    env = os.environ.copy()
    for name in ("LEAN_PATH", "EXTRACT_TEST_COMMAND_JSON", "EXTRACT_TEST_LOG_DIR"):
        env.pop(name, None)
    if args.operation == "run":
        require(not list(out.iterdir()), "runtime output directory must be empty")
        try:
            run(repo, out, env)
        except BaseException as error:
            if not (out / "failure.json").exists():
                save(out / "failure.json", {"result": "failed", "recorded_utc": utc(), "error": str(error),
                                           "traceback": traceback.format_exc(), "candidate": CANDIDATE})
            raise
    else:
        verify(repo, out, env)


if __name__ == "__main__":
    main()
