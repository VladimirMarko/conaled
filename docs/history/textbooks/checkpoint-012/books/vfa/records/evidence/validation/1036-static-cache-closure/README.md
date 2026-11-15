# Prospective static Mathlib cache inventory

Recorded during recovery task #1036 on 2026-11-04 UTC. This is source/metadata inventory and bounded command-path analysis only. It is not formal validation, artifact-integrity acceptance, a certified retention manifest, deletion authorization, or permission to change the active environment.

## Scope, identities, and retained inputs

The candidate is `c988f183887896c00b09aaff9077a6ea7fb8d68f`; Mathlib is `56a005855ea17e0b0958f73ec801ae140b0a1679`; the toolchain is `leanprover/lean4:v4.35.0` (recorded official compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). `inventory.json` records all nine exact dependency revisions/URLs, the project manifest hash, current source identities, and gate-script identities.

Paths used for this observation:

- `R`: `/workspace/scratch/60f07f0e98c8/restored/conaled-vfa-checkpoint-042-native-j1-validation-readiness`.
- `S`: `R/conaled`, the unchanged candidate source used for enumeration.
- `P`: `R/vfa-validation/.lake/packages`, the shared dependency store.
- `K`: `/workspace/scratch/60f07f0e98c8/restored/conaled-native-kit-4.35.0`, the unchanged supplied kit.
- `T`: `/workspace/scratch/60f07f0e98c8/native-state/toolchains/lean-4.35.0-linux/src/lean`, the official source accompanying the installed toolchain.

The current full fresh run uses a distinct clean worktree, `R/vfa-unified-pty-validation`, at the same candidate and with individual links to P. This inventory did not inspect or alter its private outputs and does not establish its terminal result. The earlier two fresh attempts have unknown terminal outcomes. No process-quiescence claim is made.

Retain the entire official toolchain and native profile/runtime; every non-Mathlib package output; all source checkouts/configurations; all local project artifacts and incident evidence; and all shared/native/other outputs outside the two Mathlib directories explicitly counted below. Nothing in this note authorizes removing any artifact.

## Reproduced result

| Mathlib group | Modules | Files | Logical bytes | Allocated bytes |
| --- | ---: | ---: | ---: | ---: |
| Inside static import closure | 3,525 | 52,875 | 3,055,645,721 | 3,226,292,224 |
| Outside static import closure | 5,100 | 76,500 | 3,527,532,722 | 3,774,812,160 |
| Total | 8,625 | 129,375 | 6,583,178,443 | 7,001,104,384 |

These counts and byte totals reproduced the prior read-only report exactly. The outside allocation is approximately 3.516 GiB; it is not a promise of reclaimed space or a safe-deletion estimate.

`outside-modules.txt` is UTF-8, lexicographically sorted, one module per LF-terminated line. Its SHA-256 is:

```text
2777539c1a2f3e5b64c0af1cb2bf2b71ff90ac148adf6f3ddacb5a4e45840522
```

The analogous inside-module list digest is `109cf637cb2c6b9e0f9694e5b21c2e9ec7aee977d54399ab7b5403b38982d16c`. It can be reproduced or obtained by subtracting the saved outside names from the pinned Mathlib source universe; no second bulky list is needed.

## Exact roots and graph method

`inventory.json` saves the complete root-name arrays, not only their counts:

1. All 954 integrated local modules: every root `S/*.lean`, plus every `.lean` recursively beneath `S/SquareKit`, `S/Applications`, and `S/Examples`. `ProofAudit` is included. Their parsed headers have 273 distinct direct external imports.
2. Explicit auxiliary roots: `Cache.Main`, `Lake.Build.Trace`, `Lean`, `Lean.DeclarationRange`, `Lean.Util.CollectAxioms`, and `Mathlib.Tactic.TypeStar`. This covers the hash helper, audit/regression core, setup smoke, and a conservative Cache CLI source root.
3. Every one of the 406 cached non-Mathlib modules, added conservatively even when not reached from the project. All non-Mathlib artifacts are retained independently of reachability.

The metadata universe has 9,031 `.ilean` modules: Mathlib 8,625; Batteries 195; Aesop 132; ImportGraph 35; Qq 14; Plausible 13; ProofWidgets 13; LeanSearchClient 4. Cli is the ninth pinned dependency repository and has no indexed `.ilean` in these directories. The Mathlib universe equals all 8,624 sources under `Mathlib/` plus `Mathlib.lean`.

Traverse source imports for the local roots, then version-5 `.ilean.directImports` for dependency modules. Validate the metadata module name and each `[name,bool,bool,bool]` tuple; include all flag combinations. Treat Init/Lean/Std/Lake imports as terminal core nodes because the entire official toolchain is retained. The traversal visits 3,931 `.ilean` files and uses source fallback for 18 Cache modules whose exact names/source hashes are recorded. No missing/ambiguous edge, unsupported local/fallback header, or source/metadata fingerprint change was observed.

Primary metadata semantics: `T/Lean/Server/References.lean:31-32` calls `headerToImports (includeInit := false)`; the Ilean structure uses version 5 at lines 208-212. `T/Lean/Elab/Frontend.lean:397` assigns `directImports := Server.collectImports`. Thus this is static header metadata, not a runtime loading trace. Implicit Init is omitted from that metadata and is retained by the whole-toolchain policy; explicit Init imports remain in the name comparison.

Source headers are read with a small fail-closed parser that removes nested comments and strings, recognizes ordinary/public/private/meta imports and `import all`, and rejects unsupported names or imports after the header. The complete parser and inventory routine appear below. It is not a substitute for executing Lean.

## Source-header cross-check

Actual comparison ran from `2026-11-04T02:51:01.352150+00:00` to `2026-11-04T02:51:19.069238+00:00` and parsed all **3,931** visited dependency source headers: 3,525 Mathlib plus all 406 cached non-Mathlib modules. It compared explicit imported module-name sets, included all source modifiers and all metadata flag combinations, and did not compare the flags themselves.

- Module-name mismatches: **0**.
- Missing source files: **0**.
- Unparsed headers: **0**.
- Observed source/metadata fingerprint changes during this comparison: **0**.
- All nine dependency HEAD observations match the saved pinned revisions.
- Neither side explicitly imports `Init` in this visited set. Implicit Init is separately retained by the complete-toolchain policy.

The source-header name-edge digest and metadata name-edge digest are both `e11d745ebf7060b00b0a473922e2bc2666b47b07ae7a65024c9aa255c8ab75c4`. The dependency source-byte record digest is `43f7efb1ca4adebade8a98cd35b9a91768309f6e7dfca871149dd3be10ce9e9a`. The visited metadata-byte record digest remains `d47cd67779cc6755e5ce837e59691b4753a7548acce255cb5de76d7539535b3a`, exactly matching the original inventory.

`inventory.json.dependency_source_cross_check` preserves the actual observations and their identities. The comparison did not change roots or smooth over any disagreement. This resolves the specific source-header versus ilean-name gap; it does not verify the actual olean/IR import tables or certify artifact provenance.

## Identities and artifact-family accounting

The JSON records canonical SHA-256 identities for the local source list, visited metadata bytes, static semantic graph, metadata/source universes, and per-module artifact-family allocation records. It records exact hashes of the Cache fallback sources and gate scripts. The earlier local-source digest using Python's default JSON formatting is preserved as `68c68cf61e71a79fcb7d0f069a3154efc42820067612435c1ea324770c413e30`; canonical compact JSON has its own separately named digest.

Metadata byte identity is for this observed installation. Recreated cache metadata may encode different non-semantic paths; compare both the byte identity and the separately recorded import-graph identity rather than silently declaring them equivalent. The cross-check does not decode `.olean` or `.ir` files or establish that every cached artifact was produced from these current sources.

The allocation scan covers only `P/mathlib/.lake/build/lib/lean` and `P/mathlib/.lake/build/ir`, attributing a file by its module stem to the exact source universe. Each module has 15 files: the olean/private/server families, ilean, IR/signature, their hashes, trace, and generated C/hash. `inventory.json` defines the suffix patterns, counts, and canonical family-record digest without a bulky per-file dump.

Allocated bytes are `st_blocks * 512`, deduplicated by `(st_dev,st_ino)`. No cross-group shared inode, external hardlink, symlink artifact, or unattributed file was observed. Artifact contents were not rehashed. Directory metadata, filesystem sharing/reflinks/overlay effects, concurrent writer exclusion, and guaranteed reclaimed-space semantics are not certified. The inventory records observed allocation, not future capacity availability.

## Exact remaining commands: bounded dynamic/native assessment

The source paths below were read without running any gate. They reveal no concrete dependency on an outside Mathlib family. They do reveal ancillary inputs retained by this inventory's policy.

| Command/path | Concrete observed dependency behavior |
| --- | --- |
| `./check.sh --candidate HEAD --fresh --jobs 1` | `S/scripts/check.py:70-79,281-325` invokes Lean on the 953 ordinary local sources and then ProofAudit, using private local outputs and package library paths. No plugin/dynlib flags are supplied. All 954 source modules are roots. |
| Unchanged pre-guard collector | `R/work-state/validation/1034-pre-guard-assess.py:73-87,325-350` inventories project output trees, checks tool versions, and calls `guard.inspect_outputs`; it does not inventory or hash the entire Mathlib cache. |
| Collector/guard hash helper | `S/scripts/lake_integrity.py:71-98` runs `lean --run scripts/lake-output-hashes.lean paths.json`; the helper imports only `Lake.Build.Trace` and treats the supplied project files as bytes. |
| Guarded `./check.sh --candidate HEAD` | `S/scripts/check.py:292-310` builds explicit `+Module` targets for every ordinary local module, then executes `lake env lean ProofAudit.lean`. |
| `env LAKE_ARTIFACT_CACHE=false lake --no-cache --rehash build +ProofAudit` | `T/lake/Lake/CLI/Build.lean:74` selects the module leanArts facet; `T/lake/Lake/Build/Module.lean:435,489-492` follows imported exportInfo/leanArts. The command does not request the Mathlib default library or umbrella target. |
| `lake env python3 scripts/test-proof-audit.py` | `S/scripts/test-proof-audit.py:17-46,58-74` generates Foreign, Applications.AuditProbe, and Audit. Their imports are Foreign, Applications.AuditProbe, ProofAudit, and implicit core. Managed local Applications artifacts and ProofAudit.olean are also required and retained. |
| `./check.sh --verify-candidate HEAD` | `S/scripts/check.py:223-232` compares candidate/dependency/compiler identities. Its incremental compiler-version query uses `lake env`, which still loads workspace configuration. |

`ProofAudit.auditProject` reads the current environment's module table/constants (`S/ProofAudit.lean:70-88,123-128`). `Lean.collectAxioms` reads environment extension summaries and current declarations (`T/Lean/Util/CollectAxioms.lean:101-154`); this path does not import additional modules or read their source files.

Actual ancillary inputs:

- **Lake configuration imports:** `T/lake/Lake/Load/Lean/Elab.lean:103-116` reads the cached configuration `.olean` and invokes `importModulesUsingCache` on its header. The two pinned Lean configuration sources, `P/mathlib/lakefile.lean` and `P/proofwidgets/lakefile.lean`, import only `Lake`; configuration artifacts are outside the counted directories and the whole toolchain is retained. Fallback configuration elaboration reads those same headers.
- **Conditional native expansion:** `T/lake/Lake/Build/Module.lean:130-166,583-592` can select whole imported libraries when native precompilation is requested. The root and nine pinned package configurations enable no precompileImports/precompileLibrary/plugins/dynlibs/external-library target affecting these module builds; Aesop explicitly disables precompileModules. Relevant default settings are false or empty in Lake's LeanConfig/LeanLibConfig/PackageConfig. No selected whole-Mathlib shared build was found.
- **ProofWidgets JS:** `P/proofwidgets/lakefile.lean:88-89` declares `needs := #[widgetJsAll]`; `T/lake/Lake/Build/Library.lean:163-169` follows library needs. Widget sources/configuration, generated JS, and its trace are non-import inputs. Mathlib's configuration sets errorOnBuild, so an unexpected required rebuild can refuse. All non-Mathlib sources and outputs remain retained.
- **Native runtime:** `K/lib/runtime.py:71-102,110-132` and `K/conaled_native.py:278-302,587-596` require the profile, shim, host loader, and official shared libraries. All remain outside the Mathlib-family inventory.

Mathlib's whole-cache retrieval is confined to the `post_update` hook in its `lakefile.lean:187-216`; these commands do not request an update, and Lake's updateDeps default is false. Future setup/update/cache commands can have different requirements and are not authorized or certified by this note.

Available generic APIs are not evidence of an invocation: ImportGraph's `#import_diff` and `Core.withImportModules` accept arbitrary module names, but the inspected exact gate bodies and integrated sources do not invoke them. `Mathlib.Init` makes ImportGraph tools available; importing their definitions does not by itself execute their bodies. The `readModuleData` text in Batteries.Util.Pickle is a historical comment; its actual API reads compacted data. No such call was found in the local gate paths. The global `Mathlib.Lean.CoreM` helper is outside this closure and was not a reached dynamic-loader callsite.

The independent native read-only trace also identified `Lean/Environment.lean`'s mkModuleData/mkIRData copying environment-header imports and importModulesCore following recorded module imports. Keeping every static flag edge is conservative for those import-name recursions. This source reading does not certify cached artifact contents or rule out every higher-order/native effect of tactics and initialization.

Operational source hashes checked directly:

- collector: `a2c40a0a4d786101442bfe923177e245b66b46e9c5bf5544dcbe00e766fb602c`.
- kit `conaled_native.py`: `9d1b1e6f10ae574e5c1f388d8df069f43c9ca3e1a993c372293595abd2e5090a`.
- kit `lib/runtime.py`: `e790d472353e8d9467d696d2b1f7ae245c731d61e90cbfbcc7a2a576ad4fd695`.
- official `Lean/Server/References.lean`: `dd50dee7b2e8443e1a435eaa3f2eb41335aee41ad45b47c98f9a409cd2d0bbc1`.
- official `Lean/Elab/Frontend.lean`: `423d17e49722e901e5f82bd4b86e7cf2dd80c352fc55b3d72ac1301a79ead634`.

## Reproduction

Run the following read-only Python on the same pinned source and restored dependency metadata. It writes only stdout and invokes Git only for read-only HEAD queries with optional locking disabled. It neither invokes Lean/Lake nor changes caches. Rebind the three directory arguments after recovery. Add `--outside` to emit the sorted outside list instead of JSON. The enclosing recovery tool must provision dependencies separately; this command is not a setup action.

Compare all root arrays, pins, list digests, graph/source/metadata identities, and totals. Timestamps and absolute observation paths naturally differ. Filesystem allocation may differ after restoration even when source/graph identities match. Unsupported/missing import edges abort graph construction; the source-header cross-check records discrepancies and does not rewrite the graph to conceal them.

```sh
python3 -B - \
  --source /path/to/restored/conaled \
  --packages /path/to/restored/vfa-validation/.lake/packages \
  --kit /path/to/restored/native-kit <<'PY'
from pathlib import Path
from collections import Counter, defaultdict, deque
import argparse, datetime, hashlib, json, os, re, subprocess

def sha(data):
    return hashlib.sha256(data).hexdigest()

def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()

def digest(value):
    return sha(canonical(value))

def strip_comments_strings(text):
    result = []
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; result.extend("  "); i += 2
            elif text.startswith("-/", i):
                depth -= 1; result.extend("  "); i += 2
            else:
                result.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            if text[i] == "\\":
                result.extend("  "); i += 2
            elif text[i] == '"':
                string = False; result.append(" "); i += 1
            else:
                result.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            result.extend(" " * (end - i)); i = end
        elif text.startswith("/-", i):
            depth = 1; result.extend("  "); i += 2
        elif text[i] == '"':
            string = True; result.append(" "); i += 1
        else:
            result.append(text[i]); i += 1
    if depth or string:
        raise ValueError("Unterminated comment/string")
    return "".join(result)

IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)")
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
IMPORT_LINE = re.compile(r"(?:(?:public|private|meta)\s+)*import\b")

def imports_from_source(path):
    raw = path.read_bytes()
    clean = strip_comments_strings(raw.decode("utf-8"))
    imports, body = [], False
    for line in clean.splitlines():
        line = line.strip()
        if not line:
            continue
        match = IMPORT.fullmatch(line)
        if match:
            if body:
                raise ValueError(f"Import after header: {path}")
            names = match.group(1).split()
            if not names or any(not MODULE.fullmatch(n) for n in names):
                raise ValueError(f"Unsupported import syntax: {path}: {line}")
            imports.extend(names)
        elif IMPORT_LINE.match(line):
            raise ValueError(f"Unsupported import line: {path}: {line}")
        elif not body and line in ("module", "prelude"):
            continue
        else:
            body = True
    return raw, imports

def entries(root):
    if not root.is_dir() or root.is_symlink():
        raise ValueError(f"Required real directory missing: {root}")
    def fail(error):
        raise error
    for base, dirs, files in os.walk(root, followlinks=False, onerror=fail):
        dirs.sort()
        for name in sorted(files):
            yield Path(base) / name

def fingerprint(path):
    s = path.stat()
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns)

def git_head(path):
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-C", str(path), "rev-parse", "HEAD"],
        text=True).strip()

def crosscheck_sources(metadata, names, packages):
    began = datetime.datetime.now(datetime.timezone.utc).isoformat()
    source_records, metadata_records = [], []
    source_edges, metadata_edges = [], []
    mismatches, unavailable, unparsed = [], [], []
    fingerprints, package_counts = {}, Counter()
    explicit_init_source = explicit_init_metadata = 0
    for name in sorted(names):
        path, package_name = metadata[name]
        source = packages / package_name / Path(*name.split(".")).with_suffix(".lean")
        fingerprints[path] = fingerprint(path)
        raw_metadata = path.read_bytes()
        data = json.loads(raw_metadata)
        if data.get("version") != 5 or data.get("module") != name:
            raise ValueError(f"Metadata identity/schema mismatch: {path}")
        direct = data.get("directImports")
        if not isinstance(direct, list):
            raise ValueError(f"Invalid metadata directImports: {path}")
        for entry in direct:
            if (not isinstance(entry, list) or len(entry) != 4
                or not isinstance(entry[0], str)
                or any(type(flag) is not bool for flag in entry[1:])):
                raise ValueError(f"Invalid import tuple: {path}")
        metadata_records.append([name, package_name,
                                 str(path.relative_to(packages)), sha(raw_metadata)])
        metadata_names = sorted({entry[0] for entry in direct})
        explicit_init_metadata += "Init" in metadata_names
        metadata_edges.append([name, metadata_names])
        if not source.is_file():
            unavailable.append({"module": name, "expected_source": str(source.relative_to(packages))})
            continue
        fingerprints[source] = fingerprint(source)
        source_records.append([name, package_name, str(source.relative_to(packages)),
                               sha(source.read_bytes())])
        try:
            raw_source, parsed = imports_from_source(source)
        except (OSError, UnicodeError, ValueError) as error:
            unparsed.append({"module": name, "source": str(source.relative_to(packages)),
                             "error": str(error)})
            continue
        source_names = sorted(set(parsed))
        explicit_init_source += "Init" in source_names
        source_edges.append([name, source_names])
        package_counts[package_name] += 1
        if source_names != metadata_names:
            mismatches.append({"module": name,
                               "source_only": sorted(set(source_names) - set(metadata_names)),
                               "metadata_only": sorted(set(metadata_names) - set(source_names)),
                               "parsed_source_names": source_names,
                               "metadata_names": metadata_names})
    changed = [str(path.relative_to(packages)) for path, before in fingerprints.items()
               if fingerprint(path) != before]
    return {
        "started_at_utc": began,
        "completed_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "scope": "Every visited dependency .ilean node: inside Mathlib plus all cached non-Mathlib roots",
        "comparison": "Sets of explicit imported module names; all source import modifiers and metadata flag values included; flags not compared",
        "visited_metadata_count": len(names),
        "parsed_source_count": len(source_edges),
        "parsed_sources_by_package": dict(sorted(package_counts.items())),
        "source_name_mismatches": mismatches,
        "missing_sources": unavailable,
        "unparsed_headers": unparsed,
        "observed_fingerprint_changes": changed,
        "implicit_Init": "Lean.Server.collectImports uses headerToImports(includeInit=false); implicit Init is omitted from this name comparison, explicit source imports of Init are included, and the entire official toolchain remains retained",
        "sources_explicitly_importing_Init": explicit_init_source,
        "metadata_explicitly_importing_Init": explicit_init_metadata,
        "source_records_sha256": digest(source_records),
        "source_record_shape": "[module,package,package-relative-source-path,sha256(raw source)]",
        "metadata_records_sha256": digest(metadata_records),
        "source_header_name_edges_sha256": digest(source_edges),
        "metadata_name_edges_sha256": digest(metadata_edges),
        "limitation": "Does not decode or verify .olean/.ir import tables or artifact content/provenance"
    }

def collect(source, packages, kit):
    began = datetime.datetime.now(datetime.timezone.utc).isoformat()
    candidate = git_head(source)
    manifest_raw = (source / "lake-manifest.json").read_bytes()
    lake_manifest = json.loads(manifest_raw)
    package_pins = []
    for package in sorted(lake_manifest["packages"], key=lambda p: p["name"]):
        actual = git_head(packages / package["name"])
        if actual != package["rev"]:
            raise ValueError(f"Pin mismatch: {package['name']}")
        package_pins.append({"name": package["name"], "revision": actual,
                             "url": package["url"]})
    local_paths = list(source.glob("*.lean"))
    for directory in ("SquareKit", "Applications", "Examples"):
        local_paths.extend((source / directory).rglob("*.lean"))
    local = {".".join(p.relative_to(source).with_suffix("").parts): p for p in local_paths}
    if len(local) != len(local_paths):
        raise ValueError("Duplicate local module")
    source_records, local_edges, source_fingerprints = [], {}, {}
    for name, path in sorted(local.items()):
        source_fingerprints[path] = fingerprint(path)
        raw, imports = imports_from_source(path)
        local_edges[name] = imports
        source_records.append([name, sha(raw)])
    direct_external = sorted({n for imports in local_edges.values() for n in imports
                              if n not in local})
    auxiliary = ["Cache.Main", "Lake.Build.Trace", "Lean",
                 "Lean.DeclarationRange", "Lean.Util.CollectAxioms",
                 "Mathlib.Tactic.TypeStar"]
    metadata, package_counts = {}, Counter()
    for package in package_pins:
        package_name = package["name"]
        library = packages / package_name / ".lake/build/lib/lean"
        if not library.is_dir():
            continue
        for path in entries(library):
            if path.suffix != ".ilean":
                continue
            name = ".".join(path.relative_to(library).with_suffix("").parts)
            if name in metadata:
                raise ValueError(f"Duplicate metadata module: {name}")
            metadata[name] = (path, package_name)
            package_counts[package_name] += 1
    mathlib = packages / "mathlib"
    mathlib_paths = [mathlib / "Mathlib.lean"]
    mathlib_paths.extend((mathlib / "Mathlib").rglob("*.lean"))
    universe = {".".join(p.relative_to(mathlib).with_suffix("").parts): p
                for p in mathlib_paths}
    if set(n for n, (_, p) in metadata.items() if p == "mathlib") != set(universe):
        raise ValueError("Mathlib source and metadata universes differ")
    nonmathlib = sorted(n for n, (_, p) in metadata.items() if p != "mathlib")
    queue = deque(sorted(set(local) | set(auxiliary) | set(nonmathlib)))
    visited, core, edges = set(), set(), {}
    metadata_records, metadata_fingerprints, fallback_records = [], {}, []
    while queue:
        name = queue.popleft()
        if name in visited:
            continue
        visited.add(name)
        if name.split(".")[0] in ("Init", "Lean", "Std", "Lake"):
            core.add(name); continue
        if name in local_edges:
            dependencies = local_edges[name]
            edges[name] = dependencies
        elif name in metadata:
            path, package_name = metadata[name]
            metadata_fingerprints[path] = fingerprint(path)
            raw = path.read_bytes()
            data = json.loads(raw)
            if data.get("version") != 5 or data.get("module") != name:
                raise ValueError(f"Metadata identity/schema mismatch: {path}")
            direct = data.get("directImports")
            if not isinstance(direct, list):
                raise ValueError(f"Invalid directImports: {path}")
            for entry in direct:
                if (not isinstance(entry, list) or len(entry) != 4
                    or not isinstance(entry[0], str)
                    or any(type(flag) is not bool for flag in entry[1:])):
                    raise ValueError(f"Invalid import tuple: {path}")
            dependencies = [entry[0] for entry in direct]
            edges[name] = direct
            metadata_records.append([name, package_name,
                                     str(path.relative_to(packages)), sha(raw)])
        else:
            candidates = [packages / p["name"] / Path(*name.split(".")).with_suffix(".lean")
                          for p in package_pins]
            matches = [path for path in candidates if path.is_file()]
            if len(matches) != 1:
                raise ValueError(f"Unresolved/ambiguous module: {name}: {matches}")
            path = matches[0]
            source_fingerprints[path] = fingerprint(path)
            raw, dependencies = imports_from_source(path)
            edges[name] = dependencies
            fallback_records.append([name, str(path.relative_to(packages)), sha(raw)])
        queue.extend(dependencies)
    inside = set(universe) & visited
    outside = set(universe) - inside
    family = {n: {"files": 0, "logical": 0, "allocated": 0} for n in universe}
    unique_inodes = {}
    scanned_count, symlinks = 0, []
    for build_dir in ("lib/lean", "ir"):
        root = mathlib / ".lake/build" / build_dir
        for path in entries(root):
            if path.is_symlink():
                symlinks.append(str(path.relative_to(mathlib)))
                continue
            relative = path.relative_to(root)
            stem = relative.name.split(".")[0]
            name = ".".join((*relative.parts[:-1], stem))
            if name not in family:
                raise ValueError(f"Unattributed artifact: {path}")
            st = path.stat()
            key = (st.st_dev, st.st_ino)
            bucket = "inside" if name in inside else "outside"
            row = family[name]
            row["files"] += 1; row["logical"] += st.st_size
            if key not in unique_inodes:
                unique_inodes[key] = {"bucket": bucket, "links": 0,
                                      "nlink": st.st_nlink, "bytes": st.st_blocks * 512}
                row["allocated"] += st.st_blocks * 512
            elif unique_inodes[key]["bucket"] != bucket:
                raise ValueError("Cross-bucket shared inode")
            unique_inodes[key]["links"] += 1
            scanned_count += 1
    if symlinks:
        raise ValueError(f"Symlink artifacts: {symlinks}")
    external_links = sum(1 for row in unique_inodes.values()
                         if row["nlink"] > row["links"])
    totals = {}
    for label, names in (("inside", inside), ("outside", outside), ("total", set(universe))):
        totals[label] = {"modules": len(names),
                         "files": sum(family[n]["files"] for n in names),
                         "logical_bytes": sum(family[n]["logical"] for n in names),
                         "allocated_bytes": sum(family[n]["allocated"] for n in names)}
    cross_check = crosscheck_sources(metadata, [r[0] for r in metadata_records], packages)
    cross_check["metadata_matches_original_inventory"] = (
        cross_check["metadata_records_sha256"] == digest(sorted(metadata_records)))
    cross_check["dependency_HEAD_observations"] = [
        {"package": p["name"], "expected": p["revision"],
         "observed": git_head(packages / p["name"])} for p in package_pins]
    changed = [str(path) for path, before in
               {**source_fingerprints, **metadata_fingerprints}.items()
               if fingerprint(path) != before]
    if changed:
        raise ValueError(f"Inputs changed while reading: {changed}")
    family_records = [[n, family[n]["files"], family[n]["logical"], family[n]["allocated"]]
                      for n in sorted(family)]
    script_paths = [source / p for p in (
        "check.sh", "scripts/check.py", "scripts/lake_integrity.py",
        "scripts/lake-output-hashes.lean", "scripts/test-proof-audit.py",
        "ProofAudit.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")]
    script_records = [[str(p.relative_to(source)), sha(p.read_bytes())] for p in script_paths]
    record = {
        "format": 1,
        "classification": "prospective-static-inventory-not-deletion-authorization",
        "started_at_utc": began,
        "completed_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "candidate": candidate,
        "toolchain_pin": (source / "lean-toolchain").read_text().strip(),
        "lake_manifest_sha256": sha(manifest_raw),
        "package_pins": package_pins,
        "source_root_used": str(source),
        "packages_root_used": str(packages),
        "roots": {"local_modules": sorted(local),
                  "direct_external_imports": direct_external,
                  "auxiliary": auxiliary,
                  "all_cached_nonmathlib_modules": nonmathlib},
        "root_policy": "Retain whole official toolchain and every non-Mathlib artifact; use every cached non-Mathlib module as a conservative graph root.",
        "identities": {
            "canonical_json_encoding": "UTF-8, ensure_ascii=false, sort_keys=true, separators=(',',':')",
            "local_source_record_sha256": digest(source_records),
            "local_source_record_default_json_sha256": sha(json.dumps(source_records).encode()),
            "visited_metadata_record_sha256": digest(sorted(metadata_records)),
            "visited_metadata_record_shape": "[module,package,package-relative-ilean-path,sha256(raw bytes)]",
            "source_fallback_records": sorted(fallback_records),
            "semantic_graph_sha256": digest(sorted(edges.items())),
            "semantic_graph_shape": "[module,directImports tuples] for ilean; [module,parsed module names] for local/fallback source",
            "metadata_universe_sha256": digest(sorted(metadata)),
            "mathlib_source_universe_sha256": digest(sorted(universe)),
            "artifact_family_records_sha256": digest(family_records),
            "artifact_family_record_shape": "[module,file_count,logical_bytes,unique_inode_allocated_bytes]",
            "gate_source_records": script_records,
            "kit_launcher_sha256": sha((kit / "conaled_native.py").read_bytes())},
        "dependency_source_cross_check": cross_check,
        "metadata": {"schema_version": 5,
                     "indexed_by_package": dict(sorted(package_counts.items())),
                     "visited_count": len(metadata_records),
                     "core_terminal_names": sorted(core),
                     "source_fallback_count": len(fallback_records),
                     "unresolved_edges": [],
                     "observed_input_fingerprint_changes": []},
        "allocation": {
            "totals": totals,
            "directories_relative_to_mathlib": [".lake/build/lib/lean", ".lake/build/ir"],
            "files_per_module_distribution": dict(sorted(Counter(r["files"] for r in family.values()).items())),
            "counting_rule": "st_blocks * 512; unique (st_dev,st_ino), no cross-bucket sharing",
            "cross_bucket_shared_inodes": 0,
            "external_hardlink_inodes": external_links,
            "symlink_artifacts": 0,
            "unattributed_artifacts": 0,
            "artifact_suffixes": [
                "lib/lean/<module>.ilean", "lib/lean/<module>.ilean.hash",
                "lib/lean/<module>.ir", "lib/lean/<module>.ir.hash",
                "lib/lean/<module>.ir.sig", "lib/lean/<module>.ir.sig.hash",
                "lib/lean/<module>.olean", "lib/lean/<module>.olean.hash",
                "lib/lean/<module>.olean.private", "lib/lean/<module>.olean.private.hash",
                "lib/lean/<module>.olean.server", "lib/lean/<module>.olean.server.hash",
                "lib/lean/<module>.trace", "ir/<module>.c", "ir/<module>.c.hash"]},
        "inside_module_list_sha256": sha(("\n".join(sorted(inside)) + "\n").encode()),
        "outside_module_list_sha256": sha(("\n".join(sorted(outside)) + "\n").encode()),
        "outside_module_list_encoding": "UTF-8; lexicographic order; one module per LF-terminated line",
        "limitations": [
            "Static import headers only; no complete dynamic/native execution reachability proof.",
            "No deletion authorization and no certified safe reduction manifest.",
            "No guarantee that measured allocated blocks equal reclaimed filesystem capacity.",
            "No compiler/cache execution or content mutation; source/metadata fingerprints checked for changes during read.",
            "All toolchain, non-Mathlib artifacts, source files and other/shared native outputs are retained.",
            "Artifact contents were not rehashed; per-family allocation was inventoried.",
            "Future source/gate/setup changes require re-evaluating roots and closure."
        ]}
    return record, sorted(outside)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--packages", type=Path, required=True)
    parser.add_argument("--kit", type=Path, required=True)
    parser.add_argument("--outside", action="store_true",
                        help="Emit only sorted outside module names instead of inventory JSON.")
    args = parser.parse_args()
    record, outside = collect(args.source, args.packages, args.kit)
    if args.outside:
        print("\n".join(outside))
    else:
        print(json.dumps(record, ensure_ascii=False, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
PY
```

No compiler, setup, cache hydration, formal gate, or deletion was performed for this record. The only writes are the three evidence files in this directory. No chapter or review status changes.
