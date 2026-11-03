#!/usr/bin/env python3
"""Fresh bounded checker build/audit, runtime observation, and kernel proof timings.

Run with direnv exec . python3 scripts/benchmark-order-certificate.py.
Each Lean process has CPU/wall limits and Lean's memory limit. Retains inputs/logs.
"""
from pathlib import Path
import hashlib
import json
import os
import platform
import resource
import subprocess
import tempfile
import time

from check import FORBIDDEN, IMPORT, executable_source

ROOT = Path(__file__).resolve().parents[1]
LIMIT_SECONDS = 60
LIMIT_BYTES = 4 * 1024**3
def closure(module, seen=None):
    """Find the local import closure in dependency order."""
    if seen is None:
        seen = set()
    if module in seen:
        return []
    seen.add(module)
    path = ROOT / Path(*module.split(".")).with_suffix(".lean")
    if not path.is_file():
        return []
    result = []
    for match in IMPORT.finditer(path.read_text()):
        for dependency in match.group(1).split("--", 1)[0].split():
            result.extend(closure(dependency, seen))
    return result + [module]


def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (LIMIT_SECONDS, LIMIT_SECONDS))


def main():
    work = Path(tempfile.mkdtemp(prefix="order-certificate-", dir=ROOT / ".lake"))
    print(f"Evidence: {work}", flush=True)
    output = work / "out"
    output.mkdir()
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join([str(output), *map(str, sorted(
        (ROOT / ".lake/packages").glob("*/.lake/build/lib/lean")))])
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    expected = (ROOT / "lean-toolchain").read_text().strip().split(":v")[-1]
    if f"version {expected}," not in version:
        raise RuntimeError(f"Wrong Lean version: {version}")
    records = {"version": version, "platform": platform.platform(),
               "cpu": Path("/proc/cpuinfo").read_text().split("model name\t: ")[1].splitlines()[0],
               "seconds_per_process": LIMIT_SECONDS, "lean_memory_limit_mib": LIMIT_BYTES // 1024**2,
               "manifest_sha256": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
               "sources": {}, "runs": []}

    def run(name, args):
        start = time.monotonic()
        result = subprocess.run(["lean", "-j2", "-M4096", *args], cwd=work, env=env,
                                capture_output=True, text=True,
                                timeout=LIMIT_SECONDS, preexec_fn=limits)
        elapsed = time.monotonic() - start
        (work / f"{name}.log").write_text(result.stdout + result.stderr)
        records["runs"].append({"name": name, "command": ["lean", "-j2", "-M4096", *args],
                                "seconds": elapsed, "returncode": result.returncode,
                                "stdout": result.stdout, "stderr": result.stderr})
        (work / "results.json").write_text(json.dumps(records, indent=2) + "\n")
        print(f"{name}: {elapsed:.4f}s, exit {result.returncode}", flush=True)
        if result.returncode:
            raise RuntimeError(f"See {work / (name + '.log')}")
        return result.stdout

    for module in closure("Examples.OrderCertificate"):
        source = Path(*module.split(".")).with_suffix(".lean")
        target = work / source
        target.parent.mkdir(parents=True, exist_ok=True)
        data = (ROOT / source).read_bytes()
        if FORBIDDEN.search(executable_source(data.decode())):
            raise RuntimeError(f"Forbidden source construct in {source}")
        records["sources"][str(source)] = hashlib.sha256(data).hexdigest()
        target.write_bytes(data)
        artifact = output / source.with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        run(module, ["-o", str(artifact), str(source)])

    # Use the unchanged exhaustive audit implementation on this fresh import closure.
    audit = (ROOT / "ProofAudit.lean").read_text().replace(
        "import SquareApplications\n", "import Examples.OrderCertificate\n", 1)
    (work / "ProofAudit.lean").write_text(audit)
    run("audit", ["-o", str(output / "ProofAudit.olean"), "ProofAudit.lean"])
    header = "import Examples.OrderCertificate\nopen OrderCertificate Examples.OrderCertificate\n"
    (work / "Baseline.lean").write_text(header)
    run("import-baseline", ["Baseline.lean"])
    for size in (64, 256):
        for algorithm in ("reference", "adjacent"):
            proof = "" if algorithm == "reference" else "  rw [← refinement lt_law]\n"
            source = ("import ProofAudit\n" + header + "set_option maxHeartbeats 10000000\n"
                      "set_option maxRecDepth 100000\n"
                      f"theorem certificate : (List.range {size}).Pairwise (· < ·) := by\n"
                      "  apply (reference_correct lt_law _).mp\n" + proof +
                      "  decide +kernel\n#print axioms certificate\n#audit_project_axioms\n")
            name = f"Proof_{algorithm}_{size}"
            (work / "Examples" / f"{name}.lean").write_text(source)
            run(name, [f"Examples/{name}.lean"])

    runtime = header + '''
def main : IO Unit := do
  for n in [64, 256, 1024] do
    for (name, checker) in [("reference", reference ltCmp), ("adjacent", adjacent ltCmp)] do
      let start ← IO.monoNanosNow
      let mut accepted := 0
      for offset in [:20] do
        -- Vary the input to avoid timing repeated calls on one constant expression.
        let xs := (List.range n).map (· + offset)
        if checker xs then accepted := accepted + 1
      let elapsed := (← IO.monoNanosNow) - start
      if accepted != 20 then throw (IO.userError "unexpected rejection")
      IO.println s!"{name} n={n} repeats=20 accepted={accepted} ns={elapsed}"
'''
    (work / "Runtime.lean").write_text(runtime)
    print(run("runtime", ["--run", "Runtime.lean"]), end="")
    print("PASS: fresh closure/audit and bounded measurements; runtime is not proof evidence.")


if __name__ == "__main__":
    main()
