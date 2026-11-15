from pathlib import Path
import hashlib, json, re, subprocess
root=Path.cwd()
workspace=root.parent
expected="1ce161412a2cfb725f27525ff98d400209163316"
base="7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd"
def git(*args):
    return subprocess.check_output(["git",*args],text=True).strip()
assert git("rev-parse","HEAD")==expected
assert not git("status","--porcelain=v1")
assert git("merge-base",base,expected)==base
subprocess.run(["git","diff","--check",base+"..."+expected],check=True)
files=git("diff","--name-only",base+"..."+expected).splitlines()
assert set(files)=={"docs/SOURCES.md","docs/research/pfds-reconstruction.md","docs/research/pfds-union-coverage.md"},files
links=0
for name in files:
    p=root/name
    for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)",p.read_text()):
        target=target.split("#",1)[0]
        if not target or re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:",target):
            continue
        assert (p.parent/target).is_file(),(name,target)
        links+=1
source=json.loads((workspace/"session/research/union-source-identities.json").read_text())
for item in ("book","thesis"):
    record=source[item]
    file=workspace/record["local_research_path"]
    assert hashlib.sha256(file.read_bytes()).hexdigest()==record["sha256"]
ledger=(root/"docs/research/pfds-union-coverage.md").read_text()
items=json.loads((workspace/"session/research/thesis-obligations.json").read_text())["items"]
intro=[x for x in items if x["id"].startswith("T1.")]
assert len(intro)==16
for item in intro:
    rows=[line for line in ledger.splitlines() if line.startswith("| "+item["id"]+" |")]
    assert len(rows)==1,item["id"]
    assert item["cost_mode"] in rows[0],item["id"]
    assert "Book Ch"+str(item["book_owner_chapter"]) in rows[0],item["id"]
    assert item["status"]=="unproved"
for item in items:
    assert item["id"] in ledger,item["id"]
assert "Every row is currently unproved" in ledger
print(f"Pinned clean candidate {expected}; original-base diff is documentation-only; whitespace, {links} local Markdown links, both source fingerprints, sixteen table rows/owners/cost modes and all eight initial supplement IDs passed.")
print("No Lean build or chapter mathematical proof acceptance is asserted by this documentation check.")
