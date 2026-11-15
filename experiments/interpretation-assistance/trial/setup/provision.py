#!/usr/bin/env python3
"""Coordinator-only provisioner. Requires an explicit reviewed prototype commit."""
import argparse,hashlib,json,pathlib,subprocess
p=argparse.ArgumentParser();p.add_argument('--prototype',required=True);args=p.parse_args()
root=pathlib.Path('/tmp/conaled-wave-20261111/462-trial-preparation')
repo=pathlib.Path('/home/vlad/Code/conaled')
base='2b3b344b69c4e56324c8de2eb566ee0f8aef129b'
def show(commit,path):return subprocess.check_output(['git','show',f'{commit}:{path}'],cwd=repo)
def sha(data):return hashlib.sha256(data).hexdigest()
proto=subprocess.check_output(['git','rev-parse',args.prototype+'^{commit}'],cwd=repo,text=True).strip()
original_registry=show(proto,'experiments/interpretation-assistance/registry.json')
registry=json.loads(original_registry)
additions=json.loads((root/'task-additions.json').read_text())['routes']
assert not(set(registry['routes']) & set(additions))
registry['routes'].update(additions)
rendered=(json.dumps(registry,indent=2,ensure_ascii=False)+'\n').encode()
assert rendered==(root/'task-registry.json').read_bytes(), 'Reviewed generic registry changed; redo registry diff/review.'
allow=json.loads((root/'native-allowlist.json').read_text())['sources']
common={f:show(base,f) for f in allow}
for f in ['lean-toolchain','lake-manifest.json','flake.nix','flake.lock','.envrc']:
 common[f]=show(base,f)
common['SquareKit/InterpretationAssistance.lean']=show(proto,'SquareKit/InterpretationAssistance.lean')
common['scripts/interpretation-trial-check.py']=show(proto,'scripts/interpretation-trial-check.py')
for f in ['TaskSetup462.lean','TASKS.md']:common[f]=(root/'common'/f).read_bytes()
common['.gitignore']=b'.lake/\n.direnv/\n'
common['lakefile.toml']=b'''name = "interpretationTrial462"
version = "0.1.0"
defaultTargets = ["TaskSetup462"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.35.0"

[[lean_lib]]
name = "TrialSupport"
roots = ["TaskSetup462"]
globs = ["TaskSetup462", "Squares", "Compiler", "FirstOrder", "SquareKit.+", "Applications.+", "Examples.+"]
'''
common['NeutralSmoke.lean']=b'import TaskSetup462\nexample (n : Nat) : n + 0 = n := by rfl\n'
extra={f:show(proto,f) for f in ['scripts/interpretation-assist.py','SquareKit/InterpretationDiagnostics.lean','experiments/interpretation-assistance/README.md']}
extra['experiments/interpretation-assistance/registry.json']=rendered
manifest={'baseline':base,'prototype':proto,'common_files':{f:sha(b) for f,b in common.items()},'assisted_extra_files':{f:sha(b) for f,b in extra.items()},'arms':{},'source_access':'Initial snapshot commits only; no original repository history. Pinned dependency source/cache symlink; separate writable project outputs. Author output/control paths assigned by root.'}
for arm in ['direct','assisted']:
 dest=root/'handoffs'/arm
 dest.mkdir(parents=True,exist_ok=False)
 files=common | (extra if arm=='assisted' else {})
 for f,b in files.items():
  target=dest/f;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
 subprocess.run(['git','init','-q'],cwd=dest,check=True)
 subprocess.run(['git','config','user.name','Codex task provisioning'],cwd=dest,check=True)
 subprocess.run(['git','config','user.email','codex@localhost'],cwd=dest,check=True)
 subprocess.run(['git','add','.'],cwd=dest,check=True)
 subprocess.run(['git','commit','-qm','chore: freeze isolated native trial sources (#462)'],cwd=dest,check=True)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=dest,text=True).strip()
 (dest/'.lake').mkdir()
 (dest/'.lake/packages').symlink_to('/home/vlad/Code/conaled/.lake/packages',target_is_directory=True)
 manifest['arms'][arm]={'path':str(dest),'snapshot_commit':head,'files':{f:sha(b) for f,b in files.items()}}
(root/'provision-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v['path'] for k,v in manifest['arms'].items()}))
