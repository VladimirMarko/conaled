import pathlib, subprocess, json, hashlib, tarfile, io, time, difflib
P=pathlib.Path('/tmp/conaled-wave-20261111/462-trial-preparation'); R=P/'replay'; W=pathlib.Path('/home/vlad/Code/conaled')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd,log):
 start=time.time()
 with log.open('w') as f: p=subprocess.run(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
 rec={'command':cmd,'cwd':str(cwd),'log':str(log),'exit':p.returncode,'seconds':time.time()-start}; records.append(rec); (R/'receipts.json').write_text(json.dumps(records,indent=2)); return p.returncode
records=json.loads((R/'receipts.json').read_text()) if (R/'receipts.json').exists() else []
original=subprocess.check_output(['git','show','3b5c9002:ProofAudit.lean'],cwd=W,text=True)
for arm in ['direct','assisted']:
 src=P/'handoffs'/arm; dst=R/arm; dst.mkdir(exist_ok=True)
 data=subprocess.check_output(['git','archive','HEAD'],cwd=src)
 with tarfile.open(fileobj=io.BytesIO(data)) as t:t.extractall(dst,filter='data')
 (dst/'.lake').mkdir(exist_ok=True)
 if not (dst/'.lake/packages').exists(): (dst/'.lake/packages').symlink_to((src/'.lake/packages').resolve(),target_is_directory=True)
 subprocess.run(['git','init','-q'],cwd=dst,check=True)
 subprocess.run(['git','add','.'],cwd=dst,check=True)
 subprocess.run(['git','-c','user.name=Replay','-c','user.email=replay@local','commit','--allow-empty','-qm','test: provision isolated replay (#462)'],cwd=dst,check=True)
 subprocess.run(['direnv','allow',str(dst)],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
 prefix=['flock','/tmp/conaled-wave-20261111/build.lock','direnv','exec','.', 'taskset','-c','0']
 targets=['TaskSetup462','Examples.DiagonalCoverage','Examples.ConstructionTransport']
 if arm=='assisted':targets+=['SquareKit.InterpretationDiagnostics']
 if not (dst/'.lake/build/lib/lean/TaskSetup462.olean').exists():
  if run(prefix+['lake','build']+targets,dst,R/(arm+'-build.log')):raise SystemExit('native build failed')
 audit=original.replace('import SquareApplications\n','import Lean\n').replace('`Verification]', '`Verification, `TaskSetup462]').replace('\n#audit_project_axioms\n','\n')
 (dst/'TrialAudit.lean').write_text(audit)
 (R/(arm+'-audit-adaptation.diff')).write_text(''.join(difflib.unified_diff(original.splitlines(True),audit.splitlines(True),fromfile='ProofAudit.lean',tofile='TrialAudit.lean')))
 if run(prefix+['lake','env','lean','-o','.lake/build/lib/lean/TrialAudit.olean','TrialAudit.lean'],dst,R/(arm+'-audit-helper.log')):raise SystemExit('helper failed')
 controls=sorted((P/'control'/arm).glob('round-*'))
 for ctrl in controls:
  n=ctrl.name.replace('-',''); module='Examples.Replay'+n; source=dst/(module.replace('.','/')+'.lean'); source.write_bytes((ctrl/'source.lean').read_bytes())
  expected=json.loads((ctrl/'receipt.json').read_text())['exit']; log=R/(arm+'-'+ctrl.name+'-check.log')
  out='.lake/build/lib/lean/'+module.replace('.','/')+'.olean'
  actual=run(prefix+['lake','env','lean','-o',out,str(source.relative_to(dst))],dst,log)
  records[-1].update(expected_exit=expected,source_sha256=sha(source),original_snapshot=str(ctrl/'source.lean')); (R/'receipts.json').write_text(json.dumps(records,indent=2))
  if actual!=expected:raise SystemExit('changed check result '+str(log))
  if actual==0:
   driver=dst/'AuditRun.lean';driver.write_text('import '+module+'\nimport TrialAudit\nset_option trace.ProofAudit.roots true in\n#audit_project_axioms\n')
   if run(prefix+['lake','env','lean','AuditRun.lean'],dst,R/(arm+'-'+ctrl.name+'-audit.log')):raise SystemExit('audit failed')
print('Replay complete: all exact round results matched and every passing round fully audited.')
