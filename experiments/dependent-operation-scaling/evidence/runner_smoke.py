import json
from pathlib import Path
import shutil
import subprocess
import sys
root=Path(sys.argv[1]).resolve()
evidence=Path(sys.argv[2])
evidence.mkdir(parents=True,exist_ok=False)
rows=[]
for name, body, expected in [('RunnerTrue','example : True := True.intro\n','lean-passed'),('RunnerFalse','example : False := True.intro\n','lean-failed')]:
    source=root/'attempts'/(name+'.lean')
    source.write_text('import Examples.DependentOperationTrialSpec\n'+body)
    result=subprocess.run(['direnv','exec','.','python3','run_attempt.py',str(source.relative_to(root))],cwd=root,capture_output=True)
    (evidence/(name+'.stdout')).write_bytes(result.stdout)
    (evidence/(name+'.stderr')).write_bytes(result.stderr)
    archive=root/'attempts/checks'/name
    record=json.loads((archive/'result.json').read_text())
    timing=json.loads((root/'attempts/timing'/(name+'.json')).read_text())
    assert record['status']==expected,record
    assert record['public_inputs_before']==record['public_inputs_after']=='verified'
    assert timing['exit_code']==result.returncode
    assert (result.returncode==0)==(expected=='lean-passed')
    rows.append({'name':name,'expected':expected,'record':record,'timing':timing})
    archive.chmod(0o755)
    shutil.move(str(archive),str(evidence/name))
    (evidence/name).chmod(0o555)
    shutil.move(str(source),str(evidence/source.name))
    shutil.move(str(root/'attempts/timing'/(name+'.json')),str(evidence/(name+'.timing.json')))
for name in ('checks','timing'):
    path=root/'attempts'/name
    if path.exists() and not list(path.iterdir()):
        path.rmdir()
(evidence/'summary.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Real runner smoke passed:',root)
