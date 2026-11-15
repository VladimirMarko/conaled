from pathlib import Path
import importlib.util,json,sys,hashlib
from datetime import datetime,timezone
control=Path('/workspace/scratch/6bb268f9336f/work/fdsa-control')
source=control/'tooling/record_command.py'
spec=importlib.util.spec_from_file_location('fdsa_record_command',source)
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
directory=control/'provenance/environment0068-recorder-progress-failure'
directory.mkdir(exist_ok=False)
marker=directory/'child-executed-once.txt'
child_code="from pathlib import Path; import sys; p=Path(sys.argv[1]); p.open('x').write('one execution\\n'); print('owned child terminal marker', flush=True); sys.exit(7)"
request={'cwd':'/workspace/scratch/6bb268f9336f/work/conaled-ch01-review','candidate':'07e480f6ec9958d4975bb90151005b84f2907614','command':[sys.executable,'-c',child_code,str(marker)]}
(directory/'request.json').write_text(json.dumps(request,indent=2)+'\n')
real_save=module.save
injected=[]
def fail_progress_only(path,data):
    if path.name=='progress.json':
        injected.append(str(path))
        raise OSError('intentional progress-write failure for ENV68-SPEC-001')
    return real_save(path,data)
module.save=fail_progress_only
code=module.execute(directory)
result=json.loads((directory/'result.json').read_text())
assert injected and code==7 and result['exit_code']==7
assert result['state']=='failed' and len(result['progress_bookkeeping_errors'])==1
assert marker.read_text()=='one execution\n'
assert (directory/'full.log').read_text()=='owned child terminal marker\n'
assert result['final_head']==request['candidate'] and result['final_status']==''
report={'tested_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'finding':'ENV68-SPEC-001','injected_failure':'Every progress.json save raises OSError; start and result writes succeed.','actual_child_exit':code,'actual_recorded_exit':result['exit_code'],'actual_recorded_state':result['state'],'single_execution_marker':marker.name,'closed_log':(directory/'full.log').name,'outcome':'passed; optional progress failure did not abandon the owned child or erase its nonzero terminal outcome','formal_project_validation_credit':False}
(directory/'assessment.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
