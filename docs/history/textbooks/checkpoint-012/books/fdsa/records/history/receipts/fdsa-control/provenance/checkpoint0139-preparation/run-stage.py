import sys,json
v=json.loads(sys.argv[1])

from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,subprocess,time,sys,os
b=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104');c=b/'fdsa-control';p=c/'provenance/checkpoint0139-preparation'
def ident(q):
 with q.open('rb') as f:return {'path':str(q),'bytes':q.stat().st_size,'sha256':hashlib.file_digest(f,'sha256').hexdigest()}
def write(name,obj):
 with (p/name).open('x') as f:json.dump(obj,f,indent=2);f.write('\n')
configuration_path=p/'acceptance-configuration.json'
configuration=json.loads(configuration_path.read_text())
assert configuration['state']=='RESOLVED_FROM_ACTUAL_FINAL_EVIDENCE','Prepared proposal: actual final evidence configuration is unresolved'
assert configuration['execution_enabled'] is True and configuration['root_final_schema_reconciliation_complete'] is True
assert configuration['root_independent_code_inspection_complete'] is True
assert configuration['unit']=='FDSA-XT02' and configuration['candidate']=='e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe'
assert configuration['candidate_tree']=='d002afee18c38828f01221837f4c3f302ab155cc' and configuration['accepted_base']=='90469ce4ba3fc49397d369a5db7d58aec7014f58'
assert v['terminal']['exit_code']==0
tr={'recorded_utc':datetime.now(timezone.utc).isoformat(),'owned_session':v['previousSession'],'actual_exit':0,'terminal_tool_chunk':v['terminal']['chunk_id'],'state':'CLOSED; never poll this historical session again','tool_result':v['terminal']}
write(v['terminalFile'],tr)
if v['stage']=='creation':
 capture=json.loads((p/'capture.json').read_text());pre=json.loads((p/'creation-preflight.json').read_text())
 assert capture['all_writers_held'] and not capture['compiler_live']
 assert capture['acceptance_configuration']==ident(configuration_path)
 for rel,expected in capture['held_control'].items():
  actual=ident(c/rel);assert {k:actual[k] for k in ['bytes','sha256']}==expected,rel
 s=os.statvfs(b);assert s.f_bfree*s.f_frsize>=pre['checkpoint_staging_scenario_bytes']+32*1024*1024
 argv=['python3',str(c/'checkpoint_compact.py'),'conaled-fdsa-0139-tree-shape-accepted-and-chapter04-progress']
 log=p/'create.log'
else:
 assert v['stage']=='verification'
 creation=json.loads((p/'creation-subprocess-result.json').read_text());assert creation['actual_exit']==0
 assert ident(p/'create.log')==creation['log']
 print('COMPLETE_CREATION_LOG\n'+(p/'create.log').read_text(),flush=True)
 argv=['python3',str(p/'verify-checkpoint.py')]
 log=p/'verify.log'
started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
write(v['stage']+'-start.json',{'started_utc':started,'argv':argv,'all_writers_held':True,'compiler_live':False})
with log.open('xb') as f:result=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT,check=False)
rec={'started_utc':started,'completed_utc':datetime.now(timezone.utc).isoformat(),'actual_exit':result.returncode,'elapsed_seconds':time.monotonic()-t,'argv':argv,'log':ident(log)}
write(v['stage']+'-subprocess-result.json',rec)
print(json.dumps(rec,indent=2),flush=True)
if v['stage']=='verification':print('COMPLETE_VERIFICATION_LOG\n'+log.read_text(),flush=True)
sys.exit(result.returncode)
