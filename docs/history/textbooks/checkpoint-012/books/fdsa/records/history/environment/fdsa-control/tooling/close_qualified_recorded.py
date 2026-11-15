"""Bind an actually returned execution-session terminal to complete unchanged native records."""
import sys, json
v = json.loads(sys.argv[1])
from pathlib import Path
import hashlib, shutil, re, datetime
b=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
d=b/'fdsa-control/provenance'/v['name']
assert isinstance(v['session'],int) and isinstance(v['terminal']['exit_code'],int)
assert isinstance(v['terminal']['chunk_id'],str) and v['terminal']['chunk_id']
assert v.get('terminal_observation') == 'actual execution tool result'
r=json.loads((d/'result.json').read_text()); data=(d/'full.log').read_bytes()
assert r['exit_code']==v['terminal']['exit_code'] and r['final_head']==r['candidate']==v['candidate'] and r['final_status']==''
assert hashlib.sha256(data).hexdigest()==r['log_sha256'] and len(data)==r['log_size_bytes']
pat=rb'\[result\] exit='+str(r['exit_code']).encode()+rb', [^\n]*; (/[^\n]+/result.json)\n'
matches=re.findall(pat,data); assert len(matches)==1
origin=Path(matches[0].decode()).parent; assert origin.parent==b/'conaled-native-state/logs'
nd=d/'native-records'; nd.mkdir(exist_ok=False)
def ident(p):
 x=p.read_bytes(); return {'path':str(p),'bytes':len(x),'sha256':hashlib.sha256(x).hexdigest()}
for name in ['start.json','result.json','output.log']: shutil.copyfile(origin/name,nd/name)
native=json.loads((nd/'result.json').read_text())
assert native['exit_code']==r['exit_code'] and native['passed']==(r['exit_code']==0)
assert native['command']==r['command'][r['command'].index('--')+1:] and native['lean_threads']=='1'
assert native['cwd']==r['command'][r['command'].index('--project')+1] and not native['timed_out'] and native['recorder_error'] is None
body=(nd/'output.log').read_bytes(); at=data.find(body); assert at>=0 and data.find(body,at+1)<0
(d/'outer-prefix.log').write_bytes(data[:at]); (d/'outer-suffix.log').write_bytes(data[at+len(body):])
tr={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'owned_session':v['session'],'actual_exit':r['exit_code'],'terminal_tool_chunk':v['terminal']['chunk_id'],'state':'CLOSED; never poll this historical session again','candidate':r['candidate']}
with (d/'owned-terminal.json').open('x') as f: json.dump(tr,f,indent=2); f.write('\n')
with (d/'actual-tool-terminal.json').open('x') as f: json.dump(v['terminal'],f,indent=2); f.write('\n')
vr=d/'verification.json'
record={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate':r['candidate'],'terminal':tr,'actual_recorder_and_native_exits':[r['exit_code'],native['exit_code']],'outer_log':ident(d/'full.log'),'native_origin':str(origin),'native_records':{n:ident(nd/n) for n in ['start.json','result.json','output.log']},'native_body_exact_outer_offset':at,'complete_closed_log':True,'scope':v['scope'],'verification_record_candidate':json.loads(vr.read_text())['candidate'] if vr.exists() else None,'a_focused_or_type_run_is_not_a_full_candidate_check':True}
with (d/'closed-evidence-reconciliation.json').open('x') as f: json.dump(record,f,indent=2); f.write('\n')
print('CLOSED_RECORD '+json.dumps(record),flush=True)
if len(data)<=24000: print('COMPLETE_CLOSED_LOG\n'+data.decode(),flush=True)
else: print('LOG_RETAINS_ALL_BYTES; over24000bytes, read bounded ranges separately. No complete readback claimed by this command.',flush=True)
