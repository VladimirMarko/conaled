"""Start one explicitly described immutable run through the unchanged qualified recorder."""
import sys, json
v = json.loads(sys.argv[1])
from pathlib import Path
import os, subprocess, hashlib, datetime
b=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104'); p=b/'conaled-ch01-review'; c=b/'fdsa-control'
def g(*a): return subprocess.check_output(['git','-C',str(p),*a],text=True)
assert g('rev-parse','HEAD').strip()==v['expectedHead'] and not g('status','--porcelain=v1','--untracked-files=all').strip()
assert g('diff','--name-only',v['base'],v['candidate']).splitlines()==v['expectedPaths']
assert g('rev-parse','work/fdsa-book').strip()==v['acceptedHead']
s=os.statvfs(b); assert s.f_bfree*s.f_frsize>=256*1024*1024,'Insufficient present raw headroom for bounded focused build plus checkpoint staging'
rows=[]
for name in v['expectedPaths']:
 data=subprocess.check_output(['git','-C',str(p),'show',v['candidate']+':'+name]); rows.append({'path':name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
if v['candidate']!=v['expectedHead']:
 result=subprocess.run(['git','-C',str(p),'switch','--detach',v['candidate']],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=False)
 assert result.returncode==0,result.stdout
 switch_output=result.stdout
else: switch_output='Already at exact candidate; no checkout mutation.'
assert not g('status','--porcelain=v1','--untracked-files=all').strip()
record={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**v,'checkout_exit':0,'checkout_output':switch_output,'sources':rows,'candidate_tree':g('rev-parse','HEAD^{tree}').strip(),'space':{'ordinary_available':s.f_bavail*s.f_frsize,'raw_free':s.f_bfree*s.f_frsize},'compiler_owner':'root serial; unchanged qualified native profile one thread','no_installation_or_hydration':True,'acceptance_claim':False}
d=c/'provenance'/v['recordDirectory']; d.mkdir(exist_ok=True)
with (d/v['recordName']).open('x') as f: json.dump(record,f,indent=2); f.write('\n')
argv=['python3',str(c/'tooling/record_command.py'),'--name',v['name'],'--cwd',str(p),'--candidate',v['candidate'],'--','python3',str(c/'tooling/unified-native-kit-4.35.0/conaled_native.py'),'--state',str(b/'conaled-native-state'),'run','--project',str(p),'--threads','1','--',*v['command']]
os.execvp(argv[0],argv)
