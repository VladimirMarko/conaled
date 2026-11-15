from pathlib import Path
from datetime import datetime,timezone
import json,subprocess,os,shutil
root=Path('/workspace/scratch/ca9a61d0bf30'); checkout=root/'import-correction-r3'; expected='901f734161920a76f3b399a575805b9a1d31e971'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=checkout,text=True).strip()==expected
assert not subprocess.check_output(['git','status','--porcelain'],cwd=checkout)
prior=json.loads((root/'session/validation/import-footprint-324962e-full-r1.json').read_text()); assert prior['status']=='finished' and prior['exit_code']!=0; command=prior['argv']
record_path=root/'session/validation/import-footprint-901f734-full-r1.json'; log_path=root/'active-validation/import-footprint-901f734-full-r1.log'
assert not record_path.exists() and not log_path.exists()
def now():return datetime.now(timezone.utc).isoformat()
record={'candidate':expected,'checkout':'import-correction-r3','argv':command,'started_at':now(),'status':'running','log':str(log_path.relative_to(root)),'owner_pid':os.getpid(),'acceptance':False,'ordinary_cache_evidence':'validation/import-footprint-r3-cache-copy.json','prior_failed_run':'validation/import-footprint-324962e-full-r1.json','reason':'Fourth direct-consumer import repaired; prior frozen324 run finished with recorded source compilation failure. Stock complete-candidate build/guard/exhaustive audit unchanged.'}
def save():record_path.write_text(json.dumps(record,indent=2)+'\n')
save()
with log_path.open('w') as log:
 child=subprocess.Popen(command,cwd=checkout,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,bufsize=1)
 for line in child.stdout:
  log.write(line);log.flush();print(line,end='',flush=True)
 result=child.wait()
record.update(status='finished',exit_code=result,ended_at=now(),head_after=subprocess.check_output(['git','rev-parse','HEAD'],cwd=checkout,text=True).strip(),clean_after=not subprocess.check_output(['git','status','--porcelain'],cwd=checkout))
verification=checkout/'.lake/verification.json'
record['verification_record_exists']=verification.exists()
if verification.exists():
 saved=root/'session/validation/import-footprint-901f734-verification-r1.json';shutil.copy2(verification,saved);record['verification_evidence']=str(saved.relative_to(root/'session'))
save();raise SystemExit(result)
