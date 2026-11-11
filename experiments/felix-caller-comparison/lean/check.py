import datetime,hashlib,json,pathlib,subprocess,sys
p=pathlib.Path(__file__).parent
log=p/'attempts.jsonl'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def record(x):
 with log.open('a') as f:f.write(json.dumps(x)+'\n')
rounds=sum(json.loads(s).get('event')=='check-start' for s in log.read_text().splitlines())
assert rounds < 60
n=rounds+1
source=p/'Trial.lean'
snapshot=p/f'round-{n:02}.lean';snapshot.write_bytes(source.read_bytes())
cmd=['direnv','exec','.','taskset','-c','3','lake','env','lean',str(snapshot)]
record({'event':'check-start','round':n,'task':sys.argv[1],'time':now(),'sha256':hashlib.sha256(snapshot.read_bytes()).hexdigest(),'command':cmd,'snapshot':str(snapshot)})
r=subprocess.run(cmd,cwd='/tmp/conaled-wave-20261111/25-authors/lean-baseline',stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(p/f'round-{n:02}.log').write_bytes(r.stdout)
record({'event':'check-end','round':n,'time':now(),'exit':r.returncode})
print(r.stdout.decode());print('ROUND',n,'EXIT',r.returncode)
