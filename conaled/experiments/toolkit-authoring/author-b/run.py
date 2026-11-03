import subprocess, sys, pathlib, datetime, json, hashlib
p = pathlib.Path(sys.argv[1])
base = p.with_suffix('')
cmd = ['direnv','exec','.','lake','env','lean',str(p)]
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
meta = {'command':cmd,'start':now(),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
assert not base.with_suffix('.log').exists()
with base.with_suffix('.log').open('w') as log:
    result = subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
meta.update(finish=now(),exit=result.returncode)
base.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta))
print(base.with_suffix('.log').read_text())
