import datetime, json, os, pathlib, shutil, subprocess, sys, time
root = pathlib.Path(__file__).resolve().parent
cycle, category, purpose, *cmd = sys.argv[1:]
p = root / 'cycles' / cycle.zfill(2)
p.mkdir(parents=True, exist_ok=True)
check = len(list(p.glob('check-*.json'))) + 1
stem = f'check-{check:02d}'
snapshot = p / (stem + '-source')
shutil.copytree(root / 'work', snapshot)
record = dict(cycle=int(cycle), category=category, purpose=purpose, command=cmd,
              cwd=os.environ.get("TRIAL_COMMAND_CWD", os.getcwd()),
              started=datetime.datetime.now(datetime.timezone.utc).isoformat())
(p / (stem+'.json')).write_text(json.dumps(record,indent=2)+'\n')
start=time.monotonic()
with (p / (stem+'.txt')).open('w') as out:
 result=subprocess.run(cmd,cwd=record["cwd"],stdout=out,stderr=subprocess.STDOUT)
record.update(exit_code=result.returncode,seconds=time.monotonic()-start,
              ended=datetime.datetime.now(datetime.timezone.utc).isoformat())
(p / (stem+'.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
print((p / (stem+'.txt')).read_text()[-14000:])
sys.exit(result.returncode)
