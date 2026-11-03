import sys,subprocess,datetime,json,pathlib,hashlib
p=pathlib.Path(sys.argv[1]); stem=p.with_suffix('')
assert not stem.with_suffix('.log').exists()
cmd=['direnv','exec','.','lake','env','lean',str(p)]
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
with stem.with_suffix('.log').open('wb') as f:
 r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
end=datetime.datetime.now(datetime.timezone.utc).isoformat()
stem.with_suffix('.json').write_text(json.dumps(dict(command=cmd,start=start,finish=end,exit=r.returncode,sha256=hashlib.sha256(p.read_bytes()).hexdigest()),indent=2)+'\n')
print(stem.with_suffix('.log').read_text()); print('EXIT',r.returncode)
