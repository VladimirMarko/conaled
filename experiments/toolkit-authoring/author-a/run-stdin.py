import subprocess,datetime,json,pathlib,hashlib
p=pathlib.Path('experiments/toolkit-authoring/author-a/Final.lean')
stem=p.parent/'FinalStdin'
assert not stem.with_suffix('.log').exists()
cmd=['direnv','exec','.','lake','env','lean','--stdin','Examples/ToolkitAuthorTrialA.lean']
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
with p.open('rb') as source, stem.with_suffix('.log').open('wb') as f:
 r=subprocess.run(cmd,stdin=source,stdout=f,stderr=subprocess.STDOUT)
end=datetime.datetime.now(datetime.timezone.utc).isoformat()
stem.with_suffix('.json').write_text(json.dumps(dict(command=cmd,stdin=str(p),start=start,finish=end,exit=r.returncode,sha256=hashlib.sha256(p.read_bytes()).hexdigest()),indent=2)+'\n')
print('EXIT',r.returncode)
