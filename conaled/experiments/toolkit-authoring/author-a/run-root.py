import subprocess,datetime,json,pathlib,hashlib
root=pathlib.Path('experiments/toolkit-authoring/author-a')
p=root/'Examples/ToolkitAuthorTrialA.lean'
stem=root/'FinalRoot'
assert not stem.with_suffix('.log').exists()
cmd=['direnv','exec','.','lake','env','lean','--root='+str(root),str(p)]
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
with stem.with_suffix('.log').open('wb') as f:
 r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
end=datetime.datetime.now(datetime.timezone.utc).isoformat()
stem.with_suffix('.json').write_text(json.dumps(dict(command=cmd,source=str(p),start=start,finish=end,exit=r.returncode,sha256=hashlib.sha256(p.read_bytes()).hexdigest()),indent=2)+'\n')
print('EXIT',r.returncode)
