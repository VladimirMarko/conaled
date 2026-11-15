import sys,subprocess,pathlib,datetime,json,hashlib,shutil
p=pathlib.Path(__file__).parent
log=p/'attempts.jsonl'
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def emit(x):
 with log.open('a') as f: f.write(json.dumps(x,ensure_ascii=False)+'\n')
args=sys.argv[1:]
if args[0]=='check':
 rounds=list((p/'snapshots').glob('*')) if (p/'snapshots').exists() else []
 n=len(rounds)+1
 assert n<=60
 dest=p/'snapshots'/f'{n:02d}';dest.mkdir(parents=True)
 hashes={}
 for f in p.glob('*.agda'):
  shutil.copy2(f,dest/f.name); hashes[f.name]=hashlib.sha256(f.read_bytes()).hexdigest()
 cmd=['nix','develop','/home/vlad/Code/felix','--command','agda','--no-libraries','-i',str(p),'-i','/tmp/conaled-wave-20261111/25-authors/felix-baseline/src','-i','/tmp/conaled-wave-20261111/25-environment/stdlib-src',str(p/args[1])]
 emit(dict(event='compiler_start',round=n,task=args[2],attempt_marker=args[3] if len(args)>3 else 'incremental',time=now(),command=cmd,hashes=hashes))
 r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (dest/'compiler.log').write_text(r.stdout)
 emit(dict(event='compiler_end',round=n,time=now(),exit=r.returncode,diagnostics=str(dest/'compiler.log')))
 print(r.stdout[-5000:]); print('ROUND',n,'EXIT',r.returncode)
else:
 emit(dict(event='note',time=now(),text=' '.join(args)))
