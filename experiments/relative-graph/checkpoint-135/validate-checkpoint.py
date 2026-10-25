from pathlib import Path
import os, subprocess, time, json
state=Path('/home/vlad/.local/state/conaled-supervision/2026-10-25/128/135')
build=state/'checkpoint-build'
build.mkdir(exist_ok=True)
logs=state/'checkpoint-logs'
logs.mkdir(exist_ok=True)
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
env=os.environ.copy()
env['LEAN_PATH']=str(build)+':/home/vlad/.local/state/conaled-supervision/2026-10-25/128/134/con-leche/.lake/build/lib/lean:'+base
modules=['EmissionEncoding','CheckerReduction','AcceptanceStages','EmissionSemantics','EmittedGraph','EmittedEnvironment','EmittedComparison','EmittedClosed','AndPositivityStages']
results=[]
for module in modules:
    start=time.monotonic()
    with (logs/(module+'.log')).open('w') as log:
        result=subprocess.run(['lean','-o',str(build/(module+'.olean')),'experiments/relative-graph/'+module+'.lean'],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=120)
    row={'module':module,'exit':result.returncode,'seconds':round(time.monotonic()-start,3),'log':str(logs/(module+'.log'))}
    results.append(row)
    print(json.dumps(row),flush=True)
    (state/'checkpoint-validation.json').write_text(json.dumps(results,indent=2)+'\n')
    if result.returncode: raise SystemExit(result.returncode)
