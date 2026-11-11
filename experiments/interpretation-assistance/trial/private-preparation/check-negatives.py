import datetime, json, pathlib, subprocess, sys
root = pathlib.Path('/tmp/conaled-wave-20261111/462-private-reference')
receipts=[]
for name in ['WrongH1','WrongH2']:
    command=['lake','env','lean',str(root/(name+'.lean'))]
    start=datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (root/(name+'.log')).open('w') as out:
        r=subprocess.run(command,stdout=out,stderr=subprocess.STDOUT)
    receipts.append({'name':name,'command':command,'start':start,'end':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':r.returncode})
(root/'negative-receipts.json').write_text(json.dumps(receipts,indent=2))
sys.exit(0 if all(r['exit'] != 0 for r in receipts) else 1)
