import datetime,json,pathlib,subprocess,sys
root=pathlib.Path('/tmp/conaled-wave-20261111/462-private-reference')
registry=pathlib.Path('/tmp/conaled-wave-20261111/462-trial-preparation/task-registry.json')
support=root/'applicability-support.lean'
cases=[('full','H1-full',['extension=PrivateApplicability462.extension'],'checked'),
 ('image','H1-image',[],'checked'),
 ('product','H2-product',['zero=PrivateApplicability462.product_zero','add=PrivateApplicability462.product_add'],'checked'),
 ('final','H2-final',['zero=PrivateApplicability462.final_zero','add=PrivateApplicability462.final_add'],'checked'),
 ('missing','H1-full',[],'missing evidence'),
 ('wrong-type','H1-full',['extension=PrivateApplicability462.product_zero'],'rejected evidence'),
 ('unknown','not-a-task-route',[],'registry exhausted')]
receipts=[]
for name,route,certs,status in cases:
 out=root/'applicability'/name
 command=[sys.executable,'scripts/interpretation-assist.py',route,'--registry',str(registry),'--out',str(out),'--support',str(support)]
 for cert in certs:command.extend(['--certificate',cert])
 started=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with (root/('applicability-'+name+'.log')).open('w') as log:
  result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
 record=json.loads((out/'receipt.json').read_text())
 receipts.append({'name':name,'command':command,'started':started,'finished':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':result.returncode,'expected':status,'actual':record['status']})
(root/'applicability-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
sys.exit(0 if all(r['expected']==r['actual'] for r in receipts) else 1)
