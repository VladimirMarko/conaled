
from pathlib import Path
from datetime import datetime,timezone
import os,json,hashlib,stat
b=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104');c=b/'fdsa-control';p=c/'provenance/checkpoint0134-local-archive-retirement-20261104'
assert not p.exists()
expected={
'0131':('conaled-fdsa-0131-checked-cutoffs-and-selection-bounds',35462405,'d175862b1469230d0549833dc20f9e1d9d175f23279fe1a8852fdd2ce5fa6294','libfile_0a5e522091208191b18dba386da19e76'),
'0132':('conaled-fdsa-0132-selection-composition-and-random-boundaries',36475630,'ca7309e95b12e2efc5561b689a439814d86b7e172730caa7de0575509ae8164b','libfile_115ebb7de8a881918b20f4d48ae0111e'),
'0133':('conaled-fdsa-0133-selection-integration-and-endpoint-progress',37279344,'aa77f4c286be99530cad300b38109e0a40ca06f8ad8d0b59d59eeb3cc4d687e0','libfile_243f38a7e8388191b70bff75b3777f88'),
'0134':('conaled-fdsa-0134-random-selection-path-progress',38083636,'2d70445d6636cb3e86828e5838e978b6282eb2fdfd24bdbd3e38eb6710fbcb70','libfile_5ec3dbda67688191af137be4694522b1')}
def ident(q):
 with q.open('rb') as f:h=hashlib.file_digest(f,'sha256').hexdigest()
 s=q.lstat();assert stat.S_ISREG(s.st_mode) and not q.is_symlink() and s.st_nlink==1
 return {'path':str(q),'bytes':s.st_size,'sha256':h,'device':s.st_dev,'inode':s.st_ino,'allocated_bytes':s.st_blocks*512}
def space():
 s=os.statvfs(b);return {'ordinary_available_bytes':s.f_bavail*s.f_frsize,'raw_free_bytes':s.f_bfree*s.f_frsize}
def write(q,x):
 with q.open('x') as f:json.dump(x,f,indent=2);f.write('\n')
catalog=json.loads((c/'checkpoints.json').read_text())['checkpoints'];ids={};records={}
for number,(name,size,digest,libid) in expected.items():
 q=b/'checkpoints'/(name+'.tar.gz');row=ident(q);assert row['bytes']==size and row['sha256']==digest
 r=next(x for x in catalog if x['name']==name)
 assert r['status']=='succeeded' and r['library_file_id']==libid and r['size_bytes']==size and r['sha256']==digest and r['post_upload_hash_matched'] and r['metadata_exit']==0
 d=c/('provenance/checkpoint'+number+'-preparation')
 u=json.loads((d/'upload.json').read_text());post=json.loads((d/'post-upload-hash.json').read_text());vr=json.loads((d/'integrity.json').read_text())
 assert u['status']=='succeeded' and u['library_file_id']==libid and u['file_size_bytes']==size
 assert post['post_upload_hash_matched'] and post['bytes']==size and post['sha256']==digest
 assert vr['bytes']==size and vr['sha256']==digest
 assert os.getxattr(q,'user.library-file-id').decode()==libid and os.getxattr(q,'user.library-file-version').decode()==str(u['current_version_number'])
 ids[number]=row;records[number]={'name':name,'library_file_id':libid,'size_bytes':size,'sha256':digest,'upload_succeeded':True,'integrity_and_postupload_hash_matched':True,'metadata_matched':True}
before=space();p.mkdir()
pre={'recorded_utc':datetime.now(timezone.utc).isoformat(),'purpose':'Retire only two exact redundant local task archives after verified standalone0134 upload; keep latest two local standalone archives, remote copies, sidecars and all evidence.','remove':['0131','0132'],'retain':['0133','0134'],'identities':ids,'verified_upload_records':records,'before':before,'no_compiler_currently_owned':True,'no_other_files_selected':True,'source_refs_logs_native_environment_and_compiler_outputs_not_selected':True}
write(p/'preflight.json',pre)
for number in ['0131','0132']:
 q=Path(ids[number]['path']);assert ident(q)==ids[number]
 q.unlink()
 write(p/('removed-'+number+'.json'),{'recorded_utc':datetime.now(timezone.utc).isoformat(),'number':number,'original_identity':ids[number],'path_absent':not q.exists(),'remote_not_mutated':True})
for number in ['0133','0134']:assert ident(Path(ids[number]['path']))==ids[number]
assert all(not Path(ids[n]['path']).exists() for n in ['0131','0132'])
r={'recorded_utc':datetime.now(timezone.utc).isoformat(),'removed_numbers':['0131','0132'],'removed_files':2,'removed_logical_bytes':sum(ids[n]['bytes'] for n in ['0131','0132']),'removed_allocated_bytes':sum(ids[n]['allocated_bytes'] for n in ['0131','0132']),'retained_exact':['0133','0134'],'before':before,'after':space(),'only_selected_two_local_archives_removed':True,'no_remote_mutation':True,'no_source_ref_log_environment_or_output_mutation':True,'net_filesystem_delta_not_attributed_exclusively_to_this_action':True,'one_use_completed_do_not_rerun':True}
write(p/'result.json',r);print(json.dumps(r,indent=2))
