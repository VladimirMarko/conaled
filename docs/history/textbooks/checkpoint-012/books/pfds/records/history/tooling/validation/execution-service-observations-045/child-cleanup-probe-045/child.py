import sys
from pathlib import Path
from datetime import datetime,timezone
import os,time,json,fcntl
p=Path(sys.argv[1])
with (p/'child.lock').open('w') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 (p/'started.json').write_text(json.dumps({'time':time.time(),'pid':os.getpid(),'ppid':os.getppid(),'pgid':os.getpgrp()}))
 for i in range(7):
  (p/'latest.json').write_text(json.dumps({'tick':i,'time':time.time()}))
  if i<6:time.sleep(2)
 (p/'completed.json').write_text(json.dumps({'time':time.time(),'completed':True}))
