#!/usr/bin/env python3
"""Verify or materialize an exact historical proof-check input, without Lean.

Usage: python reassemble_research.py MANIFEST --root WORKSPACE [--output NEWFILE]
Paths in MANIFEST are workspace-relative. A future archive can supply an
explicit JSON {original_path: recovered_path} through --path-map. With no
--output all reconstruction occurs in memory and only the digest is printed.
"""
import argparse
from hashlib import sha256
from pathlib import Path
import json

ap=argparse.ArgumentParser()
ap.add_argument('manifest',type=Path)
ap.add_argument('--root',type=Path,required=True)
ap.add_argument('--path-map',type=Path)
ap.add_argument('--output',type=Path)
a=ap.parse_args()
d=json.loads(a.manifest.read_text())
mapping=json.loads(a.path_map.read_text()) if a.path_map else {}
data={}
for row in d['inputs']:
    original=row['path'];p=a.root/mapping.get(original,original)
    b=p.read_bytes()
    assert len(b)==row['bytes'] and sha256(b).hexdigest()==row['sha256'],original
    data[original]=b
pieces=[]
for row in d['pieces']:
    if 'literal_utf8' in row:
        pieces.append(row['literal_utf8'].encode())
    else:
        b=data[row['source']][row['byte_start']:row['byte_end_exclusive']]
        assert sha256(b).hexdigest()==row['slice_sha256'],row['source']
        pieces.append(b)
result=b''.join(pieces)
assert len(result)==d['target']['bytes']
assert sha256(result).hexdigest()==d['target']['sha256']
if a.output:
    with a.output.open('xb') as stream: stream.write(result)
    a.output.chmod(0o644)
print(json.dumps({'bytes':len(result),'sha256':sha256(result).hexdigest(),
                  'written':str(a.output) if a.output else None,
                  'compiler_run':False,'meaning':'exact source reconstruction only'}))
