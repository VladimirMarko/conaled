#!/usr/bin/env python3
"""Verify exact prefix/slice recipes, optionally materializing only into a fresh external folder."""
import argparse, hashlib, json, os
from pathlib import Path

def verify(raw,d):
    assert len(raw)==d['bytes'] and hashlib.sha256(raw).hexdigest()==d['sha256']

def reconstruct(spec,root,mapping):
    result={}
    for row in spec['files']:
        parts=[]
        for piece in row['pieces']:
            if 'literal_utf8' in piece:part=piece['literal_utf8'].encode()
            else:
                src=piece['source'];path=Path(mapping.get(src,root/src))
                assert path.is_file() and not path.is_symlink()
                raw=path.read_bytes();verify(raw,piece['source_descriptor'])
                assert format(path.stat().st_mode,'o')==piece['source_descriptor']['mode']
                part=raw[piece['byte_start']:piece['byte_end_exclusive']]
                assert hashlib.sha256(part).hexdigest()==piece['slice_sha256']
            parts.append(part)
        raw=b''.join(parts);verify(raw,row['target_descriptor']);result[row['target_member']]=raw
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('manifest',type=Path);ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--path-map',type=Path);ap.add_argument('--output',type=Path)
    args=ap.parse_args();spec=json.loads(args.manifest.read_text());mapping=json.loads(args.path_map.read_text()) if args.path_map else {}
    result=reconstruct(spec,args.root,mapping)
    if args.output:
        assert not args.output.exists(),'Fresh output directory required';args.output.mkdir(parents=True)
        for row in spec['files']:
            rel=Path(row['target_member']);assert not rel.is_absolute() and '..' not in rel.parts
            dst=args.output/rel;dst.parent.mkdir(parents=True,exist_ok=True)
            with dst.open('xb') as f:f.write(result[str(rel)])
            dst.chmod(int(row['target_descriptor']['mode'],8)&0o777)
    print(json.dumps({'files_verified':len(result),'all_exact':True,'compiler_run':False,'materialized':bool(args.output)},indent=2))

if __name__=='__main__':main()
