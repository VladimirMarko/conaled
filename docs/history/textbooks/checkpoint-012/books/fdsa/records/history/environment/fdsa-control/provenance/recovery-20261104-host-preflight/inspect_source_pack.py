#!/usr/bin/env python3
"""Read a compact checkpoint's included Git objects without restoring it.

This is read-only archive inspection, not git fsck or a restoration test.
The single externalized baseline blob is not present and is not acquired.
"""
import hashlib
import json
import struct
import sys
import tarfile
import zlib


def read_objects(archive):
    with tarfile.open(archive, "r:gz") as tar:
        member = next(m for m in tar.getmembers() if m.name.endswith("/source.pack"))
        pack = tar.extractfile(member).read()
    assert pack[:4] == b"PACK"
    assert hashlib.sha1(pack[:-20]).digest() == pack[-20:]
    version, count = struct.unpack(">II", pack[4:12])
    assert version == 2
    offset, entries, byid, pending = 12, {}, {}, []
    types = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}

    def varint(data, i):
        value = shift = 0
        while True:
            byte = data[i]
            i += 1
            value |= (byte & 127) << shift
            if not byte & 128:
                return value, i
            shift += 7

    def apply_delta(base, data):
        size, i = varint(data, 0)
        expected, i = varint(data, i)
        assert size == len(base)
        out = bytearray()
        while i < len(data):
            byte = data[i]
            i += 1
            if byte & 128:
                start = length = 0
                for bit, shift in [(1, 0), (2, 8), (4, 16), (8, 24)]:
                    if byte & bit:
                        start |= data[i] << shift
                        i += 1
                for bit, shift in [(16, 0), (32, 8), (64, 16)]:
                    if byte & bit:
                        length |= data[i] << shift
                        i += 1
                out.extend(base[start:start + (length or 65536)])
            else:
                assert byte
                out.extend(data[i:i + byte])
                i += byte
        assert len(out) == expected
        return bytes(out)

    def save(pos, kind, data):
        oid = hashlib.sha1(f"{kind} {len(data)}\0".encode() + data).hexdigest()
        entries[pos] = kind, data, oid
        byid[oid] = kind, data

    for _ in range(count):
        start = offset
        byte = pack[offset]
        offset += 1
        kind, size, shift = (byte >> 4) & 7, byte & 15, 4
        while byte & 128:
            byte = pack[offset]
            offset += 1
            size |= (byte & 127) << shift
            shift += 7
        base = None
        if kind == 6:
            byte = pack[offset]
            offset += 1
            distance = byte & 127
            while byte & 128:
                byte = pack[offset]
                offset += 1
                distance = ((distance + 1) << 7) | (byte & 127)
            base = start - distance
        elif kind == 7:
            base = pack[offset:offset + 20].hex()
            offset += 20
        decoder = zlib.decompressobj()
        data = decoder.decompress(pack[offset:])
        assert decoder.eof and len(data) == size
        offset = len(pack) - len(decoder.unused_data)
        if kind in types:
            save(start, types[kind], data)
        else:
            assert kind in (6, 7)
            pending.append((start, kind, base, data))
    while pending:
        rest = []
        for pos, kind, base, data in pending:
            known = entries.get(base) if kind == 6 else byid.get(base)
            if known:
                save(pos, known[0], apply_delta(known[1], data))
            else:
                rest.append((pos, kind, base, data))
        assert len(rest) < len(pending), "Unresolved deltas"
        pending = rest
    assert offset == len(pack) - 20 and len(byid) == count
    return byid


def read_path(objects, commit, path):
    tree = objects[commit][1].splitlines()[0].decode().split()[1]
    oid = tree
    for part in path.split("/"):
        kind, data = objects[oid]
        assert kind == "tree"
        i, found = 0, False
        while i < len(data):
            j = data.index(b" ", i)
            k = data.index(b"\0", j)
            name = data[j + 1:k].decode()
            value = data[k + 1:k + 21].hex()
            i = k + 21
            if name == part:
                oid, found = value, True
                break
        if not found:
            raise KeyError(path)
    return objects[oid][1]


if __name__ == "__main__":
    objects = read_objects(sys.argv[1])
    print(json.dumps({"included_objects_resolved": len(objects),
                      "pack_trailer_verified": True,
                      "restoration_performed": False, "git_fsck_performed": False}))
    for path in sys.argv[3:]:
        print("\n### " + path + "\n")
        print(read_path(objects, sys.argv[2], path).decode())
