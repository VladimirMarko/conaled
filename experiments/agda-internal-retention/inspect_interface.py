#!/usr/bin/env python3
"""Bounded, untrusted inspector for Agda 2.8.0.2 interface format 202507030.

This is a research diagnostic, not a supported interchange reader. It decodes
selected declaration envelopes and term references. Other fields remain raw.
See README.md for the pinned serialization sources and known information loss.
"""
import argparse
import gzip
import hashlib
import json
import struct
from pathlib import Path


class Reader:
    def __init__(self, data):
        self.data = data
        self.position = 0

    def read(self, size):
        value = self.data[self.position:self.position + size]
        self.position += size
        if len(value) != size:
            raise ValueError("Truncated interface")
        return value

    def word(self):
        return struct.unpack(">I", self.read(4))[0]

    def length(self):
        return struct.unpack(">Q", self.read(8))[0]

    def text(self):
        return self.read(self.length()).decode("utf-8")

    def string(self):
        # Binary String counts Unicode characters; Text counts UTF-8 bytes.
        chars = []
        for _ in range(self.length()):
            first = self.read(1)
            size = 1 if first[0] < 128 else 2 if first[0] < 224 else 3 if first[0] < 240 else 4
            chars.append((first + self.read(size - 1)).decode("utf-8"))
        return "".join(chars)


class Interface:
    def __init__(self, path):
        data = path.read_bytes()
        self.digest = hashlib.sha256(data).hexdigest()
        self.header = struct.unpack(">QQQ", data[:24])
        if self.header[2] != 202507030:
            raise ValueError("Unsupported interface version")
        reader = Reader(gzip.decompress(data[24:]))
        self.root = reader.word()
        self.nodes = [[reader.word() for _ in range(reader.length())]
                      for _ in range(reader.length())]
        self.strings = [reader.string() for _ in range(reader.length())]
        self.lazy_text = [reader.text() for _ in range(reader.length())]
        self.strict_text = [reader.text() for _ in range(reader.length())]
        # Numeric literals are deliberately not decoded in this experiment.
        self.numeric_tail = reader.data[reader.position:].hex()
        self.fields = self.nodes[self.root]
        if len(self.fields) != 24:
            raise ValueError("Unexpected Interface envelope")

    def raw(self, index):
        return {"node": index, "words": self.nodes[index]}

    def name(self, index):
        fields = self.nodes[index]
        concrete = self.nodes[fields[1]]
        if concrete[0] == 0:
            return "_"
        if len(concrete) != 4 or concrete[0] != 1:
            raise ValueError("Unsupported concrete name")
        return "".join(self.strings[self.nodes[p][0]] if self.nodes[p] else "_"
                       for p in self.nodes[concrete[3]])

    def qname(self, index):
        module, name = self.nodes[index]
        return ".".join([self.name(p) for p in self.nodes[module]] + [self.name(name)])

    def summary(self, term_index):
        """Visit typed term positions, not untyped numeric node references."""
        seen = set()
        references = set()
        tags = {}
        unresolved = []

        def typ(index):
            sort, term = self.nodes[index]
            # Sort/level references are retained raw, not traversed here.
            visit(term)

        def eliminations(index):
            for elimination in self.nodes[index]:
                fields = self.nodes[elimination]
                if len(fields) == 1:
                    visit(self.nodes[fields[0]][1])  # Apply (Arg info term)
                elif len(fields) == 3 and fields[0] == 0:
                    references.add(self.qname(fields[2]))
                elif len(fields) == 4 and fields[0] == 0:
                    for term in fields[1:]:
                        visit(term)
                else:
                    raise ValueError("Unsupported elimination")

        def visit(index):
            if index in seen:
                return
            seen.add(index)
            fields = self.nodes[index]
            tag = "Var" if len(fields) == 1 else {
                0: "Var", 1: "Lam", 2: "Lit", 3: "Def", 4: "Con",
                5: "Pi", 6: "MetaV", 7: "Sort", 8: "DontCare",
                9: "Level", 10: "Dummy"}[fields[0]]
            tags[tag] = tags.get(tag, 0) + 1
            if len(fields) == 1:
                return
            if tag in ("Var", "Def", "MetaV", "Dummy"):
                if tag == "Def":
                    references.add(self.qname(fields[1]))
                if tag in ("MetaV", "Dummy"):
                    unresolved.append(self.raw(index))
                eliminations(fields[2])
            elif tag == "Lam":
                visit(self.nodes[fields[2]][-1])
            elif tag == "Con":
                references.add(self.qname(self.nodes[fields[1]][0]))
                eliminations(fields[3])
            elif tag == "Pi":
                typ(self.nodes[fields[1]][4])
                typ(self.nodes[fields[2]][-1])
            elif tag == "DontCare":
                visit(fields[1])

        visit(term_index)
        return {"root": self.raw(term_index), "termTags": tags,
                "references": sorted(references), "unresolvedTermPositions": unresolved,
                "notTraversed": ["sorts", "levels", "literals", "binder metadata"]}

    def declarations(self, suffixes):
        signature = self.nodes[self.fields[8]]
        definitions = self.nodes[signature[1]]
        result = []
        for offset in range(0, len(definitions), 2):
            name = self.qname(definitions[offset])
            if not any(name == suffix or name.endswith("." + suffix) for suffix in suffixes):
                continue
            fields = self.nodes[definitions[offset + 1]]
            if len(fields) != 18:
                raise ValueError("Unexpected Definition envelope")
            definition = self.nodes[fields[17]]
            sort, term = self.nodes[fields[2]]
            row = {"name": name, "fields": fields, "defn": definition,
                   "typeSort": self.raw(sort), "typeTerm": self.summary(term),
                   "language": self.raw(fields[16])}
            if definition[0] == 1:
                clauses = []
                for index in self.nodes[definition[1]]:
                    clause = self.nodes[index]
                    if len(clause) != 11:
                        raise ValueError("Unexpected Clause envelope")
                    body = self.nodes[clause[4]]
                    clauses.append({"raw": self.raw(index),
                                    "patterns": [self.raw(p) for p in self.nodes[clause[3]]],
                                    "body": self.summary(body[0]) if body else None})
                row.update(clauses=clauses, compiled=self.raw(definition[2]),
                           flags=self.raw(definition[8]), terminates=self.raw(definition[9]),
                           opaque=self.raw(definition[13]))
            result.append(row)
        return result

    def report(self, names):
        environment = {name: self.raw(self.fields[index]) for name, index in (
            ("imports", 3), ("metaBindings", 9), ("builtins", 13),
            ("filePragmas", 17), ("optionsUsed", 18), ("partialDefs", 21),
            ("opaqueBlocks", 22), ("opaqueNames", 23))}
        signature = self.nodes[self.fields[8]]
        return {"sha256": self.digest, "header": self.header, "interface": self.fields,
                "sourceSha256": hashlib.sha256(self.lazy_text[self.fields[1]].encode()).hexdigest(),
                "environment": environment, "rewriteRules": self.raw(signature[2]),
                "declarations": self.declarations(names)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("interface", type=Path)
    parser.add_argument("names", nargs="+")
    parser.add_argument("--raw-tables", type=Path)
    args = parser.parse_args()
    interface = Interface(args.interface)
    if args.raw_tables:
        args.raw_tables.write_text(json.dumps(vars(interface), ensure_ascii=False))
    print(json.dumps(interface.report(args.names), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
