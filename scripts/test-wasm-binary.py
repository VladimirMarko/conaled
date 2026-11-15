#!/usr/bin/env python3
"""Independent selected-Core parser and hand-calculated serializer fixtures.
Run: direnv exec . python3 scripts/test-wasm-binary.py emitted.jsonl
The input is produced by lake env lean --run scripts/wasm-fixtures.lean.
"""
import json
import sys


class Reader:
    def __init__(self, data):
        self.data = bytes(data)
        self.pos = 0

    def byte(self):
        if self.pos == len(self.data):
            raise ValueError('unexpected end')
        result = self.data[self.pos]
        self.pos += 1
        return result

    def expect(self, value):
        if self.byte() != value:
            raise ValueError('wrong byte')

    def leb(self, signed=False):
        result = 0
        for shift in range(0, 35, 7):
            digit = self.byte()
            result |= (digit & 127) << shift
            if digit < 128:
                if signed and digit & 64:
                    result -= 1 << (shift + 7)
                if not (-2**31 <= result < 2**31 if signed else 0 <= result < 2**32):
                    raise ValueError('integer overflow')
                return result
        raise ValueError('integer too long')

    def vector(self, item):
        return [item() for _ in range(self.leb())]

    def sized(self):
        size = self.leb()
        end = self.pos + size
        if end > len(self.data):
            raise ValueError('length exceeds input')
        sub = Reader(self.data[self.pos:end])
        self.pos = end
        return sub

    def done(self):
        if self.pos != len(self.data):
            raise ValueError('unconsumed bytes')

    def valtype(self):
        b = self.byte()
        if b not in (0x7f, 0x7e, 0x7d, 0x7c, 0x7b, 0x70, 0x6f):
            raise ValueError('value type')
        return b

    def functype(self):
        self.expect(0x60)
        return self.vector(self.valtype), self.vector(self.valtype)

    def export(self):
        name = self.sized()
        text = name.data.decode('utf-8')
        self.expect(0)
        return text, self.leb()

    def body(self):
        body = self.sized()
        groups = body.vector(lambda: (body.leb(), body.valtype()))
        local_count = sum(count for count, _ in groups)
        if local_count >= 2**32:
            raise ValueError('expanded locals overflow')
        instructions = []
        while True:
            op = body.byte()
            if op == 11:
                break
            if op in (0x20, 0x21):
                instructions.append((op, body.leb()))
            elif op == 0x41:
                instructions.append((op, body.leb(signed=True)))
            elif op in (0x45, 0x71, 0x72, 0x73):
                instructions.append((op,))
            else:
                raise ValueError('unsupported opcode')
        body.done()
        return groups, instructions


def parse(data):
    r = Reader(data)
    for b in b'\0asm\x01\0\0\0':
        r.expect(b)
    sections = []
    for ident, item in ((1, Reader.functype), (3, Reader.leb),
                        (7, Reader.export), (10, Reader.body)):
        r.expect(ident)
        section = r.sized()
        sections.append(section.vector(lambda: item(section)))
        section.done()
    r.done()
    types, funcs, exports, bodies = sections
    if len(types) != 1 or funcs != [0] or exports != [('run', 0)] or len(bodies) != 1:
        raise ValueError('selected module agreement')
    return types[0], bodies[0]


def rejects(data):
    try:
        parse(data)
    except (ValueError, UnicodeError):
        return
    raise AssertionError(f'accepted malformed module: {data.hex()}')


def main():
    fixtures = {r['name']: bytes(r['bytes']) for r in map(json.loads, open(sys.argv[1]))}
    unit = bytes.fromhex('0061736d01000000 010401600000 03020100 0707010372756e0000 0a040102000b')
    assert fixtures['unit'] == unit
    for name, value, encoded in [('negative', -1, '7f'), ('highbit', -2147483648, '8080808078')]:
        # Header/type/function/export sections and payload sizes calculated by hand.
        instr = bytes.fromhex('41' + encoded + '0b')
        body = b'\0' + instr
        code = bytes([10, len(body)+2, 1, len(body)]) + body
        expected = bytes.fromhex('0061736d01000000 0105016000017f 03020100 0707010372756e0000') + code
        assert fixtures[name] == expected
        assert parse(fixtures[name])[1][1] == [(0x41, value)]
    for data in fixtures.values():
        parse(data)
    signature, (groups, instructions) = parse(fixtures['selector32'])
    assert list(map(len, signature)) == [65, 96]
    assert sum(n for n, _ in groups) + 65 == 866
    assert len(instructions) == 3266
    assert list(map(len, parse(fixtures['nested'])[0])) == [6, 3]
    assert list(map(len, parse(fixtures['two-delay'])[0])) == [3, 3]
    assert parse(fixtures['index128'])[1][1] == [(0x20, 128)]
    # Header/version, order, sizes, vector agreement, type, export name/kind/index,
    # body size, expanded local layout, expression end, truncation and trailing data.
    for offset, replacement in [(0,1),(4,2),(8,3),(9,5),(10,2),(11,0x61),
                                (14,7),(17,1),(23,ord('x')),(26,1),
                                (30,3),(31,1),(32,0x45)]:
        damaged = bytearray(unit)
        damaged[offset] = replacement
        rejects(damaged)
    rejects(unit[:-1])
    rejects(unit + b'\0')
    for payload in [b'\x80'*5+b'\0', bytes.fromhex('ffffffff10')]:
        try:
            Reader(payload).leb()
        except ValueError:
            pass
        else:
            raise AssertionError('accepted overflowing u32')
    for payload in [bytes.fromhex('8080808008'), bytes.fromhex('ffffffff77')]:
        try:
            Reader(payload).leb(signed=True)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted overflowing s32')
    print(f'{len(fixtures)} fixtures and independent mutation checks passed')


if __name__ == '__main__':
    main()
