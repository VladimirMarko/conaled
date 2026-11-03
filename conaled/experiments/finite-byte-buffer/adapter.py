"""Single-threaded finite byte-buffer adapter; see the recorded trust boundary."""
import ctypes

MAX_WORD = 2**32 - 1
# Preallocated replies permit refusal reporting without constructing a tuple.
ACCEPTED = ('accepted', None)
OVERFLOW = ('overflow', None)
ALLOCATION = ('allocation', None)
OUTPUT = ('output', None)
SUMMARIES = (('summary', 0), ('summary', 1))

class Environment:
    """Controlled failures at allocation/commit-preparation and output boundaries."""
    def __init__(self, fail_allocation=False, fail_output=False):
        self.fail_allocation = fail_allocation
        self.fail_output = fail_output

    def prepare(self):
        if self.fail_allocation:
            raise MemoryError('injected allocation/preparation refusal')

    def snapshot(self, slots, size):
        if self.fail_output:
            raise MemoryError('injected output refusal')
        return bytes(slots[:size])

DEFAULT_ENV = Environment()

def successor(size, capacity, word_max=MAX_WORD):
    """Guarded finite-counter primitive; never return a modularly wrapped value."""
    if any(type(x) is not int for x in (size, capacity, word_max)) or not 0 <= size <= capacity <= word_max <= MAX_WORD:
        raise ValueError('counter outside finite word range')
    return None if size == capacity else size + 1

class Buffer:
    __slots__ = ('_slots', '_size', '_capacity', '_cached', '_parity', '_word_max')

    def step(self, command, env=DEFAULT_ENV):
        op, value = command
        if op not in ('append', 'query', 'observe'):
            raise ValueError('unknown command')
        if op == 'append' and (type(value) is not int or value not in (0, 1)):
            raise ValueError('not a Boolean byte')
        try:
            env.prepare()
            size = self._size.value
            if op == 'append':
                # All fallible Python arithmetic precedes the commit primitive.
                next_size = successor(size, self._capacity.value, self._word_max)
                if next_size is None:
                    return OVERFLOW
                next_parity = self._parity ^ value if self._cached else self._parity
                # Trust: these in-range writes to existing storage do not fail.
                self._slots[size] = value
                self._size.value = next_size
                self._parity = next_parity
                return ACCEPTED
            if op == 'query':
                parity = self._parity
                if not self._cached:
                    parity = 0
                    for i in range(size):
                        parity ^= self._slots[i]
                return SUMMARIES[parity]
        except MemoryError:
            return ALLOCATION
        try:
            return ('sequence', env.snapshot(self._slots, size))
        except MemoryError:
            return OUTPUT

    def convert(self, env=DEFAULT_ENV):
        try:
            env.prepare()
            result = object.__new__(Buffer)
            result._slots = self._slots.copy()
            result._size = ctypes.c_uint32(self._size.value)
            result._capacity = ctypes.c_uint32(self._capacity.value)
            result._cached = True
            result._word_max = self._word_max
            result._parity = 0
            for i in range(result._size.value):
                result._parity ^= result._slots[i]
            return ('ready', result)
        except MemoryError:
            return ALLOCATION


def create(capacity, cached=False, *, word_max=MAX_WORD, env=DEFAULT_ENV):
    if type(word_max) is not int or not 0 <= word_max <= MAX_WORD:
        raise ValueError('invalid word maximum')
    if type(capacity) is not int or not 0 <= capacity <= word_max:
        raise ValueError('capacity outside finite word range')
    if type(cached) is not bool:
        raise ValueError('mode is not Boolean')
    try:
        env.prepare()
        b = object.__new__(Buffer)
        b._slots = bytearray(capacity)
        b._size = ctypes.c_uint32(0)
        b._capacity = ctypes.c_uint32(capacity)
        b._cached = cached
        b._parity = 0
        b._word_max = word_max
        return ('ready', b)
    except MemoryError:
        return ALLOCATION
