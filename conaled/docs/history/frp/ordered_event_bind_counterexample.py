"""A regression example for a proposed stable chronological event bind.

This is a mathematical-model example, not a reproduction of the historical
Reactive/GHC runtime bugs. Python's sort is stable, so equal-time results retain
the outer occurrence order.
"""
from collections.abc import Callable
from typing import TypeVar

A = TypeVar("A")
B = TypeVar("B")


def bind(events: list[tuple[int, A]],
         continuation: Callable[[A], list[tuple[int, B]]]) -> list[tuple[int, B]]:
    occurrences = [
        (max(outer_time, inner_time), value)
        for outer_time, payload in events
        for inner_time, value in continuation(payload)
    ]
    return sorted(occurrences, key=lambda occurrence: occurrence[0])


def main() -> None:
    events = [(0, "a"), (1, "b")]
    first = {"a": [(3, "x")], "b": [(2, "y")]}
    second = {"x": [(4, "X")], "y": [(4, "Y")]}
    left = bind(bind(events, first.__getitem__), second.__getitem__)
    right = bind(events, lambda a: bind(first[a], second.__getitem__))
    assert left == [(4, "Y"), (4, "X")]
    assert right == [(4, "X"), (4, "Y")]
    assert left != right
    print("left association:", left)
    print("right association:", right)
    print("Stable chronological bind is not associative for ordered batches.")


if __name__ == "__main__":
    main()
