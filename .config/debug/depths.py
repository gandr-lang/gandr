"""A summary of a nested Rust aggregate, cut at lldb's child depth.

rustc's formatters summarise a struct or a tuple by the summary of every
field, and each field the same way, with no depth limit. A backtrace prints a
frame's arguments by their summaries. A receiver such as the lowering's
`Lowerer` nests deeper than Python's recursion limit, so the backtrace prints
thousands of `RecursionError` tracebacks or never returns (#3809).
`rust_formatters.py` wraps both summaries in `bounded`. Below lldb's
`target.max-children-depth`, an aggregate prints as `{…}` or `(…)`, as lldb
elides children past that depth.

Run as a script, the module checks the cases of a JSON file
(`.config/debug/depths.json`): `python3 depths.py <cases>`.
"""

import functools
import json
import sys
from typing import Any, Callable

Summary = Callable[[Any, dict], str]


class Depth:
    """The nesting of the summary being written, shared by every summary it reaches."""

    def __init__(self) -> None:
        self.current = 0
        self.limit = 0


def bounded(summary: Summary, elided: str, depth: Depth, limit: Callable[[Any], int]) -> Summary:
    """`summary`, which prints `elided` at `depth.limit` levels below the outermost.

    The outermost summary reads the limit from its value. A summary that
    raises leaves the depth as it found it.
    """

    @functools.wraps(summary)
    def bounded_summary(value: Any, internal_dict: dict) -> str:
        if depth.current == 0:
            depth.limit = limit(value)
        elif depth.current >= depth.limit:
            return elided
        depth.current += 1
        try:
            return summary(value, internal_dict)
        finally:
            depth.current -= 1

    return bounded_summary


def main(path: str) -> int:
    with open(path, encoding="utf-8") as cases:
        loaded = json.load(cases)
    depth = Depth()
    failed = 0
    for case in loaded:

        def limit(_value: Any, case: dict = case) -> int:
            return case["limit"]

        def field(value: Any) -> str:
            if isinstance(value, dict):
                return struct(value, {})
            if isinstance(value, list):
                return record(value, {})
            if value == "raises":
                raise ValueError("the case's summary raises here")
            return str(value)

        def struct_summary(value: dict, _dict: dict) -> str:
            return "{" + ", ".join(f"{name}:{field(child)}" for name, child in value.items()) + "}"

        def tuple_summary(value: list, _dict: dict) -> str:
            return "(" + ", ".join(field(child) for child in value) + ")"

        struct = bounded(struct_summary, "{…}", depth, limit)
        record = bounded(tuple_summary, "(…)", depth, limit)
        try:
            got = field(case["value"])
        except ValueError as error:
            got = f"raised: {error}"
        if got != case["summary"] or depth.current != 0:
            print(
                f"depths case FAILED: {case['name']}\n  gave {got} at depth {depth.current}, wanted {case['summary']} at depth 0",
                file=sys.stderr,
            )
            failed = 1
    return failed


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
