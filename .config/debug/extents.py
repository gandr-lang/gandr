"""Whether an extent a Rust formatter reads lies in the debugged process's memory.

A formatter reads a length or a capacity from the program, then reads that
many bytes or children. A value not yet written, such as a local at its
function's entry, holds what the stack held, often a pointer: read as a length
it asks for 94 TB (#3823). `covered` asks whether every byte of the extent lies
in readable mapped memory, so a formatter reads only what the process maps.
`rust_formatters.py` asks it through lldb's memory regions.

Run as a script, the module checks the cases of a JSON file
(`.config/debug/extents.json`): `python3 extents.py <cases>`.
"""

import json
import sys
from typing import Callable, Optional, Tuple

Region = Tuple[int, int, bool]
"""A memory region: its base, its end and whether it is readable."""

ADDRESS_SPACE = 1 << 64


def covered(region_at: Callable[[int], Optional[Region]], address: int, size: int) -> bool:
    """Whether every byte of `size` bytes at `address` lies in readable memory.

    `region_at` gives the region holding an address, or None where it names
    none. An empty extent reads nothing and is covered.
    """
    if size <= 0:
        return True
    end = address + size
    if address < 0 or end > ADDRESS_SPACE:
        return False
    while address < end:
        region = region_at(address)
        if region is None:
            return False
        base, region_end, readable = region
        if not readable or not base <= address < region_end:
            return False
        address = region_end
    return True


def main(path: str) -> int:
    with open(path, encoding="utf-8") as cases:
        loaded = json.load(cases)
    failed = 0
    for case in loaded:
        regions = [(int(r["base"], 16), int(r["end"], 16), r["readable"]) for r in case["regions"]]

        def region_at(address: int) -> Optional[Region]:
            return next((r for r in regions if r[0] <= address < r[1]), None)

        got = covered(region_at, int(case["address"], 16), int(case["size"], 16))
        if got != case["covered"]:
            print(f"extents case FAILED: {case['name']}\n  gave {got}, wanted {case['covered']}", file=sys.stderr)
            failed = 1
    return failed


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
