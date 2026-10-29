"""The variant a Rust sum-type enum value holds, read from lldb's names.

lldb names each member of an enum's `$variants$` `$variant$N`, N the
discriminant value DWARF gives the variant, and the dataful variant
`$variant$`. Xcode's lldb keeps only the low 32 bits of N (#3778). Over a tag
wider than 4 bytes its names then cannot tell a variant: a niche tag
`0x8000000000000002` is named `$variant$2`, and so is a dataful value whose
`Vec` capacity is 2. `rust_formatters.py` reads the names through `pick`.

Run as a script, the module checks the cases of a JSON file
(`.config/debug/variants.json`): `python3 variants.py <cases>`.
"""

import json
import sys
from typing import Optional, Sequence, Tuple

LOW_32 = 0xFFFF_FFFF

Variant = Tuple[str, Optional[Tuple[int, int]]]


def pick(variants: Sequence[Variant], truncated: bool) -> Tuple[int, Optional[int]]:
    """The index of the variant a value holds, and the raw tag where the names cannot tell it.

    Each variant is its name and, but for the dataful one, the tag the value
    reads at its discriminant and the tag's width in bytes. With `truncated`
    names, a name that matches the low 32 bits of a wider tag gives that tag as
    the second item, and the first item is no reading of the value.
    """
    dataful = 0
    for index, (name, tag) in enumerate(variants):
        if tag is None:
            dataful = index
            continue
        value, width = tag
        if truncated and width > 4:
            if name == f"$variant${value & LOW_32}":
                return index, value
        elif name == f"$variant${value}":
            return index, None
    return dataful, None


def main(path: str) -> int:
    with open(path, encoding="utf-8") as cases:
        loaded = json.load(cases)
    failed = 0
    for case in loaded:
        variants = [(v["name"], (v["tag"], v["width"]) if "tag" in v else None) for v in case["variants"]]
        got = pick(variants, case["truncated"])
        wanted = (case["index"], case.get("raw"))
        if got != wanted:
            print(f"variants case FAILED: {case['name']}\n  gave {got}, wanted {wanted}", file=sys.stderr)
            failed = 1
    return failed


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
