"""A Rust string as a formatter prints it: quoted, escaped, on one line.

rustc's formatters print a string's bytes raw between quotes. A string that
holds a newline then breaks its summary across lines, and the summary of every
value that holds it, a frame's arguments among them. A frame line broken so
reads as no frame (#3783). `quoted` escapes the text as Rust's `Debug` does
for the characters a line can break or hide on, and `rust_formatters.py`
prints every string summary through it.

Run as a script, the module checks the cases of a JSON file
(`.config/debug/strings.json`): `python3 strings.py <cases>`.
"""

import json
import sys

ESCAPES = {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\r": "\\r", "\t": "\\t", "\0": "\\0"}
"""The characters Rust's `Debug` escapes by name."""


def breaking(code: int) -> bool:
    """A control character, or a line or paragraph separator: Unicode's `Cc`, `Zl` and `Zp`.

    Read by code point: lldb's embedded Python may not load `unicodedata`.
    """
    return code < 0x20 or 0x7F <= code <= 0x9F or code in (0x2028, 0x2029)


def escaped(character: str) -> str:
    """One character as Rust's `Debug` writes it inside a string."""
    if character in ESCAPES:
        return ESCAPES[character]
    if breaking(ord(character)):
        return f"\\u{{{ord(character):x}}}"
    return character


def quoted(text: str) -> str:
    """The text in quotes, every character a line breaks or hides on escaped."""
    return '"' + "".join(escaped(character) for character in text) + '"'


def main(path: str) -> int:
    with open(path, encoding="utf-8") as cases:
        loaded = json.load(cases)
    failed = 0
    for case in loaded:
        got = quoted(bytes.fromhex(case["bytes"]).decode("utf-8", "replace"))
        if got != case["quoted"]:
            print(f"strings case FAILED: {case['name']}\n  gave {got}, wanted {case['quoted']}", file=sys.stderr)
            failed = 1
    return failed


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
