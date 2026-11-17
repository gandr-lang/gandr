# The structs that the positions ledger rows. Each is a struct whose one
# field is an unsigned integer or a byte array. Each stands outside the tests.
# Its source is in a kernel crate, a storage crate, the ring crate or the core
# term arena. It can also be in the dispatcher or the corpus, which compose
# the report of a session.
#
# Such a struct gives a name to a place, a count or a digest. So a positional
# identity cannot enter a key, a name or a byte form without one.
# - see: #7323
#
# The input is the lines `git grep -n` prints for three patterns over those
# sources, test files left out: such a struct, a `#[cfg(test)]` attribute
# and a `mod` that opens a block. Each line is `<file>:<line>:<text>`. The
# output is one line per struct, `<file>` and `<name>` joined by a tab, in
# the order of the files and their lines.
#
# A struct inside an inline test module is a test's own. The program reads a
# file's first `mod` that opens a block, its name alone on its line or with
# its `{`, whose `#[cfg(test)]` stands at most four lines above it, as the
# start of the file's tests. A `mod` that ends in `;` opens no block. An
# indented struct after the start is left out. A struct at the start of its
# line, after it, stays: it is no member of a module block.

def parsed:
  capture("^(?<file>[^:]+):(?<line>[0-9]+):(?<text>.*)$") | .line |= tonumber;

def struct_name:
  .text
  | capture("^\\s*(?:pub(?:\\([a-z]+\\))?\\s+)?struct\\s+(?<name>\\w+)(?:<[^>]*>)?\\((?:pub(?:\\([a-z]+\\))?\\s+)?(?:usize|u64|u32|u16|u8|\\[u8;\\s*\\w+\\])\\)")
  | .name;

def tested: .text | test("^\\s*#\\[cfg\\((?:all\\()?test\\b");
def opens: .text | test("^\\s*(?:pub(?:\\([a-z]+\\))?\\s+)?mod\\s+\\w+\\s*(?:\\{.*)?$");

[.[] | select(. != "") | parsed]
| group_by(.file)[]
| . as $lines
| ([range(1; length)
    | select(($lines[.] | opens) and ($lines[. - 1] | tested) and $lines[. - 1].line >= $lines[.].line - 4)
    | $lines[.].line]
   | min) as $tests
| .[]
| select($tests == null or .line < $tests or (.text | test("^\\S")))
| struct_name as $name
| "\(.file)\t\($name)"
