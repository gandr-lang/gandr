# The structures that the sharing ledger rows (#7339): each field whose type
# holds an `Arc`, alone or in an `Option`, a `Maybe` or a `Vec`, in a struct or
# an enum of a kernel crate or of the fork crate, outside its tests. A freeze,
# a fork or an `open_scope` clones such a field by a count, so a write after it
# either copies what the field shares or adds beside it.
#
# The input is the lines `git grep -n` prints for six patterns over those
# sources, test files left out: a named field, a tuple variant or a tuple
# struct whose first field is such a type, a struct, an enum or a union that
# opens, a function that opens, a `#[cfg(test)]` attribute and a `mod` that
# opens a block. Each line is `<file>:<line>:<text>`. The output is one line
# per field, `<file>` and `<Type>.<field>` joined by a tab, each once, sorted.
# A tuple variant's field is `<Type>.<Variant>`, and a tuple struct's is
# `<Type>.0`.
#
# A field belongs to the type that opened last before it in its file. A
# function that opened later instead makes it a parameter, which no row
# names. A field inside an inline test module is a test's own: the program
# reads the start of a file's tests as `.config/positions/hits.jq` reads it.

def parsed:
  capture("^(?<file>[^:]+):(?<line>[0-9]+):(?<text>.*)$") | .line |= tonumber;

def visibility: "(?:pub(?:\\([a-z]+\\))?\\s+)?";
def holds: "(?:(?:Option|Maybe|Vec|alloc::vec::Vec)<)?(?:alloc::sync::|std::sync::|core::sync::)?Arc<";

def type_name:
  first(.text | capture("^\\s*" + visibility + "(?:struct|enum|union)\\s+(?<name>[A-Z]\\w*)") | .name)
  // null;

def tuple_struct:
  first(.text | capture("^\\s*" + visibility + "struct\\s+(?<name>[A-Z]\\w*)(?:<[^>]*>)?\\(" + visibility + holds) | .name)
  // null;

def function: .text | test("^\\s*" + visibility + "(?:const\\s+)?(?:async\\s+)?(?:unsafe\\s+)?fn\\s+\\w+");

def field_name:
  first(.text | capture("^\\s*(?:" + visibility + "(?<field>[a-z_][a-z0-9_]*):\\s*|(?<variant>[A-Z]\\w*)\\(" + visibility + ")" + holds) | .field // .variant)
  // null;

def tested: .text | test("^\\s*#\\[cfg\\((?:all\\()?test\\b");
def opens: .text | test("^\\s*" + visibility + "mod\\s+\\w+\\s*(?:\\{.*)?$");

[.[] | select(. != "") | parsed]
| group_by(.file)[]
| sort_by(.line)
| . as $lines
| ([range(1; length)
    | select(($lines[.] | opens) and ($lines[. - 1] | tested) and $lines[. - 1].line >= $lines[.].line - 4)
    | $lines[.].line]
   | min) as $tests
| [ foreach .[] as $line ({owner: null, hit: null};
      ($tests == null or $line.line < $tests) as $kept
      | if ($line | tuple_struct) != null then
          {owner: ($line | tuple_struct), hit: (if $kept then "\($line.file)\t\($line | tuple_struct).0" else null end)}
        elif ($line | type_name) != null then {owner: ($line | type_name), hit: null}
        elif ($line | function) then {owner: null, hit: null}
        elif ($line | field_name) != null and .owner != null and $kept
        then .hit = "\($line.file)\t\(.owner).\($line | field_name)"
        else .hit = null
        end;
      .hit)
  | select(. != null) ]
| unique_by(.)
| .[]
