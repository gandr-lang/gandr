# The structures that the sharing ledger rows. Each holds a field whose type
# holds an `Arc`, or a `Shared` or a `ThinShared` of `gandr-kernel-data`, or an
# alias of one. The type holds it alone or in an `Option`, a `Maybe`, a `Vec`
# or a `SmallVec`. An alias is a `type` declaration of the read sources whose
# right side holds such a pointer in the same way.
# The field is in a struct or an enum of a kernel crate or of the fork crate,
# outside its tests.
# - see: #7339
#
# A freeze, a fork or an `open_scope` clones such a field by a count. So a
# write after it copies what the field shares, or it adds beside it.
#
# The input is the lines `git grep -n` prints for seven patterns over those
# sources, test files left out: a named field, a tuple variant or a tuple
# struct whose first field is such a type, an alias of a shared pointer, a
# struct, an enum or a union that opens, a function that opens, a
# `#[cfg(test)]` attribute and a `mod` that opens a block. Each line is
# `<file>:<line>:<text>`. The output is one line per field, `<file>` and
# `<Type>.<field>` joined by a tab, each once, sorted. A tuple variant's field
# is `<Type>.<Variant>`, and a tuple struct's is `<Type>.0`.
#
# The program reads the aliases of every file before it reads a field, so a
# field reads an alias that another file declares. A field belongs to the type
# that opened last before it in its file. A function or an alias that opened
# later instead closes that type, and no row names a parameter. A field inside
# an inline test module is a test's own: the program reads the start of a
# file's tests as `.config/positions/hits.jq` reads it.

def parsed:
  capture("^(?<file>[^:]+):(?<line>[0-9]+):(?<text>.*)$") | .line |= tonumber;

def visibility: "(?:pub(?:\\([a-z]+\\))?\\s+)?";
def containers: "(?:(?:Option|Maybe|Vec|alloc::vec::Vec|SmallVec)<)?";
def pointer: "(?:(?:alloc::sync::|std::sync::|core::sync::)?Arc|(?:gandr_kernel_data::)?(?:Shared|ThinShared))<";

# A pointer, or a name of `$aliases` behind any path, alone or in a container.
def holds($aliases):
  containers + "(?:" + pointer
  + (if ($aliases | length) > 0 then "|(?:\\w+::)*(?:" + ($aliases | join("|")) + ")\\b(?!::)" else "" end)
  + ")";

def alias_name:
  first(.text | capture("^\\s*" + visibility + "type\\s+(?<name>[A-Z]\\w*)(?:<[^>]*>)?\\s*=\\s*" + containers + pointer) | .name)
  // null;

def type_name:
  first(.text | capture("^\\s*" + visibility + "(?:struct|enum|union)\\s+(?<name>[A-Z]\\w*)") | .name)
  // null;

def tuple_struct($holds):
  first(.text | capture("^\\s*" + visibility + "struct\\s+(?<name>[A-Z]\\w*)(?:<[^>]*>)?\\(" + visibility + $holds) | .name)
  // null;

def function: .text | test("^\\s*" + visibility + "(?:const\\s+)?(?:async\\s+)?(?:unsafe\\s+)?fn\\s+\\w+");

def field_name($holds):
  first(.text | capture("^\\s*(?:" + visibility + "(?<field>[a-z_][a-z0-9_]*):\\s*|(?<variant>[A-Z]\\w*)\\(" + visibility + ")" + $holds) | .field // .variant)
  // null;

def tested: .text | test("^\\s*#\\[cfg\\((?:all\\()?test\\b");
def opens: .text | test("^\\s*" + visibility + "mod\\s+\\w+\\s*(?:\\{.*)?$");

[.[] | select(. != "") | parsed]
| (map(alias_name | select(. != null)) | unique) as $aliases
| holds($aliases) as $holds
| group_by(.file)[]
| sort_by(.line)
| . as $lines
| ([range(1; length)
    | select(($lines[.] | opens) and ($lines[. - 1] | tested) and $lines[. - 1].line >= $lines[.].line - 4)
    | $lines[.].line]
   | min) as $tests
| [ foreach .[] as $line ({owner: null, hit: null};
      ($tests == null or $line.line < $tests) as $kept
      | if ($line | tuple_struct($holds)) != null then
          {owner: ($line | tuple_struct($holds)), hit: (if $kept then "\($line.file)\t\($line | tuple_struct($holds)).0" else null end)}
        elif ($line | type_name) != null then {owner: ($line | type_name), hit: null}
        elif ($line | function) or ($line | alias_name) != null then {owner: null, hit: null}
        elif ($line | field_name($holds)) != null and .owner != null and $kept
        then .hit = "\($line.file)\t\(.owner).\($line | field_name($holds))"
        else .hit = null
        end;
      .hit)
  | select(. != null) ]
| unique_by(.)
| .[]
