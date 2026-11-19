# The names of the builtins that the surface places hold, one line for each
# name and place. A place is a list of names in a surface crate. A later unit
# moves each place into the one table of `gandr-core-term`. That table gives
# its own names through a test of its crate.
# - see: #8070, #8098, `ledger/builtins.sql`
#
# The input is the lines that `git grep -n` prints for the places and for the
# constants of their spellings. Each line is `<file>:<line>:<text>`. The
# output is one line per name, `<name>` and `<place>` joined by a tab, each
# once, sorted.
#
# A block opens at a list of names and closes at the end of its item. The
# lists are constants of the resolver, the molder, the highlighter and the
# member table. They are also rules of the type grammar whose tiles are heads.
# A member is `<Head>.<member>`, or bare when its holder is `Bare`. A member
# that a constant spells reads the constant's text.
#
# The highlighter lists the universes `Type` and `Type+` beside the atoms. A
# universe stays in the grammar and takes no declaration, so it takes no row.
# - see: `vault:01a1f320-0881-7ed1-9a54-c0c713ccf7cf` § builtin-kinds

def parsed:
  capture("^(?<file>[^:]+):(?<line>[0-9]+):(?<text>.*)$") | .line |= tonumber;

# The list that `.text` opens in its place, or null.
def opener:
  .file as $file
  | if $file | endswith("/resolve.rs") then first(.text | capture("\\bconst (?<block>TYPE_ATOMS|HOMED_ATOMS|HOMED_FORMERS)\\b") | .block) // null
    elif $file | endswith("/type_shell.rs") then
      first(.text | capture("RuleName\\(\"(?<block>primitive_type|flow_type|capability_type)\"\\)") | .block)
      // (if .text | test("\\bfor \\(name, head, retired\\) in \\[") then "carried" else null end)
    elif $file | endswith("/mold.rs") then first(.text | capture("\\bconst (?<block>CALLED_FORMERS)\\b") | .block) // null
    elif $file | endswith("/highlight.rs") then first(.text | capture("\\bconst (?<block>PRIMITIVE_TYPES)\\b") | .block) // null
    elif $file | endswith("/identity.rs") then first(.text | capture("\\bconst (?<block>SPELLED)\\b") | .block) // null
    else null
    end;

def closer: .text | test("(^\\s*(\\)\\)?;|\\] \\{)|\\];)\\s*$");

def comment: .text | test("^\\s*//");

def strings: .text | scan("\"([^\"\\\\]*)\"") | .[0];

# The names that a line of `$block` holds.
def names($block; $spelled):
  if $block == "SPELLED" then
    .text
    | capture("\\(Holder::(?<holder>\\w+),\\s*(?:\"(?<word>[^\"]+)\"|(?<constant>[A-Z_]+)),")
    | (.word // $spelled[.constant]) as $word
    | select($word != null)
    | if .holder == "Bare" then $word else "\(.holder).\($word)" end
  elif $block == "primitive_type" then .text | scan("TileLabel\\(\"([^\"]+)\"\\)") | .[0]
  elif $block == "PRIMITIVE_TYPES" then strings | select(. != "Type" and . != "Type+")
  elif $block == "TYPE_ATOMS" or $block == "CALLED_FORMERS" then strings
  else strings | select(test("^[A-Z]"))
  end;

[.[] | select(. != "") | parsed] as $lines
| ($lines
   | map(.text | capture("\\bconst (?<name>[A-Z_]+): &str = \"(?<value>[^\"]*)\";")? )
   | map({(.name): .value}) | add // {}) as $spelled
| [ $lines
    | group_by(.file)[]
    | sort_by(.line)
    | foreach .[] as $line ({block: null, names: []};
        .block as $block
        | if ($line | comment) then .names = []
          elif $block == null then
            ($line | opener) as $opened
            | if $opened == null then .names = []
              else {block: $opened,
                    names: (if $opened == "CALLED_FORMERS" then [$line | strings] else [] end)}
                | if ($line | closer) then .block = null else . end
              end
          elif ($line | closer) then {block: null, names: [$line | names($block; $spelled)]}
          else .names = [$line | names($block; $spelled)]
          end;
        .names[] | "\(.)\t\($line.file)")
  ]
| unique
| .[]
