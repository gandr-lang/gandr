# One schema of a crate's mutants: each mutated function body becomes a match
# on the mutant that the test process selects, one arm for each mutant and the
# original body as the default arm (#6878). One build of the schema then
# serves every mutant that it holds.
#
# Input: an object with
#   mutants  `cargo mutants --list --json` over the crate, in list order;
#   files    each source file that a mutant names, and each target root, by
#            its path in the workspace, as its text;
#   roots    the paths of the crate's target roots, which each get the switch;
#   dropped  the names that an earlier check refused, which stay out.
#
# A mutant is held when its function has a body mutant (`FnValue`), whose
# span is the body that the arms replace, and the mutant's span lies inside
# that body. A refused body mutant still gives its function's body, so the
# function's other mutants stay held. A function whose body lies inside
# another held body is left out, so no arm holds a second match. The mutant
# numbered `n` (its place in the list, from 1) is selected by
# `GANDR_MUTANT=n`. Columns count characters, as cargo-mutants gives them.
#
# Output: `{files, arms, held, out}`: `files` the text of each file, schema
# written; `arms` each arm's `file`, its `first` and `last` line and the
# names that an error on those lines takes out of the schema (`drop`): the
# arm's own mutant, or for the header and the default arm the body mutants of
# the function, or all its mutants when it has no body mutant left; `held`
# the names in the schema; `out` each other name with its `reason`.

def starts: [0] + [foreach (split("\n")[] | length + 1) as $n (0; . + $n)];
def at($starts): $starts[.line - 1] + .column - 1;
def lines: [match("\n"; "g")] | length;

. as $in
| ($in.dropped // []) as $dropped
| ($in.files | map_values(starts)) as $starts
| [$in.mutants | to_entries[] | .value + {id: (.key + 1), live: (.value.name | IN($dropped[]) | not)}] as $all
| [$all[] | select(.live and .function == null) | {name, reason: "no function"}] as $loose
| [$all[] | select(.function != null)]
| group_by([.file, .function.span.start.line, .function.span.start.column])
| map(
    .[0].file as $file
    | [.[] | select(.genre == "FnValue")] as $bodies
    | if ($bodies | length) == 0 then {file: $file, out: map(select(.live) | {name, reason: "no body"})}
      elif ($bodies | map(.span) | unique | length) > 1 then {file: $file, out: map(select(.live) | {name, reason: "two bodies"})}
      else
        ($bodies[0].span.start | at($starts[$file])) as $s
        | ($bodies[0].span.end | at($starts[$file])) as $e
        | map(select(.live) | . + {s: (.span.start | at($starts[$file])), e: (.span.end | at($starts[$file]))})
        | {file: $file, s: $s, e: $e,
           held: map(select(.genre == "FnValue" or ($s <= .s and .e <= $e))),
           out: map(select(.genre != "FnValue" and ($s > .s or .e > $e)) | {name, reason: "outside the body"})}
      end)
| . as $groups
| [$groups[] | select(.held != null and (.held | length) > 0)] as $bodied
| [$bodied[] | . as $g
    | select(any($bodied[]; .file == $g.file and .s <= $g.s and $g.e <= .e and (.s != $g.s or .e != $g.e)) | not)] as $held
| [$bodied[] | . as $g
    | select(any($bodied[]; .file == $g.file and .s <= $g.s and $g.e <= .e and (.s != $g.s or .e != $g.e)))
    | .held[] | {name, reason: "nested"}] as $nested
| (reduce ($in.files | keys[]) as $file ({files: {}, arms: []};
    ($in.files[$file]) as $text
    | ([$held[] | select(.file == $file)] | sort_by(.s)) as $mine
    | (reduce $mine[] as $g ({text: "", line: 1, cursor: 0, arms: []};
        ($text[.cursor:$g.s]) as $before
        | ($text[$g.s:$g.e]) as $body
        | ([$g.held[] | select(.genre == "FnValue") | .name]) as $bodies
        | .text += $before
        | .line += ($before | lines)
        | .arms += [{file: $file, first: .line, last: .line, drop: (if ($bodies | length) > 0 then $bodies else [$g.held[].name] end)}]
        | .text += "match crate::__gandr_mutant::active() {\n"
        | .line += 1
        | reduce $g.held[] as $m (.;
            ("\($m.id) => {\n"
              + (if $m.genre == "FnValue" then $m.replacement
                 else $body[:($m.s - $g.s)] + $m.replacement + $body[($m.e - $g.s):] end)
              + "\n}\n") as $arm
            | .arms += [{file: $file, first: .line, last: (.line + ($arm | lines) - 1), drop: [$m.name]}]
            | .text += $arm
            | .line += ($arm | lines))
        | ("_ => {\n" + $body + "\n}\n}") as $default
        | .arms += [{file: $file, first: .line, last: (.line + ($default | lines)), drop: (if ($bodies | length) > 0 then $bodies else [$g.held[].name] end)}]
        | .text += $default
        | .line += ($default | lines)
        | .cursor = $g.e)) as $written
    | .files[$file] = $written.text + $text[$written.cursor:]
    | .arms += $written.arms))
| reduce $in.roots[] as $root (.; .files[$root] += "\n\n#[doc(hidden)]\n#[allow(warnings)]\npub mod __gandr_mutant {\n    extern crate std;\n\n    pub fn active() -> u32 {\n        static ACTIVE: std::sync::OnceLock<u32> = std::sync::OnceLock::new();\n        *ACTIVE.get_or_init(|| std::env::var(\"GANDR_MUTANT\").ok().and_then(|value| value.parse().ok()).unwrap_or(0))\n    }\n}\n")
| .held = [$held[].held[].name]
| .out = $loose + [$groups[].out // [] | .[]] + $nested
