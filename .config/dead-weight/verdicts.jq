# The dead-weight verdicts (#2891), the second stage of `report:dead-weight`.
# Input: {units, kept}: `units` holds the facts of every compiled unit, as
# `facts.jq` gives them, and `kept` is the text of
# `.config/dead-weight/kept.txt`. Output: an array of the items with a
# verdict, sorted by crate, file and line. Each item is {crate, path, kind,
# exported, file, line, start, end, verdict, callers}:
#   verdict `unused`: no unit except a test harness names the item. Its
#           callers are `none`, or `tests only (<n>)` for <n> test items;
#   verdict `local`: the item is exported, and no unit of another crate names
#           it. Its callers are `its crate only`. A crate's integration test,
#           benchmark or binary is another crate, since it can name only what
#           the library exports. A variant and a variant's field take the
#           enum's visibility, so neither gets this verdict.
# A used child keeps its parent in use (`facts.jq`), and each child gets its
# own verdict. The verdicts skip:
#   - an item that `kept.txt` names;
#   - an item of a trait, which the verdict of the trait covers. Each
#     implementation states such an item, and a use through a projection,
#     such as `T::Item`, resolves to no path;
#   - a binary's `main` and a procedural macro crate's exports, which the
#     compiler calls.

# The kept paths of `kept.txt`: each line's text before its first tab, with
# no comment and no blank line.
def kept_paths:
  split("\n") | map(select(test("^\\s*(#|$)") | not) | split("\t")[0] | sub("\\s+$"; ""));

# The path one level above the input.
def parent: split("::") | .[:-1] | join("::");

# The crate that holds a file: its directory under `crates/`, or its first
# directory.
def crate_of: split("/") | if .[0] == "crates" and length > 2 then .[1] else .[0] end;

.units as $units
| (.kept | kept_paths | map({key: ., value: true}) | from_entries) as $kept
| (reduce ($units[] | select(.kind != "test") | {root, kind} as $unit | .items | to_entries[] | [$unit, .]) as [$unit, $item] ({};
    .[$item.key] //= ($item.value + {root: $unit.root, unit: $unit.kind}))) as $items
| (reduce ($units[] | {root, kind} as $unit | .named | to_entries[] | [$unit, .]) as [$unit, $name] ({};
    .[$name.key] |= ((. // {production: false, tests: 0, roots: {}})
      | if $unit.kind == "test" then .tests += $name.value else .production = true end
      | .roots[$unit.root] = true))) as $named
| [ $items | to_entries[] | .key as $path | .value as $item
    | select(($kept[$path] // false) | not)
    | ($items[$path | parent].kind // null) as $above
    | select($above != "trait")
    | select(($item.unit == "bin" and $item.kind == "fn" and ($path | endswith("::main"))) | not)
    | select(($item.unit == "proc-macro" and $item.exported) | not)
    | ($named[$path] // {production: false, tests: 0, roots: {}}) as $uses
    | if $uses.production | not then
        {verdict: "unused", callers: (if $uses.tests == 0 then "none" else "tests only (\($uses.tests))" end)}
      elif $item.exported and $item.kind != "variant" and $above != "variant"
        and ($uses.roots | keys | all(. == $item.root)) then
        {verdict: "local", callers: "its crate only"}
      else empty end
    | {crate: ($item.file | crate_of), path: $path} + ($item | {kind, exported, file, line, start, end}) + . ]
| sort_by(.crate, .file, .line, .path)
