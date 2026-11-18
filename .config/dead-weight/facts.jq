# The facts of one compiled unit (#2891), the first stage of
# `report:dead-weight`. Input: the unit's evidence records, as an array.
# Argument $unit: the record file's name without `.jsonl`, `<root>.<kind>`,
# the kind `lib`, `test`, `bin` or `proc-macro`. A library and its unit tests
# share a root. Output: {root, kind, items, named}:
#   items  for a unit that is not a test harness, each item record whose path
#          is not a trait implementation's, by path: {kind, exported, file,
#          line, start, end};
#   named  each path that an item of the unit names, and each path above it,
#          by the number of items that name it.
# A name does not count at the levels that it shares with the item that
# names it. So an item's own body, its children and its type's
# implementations are not uses of it. A use of `T::f` by `T::g` counts for
# `T::f` and not for `T`.

# The package that an example's paths carry before the path itself, such as
# `gandr-a/` in `gandr-a/<e::T as Trait>::m`, or "" for a library's path.
def package: (capture("^(?<package>[^<:/]+/)") // {package: ""}).package;

# Whether a path is a trait implementation's item `<T as Trait>::m`, after
# its package.
def implementation: ltrimstr(package) | startswith("<");

# The path that owns a path: a trait implementation's item `<T as Trait>::m`
# belongs to `T`, without its generic arguments, after the same package.
def owner:
  package as $package
  | ltrimstr($package) as $path
  | if $path | startswith("<") then $package + (($path | capture("^<(?<type>.+?) as ") // {type: $path}).type | sub("<.*$"; ""))
    else . end;

# The levels of the input path that a name by the item `$user` counts at:
# each path from the input up to, and not including, the deepest path that
# the two share.
def levels($user):
  (owner | split("::")) as $target
  | ($user | owner | split("::")) as $named
  | ([$target, $named] | map(length) | min) as $shorter
  | (first(range(0; $shorter) | select($target[.] != $named[.])) // $shorter) as $shared
  | range($shared + 1; ($target | length) + 1)
  | $target[:.] | join("::");

($unit | capture("^(?<root>.+)\\.(?<kind>lib|test|bin|proc-macro)$")
  // error("facts.jq: the unit `\($unit)` is not `<root>.<kind>`")) as $of
| {
    root: $of.root,
    kind: $of.kind,
    items: (if $of.kind == "test" then {}
            else reduce (.[] | select(.record == "item" and (.path | implementation | not))) as $r ({};
              .[$r.path] //= ($r | {kind, exported, file, line, start, end}))
            end),
    named: (reduce (.[] | select(.record == "use") | .item as $user | .names[] | levels($user) | [., $user]) as [$level, $user] ({};
              .[$level][$user] = true)
            | map_values(length))
  }
