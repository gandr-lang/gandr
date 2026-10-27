# An issue's label set (#2902, `tracker.md` § tracker-issues): exactly one
# `kind:`, `priority:` and `effort:`, and one or more `area:` (an issue may
# span surface and core). Read by `issue:file` and `issue:labels` (through
# `filed.jq`) and by `report:deps`.

# One line per label to add or remove and per problem, or none for a full
# set. Input: {labels: [name], defaults}, defaults being
# `.config/issues/defaults.toml` as JSON, {kind: {"<kind>": {priority,
# effort}}}.
#
# An epic is one kind: beside `kind:epic`, each other `kind:` is
# `remove<TAB><label>`. A missing `priority:` or `effort:` takes the issue's
# kind's default, as `add<TAB><label>`; a label given wins. Each problem is
# `refuse<TAB><why>`: no `kind:` or no `area:`, a `kind:`, `priority:` or
# `effort:` given twice, and a `priority:` or `effort:` missing whose kind
# has no default.
def labelled:
  . as $issue
  | [$issue.labels[] | select(startswith("kind:"))] as $kinds
  | (if $kinds | index("kind:epic") then ["kind:epic"] else $kinds end) as $kept
  | ($kept | if length == 1 then .[0] | ltrimstr("kind:") else null end) as $kind
  | ($issue.defaults.kind[$kind // ""] // {}) as $default
  | ($kinds - $kept | .[] | "remove\t\(.)"),
    (("kind:", "area:", "priority:", "effort:") as $prefix
     | (if $prefix == "kind:" then $kept else [$issue.labels[] | select(startswith($prefix))] end) as $given
     | ($prefix | rtrimstr(":")) as $name
     | if ($given | length) > 1 and $name != "area" then "refuse\tlabels \($given | map("`\(.)`") | join(", ")) give more than one `\($prefix)`: keep one"
       elif ($given | length) >= 1 then empty
       elif $name == "kind" or $name == "area" then "refuse\tno `\($prefix)` label: give one"
       elif $default[$name] != null then "add\t\($prefix)\($default[$name])"
       elif $kind == null then "refuse\tno `\($prefix)` label, and no single `kind:` to take its default from: give one"
       else "refuse\tno `\($prefix)` label, and `kind:\($kind)` has no default in `.config/issues/defaults.toml`: give one"
       end);
