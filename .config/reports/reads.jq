# The open issues `report:deps` reads for a dependency (#2902), each with
# what GitHub records for it, from one pass over the open issues (#3192).
#
# Input: `{open, graph}`: the open issues as `[{number, title, labels: [name],
# body}]`, and `deps_open_graph`'s map, `{"<n>": {blocked_by: [{number,
# state}], sub_issues: [{number, state}]}}`.
#
# Output: one issue per line, `. + {blocked_by: [n], sub_issues: [{number,
# state}]}`, for each issue that is an epic, names a dependency in prose
# (`after #n`, `blocked on #n`, `waits on #n`, `needs #n`, `once #n lands`)
# or carries `## After`. Only an epic carries its sub-issues; an issue the
# map lacks has recorded none.
.graph as $graph
| .open[]
| select((.labels | index("kind:epic")) or (.body | test("(?i)\\b(after|blocked on|waits on|needs) #[0-9]|\\bonce #[0-9]+ lands")) or (.body | split("\n") | any(test("^## After\\s*$"))))
| ($graph["\(.number)"] // {blocked_by: [], sub_issues: []}) as $read
| . + {blocked_by: [$read.blocked_by[].number], sub_issues: (if .labels | index("kind:epic") then $read.sub_issues else [] end)}
