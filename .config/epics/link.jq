# Which issues belong to each open epic by body reference (#3398), the
# membership `epics:link` sets as `blocked by`: an issue whose body names the
# epic, or that the epic's body names.
#
# Input: {issues: [{number, state, labels: [name], body}]}, every issue open
# or closed, pull requests left out.
# Output: [{epic, members: [n]}], one per open `kind:epic`, its members in
# ascending order.
#
# Neither an epic nor a `collector` is a member: an epic naming another (a
# split, a related programme) would make two epics wait on each other, and a
# collector names the issues its rows are about, so it would hold every epic
# it mentions open for as long as it collects.

def named: [scan("(?<![\\w/])#([0-9]+)\\b") | .[0] | tonumber] | unique;

.issues as $issues
| [$issues[] | select((.labels | index("kind:epic")) == null and (.labels | index("collector")) == null)
    | {number, names: ((.body // "") | named)}] as $candidates
| [$candidates[].number] as $numbers
| [$issues[] | select(.state == "open" and (.labels | index("kind:epic")) != null)
    | .number as $epic
    | ((.body // "") | named) as $named
    | {epic: $epic,
       members: ([$candidates[] | .number as $m | select($m != $epic and ((.names | index($epic)) != null or ($named | index($m)) != null)) | $m] | unique)}]
