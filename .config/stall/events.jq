# The landing events a page answers at once (#5214): a comment the landing
# watcher or `stall:watch` posted on a pull request since the last reading,
# under one of their marks. `stall:watch` reads the newest issue comments
# once a minute with a conditional request, so a minute that changes nothing
# costs no rate limit, and pages each event's seat without waiting for the
# next stall reading.
#
# Input: `{seen, comments}`: `seen` the greatest comment id already read, or
# null on the first reading, and `comments` the REST issue comments, each
# `{id, issue_url, body}`.
# Output: `{seen, events}`: `seen` the greatest id read so far, and `events`,
# oldest first, each `{number, kind, line}` for a comment newer than `seen`
# that carries a mark. A first reading pages nothing: it only sets `seen`.

def kinds:
  [ {mark: "<!-- landing:pr-dequeued:", kind: "dequeued"},
    {mark: "<!-- landing:pr-red:", kind: "red"},
    {mark: "<!-- landing:pr-dirty:", kind: "dirty"},
    {mark: "<!-- pr-ejected ", kind: "ejected"} ];

def first_line:
  [ split("\n")[] | select(test("^\\s*$") | not) | select(startswith("<!--") | not) ]
  | (first // "") | .[0:200];

.seen as $seen
| ([.comments[].id] | max) as $max
| { seen: ([$seen, $max] | map(select(. != null)) | max),
    events: (
      if $seen == null then []
      else
        [ .comments[]
          | select(.id > $seen)
          | . as $c
          | (first(kinds[] as $k | select(($c.body // "") | contains($k.mark)) | $k) // null) as $k
          | select($k != null)
          | { id: .id,
              number: (.issue_url | split("/") | last | tonumber),
              kind: $k.kind,
              line: "EVENT \($k.kind) #\(.issue_url | split("/") | last): \(.body | first_line)" } ]
        | sort_by(.id) | map(del(.id))
      end) }
