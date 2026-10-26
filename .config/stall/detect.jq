# The stalls among the open pull requests (#2785): the ways the fleet stops
# landing that no seat sees from inside its own `pr:watch`. The detector
# reads and pages; it queues, revises and comments nothing. A page obligates
# a response and a mechanism; a poll that merged would hide the stall.
#
# The kinds, each read only of pull requests neither drafts nor opened by an
# app:
#   root-unqueued  a stack's root, based on the trunk, green on every required
#                  context and mergeable, out of the merge queue, for
#                  `root_unqueued` minutes since its last required check
#                  concluded. Nothing lands while it waits (#2783).
#   ejected        removed from the merge queue unmerged `ejections` times or
#                  more in the last `ejection_window` minutes; a removal its
#                  seat made by hand (`manual`) is no ejection.
#   pile-up        a stack more than `depth` open pull requests deep, read
#                  from its root; its age runs from the opening of the member
#                  that took it past the depth.
#   red-unrevised  a required context failed on the head and no new head
#                  came in `red` minutes since it concluded.
#   conflicting    GitHub reads it conflicting, at the same head, for
#                  `conflicting` minutes since the detector first saw it so.
# The triage lane acts on a root left unqueued and on an ejected pull
# request; a pile-up, and a red or conflicting pull request of another lane,
# is escalated to the coordinator too. A pull request's lane is its branch's
# first word, `triage-2783-stack-prefix` the triage lane's. A lane outside
# `lanes`, when given, is one the triage lane cannot place: its finding is
# unplaced and escalated, and `stall:watch` files it as an issue.
#
# Input: an object with
#   now         the reading's time, in epoch seconds;
#   trunk       the default branch;
#   required    the trunk's required contexts;
#   thresholds  `{root_unqueued, ejections, ejection_window, depth, red,
#               conflicting}`, the minutes, counts and depth above;
#   lanes       the lanes a finding can be placed in; absent places every
#               lane;
#   prs         `facts.jq`'s pull requests;
#   seen        when each `<number>:conflicting:<head>` was first read so,
#               from the last reading; absent reads as none;
#   paged       when each `<number>:<kind>` finding was paged; absent reads
#               as none.
# Output: `{findings, pages, seen, paged}`:
#   findings    every stall now, ordered by pull request and kind, each
#               `{kind, number, lane, placed, age, escalate, line}`, the age
#               in minutes and the line `STALL <kind> #<number> <lane>
#               <age>m: <what>`;
#   pages       the findings not paged yet: a stall is paged once while it
#               lasts, and again only after it cleared;
#   seen, paged the next reading's, holding only what still stands.

. as $in
| ($in.seen // {}) as $seen
| ($in.paged // {}) as $paged
| $in.thresholds as $t
| def minutes: . / 60 | floor;
  def lane: .head | split("-")[0];
  def placed: lane as $lane | $in.lanes == null or ($in.lanes | index($lane)) != null;
  def reading: . as $pr
    | [$in.required[] as $name
        | ([$pr.checks[] | select(.name == $name)] | sort_by(.started // 0) | last)
          // {name: $name, verdict: "pending", conclusion: null, started: null, completed: null}];
  def finding($kind; $since; $escalate; $what):
    ($in.now - $since | minutes) as $age
    | placed as $placed
    | {kind: $kind, number: .number, lane: lane, placed: $placed, age: $age,
       escalate: ($escalate or ($placed | not)),
       line: "STALL \($kind) #\(.number) \(lane) \($age)m: \($what)"};
  def foreign: lane != "triage";
  [$in.prs[] | select((.draft | not) and (.bot | not))] as $prs
| def chain: . as $pr
    | [$prs[] | select(.base == $pr.head) | chain] as $above
    | [$pr] + ($above | max_by(length) // []);
  ([$prs[] | select(.mergeable == "CONFLICTING") | {key: "\(.number):conflicting:\(.oid)"}]
    | map({key, value: ($seen[.key] // $in.now)}) | from_entries) as $seen_now
| [
    ($prs[] | select(.base == $in.trunk and (.queued | not) and .mergeable == "MERGEABLE")
      | (reading) as $r
      | select(all($r[]; .verdict == "pass"))
      | ([$r[].completed // 0] | max) as $since
      | select($in.now - $since >= $t.root_unqueued * 60)
      | finding("root-unqueued"; $since; false; "green and mergeable on \($in.trunk), out of the merge queue")),
    ($prs[]
      | [.removals[] | select(.reason != "manual" and .at >= $in.now - $t.ejection_window * 60)] as $out
      | select(($out | length) >= $t.ejections)
      | finding("ejected"; ($out | map(.at) | min); false;
          "left the merge queue unmerged \($out | length) times in \($t.ejection_window)m (\($out | map(.reason) | unique | join(", ")))")),
    ($prs[] | select(.base == $in.trunk)
      | chain as $chain
      | select(($chain | length) > $t.depth)
      | finding("pile-up"; $chain[$t.depth].created; true;
          "\($chain | length) open pull requests stacked from it, the top #\($chain[-1].number)")),
    ($prs[]
      | [reading[] | select(.verdict == "fail")] as $red
      | select($red != [])
      | ($red | map(.completed // $in.now) | min) as $since
      | select($in.now - $since >= $t.red * 60)
      | finding("red-unrevised"; $since; foreign;
          "\($red | map("`\(.name)` \(.conclusion // "failed" | ascii_downcase)") | join(", ")), no new head since")),
    ($prs[] | select(.mergeable == "CONFLICTING")
      | $seen_now["\(.number):conflicting:\(.oid)"] as $since
      | select($in.now - $since >= $t.conflicting * 60)
      | finding("conflicting"; $since; foreign; "conflicts with its base at the same head"))
  ]
| sort_by(.number, .kind) as $findings
| ($findings | map({key: "\(.number):\(.kind)", value: ($paged["\(.number):\(.kind)"] // $in.now)}) | from_entries) as $paged_now
| {findings: $findings,
   pages: [$findings[] | select($paged["\(.number):\(.kind)"] == null)],
   seen: $seen_now,
   paged: $paged_now}
