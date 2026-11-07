# The stalls among the open pull requests (#2785): the ways the fleet stops
# landing that no seat sees from inside its own `pr:watch`. The detector
# reads and pages; it queues, revises and comments nothing itself, and
# `stall:watch` carries out what it answers. A page obligates a response and
# a mechanism; a poll that merged would hide the stall.
#
# The kinds, each read only of pull requests neither drafts nor opened by an
# app (a draft is a hold, its reason in a comment: `pr:hold`, #2972):
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
#   base-blocked   a stacked member whose base is an open pull request GitHub
#                  reads conflicting, or a branch no open pull request heads
#                  any more (merged, and the member not rebased), at the same
#                  head, for `base_blocked` minutes since the detector first
#                  saw it so (#2972): the member's own stall, though no root.
#   queued-off-trunk
#                  in the merge queue of a branch that is neither the trunk
#                  nor an open pull request's head (#4168): that branch's
#                  queue merges nothing into the trunk, and every stack
#                  carrying its commits waits on it. The queue is the one
#                  holding it, never read off its base: GitHub queues a
#                  stack's member in the trunk's queue under the base it
#                  keeps until a restack (#4643). It is paged at once, its age
#                  counted from the reading that first saw it so.
#   verdict-unfiled
#                  a merged pull request whose `## Refactoring` verdict is
#                  `yes` or `maybe` with rows, and no `kind:refactor` issue
#                  carries its `from:` line, `unfiled` minutes after it merged
#                  (#2885): the seat's watch that files it died with its
#                  session. Its fix is `mise run refactor:file <n>`; a merged
#                  pull request is never stalled, only paged.
#   seat-idle      a lane that holds a seat whose activity is `idle` for
#                  `idle` minutes (#3822, #5996): the seat is at its prompt with
#                  no foreground step and no background job, whatever it holds.
#                  The activity comes from the seat itself, never from its
#                  claims: a fixer repairs `integration` with no claim and no
#                  pull request, and a seat waits at its prompt with a claim. A
#                  seat whose activity is not known has no finding. Its line
#                  names each claim the lane holds, by the claim's marker or,
#                  with none, by one of its areas (#4174), and then the claim
#                  command that gives the lane its next work. It carries the
#                  seat's last reported line as `last`. It has no pull request,
#                  so it is keyed by its lane, paged once while it lasts and
#                  never stalled or paged again.
# A pull request's lane is the lane its first closing issue's claim marker
# names (#4524): the lane that claimed the unit holds what lands it, whatever
# the branch is called. With no claimed closing issue, it is the longest lane
# of `areas` its branch is, or opens with before a `-` (#4058):
# `triage-2783-stack-prefix` the triage lane's, `triage-2-2784-stall` the
# triage-2 lane's. A branch naming no lane of `areas` is its first word's.
# `stall:watch` pages each new finding to its lane's seat and to the
# coordinator at once (#2972). A lane outside `lanes`, when given, is one no
# seat holds: its finding is unplaced, and `stall:watch` files it as an issue.
# A `seat-idle` lane is a seat's by its reading, so it is always placed.
#
# A finding standing `escalate` minutes after it was first paged stalls its
# pull request: `stall:watch` writes the `stall` comment and adds the
# `status:stalled` label, and the coordinator decides (queue, order the
# rebase, draft the hold with its reason, or reassign). From then on the
# coordinator is paged again every `repage` minutes while the finding lasts,
# so a missed page is sent again, never assumed read. A stalled pull request
# found queued, a draft, or no longer open is released: its comment and label
# come off.
#
# Input: an object with
#   now         the reading's time, in epoch seconds;
#   trunk       the default branch;
#   required    the trunk's required contexts;
#   thresholds  `{root_unqueued, ejections, ejection_window, depth, red,
#               conflicting, base_blocked, unfiled, idle, escalate,
#               repage}`, the minutes, counts and depth above;
#   lanes       the lanes a finding can be placed in; absent places every
#               lane;
#   prs         `facts.jq`'s pull requests;
#   merged, filed, claimed
#               `facts.jq`'s merged pull requests, the numbers refactor
#               issues were filed from and the claimed issues' areas and
#               lanes; absent reads as none;
#   seats       the lanes that hold a seat; absent reads as none;
#   activity    each seat's last known activity by its lane, `{"<lane>":
#               {state, since, line}}`: `working`, `waiting` or `idle`, the
#               time it entered that state in epoch seconds, and the last line
#               the seat reported, or null; a lane it lacks is not known;
#   claim       the claim command, its `{lane}` the lane's name; absent names
#               no command;
#   areas       each lane's areas, `{"<lane>": ["<area>"]}`; a seat's lane
#               it lacks is read by no kind;
#   hold        the stack top's hold, `{holder, head, began, deadline}`, the
#               times in epoch seconds; absent or null reads as none;
#   seen        when each `<number>:conflicting:<head>`,
#               `<number>:base-blocked:<head>` and
#               `<number>:queued-off-trunk:<queue>` was first read so, from the
#               last reading; absent reads as none;
#   paged       each `<number>:<kind>` finding's `{first, last}`, or
#               `<lane>:<kind>` for one with no pull request: when it was
#               first paged and when the coordinator was last paged on it; a
#               bare time, as an older memory holds, is both; absent reads as
#               none;
# Output: `{findings, pages, repages, stall, release, seen, paged, stalled}`:
#   findings    every stall now, ordered by pull request and kind, each
#               `{kind, number, lane, placed, age, line}`, the age in minutes
#               and the line `STALL <kind> #<number> <lane> <age>m: <what>`,
#               `STALL <kind> <lane> <age>m: <what>` with no pull request;
#   pages       the findings not paged yet, for the seat and the coordinator:
#               a stall is paged once while it lasts, and again only after it
#               cleared;
#   repages     the findings the coordinator is paged on again;
#   stall       the pull requests to stall now, each `{number, comment}`, the
#               comment's body opening with the `<!-- stall -->` marker;
#   release     the numbers of the stalled pull requests to release;
#   seen, paged, stalled
#               the next reading's, holding only what still stands.

. as $in
| ($in.seen // {}) as $seen
| (($in.paged // {}) | map_values(if type == "number" then {first: ., last: .} else . end)) as $paged
| ($in.stalled // {}) as $stalled
| $in.thresholds as $t
| def minutes: . / 60 | floor;
  # The lane the first claimed closing issue names (#4524); else the longest
  # lane of `areas` the branch is, or opens with before a `-`, as `claims.sh`
  # reads a merged branch's (#4058); else its first word.
  def lane: .head as $head
    | (.claims // [])[0]
      // ([($in.areas // {}) | keys[] | select(. as $lane | $head == $lane or ($head | startswith($lane + "-")))]
          | max_by(length))
      // ($head | split("-")[0]);
  def placed: lane as $lane | $in.lanes == null or ($in.lanes | index($lane)) != null;
  def reading: . as $pr
    | [$in.required[] as $name
        | ([$pr.checks[] | select(.name == $name)] | sort_by(.started // 0) | last)
          // {name: $name, verdict: "pending", conclusion: null, started: null, completed: null}];
  def finding($kind; $since; $what):
    ($in.now - $since | minutes) as $age
    | {kind: $kind, number: .number, lane: lane, placed: placed, age: $age,
       line: "STALL \($kind) #\(.number) \(lane) \($age)m: \($what)"};
  [$in.prs[] | select((.draft | not) and (.bot | not))] as $prs
| def chain: . as $pr
    | [$prs[] | select(.base == $pr.head) | chain] as $above
    | [$pr] + ($above | max_by(length) // []);
  # A stacked member's blocked base: the open pull request below it read
  # conflicting, or none heading its base any more.
  def blocker: . as $pr
    | select($pr.base != $in.trunk)
    | ([$in.prs[] | select(.head == $pr.base)] | first) as $below
    | if $below == null then "its base `\($pr.base)` heads no open pull request (merged or closed), and #\($pr.number) is not rebased"
      elif $below.mergeable == "CONFLICTING" then "its base #\($below.number) conflicts with its own base"
      else empty
      end;
  # In the merge queue of a branch no open pull request heads, other than
  # the trunk: a queue that never merges into the trunk.
  def off_trunk: . as $pr
    | $pr.queue != null and $pr.queue != $in.trunk and all($in.prs[]; .head != $pr.queue);
  # The seats whose activity is `idle`, each with the claims its lane holds:
  # by the claim's marker or, with none, by one of the lane's areas.
  [($in.seats // [])[] | . as $lane
    | (($in.areas // {})[$lane] // empty | map("area:" + .)) as $labels
    | (($in.activity // {})[$lane] // empty | select(.state == "idle")) as $activity
    | {lane: $lane, since: $activity.since, last: $activity.line,
       held: [($in.claimed // [])[]
         | select(if .lane != null then .lane == $lane else any(.areas[]; IN($labels[])) end)
         | .number] | sort}] as $idle
| ([$prs[] | select(.mergeable == "CONFLICTING") | "\(.number):conflicting:\(.oid)"]
    + [$prs[] | select([blocker] != []) | "\(.number):base-blocked:\(.oid)"]
    + [$prs[] | select(off_trunk) | "\(.number):queued-off-trunk:\(.queue)"]
    | map({key: ., value: ($seen[.] // $in.now)}) | from_entries) as $seen_now
| [
    ($prs[] | select(.base == $in.trunk and (.queued | not) and .mergeable == "MERGEABLE")
      | (reading) as $r
      | select(all($r[]; .verdict == "pass"))
      | ([$r[].completed // 0] | max) as $since
      | select($in.now - $since >= $t.root_unqueued * 60)
      | finding("root-unqueued"; $since; "green and mergeable on \($in.trunk), out of the merge queue")),
    ($prs[]
      | [.removals[] | select(.reason != "manual" and .at >= $in.now - $t.ejection_window * 60)] as $out
      | select(($out | length) >= $t.ejections)
      | finding("ejected"; ($out | map(.at) | min);
          "left the merge queue unmerged \($out | length) times in \($t.ejection_window)m (\($out | map(.reason) | unique | join(", ")))")),
    ($prs[] | select(.base == $in.trunk)
      | chain as $chain
      | select(($chain | length) > $t.depth)
      | finding("pile-up"; $chain[$t.depth].created;
          "\($chain | length) open pull requests stacked from it, the top #\($chain[-1].number)")),
    ($prs[]
      | [reading[] | select(.verdict == "fail")] as $red
      | select($red != [])
      | ($red | map(.completed // $in.now) | min) as $since
      | select($in.now - $since >= $t.red * 60)
      | finding("red-unrevised"; $since;
          "\($red | map("`\(.name)` \(.conclusion // "failed" | ascii_downcase)") | join(", ")), no new head since")),
    ($prs[] | select(.mergeable == "CONFLICTING")
      | $seen_now["\(.number):conflicting:\(.oid)"] as $since
      | select($in.now - $since >= $t.conflicting * 60)
      | finding("conflicting"; $since; "conflicts with its base at the same head")),
    ($prs[]
      | first(blocker) as $what
      | $seen_now["\(.number):base-blocked:\(.oid)"] as $since
      | select($in.now - $since >= $t.base_blocked * 60)
      | finding("base-blocked"; $since; $what)),
    ($prs[] | select(off_trunk)
      | finding("queued-off-trunk"; $seen_now["\(.number):queued-off-trunk:\(.queue)"];
          "in the merge queue of `\(.queue)`, which heads no open pull request and merges nothing into \($in.trunk)")),
    (($in.merged // [])[]
      | select(IN(.verdict; "yes", "maybe") and .rows > 0 and .merged != null)
      | select(.number | IN(($in.filed // [])[]) | not)
      | select($in.now - .merged >= $t.unfiled * 60)
      | finding("verdict-unfiled"; .merged;
          "merged with a `\(.verdict)` refactoring verdict and no `kind:refactor` issue carries `from: #\(.number)`; run `mise run refactor:file \(.number)`")),
    ($idle[]
      | select($in.now - .since >= $t.idle * 60)
      | ($in.now - .since | minutes) as $age
      | .lane as $lane
      | (if .held == [] then "it holds no claim" else "it holds \(.held | map("#\(.)") | join(", "))" end) as $holds
      | (if $in.claim == null then "" else "; run `\($in.claim | gsub("\\{lane\\}"; $lane))` for its next work" end) as $run
      | {kind: "seat-idle", number: null, lane: $lane, placed: true, age: $age, last: .last,
         line: "STALL seat-idle \($lane) \($age)m: idle at its prompt with no step and no job running; \($holds)\($run)"})
  ]
| sort_by(.number, .kind, .lane) as $findings
| def key: "\(.number // .lane):\(.kind)";
  def escalated: $paged[key] as $p | $p != null and $in.now - $p.first >= $t.escalate * 60;
  [$findings[] | select((.kind == "seat-idle" | not) and escalated and $in.now - $paged[key].last >= $t.repage * 60)] as $repages
| [$findings[] | select((.kind | IN("verdict-unfiled", "seat-idle") | not) and escalated and $stalled["\(.number)"] == null)] as $stalling
| [$stalled | keys[] | tonumber as $n
    | ([$in.prs[] | select(.number == $n)] | first) as $pr
    | select($pr == null or ($pr.queued and ($pr | off_trunk | not)) or $pr.draft)
    | $n] as $release
| ($stalling | group_by(.number) | map({
    number: .[0].number,
    comment: ("<!-- stall -->\n**Stalled.** Paged to the `\(.[0].lane)` lane's seat and the coordinator \($t.escalate) minutes ago and still standing. The coordinator decides: queue it, order the rebase, draft the hold with its reason (`pr:hold`), or reassign it. This comment and `status:stalled` come off once it is queued, a draft or closed.\n\n" + (map("- `\(.line)`") | join("\n")))
  })) as $stall
| {findings: $findings,
   pages: [$findings[] | select($paged[key] == null)],
   repages: $repages,
   stall: $stall,
   release: $release,
   seen: $seen_now,
   paged: ($findings | map(key as $key | {key: $key, value: ($paged[$key] as $p
     | if $p == null then {first: $in.now, last: $in.now}
       elif any($repages[]; key == $key) then $p + {last: $in.now}
       else $p end)}) | from_entries),
   stalled: (($stalled | with_entries(select(.key | tonumber | IN($release[]) | not)))
     + ($stall | map({key: "\(.number)", value: $in.now}) | from_entries))}
