# The account of what a change takes out of the tree (#6817), read by
# `check:deletes` from a pull request body and the two sides of the change.
# The owner's order of 2026-11-11: no deletion lands without the architect's
# sign-off. 27 pull requests of the dead-weight collectors took items, ledger
# rows and README lines out of the tree, and each body gave no account that a
# reader could check. This rule refuses such a body.
#
# Input, written by `check.bash`:
#   body        the pull request body
#   title       the pull request title, or ""
#   mode        "full" reads both sides of the change; "rows" reads the body,
#               the sign-offs and the consumers alone, as the merge queue does
#   left        each thing of the base that the head lacks: {id, kind, names,
#               origin}. `kind` is `item`, `test`, `ledger`, `kept` or
#               `file`; `names` are the spellings that a row may give for it;
#               `origin` is the pull request of the commit that adds it, or
#               null
#   held        each id of the head, of the same kinds
#   tests       each test whose text differs between the base and the head:
#               {id, name}
#   readme      each left id that the crate's `## Provided features` names on
#               a line that the head keeps
#   lonely      the crates that no other crate names, each as its library
#               name and its directory
#   files       for each `deleted` row's item, the files of the change that
#               name it at the base
#   signoffs    each comment of the issues the body works that says `signed`:
#               {author, body, sha, changed}; `changed` holds the files that
#               change from `sha` to the head, or null when `sha` is no commit
#   architects  the logins whose comments sign
#
# Output: one line for each refusal, in the order of the rules.

include "sections";
include "account";

. as $in
| ($in.mode == "full") as $full
| ($in.body | deletes_rows) as $rows
| ($rows // []) as $rs
| ([($in.held // [])[] | {key: ., value: true}] | from_entries) as $held
| (
    # A change that takes things out needs the section.
    (if $full and $rows == null and ($in.left | length) > 0 then
       "the change takes \($in.left | length) things out of the tree, and the body has no `## Deletes` section: write one row for each (`units.md` § units-pr, #6817)"
     else empty end),
    # Each thing that leaves has its row.
    (if $full and $rows != null then
       $in.left[] as $thing
       | select([$rs[] | .item as $item | select($item | answered) | covers($item; $thing)] | any | not)
       | "`\($thing.id)` (\($thing.kind)) leaves the tree with no row in `## Deletes`"
     else empty end),
    ($rs[]
      | . as $row
      | .item as $item
      | (if ($item | answered) | not then "a `## Deletes` row names no item"
         elif (.act | IN(acts[]) | not) then
           "the `## Deletes` row of `\($item)` says `\(.act)`; the act is one of \(acts | map("`\(.)`") | join(", "))"
         else
           # A row of a thing that leaves names a thing that the head lacks.
           (if $full and (.act | IN("deleted", "moved", "renamed", "merged")) and ($held[$item] // false) then
              "`\($item)` is still in the head, and its row says `\(.act)`"
            else empty end),
           (if $full and .act == "restored" and (($held[$item] // false) | not) then
              "`\($item)` is not in the head, and its row says `restored`"
            else empty end),
           (if .act == "restored" and ((.why // "") | test("#[0-9]+") | not) then
              "the `restored` row of `\($item)` names no pull request that it reverses in `Why`"
            else empty end),
           (if .act == "deleted" then
              # The reasoning comes first (#5677).
              ([["origin", "Origin"], ["why", "Why"], ["future", "Future use"], ["instead", "In place of deletion"]][]
                | . as [$key, $name]
                | select(($row[$key] | answered) | not)
                | "the `deleted` row of `\($item)` leaves `\($name)` empty"),
              # The origin is the pull request of the commit that adds it.
              (if $full then
                 [$in.left[] | select(covers($item; .)) | .origin | select(. != null)] | unique[]
                 | . as $pr
                 | select(($row.origin // "") | test("#\($pr)\\b") | not)
                 | "the `deleted` row of `\($item)` gives `Origin` \(($row.origin // "") | @json), and the commit that adds it comes from pull request #\($pr)"
               else empty end),
              # The README is the crate's first design record.
              (if $full and any($in.left[] | select(covers($item; .)) | .id; IN(($in.readme // [])[])) then
                 "the crate's `## Provided features` names `\($item)`: no sign-off admits its deletion until the README line leaves in the same change, with its own row"
               else empty end),
              # A crate with no consumer: the answer is to find one.
              (($in.lonely // [])[]
                | select(.library as $lib | .dir as $dir
                    | ($item | startswith($lib + "::"))
                      or any($in.left[] | select(covers($item; .)); (.file // "") | startswith("crates/" + $dir + "/")))
                | "no other crate names `\(.dir)`, so its items wait for their consumer: the row of `\($item)` is refused, and the dead-weight row reads `find the consumer`"),
              # The architect's sign-off at a head that the change keeps.
              (($in.files[$item] // []) as $files
               | select([$in.signoffs[]? as $c | signs($c; $item; $files; $in.architects)] | any | not)
               | if [$in.signoffs[]? | select((.author | IN($in.architects[])) and (.body | test("\\(architect")) and (.body | contains($item)) and (.body | test("\\bsigned\\b")))] | length > 0 then
                   "the architect's sign-off of `\($item)` names no commit that the head keeps for its files; the architect signs again on the new head"
                 else
                   "the `deleted` row of `\($item)` has no sign-off: a comment of the architect on the unit names the item and the head commit and says `signed`"
                 end)
            else empty end)
         end)),
    # A test whose text changes states what it no longer asserts.
    (if $full and ($in.tests | length) > 0 then
       ((($in.body | section("Preserved and changed")) // []) | join("\n")) as $preserved
       | $in.tests[]
       | select(.name as $name | $preserved | contains($name) | not)
       | "the test `\(.id)` changes its text: name it in the second table of `## Preserved and changed`, with what it no longer asserts and why"
     else empty end),
    # A refactor states what it keeps and what it changes.
    (if ($in.title // "") | test("^refactor(\\(|!|:)") then
       if ($in.body | section("Preserved and changed")) == null then
         "a `refactor` pull request carries `## Preserved and changed`: one table of the behaviour it keeps, with the test that passes before and after, and one of the behaviour or test it changes, with the reason"
       else empty end
     else empty end)
  )
