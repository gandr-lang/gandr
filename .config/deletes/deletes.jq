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
#               origin, moved}. `kind` is `item`, `test`, `ledger`, `kept` or
#               `file`; `names` are the spellings that a row may give for it;
#               `origin` is the pull request of the commit that adds it, or
#               null; `moved` is `{act, at}` when the body of an item or a
#               test stands at an item that the head adds (`acts.bash`,
#               #7058), or null
#   held        each id of the head, of the same kinds
#   tests       each test whose text differs between the base and the head:
#               {id, name}
#   features    for each crate directory that a left item lives in, the lines
#               of its README's `## Provided features`: {base, head}
#   lonely      the crates that no other crate names, each as its library
#               name and its directory
#   files       for each `deleted`, `merged` or `narrowed` row's item, the
#               files of the change that name it at the base
#   signoffs    each comment of the issues the body works that says `signed`:
#               {author, body, sha, fork, changed, reshaped};
#               `changed` maps each item to the files whose words that name
#               it move since `sha` (#7025), or is null when `sha` is no
#               commit; `reshaped` lists the items whose record at the base
#               changes since `fork`
#   architects  for each login whose comments sign, the heading text that its
#               comment must hold, or "" when it needs none
#
# Output: one line for each refusal, in the order of the rules.

include "sections";
include "account";

# Each left item that its crate's `## Provided features` names on a line that
# the head keeps: by its own segment, in backquotes or as the words of its
# name. The owner's segment names it too when the owner leaves in the same
# change (#7006); a line that names a type that stays names none of its
# methods. `$held` is the head's ids as an object, each mapped to true.
def featured($in; $held):
  [$in.left[] | select(.kind == "item" and ((.file // "") | test("^crates/[^/]+/")))
     | . as $it
     | ($in.features[$it.file | split("/")[1]] // {base: [], head: []}) as $lines
     | ($it.id | split("::")) as $path
     | ($path | map(gsub("<.*$"; ""))) as $segments
     | [$segments[-1]]
       + (if ($path | length) > 1 and ($held[$path[:-1] | join("::")] | not) then [$segments[-2]] else [] end)
     | select(any(.[] | select(test("^[A-Za-z_][A-Za-z0-9_]*$"));
         . as $name
         | ($name | gsub("(?<a>[a-z0-9])(?<b>[A-Z])"; "\(.a) \(.b)") | ascii_downcase) as $words
         | any($lines.base[];
             . as $line
             | (($line | contains("`\($name)`")) or (($words | contains(" ")) and ($line | ascii_downcase | contains($words))))
               and IN($lines.head[]; $line))))
     | $it.id]
  | unique;

# The row that reads a thing: of the answered row items that cover it, the
# longest (#7105). A row of an item reads that item over the row of its
# module, so a `narrowed` item of a moved module keeps its own act.
def reader($items; $thing): [$items[] | select(covers(.; $thing))] | max_by(length);

. as $in
| ($in.mode == "full") as $full
| ($in.body | deletes_rows) as $rows
| ($rows // []) as $rs
| ([($in.held // [])[] | {key: ., value: true}] | from_entries) as $held
| ([$rs[] | .item | select(answered)]) as $items
| ([$in.left[] | select(.kind | IN("item", "test")) | {key: .id, value: reader($items; .)}] | from_entries) as $readers
| featured($in; $held) as $featured
| (
    # A change that takes things out needs the section. A thing whose body
    # stands at another path of the head needs no row (#7058).
    ([$in.left[] | select(.moved == null)] as $owed
     | if $full and $rows == null and ($owed | length) > 0 then
         "the change takes \($owed | length) things out of the tree, and the body has no `## Deletes` section: write one row for each (`units.md` § units-pr, #6817)"
       else empty end),
    # Each thing that leaves has its row.
    (if $full and $rows != null then
       $in.left[] as $thing
       | select($thing.moved == null)
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
           # The check computes the act of an item or a test from the bodies
           # (#7058). A row that says `moved` or `renamed` names a body that
           # stands in the head, and a row that asks a sign-off names a body
           # that stands nowhere in the head. Each thing answers to the
           # longest row that covers it (#7105).
           ([$in.left[] | select(.kind | IN("item", "test")) | select($readers[.id] == $item)] as $things
            | (if $full and ($row.act | IN("moved", "renamed")) then
                 $things[] | select(.moved == null)
                 | "`\(.id)` stands nowhere in the head with the same body, and the row of `\($item)` says `\($row.act)`: no item that the head adds has its tokens, so the row says `deleted`, `merged` or `narrowed`, with the architect's sign-off (#7058)"
               else empty end),
              (if $full and ($row.act | IN("deleted", "merged", "narrowed")) and ($things | length) > 0 and all($things[]; .moved != null) then
                 "`\($item)` stands at `\($things[0].moved.at)` with the same body, and its row says `\($row.act)`: the row says `\($things[0].moved.act)`, or it leaves, since the check reads the move (#7058)"
               else empty end)),
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
              (if $full and any($in.left[] | select(covers($item; .)) | .id; IN($featured[])) then
                 "the crate's `## Provided features` names `\($item)`: no sign-off admits its deletion until the README line leaves in the same change, with its own row"
               else empty end),
              # A crate with no consumer: the answer is to find one.
              (($in.lonely // [])[]
                | select(.library as $lib | .dir as $dir
                    | ($item | startswith($lib + "::"))
                      or any($in.left[] | select(covers($item; .)); (.file // "") | startswith("crates/" + $dir + "/")))
                | "no other crate names `\(.dir)`, so its items wait for their consumer: the row of `\($item)` is refused, and the dead-weight row reads `find the consumer`")
            else empty end),
           # The architect's sign-off, with both halves still in place: the
           # architect reads each item that stands nowhere in the head (#7058).
           (if .act | IN("deleted", "merged", "narrowed") then
              ($in.files[$item] // []) as $files
              | select([$in.signoffs[]? as $c | signs($c; $item; $files; $in.architects)] | any | not)
              | [$in.signoffs[]? | select(signer(.; $in.architects) and (.body | contains($item)) and (.body | test("\\bsigned\\b")))] as $own
              | if ($own | length) > 0 then
                  "the architect's sign-off of `\($item)` is stale: \([moves($own[-1]; $item; $files)] | join("; ")); the architect reads that and signs again"
                else
                  "the `\($row.act)` row of `\($item)` has no sign-off: a comment of the architect on the unit names the item and the head commit and says `signed`"
                end
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
