# Whether `pr:open` opens a body: one line per refusal to print, a `note: `
# line per finding it prints and opens anyway, or nothing.
#
# Input:
#   branch    the branch being opened, `<lane>-<n>-<slug>` when it works an
#             issue
#   body      the body file's text
#   issues    the issues the body works: [{number, body}]
#   mentions  per key the body supersedes, the tree's lines naming it:
#             {key: ["<path>:<line>:<text>"]}
#
# A merge takes the claim off what the body works (`decide.jq`), so the body
# must name it (#2462): a branch that carries an issue number needs
# `Advances #n` or a closing keyword for that issue, and a branch with none
# needs one such line for some issue, the issue the change advances.
#
# The body answers the sources its issues request (#2499): every key an
# issue's `## Sources` names has an item in the body's `## Sources read`, and
# every item there carries a disposition from the vocabulary with its
# evidence. A `supersedes` item is refused while the tree still names the old
# key on a line that does not mark it demoted. An issue's `## Sources` line
# that names no key is noted, not refused.

include "targets";
include "sections";

def vocabulary: "`taken: <site>` (the function, test or fixture), `departed: <the recorded design, the change, why>`, `declined: <reason>` or `n/a: <reason>`";

# The refusal when the body does not work the branch's issue, or works none.
def claim:
  (.body | targets(working)) as $worked
  | (.branch | capture("^[a-z]+-(?<n>[0-9]+)(-|$)").n // null | if . == null then null else tonumber end) as $n
  | if $n != null then
      if ($worked | index($n)) then empty
      else "the body names no `Advances` or `Closes` line for #\($n), the issue `\(.branch)` names: add `Advances #\($n)` for a slice, or `Closes #\($n)` if it finishes the issue, then run `pr:open` again"
      end
    elif ($worked | length) > 0 then empty
    else "the body names no issue it works: add `Advances #n` for the issue the change advances, or `Closes #n` for one it finishes, then run `pr:open` again"
    end;

# The notes and refusals of `## Sources read` against the issues' `## Sources`.
def sources:
  (.mentions // {}) as $mentions
  | [(.issues // [])[] | .number as $n | (.body | section("Sources") // []) | items | {n: $n, line: ., item: keyed}] as $asked
  | [(.body | section("Sources read") // []) | items] as $read
  | [$read[] | keyed | select(. != null) | .keys[]] as $listed
  | ($asked[] | select(.item == null) | "note: #\(.n)'s `## Sources` line `\(.line)` is not `- `<key>` — <text>`, so no key is read from it"),
    ([$asked[] | select(.item != null) | .n as $n | .item.keys[] | {n: $n, key: .}]
      | map(select(.key as $key | $listed | index($key) | not))
      | unique_by(.key)
      | if length == 0 then empty
        else "the body's `## Sources read` lacks the sources its issue names: add one item per key, `- `<key>` — <disposition>`, the disposition \(vocabulary), then run `pr:open` again:\n" + (map("  - `\(.key)` (#\(.n)'s `## Sources`)") | join("\n"))
        end),
    ($read[]
      | . as $line
      | supersession as $replaced
      | if $replaced != null then
          if $replaced.confirmation == "" then "the `## Sources read` item `\($line)` gives no confirmation: write `- supersedes: `<old key>` — <confirmation>`, then run `pr:open` again"
          else ($mentions[$replaced.old] // [] | map(select(test("demoted"; "i") | not))) as $undemoted
          | if ($undemoted | length) == 0 then empty
            else "the `## Sources read` item `\($line)` supersedes `\($replaced.old)`, and the tree still names it undemoted: remove each reference, or mark it demoted on its line, then run `pr:open` again:\n" + ($undemoted | map("  \(.)") | join("\n"))
            end
          end
        else keyed as $item
        | if $item == null then "the `## Sources read` item `\($line)` names no source: write `- `<key>` — <disposition>`, the disposition \(vocabulary), then run `pr:open` again"
          else ($item.text | capture("^(?<disposition>taken|departed|declined|n/a):\\s*(?<evidence>.*)$") // null) as $answer
          | if $answer == null then "the `## Sources read` item `\($line)` has no disposition: end it with \(vocabulary), then run `pr:open` again"
            elif $answer.evidence == "" then "the `## Sources read` item `\($line)` leaves its `\($answer.disposition)` blank: give its evidence, \(vocabulary), then run `pr:open` again"
            else empty
            end
          end
        end);

claim, sources
