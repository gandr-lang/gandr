# Whether a landing absorbs the design pages it builds on (#3161,
# `design.md` § design-research): one refusal line, or nothing.
#
# Input: `{body, issues: [{number, body}], absorption}`: the pull request's
# body, the issues it works, and the vault's page statuses as
# `report:absorption` writes them, `{"<filename>": [{path, status}]}`, or
# null where no vault checkout has written them, as in CI.
#
# A vault page an issue's `## Sources` marks primary, named by its filename
# (every page that filename names) or by its vault path (that page alone),
# whose status is `design` or `partly` (the tree does not yet state all of
# it), is answered in the body's `## Vault`: an item `` - `<page>` —
# absorbed: <the tree locations this change adds> ``, the paired vault pull
# request rewriting the page to point at them, or `` - `<page>` — stays
# design: <why> `` when the landing states a part and the page keeps the
# rest. The vault pull request is named in neither: the vault is private,
# and the item says what moved. A page `absorbed`, `concept` or `stale`, or
# one no status names, needs nothing.

include "sections";

def open_status: IN("design", "partly");
def answer: test("^(absorbed|stays design):\\s*\\S");

. as $in
| select($in.absorption != null)
| [($in.issues // [])[] | .number as $n
    | (.body // "" | section("Sources") // []) | items | keyed
    | select(. != null and (.text | test("\\bprimary\\b"; "i")))
    | .keys[] | select(test("^[^\\s]+\\.md$"))
    | . as $name
    | (if test("/") then [$in.absorption[split("/") | last] // [] | .[] | select(.path == $name)]
       else $in.absorption[$name] // [] end) as $entries
    | select(any($entries[]; .status | open_status))
    | {n: $n, name: $name, status: ([$entries[].status | select(open_status)] | first)}]
| unique_by(.name) as $owed
| select($owed | length > 0)
| [($in.body // "" | section("Vault") // []) | items | keyed | select(. != null and (.text | answer)) | .keys[]] as $answered
| [$owed[] | select(.name as $name | $answered | index($name) | not)]
| select(length > 0)
| "the body's `## Vault` does not answer the design pages its issues build on: a landing absorbs its page in the same pair (`design.md` § design-research). For each, add `- `<page>` — absorbed: <the tree locations this change adds>` with the vault pull request rewriting the page to point at them, or `- `<page>` — stays design: <why>`, then run `pr:open` again:\n"
  + (map("  - `\(.name)` (`\(.status)`, a primary source of #\(.n))") | join("\n"))
