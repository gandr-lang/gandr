# The body of a recovery collector (#1782, #3596), which `ci:recovery-file`
# files for one cause of the night's sweep. Its first sentence says what the
# collector is. `## Findings` gives the cause's first findings in a text
# block. `## Families` gives each family as a checkbox row, the row a landing
# ticks (#3326, `landed.jq`) and the night's sweep marks (`swept.jq`).
#
# Input: one cause of the report, `{name, kind, count, family_count,
# families, findings, run}`. `kind` is `deleted` or `missed`, and `families`
# the report's comma-separated family names. `findings` holds the first
# findings' lines as text, and `run` the nightly run's address or null.
# Output: the body, as raw text.

(if .kind == "deleted" then "a deleted tile" else "a tile written as its near miss" end) as $tile
| "This issue collects the mutants of the recovery sweep whose first error, `\(.name)`, falls at other bytes than the mutation.\n\n"
  + "The recovery sweep (`gandr ledger recovery corpus/ledger`, #1782) writes each literal tile of each syntax exemplar wrong and reads the first error. "
  + "It finds \(.count) such \(if .count == 1 then "mutant" else "mutants" end) with \($tile).\n\n"
  + "## Findings\n\n"
  + "The first findings follow. The nightly run lists each one\(if .run == null then "" else " (\(.run))" end).\n\n"
  + "```text\n\(.findings)```\n\n"
  + "## Families\n\n"
  + "The list gives each family. `ci:recovery-file` ticks its box once the sweep marks the mutants of the family at the mutation.\n\n"
  + "<details><summary>\(.family_count) \(if .family_count == 1 then "family" else "families" end) — open</summary>\n\n"
  + (.families | split(",") | map("- [ ] `\(sub("^ +"; ""))`\n") | join(""))
  + "\n</details>"
