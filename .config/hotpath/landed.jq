# The body of the `Hotpath: the landed deltas` ledger, which
# `ci:hotpath-landed` writes on each push to `main` (#3596).
#
# Input: `{body, rows, states}`. `body` is the open ledger's body, or null
# when no ledger is open. `rows` is the push's rows, each
# `| <commit> | #<pr> | <benchmark> | <verdict> | <issue> |`. `states` maps
# each issue the table links, as `#<n>`, to its state, `OPEN` or `CLOSED`.
# Output: the ledger's body, as raw text.
#
# A filed ledger keeps its prose: the lines before the table's heading row,
# less the opening of the collapsed block and the blank lines that end them.
# It keeps its rows too: the lines that start with `|` between the heading
# row's alignment row and `</details>`. A new ledger opens with the sentence
# that says what it is, and a one-sentence lead for the table. A row joins
# the table once no row holds its pull request and benchmark. The table
# stands collapsed under a summary that counts the rows, the regressed ones
# (a `⚠️` verdict) and the improved ones.
#
# A row settles in its issue cell (#3348), so `collector_rows` counts only the
# rows with work open. A row that links no issue reads `fixed — no issue`: an
# improvement, or a red check accepted at landing. A row whose linked issues
# `states` holds all as `CLOSED` reads `fixed — <issues>`. A cell that opens
# with a status already, or that links an issue `states` does not hold, stays.

def header: "| Commit | PR | Benchmark | Verdict | Issue |";
def separator: "| --- | --- | --- | --- | --- |";
def fresh: [
  "This issue lists the landings whose hotpath checks regress, or improve past the band of their policy.",
  "",
  "The table gives one row for each red `hotpath / <benchmark>` check of a landing, and one row for each report that improves past its band. `mise run ci:hotpath-landed` adds the rows on the push to `main`. A red row links the issues of the functions that it regresses. A fix or a stated acceptance settles the row of the pull request there. A row reads `fixed` once each issue it links is closed, and at once when it links none."
];
def key: split("|")[2:4] | join("|");
def verdict: split("|")[4] // "";
def settled($states):
  split("|") as $cells
  | ($cells[5] // "" | gsub("^\\s+|\\s+$"; "")) as $issue
  | ([$issue | match("#[0-9]+"; "g") | .string]) as $linked
  | (if $issue | test("^(landed|fixed|accepted|runner shift)\\b"; "i") then null
     elif $issue == "—" or $issue == "" then "fixed — no issue"
     elif ($linked | length) > 0 and all($linked[]; $states[.] == "CLOSED") then "fixed — \($issue)"
     else null
     end) as $status
  | if $status == null then . else ($cells[:5] + [" \($status) "] + $cells[6:]) | join("|") end;

. as $in
| (if .body == null then [] else .body | gsub("\r"; "") | split("\n") end) as $lines
| (first(range(0; $lines | length) | select($lines[.] == header)) // ($lines | length)) as $at
| (first(range($at + 2; $lines | length) | select($lines[.] | startswith("</details>"))) // ($lines | length)) as $end
| (if .body == null then fresh
   else [$lines[:$at][] | select(startswith("<details><summary>") | not)]
     | until(length == 0 or (last | test("^\\s*$") | not); .[:-1])
   end) as $prose
| reduce .rows[] as $row ([$lines[$at + 2:$end][] | select(startswith("|"))];
    if any(.[]; contains($row | key)) then . else . + [$row] end)
| map(settled($in.states // {}))
| length as $count
| ([.[] | select(verdict | contains("⚠️"))] | length) as $regressed
| ([.[] | select(verdict | test("improv"; "i"))] | length) as $improved
| (if $prose == [] then "" else ($prose | join("\n")) + "\n" end)
  + "\n<details><summary>\($count) \(if $count == 1 then "row" else "rows" end) — \($regressed) regressed, \($improved) improved</summary>\n\n"
  + header + "\n" + separator + "\n"
  + (map(. + "\n") | join(""))
  + "\n</details>"
