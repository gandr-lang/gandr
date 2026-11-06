# The body of the `Hotpath: the landed deltas` ledger, which
# `ci:hotpath-landed` writes on each push to `main` (#3596).
#
# Input: `{body, rows}`. `body` is the open ledger's body, or null when no
# ledger is open. `rows` is the push's rows, each
# `| <commit> | #<pr> | <benchmark> | <verdict> | <issue> |`.
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

def header: "| Commit | PR | Benchmark | Verdict | Issue |";
def separator: "| --- | --- | --- | --- | --- |";
def fresh: [
  "This issue lists the landings whose hotpath checks regress, or improve past the band of their policy.",
  "",
  "The table gives one row for each red `hotpath / <benchmark>` check of a landing, and one row for each report that improves past its band. `mise run ci:hotpath-landed` adds the rows on the push to `main`. A red row links the issues of the functions that it regresses. A fix or a stated acceptance settles the row of the pull request there."
];
def key: split("|")[2:4] | join("|");
def verdict: split("|")[4] // "";

(if .body == null then [] else .body | gsub("\r"; "") | split("\n") end) as $lines
| (first(range(0; $lines | length) | select($lines[.] == header)) // ($lines | length)) as $at
| (first(range($at + 2; $lines | length) | select($lines[.] | startswith("</details>"))) // ($lines | length)) as $end
| (if .body == null then fresh
   else [$lines[:$at][] | select(startswith("<details><summary>") | not)]
     | until(length == 0 or (last | test("^\\s*$") | not); .[:-1])
   end) as $prose
| reduce .rows[] as $row ([$lines[$at + 2:$end][] | select(startswith("|"))];
    if any(.[]; contains($row | key)) then . else . + [$row] end)
| length as $count
| ([.[] | select(verdict | contains("⚠️"))] | length) as $regressed
| ([.[] | select(verdict | test("improv"; "i"))] | length) as $improved
| (if $prose == [] then "" else ($prose | join("\n")) + "\n" end)
  + "\n<details><summary>\($count) \(if $count == 1 then "row" else "rows" end) — \($regressed) regressed, \($improved) improved</summary>\n\n"
  + header + "\n" + separator + "\n"
  + (map(. + "\n") | join(""))
  + "\n</details>"
