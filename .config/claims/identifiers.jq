# The design pages that a unit's identifiers give its `## Sources` (#7019,
# `units.md` § units-sources): one line for each design page that names one
# of the unit's identifiers, or that such a page links, while `## Sources`
# names it nowhere.
#
# Input: `{number, parent, body, rows, crates, design, texts, before}`: the
# issue's number and its parent's on GitHub, or null; its body; the ledger's
# feature ids and the tree's crate directories; the vault's design pages by
# path, or null on a host with no vault; the text of each design page that
# names an identifier, by path; and the body as it stood when this rule
# landed, for an issue signed by then, or null.
#
# The identifiers are those of `unit_identifiers` in `sections.jq`. A
# level-two section of a page that names a number or a row gives the page,
# and each design page that the same section links. A page names an
# identifier in a `###` section and links its design in a sibling `###`
# section, so the search reads the level-two section. A crate gives its own
# page, `crates/<dir>.md`, alone: its name meets up to 166 pages of one
# unit. `## Sources` cites a page by its filename, as `cited` reads it, and a
# `not read` row cites it too.
#
# The rule stops no unit in flight: while the `## Sources` of an issue signed
# before the rule landed is as it was then, each line is a `note:`, and no
# refusal.

include "sections";
# A text's level-two sections, each as {head, text}: the lines before the
# first `## ` heading under the head "", then each `## ` heading with its
# lines up to the next. A line inside a fenced block opens no section. The
# sections are slices at the headings' indexes, so a page costs one pass.
def level_two:
  lines as $lines
  | [foreach range(0; $lines | length) as $i ({fenced: false, head: false};
      ($lines[$i] | test("^\\s*(```|~~~)")) as $fence
      | .head = ((.fenced | not) and ($lines[$i] | test("^## ")))
      | if $fence then .fenced |= not else . end;
      if .head then $i else empty end)] as $heads
  | ([0] + $heads + [$lines | length] | unique) as $cuts
  | range(0; ($cuts | length) - 1) as $k
  | $lines[$cuts[$k]:$cuts[$k + 1]] as $part
  | {head: (if $cuts[$k] | IN($heads[]) then $part[0] | sub("^##\\s+"; "") | sub("\\s+$"; "") else "" end),
     text: ($part | join("\n"))};
# The path of the relative link `.` from the page `$from`, its `.` and `..`
# read.
def beside($from):
  ($from | split("/") | .[:-1]) + split("/")
  | reduce .[] as $part ([]; if $part == "" or $part == "." then . elif $part == ".." then .[:-1] else . + [$part] end)
  | join("/");

# The pages that the links of a text name, each read beside `$from`.
def linked($from): [scan("\\]\\(([^)\\s#]+\\.md)(?:#[^)]*)?\\)") | .[0] | beside($from)];

# The name of a page: its filename.
def filename: split("/") | last;

. as $in
| select($in.design != null)
| ($in.body // "") as $body
| ($body | section("Sources") // [] | join("\n")) as $sources
| ($in.before != null and (($in.before | section("Sources")) == ($body | section("Sources")))) as $kept
| ($body | unit_identifiers($in.number; $in.parent; $in.rows; $in.crates)) as $ids
| ($ids | identifier_marks) as $marks
| [($in.texts // {} | to_entries[]
     | .key as $page
     | .value
     | level_two
     | . as $section
     | [$marks[] | .test as $test | select($section.text | test($test)) | .label] as $met
     | select($met | length > 0)
     | (if $section.head == "" then "lead" else "section `\($section.head)`" end) as $where
     | ($met | join(", ")) as $named
     | {page: $page, rank: 0, why: "`\($page | filename)` names \($named) in its \($where)"},
       ($section.text | linked($page)[]
        | select(. != $page and IN($in.design[]))
        | {page: ., rank: 1, why: "the \($where) of `\($page | filename)` names \($named) and links `\(. | filename)`"})),
   ($ids.crates[] as $crate
     | $in.design[]
     | select(endswith("/crates/\($crate).md"))
     | {page: ., rank: 2, why: "`\(. | filename)` is the page of the crate `\($crate)`"})]
| group_by(.page)
| map(min_by(.rank))[]
| (.page | filename) as $name
| select($name | cited($sources) | not)
| "sources: \(.why): cite `\($name)` in `## Sources`, or add the row `| `\($name)` | not read | <why> |` (`units.md` § units-sources)"
| if $kept then "note: \(.); the issue was signed before this check landed, so it is not refused until its `## Sources` changes" else . end
