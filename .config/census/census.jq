# The bootstrap census (#2896): each crate's row as `report:bootstrap-census`
# gathers it, rendered into `$doc`, `ledger/census.md`, between its `census`
# markers. The input is `{rows: [row]}`, one row per workspace crate with a
# library:
#
#   {crate, items, types, foreign, clauses, witnesses, specs, hotpath, deps, lines}
#
# `items` its public items, `types` and `foreign` the types its surface
# mentions and those another crate defines (`surface.jq`), `clauses` and
# `witnesses` its documented specification bullets, `specs` its `#[spec]`
# attributes, `hotpath` whether a function of it is measured, `deps` the
# workspace crates it depends on, and `lines` its library's size.
#
# - Depth: 0 for a crate with no workspace dependency, a leaf; otherwise one
#   more than its deepest dependency's.
# - Specs per item: the clauses, the witnesses and the attributes over the
#   public items.
# - Rank: hotpath crates after the others; within each, leaves first, then
#   fewest boundary types per public item, then most specs per item, then by
#   name. A crate with no public item is ranked last.
#
# The block is three parts: the census by crate, the ranking, and the top
# three's types from other crates. Each table's delimiter row is as wide as
# its header cells, the form `rumdl fmt` keeps.

# A number to two decimals.
def fixed:
  (. * 100 | round) as $hundredths
  | "\($hundredths / 100 | floor).\($hundredths % 100 | tostring | if length < 2 then "0" + . else . end)";

# A count with its noun, singular at one.
def counted($one; $many):
  "\(.) \(if . == 1 then $one else $many end)";

# Each crate's depth: iterated once per crate, enough for any acyclic graph.
def depths:
  (map({key: .crate, value: .deps}) | from_entries) as $deps
  | reduce range(0; length) as $_ ((map({key: .crate, value: 0}) | from_entries);
      . as $depth
      | with_entries(.value = ($deps[.key] | if length == 0 then 0 else ([.[] | $depth[.] // 0] | max) + 1 end)));

def measured:
  depths as $depth
  | map(
      . + {depth: $depth[.crate]}
      | . + if .items == 0 then {types_per_item: null, specs_per_item: null}
            else {types_per_item: (.types / .items), specs_per_item: ((.clauses + .witnesses + .specs) / .items)}
            end);

def ranked:
  sort_by(
    (if .items == 0 then 1 else 0 end),
    (if .hotpath then 1 else 0 end),
    (if .depth == 0 then 0 else 1 end),
    (.types_per_item // 0),
    (-(.specs_per_item // 0)),
    .crate);

def why:
  if .items == 0 then "no public items"
  else
    [
      (if .hotpath then "hotpath" else empty end),
      (if .depth == 0 then "leaf" else "depth \(.depth)" end),
      "\(.types_per_item | fixed) boundary types per item",
      "\(.specs_per_item | fixed) specs per item"
    ]
    | join("; ")
  end;

def table($headers):
  "| \($headers | join(" | ")) |",
  "| \($headers | map("-" * length) | join(" | ")) |";

def block:
  measured as $rows
  | ($rows | ranked) as $ranked
  | [
      table(["Crate", "Public items", "Boundary types", "Specs per item", "Hotpath", "Depth", "Lines"]),
      ($rows
       | sort_by(.crate)[]
       | "| `\(.crate)` | \(.items) | \(.types) | \(.specs_per_item | if . == null then "none" else fixed end) | \(if .hotpath then "yes" else "no" end) | \(.depth) | \(.lines) |"),
      "",
      table(["Rank", "Crate", "Why"]),
      ($ranked | to_entries[] | "| \(.key + 1) | `\(.value.crate)` | \(.value | why) |"),
      "",
      "The top three's boundary types from other crates, each by the path rustdoc records for its definition:",
      "",
      ($ranked[:3][]
       | (.foreign | length) as $foreign
       | "- `\(.crate)`: \(.types | counted("boundary type"; "boundary types")), \(if $foreign == 0 then "none from another crate" else "\($foreign | counted("from another crate"; "from other crates")): \(.foreign | map("`\(.)`") | join(", "))" end)")
    ]
  | join("\n");

.rows
| block as $block
| $doc
| (capture("^(?<head>(?:.|\n)*<!-- census:begin -->\n)(?:.|\n)*?(?<tail><!-- census:end -->(?:.|\n)*)$")
   // error("ledger/census.md holds no `<!-- census:begin -->` … `<!-- census:end -->` block"))
| .head + $block + "\n" + .tail
