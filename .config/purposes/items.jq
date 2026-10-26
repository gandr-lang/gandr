# The entries the purposes ledger rows for one crate (`ledger/purposes.sql`),
# read from the rustdoc JSON of the crate's library built without private
# items. `$crate` is the crate's directory under `crates/`. Prints one
# tab-separated line per entry, sorted by path, then kind:
#
#   <crate>  <path>  <kind>  <location>
#
# - an item: each entry of rustdoc's `paths` table that the crate itself
#   defines with a module-level kind, by the path it is defined at, so an item
#   a private module defines and the root re-exports keeps its module. Its
#   kind is rustdoc's; its location the file and line its definition opens
#   at. A variant, a field, an associated item, an implementation and a
#   re-export belong to the item that holds them and have no entry, and so
#   does an item one macro invocation generates with the module holding it:
#   its span is the module's, and the module's entry stands for both;
# - a module: every module the table lists, and every module on an item's
#   path, a private one included. A module the table lists is located at its
#   declaration; a private one at the file of the first entry beneath it;
# - the crate: the root module, kind `crate`, path empty.
#
# The reading is rustdoc's JSON format 58. Another format stops the program
# with an error naming it.

def item_kinds:
  ["struct", "union", "enum", "function", "type_alias", "constant", "static", "trait", "trait_alias", "extern_type", "macro", "proc_attribute", "proc_derive"];

def location:
  if .span == null then "" else "\(.span.filename):\(.span.begin[0])" end;

if .format_version != 58 then
  error("rustdoc JSON format \(.format_version): .config/purposes/items.jq reads format 58; read its `paths` and `index` against the new format and move the version with it")
end
| .index as $index
| [.paths
   | to_entries[]
   | select(.value.crate_id == 0 and (.value.kind == "module" or (.value.kind | IN(item_kinds[]))))
   | {
       segments: .value.path[1:],
       kind: (if .value.path | length == 1 then "crate" else .value.kind end),
       span: $index[.key].span
     }] as $table
| ($table | map(select(.kind == "module") | {key: (.segments | join("::")), value: .span}) | from_entries) as $modules
| [$table[]
   | select(
       . as $entry
       | [first(range($entry.segments | length - 1; 0; -1) as $depth
           | $modules[$entry.segments[:$depth] | join("::")] // empty)][0] as $holder
       | $entry.span == null or $holder != $entry.span
     )
   | {path: (.segments | join("::")), kind, location: location}] as $listed
| [$listed[]
   | .path
   | split("::")
   | range(1; length) as $depth
   | .[:$depth]
   | join("::")]
| unique
| map(select(. as $module | $modules | has($module) | not)) as $private
| ($listed | sort_by(.path)) as $sorted
| $listed
  + [$private[]
     | . as $module
     | {
         path: $module,
         kind: "module",
         location: (first($sorted[] | select(.path | startswith($module + "::")) | .location | sub(":[0-9]+$"; "")))
       }]
| sort_by(.path, .kind)[]
| [$crate, .path, .kind, .location]
| @tsv
