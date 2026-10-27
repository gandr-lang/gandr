# The crate leads (#3155): each crate that `crates/README.md` § Storage and
# distribution places in the storage picture opens with a lead naming its
# layer, its wall and the section's paper. The input is
# `{readme, sources}`: the README's text, and each source the section's table
# names, by path, absent where the file is missing. `$form` picks the output:
#
# - `paths`: the source each table row names, one a line: `src/lib.rs` for a
#   crate's row, `src/<module>.rs` for a `crate::module` row;
# - `findings`: one line per lead that does not name its row's layer, a wall
#   its row names (`integrity`, `validity`) or the paper key, per row whose
#   source is missing, and one when the section has no table or no key.
#
# A lead is a source's opening: its first `//!` line and those after it, up
# to its first heading or the first line that is no `//!` line. A module's
# summary paragraph stays short (clippy's `too_long_first_doc_paragraph`), so
# the lead may be the paragraph after it.

def place: "crates/README.md § Storage and distribution";

def section:
  .readme
  | (capture("\n## Storage and distribution\n(?<body>(?:.|\n)*?)(?=\n## |\\z)").body // "");

def rows:
  [section
   | splits("\n")
   | select(test("^\\| `"))
   | [splits(" *\\| *")][1:-1]
   | {name: (.[0] | ltrimstr("`") | rtrimstr("`")), layer: .[1], wall: .[4]}];

def path_of:
  (.name | split("::")) as $parts
  | "crates/\($parts[0])/src/\(if ($parts | length) == 1 then "lib" else $parts[1] end).rs";

def key:
  [section | scan("`([A-Z][A-Za-z]+-[0-9]{4}-[a-z0-9_]+)`") | .[0]] | first // null;

def lead($text):
  [$text | splits("\n")]
  | (map(test("^//!")) | index(true)) as $start
  | if $start == null then ""
    else .[$start:]
    | (map(test("^//! ?#") or (test("^//!") | not)) | index(true)) as $end
    | .[:($end // length)]
    | map(sub("^//! ?"; ""))
    | join(" ")
    end;

def names($word): test("\\b" + $word + "\\b");

def findings:
  . as $input
  | rows as $rows
  | key as $key
  | if ($rows | length) == 0 then "\(place) holds no crate table"
    else
      (if $key == null then "\(place) names no paper by its key" else empty end),
      ($rows[]
       | . as $row
       | path_of as $path
       | $input.sources[$path] as $text
       | if $text == null then "\($path): \(place) names it, and the file does not exist"
         else lead($text) as $lead
         | (if $lead | names($row.layer) then empty
            else "\($path): its lead paragraph names no `\($row.layer)`, its layer in \(place)" end),
           (["integrity", "validity"][]
            | . as $wall
            | select(($row.wall | names($wall)) and ($lead | names($wall) | not))
            | "\($path): its lead paragraph names no `\($wall)`, its wall in \(place)"),
           (if $key == null or ($lead | contains($key)) then empty
            else "\($path): its lead paragraph names no `\($key)`, the paper of \(place)" end)
         end)
    end;

if $form == "paths" then rows[] | path_of
elif $form == "findings" then findings
else error("form is paths or findings, not \($form)")
end
