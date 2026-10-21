# The mutants of one crate grouped by the function each sits in, each group
# with the regex that selects exactly its mutants and the nextest filterset
# of the witnesses naming that function (#1456).
#
# Input: an object with
#   mutants  `cargo mutants --list --json` over the crate;
#   items    `items.jq` over the crate's rustdoc JSON;
#   package  the crate's package name;
#   targets  the names of the crate's integration test targets.
#
# A mutant sits in the function cargo-mutants names for it: the documented
# function whose definition ends on that function's last line and starts
# within it (cargo-mutants' span opens at the documentation, rustdoc's at the
# signature). A mutant cargo-mutants places in no function sits in the
# innermost documented function spanning it. A mutant in no documented
# function groups with the others of its file under a null item.
#
# Output: one `{file, item, names, re, filter}` per group, ordered by file
# then item: `item` is the function's `file:line`, `re` matches the group's
# mutant names and no other, and `filter` selects the function's witnesses as
# the obligations report's selection does (an integration witness names its
# target binary first), or is null when no witness names the function: those
# mutants run under no test and read missed.

def escaped: gsub("(?<c>[\\\\.+*?()|\\[\\]{}^$])"; "\\\(.c)");

def alternative($targets):
  split("::") as $segments
  | if ($segments | length) > 1 and ($targets | index($segments[0])) != null then
      "(binary(=\($segments[0])) & test(=\($segments[1:] | join("::"))))"
    else
      "test(=\(.))"
    end;

. as $in
| [$in.mutants[]
    | . as $mutant
    | (if .function == null then
         [$in.items[]
           | select(.file == $mutant.file and .begin <= $mutant.span.start.line and $mutant.span.end.line <= .end)]
         | min_by(.end - .begin)
       else
         .function.span as $span
         | [$in.items[]
             | select(.file == $mutant.file and .end == $span.end.line and $span.start.line <= .begin)]
         | min_by(.begin)
       end) as $item
    | {
        file,
        name,
        item: (if $item == null then null else "\($item.file):\($item.begin)" end),
        witnesses: ($item.witnesses // [])
      }]
| group_by([.file, .item])
| map({
    file: .[0].file,
    item: .[0].item,
    names: map(.name),
    re: ("^(" + (map(.name | escaped) | join("|")) + ")$"),
    filter: (.[0].witnesses | unique
      | if length == 0 then null
        else "package(=\($in.package)) & (" + (map(alternative($in.targets)) | join(" | ")) + ")"
        end)
  })
