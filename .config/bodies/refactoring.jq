# Whether every `Where` of a body's `## Refactoring` names something the
# workspace carries (#2884): one refusal line per `Where` it does not, or
# nothing. `pr:open` runs it through `check:refactoring` once
# `evidence:rustdoc` has written the workspace's rustdoc JSON, so no network
# is read; `opening.jq` has already refused a `Where` of neither spelling.
#
# Input:
#   body   the body file's text
#   paths  every item path the workspace's rustdoc JSON carries,
#          `crate::module::Item`, the crate as rustdoc names it
#   names  every item name of each crate's index, `crate#name`: a method, a
#          field or a private function, which rustdoc gives no path
#   tree   the repository's tracked files
#
# An item path resolves when rustdoc carries it, or when rustdoc carries its
# parent and the crate's index holds an item of its last name
# (`crate::Type::method`). A crate alone resolves when rustdoc carries an item
# under it. A repository path resolves when it is a tracked file or a
# directory holding one, a trailing `/` dropped.

include "sections";

(.paths // []) as $paths
| (.names // []) as $names
| (.tree // []) as $tree
| (reduce $paths[] as $p ({}; .[$p] = true)) as $carried
| (reduce $names[] as $n ({}; .[$n] = true)) as $named
| (reduce $tree[] as $t ({}; .[$t] = true)) as $tracked
| def resolves:
    if item_path then
      (split("::")) as $parts
      | if ($parts | length) == 1 then any($paths[]; startswith($parts[0] + "::"))
        else $carried[.] == true
          or ($carried[$parts[:-1] | join("::")] == true and $named["\($parts[0])#\($parts[-1])"] == true)
        end
    else
      sub("/$"; "") as $path
      | $tracked[$path] == true or any($tree[]; startswith($path + "/"))
    end;
(.body | refactoring) as $section
| select($section != null)
| $section.rows[]
| .line as $line
| .whereas[]
| select((item_path or tree_path) and (resolves | not))
| if item_path then "the `## Refactoring` row `\($line)` names `\(.)`, which no item of the workspace's rustdoc carries: write the path as rustdoc names it (`gandr_surface_corpus::settle::settle`), then run `pr:open` again"
  else "the `## Refactoring` row `\($line)` names `\(.)`, which the repository does not track: name a tracked file or a directory holding one, then run `pr:open` again"
  end
