# What `unit:check` prints for the vault pages an issue's `## Sources` names
# (#2793): one tab-separated line per page, `refuse` and the refusal for a
# filename no vault page carries, `show` and what it resolves to otherwise.
#
# Input: {body, pages, tree}: the issue's body, `vault_pages`'s object, and
# the tree's filenames as newline-separated text. The rule is `vault.jq`'s.

include "sections";
include "vault";

.pages as $pages
| (.tree | vault_tree) as $tree
| .body
| section("Sources") // []
| vault_sources($pages; $tree)
| vault_shown
