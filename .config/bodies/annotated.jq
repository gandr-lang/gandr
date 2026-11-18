# The body `pr:open` writes back (#2793): each filename of a vault page an
# item of `## Sources read` keys, followed by the page's `vault:<mint>`.
#
# Input: {body, pages, tree}: the body file's text, `vault_pages`'s object,
# and the tree's filenames as newline-separated text. The rule is
# `vault.jq`'s.

include "vault";

.pages as $pages
| (.tree | vault_tree) as $tree
| .body
| vault_annotated($pages; $tree)
