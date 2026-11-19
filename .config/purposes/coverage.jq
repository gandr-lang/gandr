# The items tagged with a concern that no site of that concern covers, one
# finding per item, from `{tags: [{crate, path, kind, tag}], sites: [{concern,
# crate, module}]}`: `tags` from `ledger/purposes.sql`, `sites` from
# `ledger/concerns.sql`. A site covers its module, the modules below it and
# the items they define; a site at the empty module covers its whole crate.

# Whether the site in `.` covers `$item`.
def covers($item):
  . as $site
  | $site.crate == $item.crate
    and ($site.module == ""
      or $item.path == $site.module
      or ($item.path | startswith($site.module + "::")));

# An entry as `mise run purposes:list` names it.
def shown: .crate + (if .path == "" then "" else "::" + .path end);

.sites as $sites
| .tags[]
| . as $item
| select([$sites[] | select(.concern == $item.tag) | covers($item)] | any | not)
| "\($item | shown) (\($item.kind)): tagged \($item.tag), and no \($item.tag) site of ledger/concerns.sql covers it; add the site, or correct the tag"
