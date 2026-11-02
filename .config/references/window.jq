# The allowlist of `window.toml`, read as JSON (`yq -o json`), as the rows
# `window.sql` reads from `allow`, tab-separated: kind, crate, subject, site,
# work, why, and the entry as written. A `[[crate]]` entry covers a crate
# whole by its `name`, a `[[corpus]]` entry a corpus subject whole, and a
# `[[site]]` entry one work at one site, with `exemplar` saying why no newer
# work states what the site builds. An entry missing what its kind needs is
# a `refused` row, its reason in the `why` column.

def text: type == "string" and length > 0;

[(.crate // [])[]
  | if (.name | text) then ["crate", .name, "", "", "", "", "[[crate]] \(.name)"]
    else ["refused", "", "", "", "", "names no crate: write `name = \"<crate directory>\"`", "[[crate]] \(tojson)"] end],
[(.corpus // [])[]
  | if (.subject | text) then ["corpus", "", .subject, "", "", "", "[[corpus]] \(.subject)"]
    else ["refused", "", "", "", "", "names no subject: write `subject = \"<directory under corpus/>\"`", "[[corpus]] \(tojson)"] end],
[(.site // [])[]
  | if (.site | text) and (.work | text) and (.exemplar | text)
    then ["site", "", "", .site, .work, .exemplar, "[[site]] \(.site) \(.work)"]
    else ["refused", "", "", "", "", "needs a `site`, the `work` it keeps and its `exemplar`: why no newer work states what the site builds", "[[site]] \(tojson)"] end]
| .[] | @tsv
