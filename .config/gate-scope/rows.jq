# Whether a row of `table.json` maps a path, for `select.jq` and
# `packages.jq`. A row's path is a file, a directory that ends in `/`, or a
# glob (#6648): `*` stands for any run of characters but `/`, and `**` for
# any run at all.

def glob:
  gsub("(?<c>[.+?^${}()|\\[\\]\\\\])"; "\\\(.c)")
  | gsub("\\*\\*"; "\u0000")
  | gsub("\\*"; "[^/]*")
  | gsub("\u0000"; ".*")
  | "^" + . + "$";

def mapped($row; $path):
  if ($row.path | contains("*")) then $path | test($row.path | glob)
  else $row.path == $path or (($row.path | endswith("/")) and ($path | startswith($row.path)))
  end;
