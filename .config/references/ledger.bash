# The references tasks' shared reading of the tree, sourced from the workspace
# root: the sources `cites.awk` reads, and a database holding the ledger
# beside what the tree cites now.

# Each crate's README and module sources: its library's, or a binary-only
# crate's, never a `src/bin/` target's.
references_sources() {
  git ls-files --cached --others --exclude-standard -- 'crates/*/README.md' ':(glob)crates/*/src/**/*.rs' \
    | awk -F/ '
        $4 == "bin" { next }
        { path[++n] = $0; if ($3 == "src" && $4 == "lib.rs") library[$2] = 1 }
        END { for (i = 1; i <= n; i++) { split(path[i], part, "/"); if (!(part[3] == "src" && part[4] == "main.rs" && library[part[2]])) print path[i] } }' \
    | while IFS= read -r path; do if [[ -e $path ]]; then printf '%s\n' "$path"; fi; done
}

# Builds the database named: `reference`, the ledger as committed; `cite`, one
# row per line `cites.awk` prints; `source`, each module's source with its
# blob id now; `derived`, the rows the citations make, each key at each site
# once, its role the one its key lines state or `background`.
references_load() {
  local db=$1 dir sources
  dir=$(dirname "$db")
  mapfile -t sources < <(references_sources)
  LC_ALL=C awk -f .config/references/cites.awk "${sources[@]}" > "$dir/cites.tsv"
  awk -F'\t' '$1 == "file" { print $6 }' "$dir/cites.tsv" > "$dir/paths"
  git hash-object --stdin-paths < "$dir/paths" > "$dir/blobs"
  paste "$dir/paths" "$dir/blobs" > "$dir/hashes.tsv"
  sqlite3 -bail "$db" < ledger/references.sql
  sqlite3 -bail -tabs "$db" \
    'CREATE TABLE cite(kind TEXT, key TEXT, crate TEXT, module TEXT, role TEXT, location TEXT);' \
    ".import $dir/cites.tsv cite" \
    'CREATE TABLE hash(path TEXT PRIMARY KEY, blob TEXT);' \
    ".import $dir/hashes.tsv hash" \
    "CREATE VIEW source AS SELECT c.crate, c.module, c.location AS path, h.blob, c.crate || CASE c.module WHEN '' THEN '' ELSE '::' || c.module END AS shown FROM cite c JOIN hash h ON h.path = c.location WHERE c.kind = 'file';" \
    "CREATE VIEW derived AS SELECT key, crate, module, min(role) AS role FROM cite WHERE kind IN ('cite', 'locator') GROUP BY key, crate, module;"
}

# Builds `fresh.db` beside the database named: the ledger the tree makes, the
# rows `derived` holds, each carrying its committed reading.
references_fresh() {
  local db=$1 dir
  dir=$(dirname "$db")
  rm -f "$dir/fresh.db"
  sqlite3 -bail "$db" '.schema reference' | sqlite3 -bail "$dir/fresh.db"
  sqlite3 -bail "$dir/fresh.db" "ATTACH '$db' AS tree;" \
    'INSERT INTO reference SELECT d.key, d.crate, d.module, d.role, r.read_commit, r.read_date, r.read_blob FROM tree.derived d LEFT JOIN tree.reference r USING (key, crate, module);'
}
