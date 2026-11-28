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

# The corpus sources, whose comments' locators the citation window reads.
references_corpus() {
  git ls-files --cached --others --exclude-standard -- ':(glob)corpus/**/*.gandr' \
    | while IFS= read -r path; do if [[ -e $path ]]; then printf '%s\n' "$path"; fi; done
}

# Builds the database named: `reading`, `work` and `fidelity`, the ledger as
# committed; `cite`, one row per line `cites.awk` prints over the crates and
# the corpus; `source`, each module's source with its blob id now; `corpus`,
# each corpus source's path; `derived`, the rows the crates' citations make,
# each key at each site once, its role the one its key lines state or
# `background`; `reference`, each row of `derived` with its reading.
references_load() {
  local db=$1 dir sources
  dir=$(dirname "$db")
  mapfile -t sources < <(references_sources; references_corpus)
  LC_ALL=C awk -f .config/references/cites.awk "${sources[@]}" > "$dir/cites.tsv"
  awk -F'\t' '$1 == "file" { print $6 }' "$dir/cites.tsv" > "$dir/paths"
  git hash-object --stdin-paths < "$dir/paths" > "$dir/blobs"
  paste "$dir/paths" "$dir/blobs" > "$dir/hashes.tsv"
  references_corpus > "$dir/corpus"
  sqlite3 -bail "$db" < ledger/references.sql
  sqlite3 -bail -tabs "$db" \
    'CREATE TABLE cite(kind TEXT, key TEXT, crate TEXT, module TEXT, role TEXT, location TEXT);' \
    ".import $dir/cites.tsv cite" \
    'CREATE TABLE hash(path TEXT PRIMARY KEY, blob TEXT);' \
    ".import $dir/hashes.tsv hash" \
    'CREATE TABLE corpus(path TEXT PRIMARY KEY);' \
    ".import $dir/corpus corpus" \
    "CREATE VIEW source AS SELECT c.crate, c.module, c.location AS path, h.blob, c.crate || CASE c.module WHEN '' THEN '' ELSE '::' || c.module END AS shown FROM cite c JOIN hash h ON h.path = c.location WHERE c.kind = 'file';" \
    "CREATE VIEW derived AS SELECT key, crate, module, min(role) AS role FROM cite WHERE kind IN ('cite', 'locator') GROUP BY key, crate, module;" \
    'INSERT INTO reference SELECT d.key, d.crate, d.module, d.role, r.read_commit, r.read_date, r.read_blob FROM derived d LEFT JOIN reading r USING (key, crate, module);'
}

# Builds `fresh.db` beside the database named: the ledger the tree makes, its
# `reference` rows, each with its reading, and the committed `work` and
# `fidelity` rows.
references_fresh() {
  local db=$1 dir
  dir=$(dirname "$db")
  rm -f "$dir/fresh.db"
  sqlite3 -bail "$db" '.schema reference' '.schema work' '.schema fidelity' | sqlite3 -bail "$dir/fresh.db"
  sqlite3 -bail "$dir/fresh.db" "ATTACH '$db' AS tree;" \
    'INSERT INTO reference SELECT * FROM tree.reference;' \
    'INSERT INTO work SELECT * FROM tree.work;' \
    'INSERT INTO fidelity SELECT * FROM tree.fidelity;'
}

# Prints the rows of `ledger/references.sql` that name nothing the tree
# cites, over the database named as `references_load` builds it: a reading of
# a key at a site that does not cite it, and a `work` row of a work that the
# crates and the corpus do not cite.
references_orphans() {
  sqlite3 -bail "$1" "
    SELECT 'ledger/references.sql: the reading of \`' || key || '\` at ' || crate || CASE module WHEN '' THEN '' ELSE '::' || module END
      || ' names a citation that the tree does not make; delete the row'
    FROM reading r WHERE NOT EXISTS (SELECT 1 FROM derived d WHERE d.key = r.key AND d.crate = r.crate AND d.module = r.module)
    UNION ALL
    SELECT 'ledger/references.sql: the \`work\` row of \`' || key || '\` names a work that the crates and the corpus do not cite; delete the row'
    FROM work w WHERE NOT EXISTS (SELECT 1 FROM cite c WHERE c.key = w.key AND c.kind IN ('cite', 'locator', 'corpus'))
    ORDER BY 1;"
}

# Prints the citation refresh's findings over the database named, which holds
# `cite`, `corpus` and `fidelity` as `references_load` builds them
# (`fidelity.sql`, #4533).
references_fidelity() {
  sqlite3 -bail "$1" '.mode list' '.read .config/references/fidelity.sql'
}
references_vault_upstream() {
  local vault=$1 unresolved=$2 known=$3 state=$4 upstream behind
  : > "$known"
  : > "$state"
  upstream=$(git -C "$vault" rev-parse --abbrev-ref --symbolic-full-name '@{upstream}' 2> /dev/null || true)
  [[ -n $upstream ]] || return 0
  behind=$(git -C "$vault" rev-list --count "HEAD..$upstream" 2> /dev/null || true)
  [[ $behind =~ ^[1-9][0-9]*$ && -s $unresolved ]] || return 0
  awk -F: '{ print "mint: " $2 }' "$unresolved" > "${known%/*}/unresolved-mints"
  git -C "$vault" grep -hF -f "${known%/*}/unresolved-mints" "$upstream" -- '*.md' 2> /dev/null \
    | awk '{ print "vault:" $2 }' > "$known" || true
  [[ -s $known ]] || return 0
  printf '%s\t%s\t%s\n' "$vault" "$behind" "$upstream" > "$state"
}
