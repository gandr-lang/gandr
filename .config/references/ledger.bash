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

# Builds the database named: `reference`, `work` and `fidelity`, the ledger as
# committed; `cite`, one row per line `cites.awk` prints over the crates and
# the corpus; `source`, each module's source with its blob id now; `corpus`,
# each corpus source's path; `derived`, the rows the crates' citations make,
# each key at each site once, its role the one its key lines state or
# `background`.
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
    "CREATE VIEW derived AS SELECT key, crate, module, min(role) AS role FROM cite WHERE kind IN ('cite', 'locator') GROUP BY key, crate, module;"
}

# Builds `fresh.db` beside the database named: the ledger the tree makes, the
# rows `derived` holds, each carrying its committed reading, the committed
# `work` rows of the works the crates or the corpus still cite, and every
# committed `fidelity` row, which the citation refresh writes by hand.
references_fresh() {
  local db=$1 dir
  dir=$(dirname "$db")
  rm -f "$dir/fresh.db"
  sqlite3 -bail "$db" '.schema reference' '.schema work' '.schema fidelity' | sqlite3 -bail "$dir/fresh.db"
  sqlite3 -bail "$dir/fresh.db" "ATTACH '$db' AS tree;" \
    'INSERT INTO reference SELECT d.key, d.crate, d.module, d.role, r.read_commit, r.read_date, r.read_blob FROM tree.derived d LEFT JOIN tree.reference r USING (key, crate, module);' \
    "INSERT INTO work SELECT * FROM tree.work w WHERE EXISTS (SELECT 1 FROM tree.cite c WHERE c.key = w.key AND c.kind IN ('cite', 'locator', 'corpus'));" \
    'INSERT INTO fidelity SELECT * FROM tree.fidelity;'
}

# Prints the citation window's findings over the database named, which holds
# `cite` and `work` as `references_load` builds them, under the policy file
# named: its cutoff year and its allowlist, read by `window.jq`. The cutoff
# `unit:check` reads from the text (`.config/claims/cutoff.jq`, #4708) is held
# to the one yq reads.
references_window() {
  local db=$1 policy=$2 dir json cutoff
  dir=$(dirname "$db")
  json=$(yq -p toml -o json '.' "$policy")
  if ! cutoff=$(jq -er '.cutoff | select(type == "number" and . == floor)' <<< "$json"); then
    echo "$policy: \`cutoff\` is the year the citation window opens, a whole number" >&2
    return 1
  fi
  if [[ $(jq -R -s -f .config/claims/cutoff.jq "$policy" 2> /dev/null) != "$cutoff" ]]; then
    echo "$policy: \`.config/claims/cutoff.jq\` does not read the cutoff $cutoff: write it as one line, \`cutoff = <year>\`" >&2
    return 1
  fi
  jq -r -f .config/references/window.jq <<< "$json" > "$dir/allow.tsv"
  sqlite3 -bail -tabs "$db" \
    'DROP TABLE IF EXISTS allow;' 'DROP TABLE IF EXISTS window;' \
    'CREATE TABLE allow(kind TEXT, crate TEXT, subject TEXT, site TEXT, work TEXT, why TEXT, entry TEXT);' \
    ".import $dir/allow.tsv allow" \
    "CREATE TABLE window(cutoff INTEGER); INSERT INTO window VALUES($cutoff);" \
    '.mode list' '.read .config/references/window.sql'
}

# Prints the citation refresh's findings over the database named, which holds
# `cite`, `corpus` and `fidelity` as `references_load` builds them
# (`fidelity.sql`, #4533).
references_fidelity() {
  sqlite3 -bail "$1" '.mode list' '.read .config/references/fidelity.sql'
}
