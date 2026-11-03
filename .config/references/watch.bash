# The paper watch (#2544), sourced by `refs:watch` beside `ledger.bash`. It
# asks OpenAlex what is new since the last run and files the delta on one
# review issue. `watch.jq` reads the delta; this file gathers what it reads.
#
# The configuration lives under the XDG configuration directory:
# `gandr/references` names the library (`library <path>`) and the vault's
# checkout (`vault <path>`), and `gandr/paper-watch.toml` holds `repository`,
# the one taking the review issue, `threshold`, the library entries a journal
# or a conference holds before its new works are read (a book series or an
# ebook platform prints every subject, and a repository every preprint),
# `mailto`, the contact address OpenAlex asks for, and an optional `api_key`,
# which raises the daily budget a keyless run shares with its network. The
# state lives under the XDG state
# directory, `gandr/paper-watch/state.json`: `start`, the first run's earliest
# day, `last`, the last run's day, and `reported`, every OpenAlex id filed.
#
# OpenAlex's free date filter is the publication day, which misses a work
# indexed after it: each run reads from 90 days before its last run, never
# before the first run's start, and the state's ids keep a work from
# reappearing. Every list query reads at most `WATCH_PAGES` pages of 100 and
# notes a query it truncates.

WATCH_API=https://api.openalex.org/works
WATCH_PAGES=20
WATCH_SELECT=id,doi,display_name,publication_date,authorships,primary_location,primary_topic
WATCH_TITLE='Paper watch'

# Prints the OpenAlex works `filter` names, every page up to `WATCH_PAGES`,
# as one JSON array; `select` names the fields. A truncated listing adds a line
# to the notes file `$dir/notes`.
watch_list() {
  local filter=$1 select=$2 page=1 count=0 got=0 response
  local -a key=()
  [[ -n ${WATCH_KEY:-} ]] && key=(--data-urlencode "api_key=$WATCH_KEY")
  : > "$WATCH_DIR/pages"
  while :; do
    response=$(curl -sS --fail-with-body --retry 3 --retry-delay 2 --get "$WATCH_API" \
      --data-urlencode "filter=$filter" --data-urlencode "select=$select" \
      --data-urlencode per-page=100 --data-urlencode "page=$page" \
      --data-urlencode "mailto=$WATCH_MAILTO" "${key[@]}")
    jq -c '.results' <<< "$response" >> "$WATCH_DIR/pages"
    count=$(jq '.meta.count' <<< "$response")
    got=$((got + $(jq '.results | length' <<< "$response")))
    (( got < count )) || break
    if (( page >= WATCH_PAGES )); then
      printf 'a query read %d of its %d works: `%s`\n' "$got" "$count" "${filter:0:120}" >> "$WATCH_DIR/notes"
      break
    fi
    page=$((page + 1))
  done
  jq -cs 'add // []' "$WATCH_DIR/pages"
}

# Prints the works of the values on standard input, one a line, under the
# filter `field`, fifty values a query, as one JSON array. A value holding a
# comma or a bar, which the filter syntax reads as separators, is left out
# and noted.
watch_batched() {
  local field=$1 select=$2 batch
  local -a values=()
  mapfile -t values
  : > "$WATCH_DIR/batches"
  local i
  for ((i = 0; i < ${#values[@]}; i += 50)); do
    batch=$(printf '%s\n' "${values[@]:i:50}" | awk '/[,|]/ { print "a value the filter cannot hold: `" $0 "`" > "/dev/stderr"; next } NF { print }' 2>> "$WATCH_DIR/notes" | paste -sd'|')
    [[ -n $batch ]] || continue
    watch_list "$field:$batch$WATCH_SINCE" "$select" >> "$WATCH_DIR/batches"
  done
  jq -cs 'add // []' "$WATCH_DIR/batches"
}

# Prints the OpenAlex work whose title and year match a library entry's, as a
# JSON array of at most one, matching the title with case, spacing and
# punctuation taken out.
watch_titled() {
  local title=$1 year=$2 response
  local -a key=()
  [[ -n ${WATCH_KEY:-} ]] && key=(--data-urlencode "api_key=$WATCH_KEY")
  response=$(curl -sS --fail-with-body --retry 3 --retry-delay 2 --get "$WATCH_API" \
    --data-urlencode "search=$title" --data-urlencode "filter=publication_year:$year" \
    --data-urlencode "select=$WATCH_SELECT" --data-urlencode per-page=5 \
    --data-urlencode "mailto=$WATCH_MAILTO" "${key[@]}")
  jq -c --arg title "$title" \
    'def plain: ascii_downcase | gsub("[^a-z0-9]"; ""); [.results[] | select((.display_name // "" | plain) == ($title | plain))] | .[0:1]' <<< "$response"
}

# Runs the watch: `dry` is `true` to print the review comment and leave the
# issue and the state alone.
references_watch() {
  local dry=$1 refs config state today start last from library vault repository threshold
  refs=${XDG_CONFIG_HOME:-$HOME/.config}/gandr/references
  config=${XDG_CONFIG_HOME:-$HOME/.config}/gandr/paper-watch.toml
  state=${XDG_STATE_HOME:-$HOME/.local/state}/gandr/paper-watch/state.json
  if [[ ! -f $refs || ! -f $config ]]; then
    echo "refs:watch: $refs names the library and the vault, and $config the repository, the threshold and the contact address; write both" >&2
    return 2
  fi
  library=$(awk '$1 == "library" { sub(/^library[[:space:]]+/, ""); print }' "$refs")
  vault=$(awk '$1 == "vault" { sub(/^vault[[:space:]]+/, ""); print }' "$refs")
  local settings
  settings=$(yq -p toml -o json '.' "$config")
  repository=$(jq -r '.repository // empty' <<< "$settings")
  threshold=$(jq -r '.threshold // empty' <<< "$settings")
  WATCH_MAILTO=$(jq -r '.mailto // empty' <<< "$settings")
  WATCH_KEY=$(jq -r '.api_key // empty' <<< "$settings")
  if [[ ! -f $library || ! -f $vault/ledger/ledger.sql || -z $repository || ! $threshold =~ ^[1-9][0-9]*$ || -z $WATCH_MAILTO ]]; then
    echo "refs:watch: the library ($library) and the vault's ledger ($vault/ledger/ledger.sql) must exist, and $config must hold \`repository\`, a whole \`threshold\` and \`mailto\`" >&2
    return 2
  fi

  today=$(date -u +%F)
  if [[ -f $state ]]; then
    start=$(jq -r .start "$state")
    last=$(jq -r .last "$state")
    from=$(date -u -d "$last -90 days" +%F)
    [[ $from < $start ]] && from=$start
  else
    start=$(date -u -d "$today -7 days" +%F)
    from=$start
  fi
  WATCH_SINCE=",from_publication_date:$from"

  WATCH_DIR=$(mktemp -d)
  local dir=$WATCH_DIR
  : > "$dir/notes"

  # The library, and the works the tree cites, from the tree's own scan.
  LC_ALL=C awk -f .config/references/library.awk "$library" > "$dir/library.tsv"
  references_load "$dir/references.db"
  sqlite3 -bail -tabs "$dir/references.db" \
    'CREATE TABLE library(key TEXT, doi TEXT, year TEXT, title TEXT);' ".import $dir/library.tsv library" \
    "CREATE VIEW cited AS SELECT DISTINCT key FROM cite WHERE kind IN ('cite', 'locator', 'corpus') AND key NOT GLOB 'vault:*';" \
    '.output '"$dir"'/cited-dois' \
    "SELECT lower(substr(key, 5)) FROM cited WHERE key GLOB 'doi:*'
     UNION SELECT '10.48550/arxiv.' || lower(substr(key, 7)) FROM cited WHERE key GLOB 'arXiv:*'
     UNION SELECT l.doi FROM cited c JOIN library l USING (key) WHERE l.doi <> '';" \
    '.output '"$dir"'/cited-titles' \
    "SELECT l.title, l.year FROM cited c JOIN library l USING (key) WHERE l.doi = '' AND l.title <> '' AND l.year <> '';" \
    '.output '"$dir"'/cited-unheld' \
    "SELECT key FROM cited WHERE key NOT GLOB 'doi:*' AND key NOT GLOB 'arXiv:*' AND key NOT IN (SELECT key FROM library);"
  [[ -s $dir/cited-unheld ]] && printf '%d cited keys are no library entry, so no work stands for them\n' "$(wc -l < "$dir/cited-unheld")" >> "$dir/notes"

  local since=$WATCH_SINCE
  WATCH_SINCE=
  {
    watch_batched doi "$WATCH_SELECT" < "$dir/cited-dois"
    while IFS=$'\t' read -r title year; do watch_titled "$title" "$year"; done < "$dir/cited-titles"
  } | jq -cs 'add // [] | unique_by(.id)' > "$dir/cited.json"
  awk -F'\t' '$2 != "" { print $2 }' "$dir/library.tsv" | watch_batched doi "$WATCH_SELECT" > "$dir/held.json"
  printf '%d of %d cited works and %d of %d library entries with a DOI resolve in OpenAlex\n' \
    "$(jq length "$dir/cited.json")" "$(( $(wc -l < "$dir/cited-dois") + $(wc -l < "$dir/cited-titles") ))" \
    "$(jq length "$dir/held.json")" "$(awk -F'\t' '$2 != ""' "$dir/library.tsv" | wc -l)" >> "$dir/notes"
  WATCH_SINCE=$since

  # The three queries; the follow-ups are read from the citing works.
  jq -r '.[].id | sub("^https://openalex.org/"; "")' "$dir/cited.json" \
    | watch_batched cites "$WATCH_SELECT,referenced_works" > "$dir/seed-cited.json"
  jq -r '[.[].authorships[]?.author.id | select(. != null) | sub("^https://openalex.org/"; "")] | unique[]' "$dir/held.json" \
    | watch_batched authorships.author.id "$WATCH_SELECT" > "$dir/seed-authors.json"
  jq -r --argjson threshold "$threshold" \
    '[.[].primary_location.source | select(. != null and (.type == "journal" or .type == "conference")) | .id | sub("^https://openalex.org/"; "")]
     | group_by(.) | map(select(length >= $threshold) | first)[]' "$dir/held.json" \
    | watch_batched primary_location.source.id "$WATCH_SELECT" > "$dir/seed-venues.json"

  # The dismissed list: the vault ledger's paper table.
  sqlite3 :memory: ".read $vault/ledger/ledger.sql" '.mode json' 'SELECT openalex, doi FROM paper;' > "$dir/dismissed.json"
  [[ -s $dir/dismissed.json ]] || echo '[]' > "$dir/dismissed.json"
  if [[ -f $state ]]; then jq '.reported' "$state" > "$dir/reported.json"; else echo '[]' > "$dir/reported.json"; fi
  yq -o json '.term' .config/references/terms.toml | jq -c 'map({name, match})' > "$dir/terms.json"

  jq -n -L .config/references 'include "watch";
    {
      cited_works: $cited[0],
      held: ($held[0] | map(.id | short)),
      held_authors: ([$held[0][].authorships[]?.author.id | select(. != null) | short] | unique),
      terms: $terms[0],
      seeds: {cited: $seed_cited[0], authors: $seed_authors[0], venues: $seed_venues[0]},
      reported: $reported[0],
      dismissed: $dismissed[0],
      cap: 200,
      per_author: 3
    } | delta' \
    --slurpfile cited "$dir/cited.json" --slurpfile held "$dir/held.json" --slurpfile terms "$dir/terms.json" \
    --slurpfile seed_cited "$dir/seed-cited.json" --slurpfile seed_authors "$dir/seed-authors.json" \
    --slurpfile seed_venues "$dir/seed-venues.json" --slurpfile reported "$dir/reported.json" \
    --slurpfile dismissed "$dir/dismissed.json" > "$dir/delta.json"
  jq -r -L .config/references --arg today "$today" --arg from "$from" --rawfile notes "$dir/notes" \
    'include "watch"; body($today; $from; $notes | split("\n") | map(select(. != "")))' "$dir/delta.json" > "$dir/body.md"

  local rows
  rows=$(jq '.reported | length' "$dir/delta.json")
  if [[ $dry == true ]]; then
    cat "$dir/body.md"
    echo "refs:watch: $rows new works from $from; a dry run files nothing and leaves the state" >&2
    return 0
  fi
  if (( rows > 0 )); then
    local number
    number=$(gh issue list --repo "$repository" --state open --search "\"$WATCH_TITLE\" in:title" --json number,title \
      --jq "map(select(.title == \"$WATCH_TITLE\"))[0].number // empty")
    if [[ -n $number ]]; then
      gh issue comment "$number" --repo "$repository" --body-file "$dir/body.md"
    else
      gh issue create --repo "$repository" --title "$WATCH_TITLE" --body-file "$dir/body.md"
    fi
  fi
  mkdir -p "$(dirname "$state")"
  jq -n --arg start "$start" --arg last "$today" --slurpfile reported "$dir/reported.json" --slurpfile delta "$dir/delta.json" \
    '{start: $start, last: $last, reported: (($reported[0] + $delta[0].reported) | unique)}' > "$state.new"
  mv "$state.new" "$state"
  echo "refs:watch: $rows new works from $from; the state records $(jq '.reported | length' "$state") reported"
}
