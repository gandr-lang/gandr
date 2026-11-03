# The paper watch's readings (#2544), included by `refs:watch` and by
# `check:references`'s cases as `jq -L .config/references 'include "watch"; …'`.
#
# A work is an OpenAlex work object as the watch selects it: `id`, `doi`,
# `display_name`, `publication_date`, `authorships`, `primary_location`,
# `primary_topic` and, for the cited works' seed, `referenced_works`.
#
# `delta` reads one object:
#   cited_works  the works the tree cites, resolved
#   held         the OpenAlex ids of the library's works, resolved
#   held_authors the OpenAlex ids of the library's authors
#   terms        the term map's rows, `name` and `match`
#   seeds        `cited`, `authors` and `venues`: the works each query returned
#   reported     the OpenAlex ids the state records as reported
#   dismissed    the vault ledger's `paper` rows, `openalex` and `doi`
#   cap          the works the held authors' seed keeps before it caps
#   per_author   the works per held author a capped seed keeps
# and returns the new works by seed, each a row, newest first: `followups`,
# `cited`, `authors` and `venues`, a work in the first seed that holds it;
# `capped`, the held authors' seed's count before and after its cap, or
# null; and `reported`, every reported row's id.
#
# A work is new when no state, ledger row, library entry or citation holds
# it. A follow-up cites a cited work, shares an author with it and has its
# primary topic. A venue's work is kept only when its title matches a term.

def short: if . == null then null else sub("^https://openalex.org/"; "") end;

def bare: if . == null then null else sub("^https://doi.org/"; "") | ascii_downcase end;

def set: map({key: ., value: true}) | from_entries;

def row($because):
  {
    id: (.id | short),
    title: (.display_name // ""),
    date: (.publication_date // ""),
    venue: (.primary_location.source.display_name // ""),
    doi: (.doi | bare),
    authors: ([.authorships[]?.author.display_name] | if length > 3 then .[0:3] + ["et al."] else . end | join(", ")),
    because: $because
  };

def newest: sort_by(.date, .id) | reverse;

def delta:
  . as $in
  | (($in.reported + $in.held + ($in.cited_works | map(.id | short))) | set) as $known
  | ($in.dismissed | map(.openalex) | set) as $gone
  | ($in.dismissed | map(.doi | select(. != null)) | set) as $gone_doi
  | ($in.cited_works | map({key: (.id | short), value: .}) | from_entries) as $cited
  | ($in.held_authors | set) as $held_authors
  | def fresh: (.id | short) as $id | (.doi | bare) as $doi
      | ($known[$id] | not) and ($gone[$id] | not) and ($doi == null or ($gone_doi[$doi] | not));
    def authors_of: [.authorships[]?.author.id];
  ($in.seeds.cited | unique_by(.id) | map(select(fresh))) as $citing
  | [$citing[]
      | . as $work
      | [.referenced_works[]? | short | select($cited[.] != null) | $cited[.]] as $cites
      | ($cites | map(select(
          (.primary_topic.id // null) as $topic
          | $topic != null and $topic == ($work.primary_topic.id // null)
            and ((authors_of - ($work | authors_of)) | length) < (authors_of | length)
        ))) as $follows
      | select($follows | length > 0)
      | row("follows " + ($follows | map(.display_name) | first))] as $followups
  | ($followups | map(.id) | set) as $taken
  | [$citing[]
      | select($taken[.id | short] | not)
      | . as $work
      | row("cites " + ([.referenced_works[]? | short | select($cited[.] != null) | $cited[.].display_name] | .[0:3] | join("; ")))] as $cites
  | ($taken + ($cites | map(.id) | set)) as $taken
  | [$in.seeds.authors | unique_by(.id)[]
      | select(fresh and ($taken[.id | short] | not))
      | [.authorships[]? | select(.author.id != null and $held_authors[.author.id | short] != null)] as $held
      | select($held | length > 0)
      | row("by " + ($held | map(.author.display_name) | join(", ")))
      + {held: ($held | map(.author.id | short) | first)}] as $by
  | (if ($by | length) > $in.cap
     then ($by | group_by(.held) | map(newest | .[0:$in.per_author]) | add) else $by end) as $kept
  | ($taken + ($kept | map(.id) | set)) as $taken
  | [$in.seeds.venues | unique_by(.id)[]
      | select(fresh and ($taken[.id | short] | not))
      | (.display_name // "") as $title
      | [$in.terms[] | select(. as $term | $title | test($term.match; "i"))] as $matched
      | select($matched | length > 0)
      | row((.primary_location.source.display_name // "a venue") + ", on " + ($matched | map(.name) | join(", ")))] as $venues
  | {
      followups: ($followups | newest),
      cited: ($cites | newest),
      authors: ($kept | map(del(.held)) | newest),
      venues: ($venues | newest),
      capped: (if ($by | length) > $in.cap then {before: ($by | length), after: ($kept | length)} else null end),
      reported: ([$followups, $cites, $kept, $venues] | add | map(.id) | sort)
    };

def cell: tostring | gsub("\\|"; "\\|") | gsub("\n"; " ");

def table($heading; $rows):
  if ($rows | length) == 0 then empty
  else
    "### \($heading) (\($rows | length))\n\n| Work | Published | Venue | Authors | Why |\n| --- | --- | --- | --- | --- |\n"
    + ($rows | map(
        "| [\(.title | cell)](https://openalex.org/\(.id))\(if .doi then " · `doi:\(.doi)`" else "" end) | \(.date) | \(.venue | cell) | \(.authors | cell) | \(.because | cell) |"
      ) | join("\n"))
    + "\n"
  end;

# The review comment for a delta: `$today`, the run's day; `$from`, the
# earliest publication day its queries read; `$notes`, lines the run states
# beside the works, such as a query truncated or a library entry unresolved.
def body($today; $from; $notes):
  "## Paper watch, \($today)\n\n"
  + "New works published from \($from), by seed. Settle a work by its OpenAlex id in the vault ledger's `paper` table, and the watch never reports it again.\n\n"
  + ([table("Follow-ups of cited works"; .followups),
      table("Works citing what the tree cites"; .cited),
      table("Works by the library's authors"; .authors),
      table("Works in the library's venues"; .venues)] | join("\n"))
  + (if .capped then "\nThe held authors' seed returned \(.capped.before) works and keeps each author's newest, \(.capped.after) in all.\n" else "" end)
  + (if ($notes | length) > 0 then "\n" + ($notes | map("- " + .) | join("\n")) + "\n" else "" end);
