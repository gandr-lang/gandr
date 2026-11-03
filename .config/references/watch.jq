# The paper watch's readings (#2544), included by `refs:watch` and by
# `check:references`'s cases as `jq -L .config/references 'include "watch"; …'`.
#
# A work is an OpenAlex work object as the watch selects it: `id`, `doi`,
# `display_name`, `publication_date`, `authorships`, `primary_location`,
# `primary_topic`, `locations` and, for the cited works' seed,
# `referenced_works`.
#
# `delta` reads one object:
#   cited_works  the works the tree cites, resolved
#   held         the OpenAlex ids of the library's works, resolved
#   held_authors the OpenAlex ids of the library's authors
#   library      the library's entries as `library.awk` prints them: `key`,
#                `doi`, `arxiv`, `hal`, `title` and `family`
#   terms        the term map's rows, `name` and `match`
#   seeds        `cited`, `authors` and `venues`: the works each query returned
#   reported     the OpenAlex ids the state records as reported
#   dismissed    the vault ledger's `paper` rows, `openalex` and `doi`
#   cap          the works the held authors' seed keeps before it caps
#   per_author   the works per held author a capped seed keeps
# and returns the new works by seed, each a row, newest first: `followups`,
# `cited`, `authors` and `venues`, a work in the first seed that holds it;
# `versions`, the works a library entry holds in another version; `capped`,
# the held authors' seed's count before and after its cap, or null; and
# `reported`, every reported row's id.
#
# A work is new when no state, ledger row, library entry or citation holds
# it. A library entry holds a work in any version (#4709): a DOI, an arXiv or
# a HAL identifier any of the work's locations shares with it, or its
# normalised title and first author's family name. OpenAlex merges most
# versions into one work, which the held ids already cover; a version it keeps
# apart is reported once among `versions`, naming the entry, and never as a new
# work. A follow-up cites a cited work, shares an author with it and has its
# primary topic. A venue's work is kept only when its title matches a term.
# A row links its arXiv version, else its HAL one, else its DOI, so a fetch
# reads the preprint, which usually carries the later updates, first.

def short: if . == null then null else sub("^https://openalex.org/"; "") end;

def bare: if . == null then null else sub("^https://doi.org/"; "") | ascii_downcase end;

def set: map({key: ., value: true}) | from_entries;

# Latin-1 and Latin Extended-A letters, U+00C0 to U+017F, each as the ASCII
# letter it decorates, a space for a sign.
def folded: "AAAAAAACEEEEIIIIDNOOOOO OUUUUYTsaaaaaaaceeeeiiiidnooooo ouuuuytyAaAaAaCcCcCcCcDdDdEeEeEeEeEeGgGgGgGgHhHhIiIiIiIiIiIiJjKkkLlLlLlLlLlNnNnNnnNnOoOoOoOoRrRrRrSsSsSsSsTtTtTtUuUuUuUuUuUuWwYyYZzZzZzs" | explode;

# A string as the watch compares titles and names: its accents folded, then
# its letters and digits alone, in lower case, as `watch_titled` matches.
def normal:
  folded as $folded
  | explode | map(if . >= 192 and . < 384 then $folded[. - 192] else . end) | implode
  | ascii_downcase | gsub("[^a-z0-9]"; "");

# The identifier a location's URL, or a work's DOI, names: `arxiv:<id>`, the
# version taken off, `hal:<id>`, or `doi:<doi>`, all in lower case; nothing
# for any other URL.
def identifier:
  ascii_downcase
  | if test("arxiv\\.org/(abs|pdf)/") then "arxiv:" + (capture("arxiv\\.org/(abs|pdf)/(?<id>[^?#]+)").id | sub("\\.pdf$"; "") | sub("v[0-9]+$"; ""))
    elif test("doi\\.org/10\\.48550/arxiv\\.") then "arxiv:" + (capture("arxiv\\.(?<id>.+)$").id | sub("v[0-9]+$"; ""))
    elif test("doi\\.org/") then "doi:" + sub("^.*doi\\.org/"; "")
    elif test("(hal\\.science|hal\\.archives-ouvertes\\.fr)/") then (capture("/(?<id>[a-z]+-[0-9]{8})") // empty | "hal:" + .id)
    else empty
    end;

# Every identifier a work's DOI and locations name.
def identifiers: [.doi, (.locations[]? | .landing_page_url, .pdf_url) | select(. != null) | identifier] | unique;

# A library entry's identifiers, as `identifier` spells them.
def entry_identifiers:
  (if .doi == "" then empty elif .doi | startswith("10.48550/arxiv.") then "arxiv:" + .doi[15:] else "doi:" + .doi end),
  (if .arxiv == "" then empty else "arxiv:" + (.arxiv | ascii_downcase) end),
  (if .hal == "" then empty else "hal:" + (.hal | ascii_downcase | sub("v[0-9]+$"; "")) end);

# A title and a first author's family name as one key, or null when either
# is empty once normalised.
def titled($title; $family):
  ($title | normal) as $t | ($family | normal) as $f
  | if $t == "" or $f == "" then null else "\($t)/\($f)" end;

def work_titled: titled(.display_name // ""; (.authorships[0].author.display_name // "") | split(" ") | last // "");

# Where a fetch reads a work: its arXiv version, else its HAL one, else its
# DOI, else its OpenAlex page.
def link:
  identifiers as $ids
  | (first($ids[] | select(startswith("arxiv:"))) // first($ids[] | select(startswith("hal:"))) // null) as $preprint
  | if $preprint != null and ($preprint | startswith("arxiv:")) then "https://arxiv.org/abs/" + $preprint[6:]
    elif $preprint != null then "https://hal.science/" + $preprint[4:]
    elif .doi != null then "https://doi.org/" + (.doi | bare)
    else .id
    end;

def row($because):
  {
    id: (.id | short),
    title: (.display_name // ""),
    date: (.publication_date // ""),
    venue: (.primary_location.source.display_name // ""),
    doi: (.doi | bare),
    link: link,
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
  | ([$in.library[] | .key as $key | entry_identifiers | {key: ., value: $key}] | from_entries) as $by_identifier
  | ([$in.library[] | .key as $key | titled(.title; .family) | select(. != null) | {key: ., value: $key}] | from_entries) as $by_title
  | def version: first(identifiers[] | $by_identifier[.] // empty) // (work_titled as $t | if $t == null then null else $by_title[$t] end);
    def unseen: (.id | short) as $id | (.doi | bare) as $doi
      | ($known[$id] | not) and ($gone[$id] | not) and ($doi == null or ($gone_doi[$doi] | not));
    def fresh: unseen and version == null;
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
  | [[$in.seeds.cited, $in.seeds.authors, $in.seeds.venues] | add | unique_by(.id)[]
      | select(unseen)
      | version as $entry
      | select($entry != null)
      | row("a version of `\($entry)`")] as $versions
  | {
      followups: ($followups | newest),
      cited: ($cites | newest),
      authors: ($kept | map(del(.held)) | newest),
      venues: ($venues | newest),
      versions: ($versions | newest),
      capped: (if ($by | length) > $in.cap then {before: ($by | length), after: ($kept | length)} else null end),
      reported: ([$followups, $cites, $kept, $venues, $versions] | add | map(.id) | sort)
    };

def cell: tostring | gsub("\\|"; "\\|") | gsub("\n"; " ");

def table($heading; $rows):
  if ($rows | length) == 0 then empty
  else
    "### \($heading) (\($rows | length))\n\n| Work | Published | Venue | Authors | Why |\n| --- | --- | --- | --- | --- |\n"
    + ($rows | map(
        "| [\(.title | cell)](\(.link)) · `\(.id)`\(if .doi then " · `doi:\(.doi)`" else "" end) | \(.date) | \(.venue | cell) | \(.authors | cell) | \(.because | cell) |"
      ) | join("\n"))
    + "\n"
  end;

# The review comment for a delta: `$today`, the run's day; `$from`, the
# earliest publication day its queries read; `$notes`, lines the run states
# beside the works, such as a query truncated or a library entry unresolved.
def body($today; $from; $notes):
  "## Paper watch, \($today)\n\n"
  + "New works published from \($from), by seed. Each links its arXiv or HAL version when one exists. Settle a work by its OpenAlex id in the vault ledger's `paper` table, and the watch never reports it again.\n\n"
  + ([table("Follow-ups of cited works"; .followups),
      table("Works citing what the tree cites"; .cited),
      table("Works by the library's authors"; .authors),
      table("Works in the library's venues"; .venues),
      table("New versions of held works"; .versions)] | join("\n"))
  + (if .capped then "\nThe held authors' seed returned \(.capped.before) works and keeps each author's newest, \(.capped.after) in all.\n" else "" end)
  + (if ($notes | length) > 0 then "\n" + ($notes | map("- " + .) | join("\n")) + "\n" else "" end);
