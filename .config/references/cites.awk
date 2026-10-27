# The citations the crates' documentation makes: run as
# `LC_ALL=C awk -f cites.awk <path>...` from the workspace root over crates'
# README files and module sources, paths as `crates/<crate>/README.md` and
# `crates/<crate>/src/<module>.rs`. One tab-separated line each: kind, key,
# crate, module, role, location.
#
#   cite     a key line of a module's `# References`:
#              - `<key>` — <role>: <what it decides at this site>
#            its role `exemplar`, `lineage` or `background`, its key the
#            library's citation key or `vault:` and a vault page's `mint:`
#            uuid
#   mirror   a key line of the README's `## References`, the same shape
#   locator  a DOI or arXiv locator anywhere in documentation outside a key
#            line, its key the locator normalized: `doi:` and the DOI in
#            lower case, or `arXiv:` and the identifier without its version;
#            its role `background`; a README's at the crate root
#   file     a module source read, its location its path
#   refused  a line refused, the reason in the key column
#
# A module is its source's path under `src/`: `lib.rs` and `main.rs` the root,
# written '', `a/b.rs` and `a/b/mod.rs` `a::b`. A source's documentation is
# its `//!` and `///` lines, a block ending where another kind of line starts;
# a README's is every line outside a code fence. A References section runs
# from its heading to the next one; an entry of it from its `- ` line through
# the indented lines under it. A `- ` line holding the key alone, whose first
# indented line opens with the dash, is one key line across the two: the key
# outruns the comment width, and `cargo fmt` wraps the dash onto the next
# line (#3171).

function site(path,    rest) {
  rest = path
  sub(/^crates\//, "", rest)
  crate = rest
  sub(/\/.*/, "", crate)
  rest = substr(rest, length(crate) + 2)
  readme = rest == "README.md"
  module = ""
  if (readme) return
  module = rest
  sub(/^src\//, "", module)
  sub(/\.rs$/, "", module)
  if (module == "lib" || module == "main") module = ""
  sub(/\/mod$/, "", module)
  gsub(/\//, "::", module)
}

function emit(kind, key, role) {
  printf "%s\t%s\t%s\t%s\t%s\t%s:%d\n", kind, key, crate, module, role, FILENAME, FNR
}

function count(text, character,    n, i) {
  n = 0
  for (i = 1; i <= length(text); i++) if (substr(text, i, 1) == character) n++
  return n
}

# A DOI as matched, less the punctuation that ends a sentence and a closing
# parenthesis it does not open.
function trim_doi(doi) {
  for (;;) {
    if (doi ~ /[.,:;]$/) doi = substr(doi, 1, length(doi) - 1)
    else if (doi ~ /\)$/ && count(doi, "(") < count(doi, ")")) doi = substr(doi, 1, length(doi) - 1)
    else return doi
  }
}

function locators(text,    rest, found, key, seen) {
  rest = text
  while (match(rest, /10\.[0-9][0-9][0-9][0-9][0-9]*\/[^][[:space:]<>`"{}|]+/)) {
    found = tolower(trim_doi(substr(rest, RSTART, RLENGTH)))
    rest = substr(rest, RSTART + RLENGTH)
    if (found ~ /^10\.48550\/arxiv\./) {
      sub(/^10\.48550\/arxiv\./, "", found)
      sub(/v[0-9]+$/, "", found)
      key = "arXiv:" found
    } else key = "doi:" found
    if (!(key in seen)) { seen[key] = 1; emit("locator", key, "background") }
  }
  rest = tolower(text)
  while (match(rest, /arxiv(\.org\/(abs|pdf)\/|:[[:space:]]*|[[:space:]]+)([0-9][0-9][0-9][0-9]\.[0-9][0-9][0-9][0-9][0-9]?|[a-z-]+(\.[a-z][a-z])?\/[0-9][0-9][0-9][0-9][0-9][0-9][0-9])/)) {
    found = substr(rest, RSTART, RLENGTH)
    rest = substr(rest, RSTART + RLENGTH)
    sub(/^arxiv(\.org\/(abs|pdf)\/|:[[:space:]]*|[[:space:]]+)/, "", found)
    key = "arXiv:" found
    if (!(key in seen)) { seen[key] = 1; emit("locator", key, "background") }
  }
}

# Why a key line's key is refused, or the empty string.
function refusal(key) {
  if (key ~ /^vault:/) {
    if (key ~ /^vault:[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]-[0-9a-f][0-9a-f][0-9a-f][0-9a-f]-7[0-9a-f][0-9a-f][0-9a-f]-[89ab][0-9a-f][0-9a-f][0-9a-f]-[0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]$/) return ""
    return "a vault key is `vault:` and the page's `mint:` uuid, in lower case"
  }
  if (tolower(key) ~ /^(doi:|arxiv:|isbn:|hal:|https?:|10\.)/) return "a key is the library's citation key or `vault:<uuid>`, never a locator: the locator belongs in the README's entry"
  if (key ~ /[[:space:]]/) return "a key holds no whitespace"
  return ""
}

# The key line of `key`, `said` the text after its dash.
function cited(key, said,    why) {
  entry = "key"
  why = refusal(key)
  if (why != "") emit("refused", why, "")
  else if (match(said, /^(exemplar|lineage|background): [^[:space:]]/)) emit(readme ? "mirror" : "cite", key, substr(said, 1, index(said, ":") - 1))
  else emit("refused", "a References line gives its key a role and what it decides: - `" key "`" dash "<exemplar|lineage|background>: <what it decides>", "")
}

BEGIN { dash = " — " }

FNR == 1 {
  site(FILENAME)
  block = ""
  refs = 0
  entry = ""
  fence = 0
  if (!readme) printf "file\t\t%s\t%s\t\t%s\n", crate, module, FILENAME
}

{
  text = ""
  kind = ""
  if (readme) {
    if ($0 ~ /^[[:space:]]*(```|~~~)/) fence = !fence
    else if (!fence) { text = $0; kind = "readme" }
  } else if (match($0, /^[[:space:]]*\/\/[!\/]/)) {
    mark = substr($0, RSTART + RLENGTH - 1, 1)
    rest = substr($0, RSTART + RLENGTH)
    if (mark == "!" || substr(rest, 1, 1) != "/") {
      text = rest
      sub(/^ /, "", text)
      kind = mark == "!" ? "inner" : "outer"
    }
  }
  if (kind != block) { block = kind; refs = 0; entry = "" }
  if (kind == "") next
  if (match(text, /^#+ /)) {
    level = RLENGTH - 1
    title = substr(text, RLENGTH + 1)
    sub(/[[:space:]]+$/, "", title)
    refs = title == "References" && level == (readme ? 2 : 1) && kind != "outer"
    entry = ""
  } else if (refs && text ~ /^[-*] /) {
    entry = "legacy"
    rest = substr(text, 3)
    tick = substr(rest, 1, 1) == "`" ? index(substr(rest, 2), "`") : 0
    if (tick > 1 && substr(rest, tick + 2, length(dash)) == dash) cited(substr(rest, 2, tick - 1), substr(rest, tick + 2 + length(dash)))
    else if (tick > 1 && substr(rest, tick + 2) ~ /^[[:space:]]*$/) { entry = "bare"; key = substr(rest, 2, tick - 1) }
  } else if (entry == "bare" && match(text, /^[[:space:]]+— /)) {
    cited(key, substr(text, RSTART + RLENGTH))
  } else if (entry != "" && text ~ /^[[:space:]]+[^[:space:]]/) {
    if (entry == "bare") entry = "legacy"
  } else entry = ""
  if (entry != "key") locators(text)
}
