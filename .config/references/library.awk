# The research library's entries, as the paper watch reads them (#2544): run
# as `LC_ALL=C awk -f library.awk <library.bib>` over the BibLaTeX file the
# references configuration names, which writes one field a line. One
# tab-separated line per entry: key, DOI, year, title, arXiv, HAL, family.
#
#   key    the entry's citation key
#   doi    its DOI in lower case, without a resolver; for an arXiv entry with
#          no DOI, arXiv's own, `10.48550/arxiv.` and the identifier without
#          its version; empty when it has neither
#   year   the first four digits of its `date` or `year`
#   title  its title, braces and tabs taken out
#   arxiv  its arXiv identifier without its version (`eprint` under
#          `eprinttype = arxiv`), or empty (#4709)
#   hal    its HAL identifier, from `eprint` under `eprinttype = hal` or a
#          `url` at `hal.science` or `hal.archives-ouvertes.fr`, or empty
#   family its first author's family name: the part before the comma of
#          `Family, Given`, else the last word of `Given Family`; empty with no
#          `author`
#
# An entry with no DOI is matched on its title and year, never on its key.
# The watch matches every entry on its identifiers, and on its title and
# first author, so a version the library holds is never a new work.

function value(line) {
  sub(/^[ \t]*[A-Za-z]+[ \t]*=[ \t]*/, "", line)
  sub(/,[ \t]*$/, "", line)
  gsub(/[{}"\t]/, "", line)
  return line
}

function family_of(names, first) {
  first = names
  sub(/[ \t]+and[ \t].*$/, "", first)
  if (first ~ /,/) sub(/,.*$/, "", first)
  else sub(/^.*[ \t]/, "", first)
  gsub(/^[ \t]+|[ \t]+$/, "", first)
  return first
}

function flush() {
  if (key == "") return
  if (eprinttype == "arxiv" && eprint != "") {
    sub(/v[0-9]+$/, "", eprint)
    arxiv = eprint
    if (doi == "") doi = "10.48550/arxiv." eprint
  }
  if (eprinttype == "hal" && eprint != "") hal = eprint
  else if (tolower(url) ~ /(hal\.science|hal\.archives-ouvertes\.fr)\// && match(url, /\/[a-z]+-[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]/)) hal = substr(url, RSTART + 1, RLENGTH - 1)
  print key "\t" tolower(doi) "\t" substr(year, 1, 4) "\t" title "\t" arxiv "\t" hal "\t" family_of(author)
  key = doi = year = title = eprint = eprinttype = arxiv = hal = author = url = ""
}

/^@[A-Za-z]+\{/ {
  flush()
  key = $0
  sub(/^@[A-Za-z]+\{/, "", key)
  sub(/,.*$/, "", key)
  next
}

key != "" && /^[ \t]*doi[ \t]*=/ { doi = value($0); next }
key != "" && /^[ \t]*title[ \t]*=/ { title = value($0); next }
key != "" && /^[ \t]*(date|year)[ \t]*=/ { if (year == "") year = value($0); next }
key != "" && /^[ \t]*eprint[ \t]*=/ { eprint = value($0); next }
key != "" && /^[ \t]*eprinttype[ \t]*=/ { eprinttype = tolower(value($0)); next }
key != "" && /^[ \t]*author[ \t]*=/ { author = value($0); next }
key != "" && /^[ \t]*url[ \t]*=/ { url = value($0); next }

END { flush() }
