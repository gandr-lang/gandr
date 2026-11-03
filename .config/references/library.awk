# The research library's entries, as the paper watch reads them (#2544): run
# as `LC_ALL=C awk -f library.awk <library.bib>` over the BibLaTeX file the
# references configuration names, which writes one field a line. One
# tab-separated line per entry: key, DOI, year, title.
#
#   key    the entry's citation key
#   doi    its DOI in lower case, without a resolver; for an arXiv entry with
#          no DOI, arXiv's own, `10.48550/arxiv.` and the identifier without
#          its version; empty when it has neither
#   year   the first four digits of its `date` or `year`
#   title  its title, braces and tabs taken out
#
# An entry with no DOI is matched on its title and year, never on its key.

function value(line) {
  sub(/^[ \t]*[A-Za-z]+[ \t]*=[ \t]*/, "", line)
  sub(/,[ \t]*$/, "", line)
  gsub(/[{}"\t]/, "", line)
  return line
}

function flush() {
  if (key == "") return
  if (doi == "" && eprinttype == "arxiv" && eprint != "") {
    sub(/v[0-9]+$/, "", eprint)
    doi = "10.48550/arxiv." eprint
  }
  print key "\t" tolower(doi) "\t" substr(year, 1, 4) "\t" title
  key = doi = year = title = eprint = eprinttype = ""
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

END { flush() }
