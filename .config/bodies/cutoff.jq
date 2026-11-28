# The year that the citation window opens, from the text of its policy file.
# So the issues workflow needs no TOML reader on its runner. `findings` takes
# the year as the named argument `cutoff`. `references window` holds the
# line to its own reading of the file.
#
# - see: `.config/references/window.toml`
# - see: #4708
capture("(?m)^cutoff\\s*=\\s*(?<year>[0-9]+)\\s*$").year | tonumber
