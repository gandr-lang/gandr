# The year the citation window opens (#4708), read from the text of
# `.config/references/window.toml`, so the issues workflow needs no TOML
# reader on its runner. `findings` takes it as the named argument `cutoff`;
# `references_window` holds it to yq's reading of the same file.
capture("(?m)^cutoff\\s*=\\s*(?<year>[0-9]+)\\s*$").year | tonumber
