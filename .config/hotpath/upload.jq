# How one hotpath upload ended (#2641), read by `ci:hotpath` after each
# profiled run: `{act, sent}`, where `act` is whether the run is act's, and
# `sent` whether hotpath Cloud's response was written. The run's report is
# kept whatever the outcome.
#
# `sent` when the Cloud answered; `skipped` under act, which holds no OIDC
# token; otherwise `unsent`: a report is a report, never a red run, so it is
# a warning and a row on one `kind:ci` issue (`ci:hotpath-unsent`).

if .act then "skipped"
elif .sent then "sent"
else "unsent" end
