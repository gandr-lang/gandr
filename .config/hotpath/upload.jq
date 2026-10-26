# How one hotpath upload ended (#2641), read by `ci:hotpath` after each
# profiled run: `{mode, act, sent}`, where `mode` is `HOTPATH_UPLOAD`, `act`
# whether the run is act's, and `sent` whether hotpath Cloud's response was
# written. The run's report is kept whatever the outcome.
#
# `sent` when the Cloud answered; `skipped` under act, which holds no OIDC
# token; otherwise the report went unsent. Where a failed upload fails the
# job (`fail-on-error`, a pull request's lane) that is `refused`; elsewhere
# (main's push) a report is a report, never a red `main`: `unsent`, a warning
# and a row on one `kind:ci` issue (`ci:hotpath-unsent`).

if .act then "skipped"
elif .sent then "sent"
elif .mode == "fail-on-error" then "refused"
else "unsent" end
