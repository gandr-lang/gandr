# `rustc --print cfg`'s text, a JSON string, as a host's platform atoms
# (`cfg.jq`). `check:witnesses` reads this host's atoms so; `hosts.json`
# holds each gate host's, read so from `rustc --print cfg --target <triple>`.
include "cfg";
atoms
