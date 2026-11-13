#!/usr/bin/env bash
# Prints the medians of the gates on this host (#7021, `report.jq`): the
# rows that each run of `check` and `gate:all` leaves in the host's state,
# `gate_rows` of `.config/mise/gate.bash`. It writes nothing.
#
# Usage: report.bash [<day>]
#   <day>  the first day of the window, `YYYY-MM-DD` in UTC; by default the
#          window is the last 7 days
# Exits 2 on a day of another form.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/../mise/gate.bash"
since=${1:-}
if [[ -n $since && ! $since =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}$ ]]; then
  echo "report:gates: \`$since\` is no day of the form YYYY-MM-DD" >&2
  exit 2
fi
if [[ ! -s $gate_rows ]]; then
  echo "report:gates: no gate has a row in $gate_rows" >&2
  exit 0
fi
jq -R -n -r --arg since "$since" --arg file "$gate_rows" -f "$here/report.jq" "$gate_rows"
