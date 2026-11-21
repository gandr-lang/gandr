#!/usr/bin/env bash
# The cases of `check.bash` (#7539), run by `check:reserved-width`. Each case
# writes a nextest config and one test to a scratch tree. It states whether the
# check admits them, or refuses them by the name that the refusal holds.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
count=0
# run_case <case> <override filter, or empty for none> <the test's body> <ok or refused> <the name a refusal holds>
run_case() {
  local name=$1 filter=$2 body=$3 want=$4 holds=$5 tree output status=0
  count=$((count + 1))
  tree=$scratch/$count
  mkdir -p "$tree/crate/tests"
  if [[ -n $filter ]]; then
    printf '[[profile.default.overrides]]\nfilter = "%s"\nthreads-required = "num-test-threads"\n' "$filter" > "$tree/nextest.toml"
  else
    printf '[profile.default]\nstatus-level = "pass"\n' > "$tree/nextest.toml"
  fi
  printf '#[test]\nfn wide_sweep()\n{\n    %s\n}\n' "$body" > "$tree/crate/tests/sweeps.rs"
  output=$("$here/check.bash" "$tree/nextest.toml" "$tree" 2>&1) || status=$?
  if [[ $want == ok && $status -ne 0 ]]; then
    echo "reserved-width case FAILED: $name: refused, recorded admitted: $output" >&2
    failed=1
  elif [[ $want == refused && ($status -eq 0 || $output != *"$holds"*) ]]; then
    echo "reserved-width case FAILED: $name: recorded a refusal that names \`$holds\`, got: $output" >&2
    failed=1
  fi
}
run_case "the request and the reservation" "test(=sweeps::wide_sweep)" "each(Width::Reserved);" ok ""
run_case "a request alone" "" "each(Width::Reserved);" refused "wide_sweep"
run_case "a reservation alone" "test(=sweeps::wide_sweep)" "each(Width::PerformanceCores);" refused "wide_sweep"
run_case "a term the check cannot read" "package(crate)" "each(Width::PerformanceCores);" refused "package(crate)"
run_case "a comment asks for nothing" "" "// Width::Reserved" ok ""
(( failed == 0 )) || exit 1
echo "reserved-width cases OK: $count cases admitted or refused as recorded"
