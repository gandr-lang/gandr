#!/usr/bin/env bash
# `claim:take` and `claim:release` accept the same lanes (#6639), run by
# `check:claims`. A stubbed GitHub holds one open issue in a file: a read
# gives it, and the label and body writes change it. The engine lane, a row
# of `.config/issues/lanes.toml` since #6639, takes the issue and releases
# it. A lane the table does not hold is refused by both tasks, and nothing is
# written to the issue.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=../mise/disabled-tools.bash
source "$here/../mise/disabled-tools.bash"
disabled=$(disabled_tools github:cli/cli)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-take-release.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin"
cat > "$work/bin/gh" << 'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ $1 == api ]] || { echo "gh stub: unexpected $*" >&2; exit 1; }
shift
method=GET path= expr=. input=false
while (($#)); do
  case $1 in
    -X) method=$2; shift 2 ;;
    --jq) expr=$2; shift 2 ;;
    --input) input=true; shift 2 ;;
    -f) shift 2 ;;
    *) path=$1; shift ;;
  esac
done
issue=$STUB_ISSUE
case "$method $path" in
  "GET repos/case/case/issues/7") jq -r "$expr" "$issue" ;;
  "POST repos/case/case/issues/7/labels")
    jq '.labels |= (. + [{name: "status:claimed"}] | unique_by(.name))' "$issue" > "$issue.new" && mv "$issue.new" "$issue" ;;
  "DELETE repos/case/case/issues/7/labels/status:claimed")
    jq '.labels |= map(select(.name != "status:claimed"))' "$issue" > "$issue.new" && mv "$issue.new" "$issue" ;;
  "PATCH repos/case/case/issues/7")
    [[ $input == true ]] || { echo "gh stub: a PATCH with no body" >&2; exit 1; }
    jq --slurpfile edit /dev/stdin '.body = $edit[0].body' "$issue" > "$issue.new" && mv "$issue.new" "$issue" ;;
  *) echo "gh stub: unexpected $method $path" >&2; exit 1 ;;
esac
EOF
chmod +x "$work/bin/gh"
# The stub reads no token, so a host's wrapper of gh asks it for none (#6632).
export GH_TOKEN=case
failed=0
fail() {
  echo "take-release case FAILED: $1"
  echo "  got: $2"
  failed=1
}
issue=$work/issue.json
jq -n '{number: 7, state: "open", labels: [{name: "kind:defect"}], body: "A unit."}' > "$issue"
run() {
  STUB_ISSUE=$issue GH_REPO=case/case PATH="$work/bin:$PATH" MISE_DISABLE_TOOLS="$disabled" mise run --quiet "$@" 2>&1
}
labels() { jq -r '[.labels[].name] | join(" ")' "$issue"; }

# The engine lane takes the issue and releases it.
out=$(run claim:take 7 --lane engine) || fail "#6639: claim:take refuses the engine lane" "$out"
[[ $(labels) == "kind:defect status:claimed" && $(jq -r .body "$issue") == *"<!-- claim: lane=engine -->"* ]] \
  || fail "#6639: claim:take leaves no claim of the engine lane" "$(jq -c . "$issue")"
out=$(run claim:release engine 7) || fail "#6639: claim:release refuses the engine lane that claim:take accepts" "$out"
[[ $(labels) == "kind:defect" && $(jq -r .body "$issue") == *"<!-- released: lane=engine at="* ]] \
  || fail "#6639: claim:release leaves the claim of the engine lane" "$(jq -c . "$issue")"

# The drift lane's row lists no area, and it takes the issue and releases it.
out=$(run claim:take 7 --lane drift) || fail "#6639: claim:take refuses the drift lane, whose row is empty" "$out"
[[ $(labels) == "kind:defect status:claimed" && $(jq -r .body "$issue") == *"<!-- claim: lane=drift -->"* ]] \
  || fail "#6639: claim:take leaves no claim of the drift lane" "$(jq -c . "$issue")"
out=$(run claim:release drift 7) || fail "#6639: claim:release refuses the drift lane, whose row is empty" "$out"
[[ $(labels) == "kind:defect" && $(jq -r .body "$issue") == *"<!-- released: lane=drift at="* ]] \
  || fail "#6639: claim:release leaves the claim of the drift lane" "$(jq -c . "$issue")"

# A lane the table does not hold is refused by both tasks, before any write.
before=$(jq -c . "$issue")
status=0
out=$(run claim:take 7 --lane nowhere) || status=$?
[[ $status == 2 && $out == *"no lane \`nowhere\` in .config/issues/lanes.toml"* ]] \
  || fail "#6639: claim:take accepts a lane the table does not hold" "exit $status: $out"
status=0
out=$(run claim:release nowhere 7) || status=$?
[[ $status == 2 && $out == *"no lane \`nowhere\` in .config/issues/lanes.toml"* ]] \
  || fail "#6639: claim:release accepts a lane the table does not hold" "exit $status: $out"
[[ $(jq -c . "$issue") == "$before" ]] || fail "#6639: a refused lane wrote to the issue" "$(jq -c . "$issue")"

(( failed == 0 )) || exit 1
echo "take-release check OK: the engine lane and the drift lane, whose row is empty, take a claim and release it, and a lane the table does not hold is refused by both"
