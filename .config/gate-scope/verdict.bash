#!/usr/bin/env bash
# The verdict of a check on a tree. A pass of a check is a record, a commit
# with no parent. Its tree is the tree of the check's pass, and its
# message holds the key of the pass. The writer signs the commit with the key
# that signs its commits. The record's ref is
# `refs/verdicts/<tree>/<check>/<hash>`, where <hash> is the first 16 digits
# of the SHA-256 of the key.
# - see: #7684
#
# A lane's gate writes the record, `pr:open` pushes it, and the jobs of the
# pull request and of the merge group read it. A job that reads a record for
# each of its checks runs none of them.
#
# A write retries one failed signing call. The tree, check and key stay fixed,
# so the retry writes the same record. A second failure leaves no record and
# names the command that writes it without another gate run.
#
# The key binds each input that the verdict reads (`verdicts.json` names the
# checks and the profile of each):
#   - `tree` and `check`: the tree and the task;
#   - `target` and `compiler`: the host triple and the commit of `rustc -vV`;
#   - `profile`: the profile that the check builds;
#   - `policy`: the policy's revision (`mise run workflow:revision`);
#   - `base` and `scope`: `GATE_BASE`, and `GATE_SCOPE`, which the check
#     reads its packages and its features from;
#   - `flags`: each variable of the environment that Cargo reads for the
#     flags, the target and the profile of the build;
#   - `target_features`: each value of `target_feature` that a source of the
#     tree reads, on or off under the flags of the host. A host flag such as
#     `-Ctarget-cpu=native` changes no verdict of a tree that reads none.
# The key omits the image's digest, because a lane's gate runs on a host with
# no image. The image's part in a verdict is its compiler and its policy
# driver, and the key binds both.
#
# Usage:
#   verdict.bash key <check>
#     Prints the key of <check> for the tree at HEAD, as one line of JSON.
#   verdict.bash write <tree> <check>...
#     Writes a record for each <check>, and each check that one of them
#     depends on, that `verdicts.json` names, when HEAD's tree is <tree>.
#     Else it writes nothing and says why: a record of work that is not a
#     commit is of no use to a runner.
#   verdict.bash publish <commit>
#     Pushes each record of the tree of <commit> to the remote
#     `GATE_VERDICT_REMOTE`, `origin` by default.
#   verdict.bash read <check>...
#     Exits 0 when the remote holds a record of each <check> for HEAD's tree
#     that this run's key matches and an allowed signer signed. Else it names
#     each check that it holds no record of, and exits 1. Each run takes the
#     base of each record, when the base is a commit of the trunk, and reads
#     the scope against it as the merge group does (`scope.bash --lints`).
#     So a record of a base below the group's base serves the group: each
#     package outside the record's scope is the base's, and the base passed.
#     The policy holds each function that the change alters against the
#     older base, which holds no fewer functions.
#
# `GATE_VERDICT_SIGNERS` names a file of allowed signers in the form of
# `ssh-keygen -Y verify`. Without it the reader asks GitHub for the signing
# keys of each login in `verdicts.json`'s `signers`. `GATE_VERDICT_RUSTC`
# names the compiler to read, `rustc` by default. `GATE_VERDICT_POLICY` gives
# the policy's revision, and `GATE_VERDICT_TRUNK_OK` gives the trunk's verdict
# on a base, for the cases (`verdict-cases.bash`).
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# The reads of the signers' keys and of the trunk go through the budget.
source "$here/../gh/budget.bash"
table=$here/verdicts.json
remote=${GATE_VERDICT_REMOTE:-origin}

# The first 16 digits of the SHA-256 of a key.
key_hash() { printf '%s' "$1" | sha256sum | cut -c1-16; }

# The name of a check as one segment of a ref: a ref holds no colon.
ref_name() { printf '%s' "${1//:/-}"; }

# Git against the remote. A job's checkout keeps no credential
# (`persist-credentials: false`), so a job gives its token in `GH_TOKEN`, and
# only these calls send it.
remote_git() {
  if [[ -n ${GITHUB_ACTIONS:-} && -n ${GH_TOKEN:-} ]]; then
    git -c "http.https://github.com/.extraheader=AUTHORIZATION: basic $(printf 'x-access-token:%s' "$GH_TOKEN" | base64 -w0)" "$@"
  else
    git "$@"
  fi
}

# The flags of the host for the target, in the order that Cargo reads them:
# the encoded variable, `RUSTFLAGS`, the target's table, then `build`.
host_flags() {
  local target=$1 upper
  if [[ -n ${CARGO_ENCODED_RUSTFLAGS+set} ]]; then
    tr '\037' '\n' <<< "$CARGO_ENCODED_RUSTFLAGS"
  elif [[ -n ${RUSTFLAGS+set} ]]; then
    tr -s ' ' '\n' <<< "$RUSTFLAGS"
  else
    upper=$(tr 'a-z.-' 'A-Z__' <<< "$target")
    local var=CARGO_TARGET_${upper}_RUSTFLAGS
    if [[ -n ${!var:-} ]]; then
      tr -s ' ' '\n' <<< "${!var}"
    else
      cargo -Zunstable-options config get --format json-value "target.$target.rustflags" 2> /dev/null | jq -r '.[]?' \
        || cargo -Zunstable-options config get --format json-value build.rustflags 2> /dev/null | jq -r '.[]?' || true
    fi
  fi
}

# The part of the key that each check of one run shares: the tree, the
# compiler, the policy, the flags and the target features. A run reads it
# once.
common() {
  local tree version target compiler policy read_features on
  tree=$(git rev-parse 'HEAD^{tree}')
  version=$("${GATE_VERDICT_RUSTC:-rustc}" -vV)
  target=$(awk '/^host:/ { print $2 }' <<< "$version")
  compiler=$(awk '/^commit-hash:/ { print $2 }' <<< "$version")
  policy=${GATE_VERDICT_POLICY:-$(mise run --quiet workflow:revision)}
  read_features=$(git grep -h -o -E 'target_feature *= *"[^"]+"' HEAD -- 'crates/*.rs' 2> /dev/null \
    | sed -E 's/.*"([^"]+)"/\1/' | LC_ALL=C sort -u || true)
  on=
  if [[ -n $read_features ]]; then
    local -a host
    mapfile -t host < <(host_flags "$target")
    on=$("${GATE_VERDICT_RUSTC:-rustc}" --print cfg --target "$target" "${host[@]}" | sed -n -E 's/^target_feature="([^"]+)"$/\1/p')
  fi
  env | LC_ALL=C sort | jq -R -s -c --arg tree "$tree" --arg target "$target" --arg compiler "$compiler" --arg policy "$policy" \
    --arg read "$read_features" --arg on "$on" '
    {tree: $tree, target: $target, compiler: $compiler, policy: $policy,
     flags: ([split("\n")[] | select(test("^(RUSTFLAGS|RUSTDOCFLAGS|CARGO_ENCODED_RUSTFLAGS|CARGO_ENCODED_RUSTDOCFLAGS|CARGO_BUILD_RUSTFLAGS|CARGO_BUILD_RUSTDOCFLAGS|CARGO_BUILD_TARGET|CARGO_PROFILE_[A-Z0-9_]+|CARGO_TARGET_[A-Z0-9_]+_RUSTFLAGS)="))
       | capture("^(?<k>[^=]+)=(?<v>.*)$") | {(.k): .v}] | add // {}),
     target_features: (($on | split("\n")) as $on | [$read | split("\n")[] | select(length > 0) | {(.): IN($on[])}] | add // {})}'
}

# The key of <check>: the run's common part, the check, its profile, the base
# `GATE_BASE` and the scope `GATE_SCOPE`.
key() {
  jq -c -S --arg check "$1" --arg base "${GATE_BASE:-}" --arg scope "${GATE_SCOPE:---workspace}" --slurpfile table "$table" '
    ($table[0].checks[$check].profile // error("verdict: \($check) holds no row in verdicts.json")) as $profile
    | . + {check: $check, profile: $profile, base: $base, scope: $scope}' <<< "${common_key:-$(common)}"
}

# The allowed signers, from `GATE_VERDICT_SIGNERS` or from GitHub.
signers() {
  if [[ -n ${GATE_VERDICT_SIGNERS:-} ]]; then
    cp "$GATE_VERDICT_SIGNERS" "$1"
    return
  fi
  : > "$1"
  local login
  for login in $(jq -r '.signers[]' "$table"); do
    gh api "users/$login/ssh_signing_keys" --jq '.[].key' \
      | awk -v who="$login@users.noreply.github.com" '{ print who " namespaces=\"git\" " $0 }' >> "$1"
  done
  [[ -s $1 ]] || { echo "verdict: GitHub gave no signing key for the signers of $table" >&2; return 2; }
}

# Whether the trunk holds <base>: a record's base is a commit that passed.
on_trunk() {
  if [[ -n ${GATE_VERDICT_TRUNK_OK+set} ]]; then
    [[ " $GATE_VERDICT_TRUNK_OK " == *" $1 "* ]]
    return
  fi
  local trunk status
  source "$here/../pr-stack/trunk.bash"
  status=$(gh api "repos/{owner}/{repo}/compare/$1...$trunk" --jq .status 2> /dev/null) || return 1
  [[ $status == ahead || $status == identical ]]
}

# Verifies the record <commit> against <key>. Prints nothing. The status tells.
verify() {
  local commit=$1 key=$2 allowed=$3 parents body
  [[ $(git cat-file -t "$commit") == commit ]] || return 1
  parents=$(git rev-list --parents -n 1 "$commit")
  [[ $parents == "$commit" ]] || return 1
  [[ $(git rev-parse "$commit^{tree}") == "$(jq -r .tree <<< "$key")" ]] || return 1
  body=$(git log -1 --format=%b "$commit" | jq -c -S . 2> /dev/null) || return 1
  [[ $body == "$key" ]] || return 1
  git -c gpg.ssh.allowedSignersFile="$allowed" verify-commit "$commit" > /dev/null 2>&1
}

case ${1:-} in
  key)
    (( $# == 2 )) || { echo 'usage: verdict.bash key <check>' >&2; exit 2; }
    key "$2"
    ;;
  write)
    (( $# >= 3 )) || { echo 'usage: verdict.bash write <tree> <check>...' >&2; exit 2; }
    tree=$2
    shift 2
    if [[ $(git rev-parse 'HEAD^{tree}') != "$tree" ]]; then
      echo "verdict: the work is not the tree of HEAD, so no record is written; commit the work and gate again for a record" >&2
      exit 0
    fi
    common_key=$(common)
    # A check that the gate runs by its name runs each of its `depends` too:
    # `check:landing` runs Clippy and the policy. Without the task list, the
    # gate takes the names as the caller gives them.
    mapfile -t ran < <(mise tasks ls --json 2> /dev/null | jq -r --args '
      (map({key: .name, value: [(.depends // [])[] | if type == "array" then .[0] else . end | split(" ")[0]]}) | from_entries) as $deps
      | def ran: ., (($deps[.] // [])[] | ran); [$ARGS.positional[] | ran] | unique[]' "$@" || printf '%s\n' "$@")
    failed=0
    for check in "${ran[@]}"; do
      jq -e --arg check "$check" '.checks | has($check)' "$table" > /dev/null || continue
      k=$(key "$check")
      signed=false
      for attempt in 1 2; do
        if commit=$(git commit-tree -S -m "verdict: $check passes on ${tree:0:12}" -m "$k" "$tree"); then
          signed=true
          break
        fi
        echo "verdict: $check passed; signing attempt $attempt of 2 failed" >&2
      done
      if [[ $signed != true ]]; then
        echo "verdict: $check passed, but its record did not sign after 2 attempts; write it without running the check: $here/verdict.bash write $tree $check" >&2
        failed=1
        continue
      fi
      git update-ref "refs/verdicts/$tree/$(ref_name "$check")/$(key_hash "$k")" "$commit"
      echo "verdict: $check passes on ${tree:0:12}; the record is ${commit:0:12}" >&2
    done
    (( failed == 0 )) || exit 1
    ;;
  publish)
    (( $# == 2 )) || { echo 'usage: verdict.bash publish <commit>' >&2; exit 2; }
    tree=$(git rev-parse "$2^{tree}")
    if [[ -z $(git for-each-ref --count=1 "refs/verdicts/$tree/") ]]; then
      echo "verdict: no record of the tree ${tree:0:12}, so none is pushed" >&2
      exit 0
    fi
    git push --quiet --no-verify "$remote" "refs/verdicts/$tree/*:refs/verdicts/$tree/*"
    echo "verdict: pushed the records of the tree ${tree:0:12}: $(git for-each-ref --format='%(refname)' "refs/verdicts/$tree/" | awk -F/ '{ print $4 }' | sort -u | paste -sd ' ')" >&2
    ;;
  read)
    (( $# >= 2 )) || { echo 'usage: verdict.bash read <check>...' >&2; exit 2; }
    shift
    tree=$(git rev-parse 'HEAD^{tree}')
    # The common part of the key holds for each check of this run, so the run
    # reads it once.
    common_key=$(common)
    allowed=$(mktemp)
    trap 'rm -f "$allowed"' EXIT
    signers "$allowed"
    missing=()
    for check in "$@"; do
      held=
      while read -r _ ref; do
        [[ -n $ref ]] || continue
        remote_git fetch --quiet --no-tags "$remote" "+$ref:$ref" 2> /dev/null || continue
        commit=$(git rev-parse "$ref")
        base=$(git log -1 --format=%b "$commit" | jq -r '.base // empty' 2> /dev/null) || continue
        if [[ -z $base ]] || ! on_trunk "$base"; then continue; fi
        scope=${GATE_VERDICT_SCOPE:-$(GATE_BASE=$base "$here/scope.bash" --lints 2> /dev/null)} || continue
        k=$(GATE_BASE=$base GATE_SCOPE=$scope key "$check")
        [[ ${ref##*/} == "$(key_hash "$k")" ]] || continue
        if verify "$commit" "$k" "$allowed"; then held=$commit; break; fi
      done < <(remote_git ls-remote "$remote" "refs/verdicts/$tree/$(ref_name "$check")/*")
      if [[ -n $held ]]; then
        echo "verdict: $check passed on ${tree:0:12}; the record ${held:0:12} holds, so the check does not run again" >&2
      else
        missing+=("$check")
      fi
    done
    if (( ${#missing[@]} )); then
      echo "verdict: no record holds ${missing[*]} on ${tree:0:12}, so the job runs them" >&2
      exit 1
    fi
    ;;
  *)
    echo 'usage: verdict.bash key|write|publish|read …' >&2
    exit 2
    ;;
esac
