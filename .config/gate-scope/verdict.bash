#!/usr/bin/env bash
# The verdict of a check on a tree. A pass of a check is a record, a commit
# with no parent. Its tree is the tree of the check's pass, and its
# message holds the key of the pass. The writer signs the commit with the key
# that signs its commits.
#
# The record's ref is `refs/verdicts/<tree>/<check>/<hash>`, where <hash> is
# the first 16 digits of the SHA-256 of the key. A check whose inputs
# `verdicts.json` lists binds their digest in place of the tree. Its record's
# ref is `refs/verdicts/inputs/<check>/<hash>`.
# - see: #7684, `inputs.bash`
#
# A lane gate writes the record. The pre-push hook sends it. Every pull
# request and merge group job uses it. A job with records for each check runs
# none of them.
#
# A write retries one failed signing call. The tree, check and key stay fixed,
# so the retry writes the same record. A second failure leaves no record and
# names the command that writes it without another gate run.
#
# The key binds each input that the verdict reads (`verdicts.json` names the
# checks and the profile of each):
#   - `check`, and either `tree` and `base` or `inputs`: the task, and the
#     tree and `GATE_BASE`, or the digest of the inputs of the check over its
#     scope (`inputs.bash`). A check that reads its base binds the digest of
#     the same inputs at `GATE_BASE` too, as `base_inputs`. So a merge group
#     whose base moved reads the record of its pull request's gate, when no
#     input of the check changed;
#   - `target` and `compiler`: the host triple and the commit of `rustc -vV`;
#   - `profile`: the profile that the check builds;
#   - `policy`: the policy's revision (`mise run workflow:revision`);
#   - `scope`: `GATE_SCOPE`, which the check reads its packages and its
#     features from;
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
#     One run of the program `gate` gives it (`gate verdict key`).
#   verdict.bash write <tree> <check>...
#     Writes a record for each <check>, and each check that one of them
#     depends on, that `verdicts.json` names. A completed gate can pass a tree
#     that no commit holds. A later commit with that tree can publish and read
#     the record.
#   verdict.bash publish <commit>
#     Pushes each record of the tree of <commit> to the remote
#     `GATE_VERDICT_REMOTE`, `origin` by default: each ref under the tree, and
#     each record of inputs whose commit holds that tree.
#   verdict.bash read <check>...
#     Exits 0 when each <check> holds, and 1 when one does not. One run of
#     the program `gate` reads (`gate verdict read`), and its crate states
#     each rule of a read. A check of inputs holds with no record when its
#     inputs at HEAD are its inputs at `GATE_BASE`, the trunk holds that
#     base, and the change holds no task file. Else a check holds when the
#     remote holds a record of it that the run's key matches and an allowed
#     signer signed. The run names each check that does not hold.
#
# `GATE_VERDICT_SIGNERS` names a file of allowed signers in the form of
# `ssh-keygen -Y verify`. Without it the reader asks GitHub for the signing
# keys of each login in `verdicts.json`'s `signers`. `GATE_VERDICT_RUSTC`
# names the compiler to read, `rustc` by default. `GATE_VERDICT_POLICY` gives
# the policy's revision, and `GATE_VERDICT_TRUNK_OK` gives the trunk's verdict
# on a base, for the cases (`verdict-cases.bash`).
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
table=$here/verdicts.json
remote=${GATE_VERDICT_REMOTE:-origin}

# The first 16 digits of the SHA-256 of a key.
key_hash() { printf '%s' "$1" | sha256sum | cut -c1-16; }

# The name of a check as one segment of a ref: a ref holds no colon.
ref_name() { printf '%s' "${1//:/-}"; }

# Whether the record of <check> binds the digest of its inputs in place of
# the tree. `verdicts.json` lists the inputs for the check, or takes them from
# its row of `table.json`.
digested() { jq -e --arg check "$1" '.checks[$check] | .inputs != null or .table == true' "$table" > /dev/null; }

# The program `gate`, which reads its tables beside this script.
# - see: `tool.bash`, `crates/workflow-gate/README.md`
gate() { "$here/tool.bash" gandr-workflow-gate gate --tables "$here" "$@"; }

# The ref of the record of <check> on <tree> under the key <key>.
ref_of() {
  if digested "$1"; then
    printf 'refs/verdicts/inputs/%s/%s\n' "$(ref_name "$1")" "$(key_hash "$3")"
  else
    printf 'refs/verdicts/%s/%s/%s\n' "$2" "$(ref_name "$1")" "$(key_hash "$3")"
  fi
}

case ${1:-} in
  key)
    (( $# == 2 )) || { echo 'usage: verdict.bash key <check>' >&2; exit 2; }
    gate verdict key "$2"
    ;;
  write)
    (( $# >= 3 )) || { echo 'usage: verdict.bash write <tree> <check>...' >&2; exit 2; }
    tree=$2
    shift 2
    # A check that the gate runs by its name runs each of its `depends` too:
    # `check:landing` runs Clippy and the policy. Without the task list, the
    # gate takes the names as the caller gives them.
    mapfile -t ran < <(mise tasks ls --json 2> /dev/null | jq -r --args '
      (map({key: .name, value: [(.depends // [])[] | if type == "array" then .[0] else . end | split(" ")[0]]}) | from_entries) as $deps
      | def ran: ., (($deps[.] // [])[] | ran); [$ARGS.positional[] | ran] | unique[]' "$@" || printf '%s\n' "$@")
    # The checks that the run signs: each that `verdicts.json` names, and that
    # the gate does not hold. A check that the gate holds does not run, so the
    # gate signs no record of it. Its base or an older record answers for it.
    # - see: #8265, #8268
    signed_checks=()
    for check in "${ran[@]}"; do
      jq -e --arg check "$check" '.checks | has($check)' "$table" > /dev/null || continue
      [[ " ${GATE_HELD:-} " != *" $check "* ]] || continue
      signed_checks+=("$check")
    done
    (( ${#signed_checks[@]} > 0 )) || exit 0
    # One run of `gate` gives the key of each check, one line each, in the
    # order of the checks.
    # - see: #8279
    answer=$(gate verdict key --tree "$tree" "${signed_checks[@]}")
    mapfile -t keys <<< "$answer"
    failed=0
    for i in "${!signed_checks[@]}"; do
      check=${signed_checks[$i]}
      k=${keys[$i]}
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
      git update-ref "$(ref_of "$check" "$tree" "$k")" "$commit"
      echo "verdict: $check passes on ${tree:0:12}; the record is ${commit:0:12}" >&2
    done
    (( failed == 0 )) || exit 1
    ;;
  publish)
    (( $# == 2 )) || { echo 'usage: verdict.bash publish <commit>' >&2; exit 2; }
    tree=$(git rev-parse "$2^{tree}")
    # The refs under the tree, and each record of inputs whose commit holds
    # the tree. The gate writes such a record on this tree.
    mapfile -t refs < <(git for-each-ref --format='%(refname)' "refs/verdicts/$tree/"
      git for-each-ref --format='%(refname) %(tree)' refs/verdicts/inputs/ | awk -v tree="$tree" '$2 == tree { print $1 }')
    if (( ${#refs[@]} == 0 )); then
      echo "verdict: no record of the tree ${tree:0:12}, so none is pushed" >&2
      exit 0
    fi
    git push --quiet --no-verify "$remote" "${refs[@]}"
    echo "verdict: pushed the records of the tree ${tree:0:12}: $(printf '%s\n' "${refs[@]}" | awk -F/ '{ print $(NF - 1) }' | sort -u | paste -sd ' ')" >&2
    ;;
  read)
    (( $# >= 2 )) || { echo 'usage: verdict.bash read <check>...' >&2; exit 2; }
    shift
    # - see: #8279
    gate verdict read "$@"
    ;;
  *)
    echo 'usage: verdict.bash key|write|publish|read …' >&2
    exit 2
    ;;
esac
