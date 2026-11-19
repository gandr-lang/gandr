#!/usr/bin/env bash
# The cases of the records of a check's pass. `check:gate-scope` runs them.
# Each case builds a scratch repository with a bare remote. It writes a record
# of `check:clippy-arch` on the tree of HEAD, pushes it and reads it as a
# runner does. The last cases take a record of the inputs of `check:dylint`
# and of `check:clippy-plain-only`, in a scratch workspace of three crates.
# - see: #7684, `verdict.bash`
#
# A stub compiler and a fixed policy revision stand for the toolchain, so no
# case builds or reaches the network. Each case signs through `ssh-keygen`,
# which each host and the CI image hold. An image without it fails here, as
# each read of a job's records fails there.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
verdict=$here/verdict.bash
push=$here/push.bash
source "$here/../cases/scratch.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "verdict case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A compiler that reports the commit `$1`.
stub_rustc() {
  printf '#!/usr/bin/env bash\nprintf "rustc 1.0.0-nightly\\ncommit-hash: %s\\nhost: x86_64-unknown-linux-gnu\\n"\n' "$1" > "$scratch/rustc-$1"
  chmod +x "$scratch/rustc-$1"
  printf '%s' "$scratch/rustc-$1"
}

# The scratch repository at `$1` holds one commit of `main`, and it has a
# bare remote. An allowed signers file holds the scratch key, and a trunk holds
# the gate's base. Each run reads the whole workspace as its scope.
setup() {
  git init --quiet --bare "$1.remote"
  git init --quiet -b main "$1"
  cd "$1"
  identity
  git remote add origin "$1.remote"
  commit file one base
  git push --quiet --no-verify origin main
  printf 'case@example.invalid namespaces="git" %s\n' "$(< "$(git rev-parse --absolute-git-dir)/scratch-signing-key.pub")" > "$1.signers"
  export GATE_VERDICT_SIGNERS=$1.signers GATE_VERDICT_POLICY=policy-1 GATE_VERDICT_RUSTC
  GATE_VERDICT_RUSTC=$(stub_rustc compiler-1)
  export GATE_BASE
  GATE_BASE=$(git rev-parse HEAD)
  unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS GATE_SCOPE
  export GATE_VERDICT_TRUNK_OK=$GATE_BASE GATE_VERDICT_SCOPE=--workspace
}

# Writes and pushes the record of `check:clippy-arch` on the tree of HEAD.
gate() {
  "$verdict" write "$(git rev-parse 'HEAD^{tree}')" check:clippy-arch 2> /dev/null
  "$verdict" publish HEAD 2> /dev/null
}

# Whether a read of `check:clippy-arch` holds, as `held` or `runs`.
reads() { if "$verdict" read check:clippy-arch 2> /dev/null; then echo held; else echo runs; fi; }

# A `git` wrapper whose signer fails as its mode states, then delegates every
# other call to the real Git.
signer() {
  local mode=$1 bin=$2
  mkdir -p "$bin"
  case $mode in
    once)
      printf '%s\n' \
        '#!/usr/bin/env bash' \
        'if [[ $1 == commit-tree && ! -e $GATE_VERDICT_CASE_FAILURE ]]; then' \
        '  : > "$GATE_VERDICT_CASE_FAILURE"' \
        '  echo "case signer failed" >&2' \
        '  exit 1' \
        'fi' \
        'exec "$GATE_VERDICT_CASE_GIT" "$@"' \
        > "$bin/git"
      ;;
    always)
      printf '%s\n' \
        '#!/usr/bin/env bash' \
        'if [[ $1 == commit-tree ]]; then' \
        '  echo "case signer failed" >&2' \
        '  exit 1' \
        'fi' \
        'exec "$GATE_VERDICT_CASE_GIT" "$@"' \
        > "$bin/git"
      ;;
  esac
  chmod +x "$bin/git"
}

got=$(setup "$scratch/same" && gate && reads)
[[ $got == held ]] || fail "#7684: a run on the gated tree with the gate's key reads the record" "$got"

# The push hook sends a passed head's record before the head moves the remote.
got=$(
  setup "$scratch/pushed"
  commit file two pushed > /dev/null
  "$verdict" write "$(git rev-parse 'HEAD^{tree}')" check:clippy-arch 2> /dev/null
  PRE_COMMIT_TO_REF=$(git rev-parse HEAD) PRE_COMMIT_REMOTE_BRANCH=refs/heads/main "$push" > /dev/null 2>&1
  git push --quiet --no-verify origin main
  reads
)
[[ $got == held ]] || fail "#8166: a gated head pushes its record without pr:open" "$got"

got=$(
  setup "$scratch/retry-once"
  signer once "$scratch/retry-once-bin"
  tree=$(git rev-parse 'HEAD^{tree}')
  status=0
  output=$(PATH="$scratch/retry-once-bin:$PATH" GATE_VERDICT_CASE_FAILURE="$scratch/retry-once.failed" \
    GATE_VERDICT_CASE_GIT="$(command -v git)" "$verdict" write "$tree" check:clippy-arch 2>&1) || status=$?
  "$verdict" publish HEAD > /dev/null 2>&1
  if [[ $status == 0 && -e $scratch/retry-once.failed && $output == *"signing attempt 1 of 2 failed"* ]]; then
    reads
  else
    printf 'status %s, output %s\n' "$status" "$output"
  fi
)
[[ $got == held ]] || fail "#8147: a second signing attempt writes the passed check's record" "$got"

got=$(
  setup "$scratch/retry-always"
  signer always "$scratch/retry-always-bin"
  tree=$(git rev-parse 'HEAD^{tree}')
  status=0
  output=$(PATH="$scratch/retry-always-bin:$PATH" GATE_VERDICT_CASE_GIT="$(command -v git)" \
    "$verdict" write "$tree" check:clippy-arch 2>&1) || status=$?
  ref=$(git for-each-ref --count=1 refs/verdicts/)
  if [[ $status == 1 && -z $ref && $output == *"record did not sign after 2 attempts"* \
    && $output == *"verdict.bash write"* ]]; then
    echo refused
  else
    printf 'status %s, ref %s, output %s\n' "$status" "$ref" "$output"
  fi
)
[[ $got == refused ]] || fail "#8147: a failed record names its no-gate write command" "$got"

got=$(setup "$scratch/tree" && gate && commit file two other > /dev/null && reads)
[[ $got == runs ]] || fail "#7684: a run on another tree reads no record" "$got"

got=$(setup "$scratch/scope" && gate && GATE_VERDICT_SCOPE='--workspace --exclude other' reads)
[[ $got == runs ]] || fail "#7684: a run whose scope against the record's base differs reads no record" "$got"

got=$(setup "$scratch/flags" && gate && RUSTFLAGS='--cfg other' reads)
[[ $got == runs ]] || fail "#7684: a run under other flags reads no record" "$got"

got=$(setup "$scratch/compiler" && gate && GATE_VERDICT_RUSTC=$(stub_rustc compiler-2) reads)
[[ $got == runs ]] || fail "#7684: a run under another compiler reads no record" "$got"

got=$(setup "$scratch/policy" && gate && GATE_VERDICT_POLICY=policy-2 reads)
[[ $got == runs ]] || fail "#7684: a run under another policy revision reads no record" "$got"

# A signer outside the allowed signers.
got=$(
  setup "$scratch/signer"
  gate
  ssh-keygen -q -t ed25519 -N '' -C other -f "$scratch/other-key"
  printf 'case@example.invalid namespaces="git" %s\n' "$(< "$scratch/other-key.pub")" > "$scratch/signer.signers"
  reads
)
[[ $got == runs ]] || fail "#7684: a record that no allowed signer signed is refused" "$got"

# A record whose body binds another key under the run's ref.
got=$(
  setup "$scratch/forged"
  tree=$(git rev-parse 'HEAD^{tree}')
  key=$("$verdict" key check:clippy-arch)
  hash=$(printf '%s' "$key" | sha256sum | cut -c1-16)
  forged=$(git commit-tree -S -m "verdict: check:clippy-arch passes" -m "$(jq -c '.policy = "policy-0"' <<< "$key")" "$tree")
  git update-ref "refs/verdicts/$tree/check-clippy-arch/$hash" "$forged"
  "$verdict" publish HEAD 2> /dev/null
  reads
)
[[ $got == runs ]] || fail "#7684: a record whose body is not the run's key is refused" "$got"

# Work that is not the tree of HEAD writes no record.
got=$(
  setup "$scratch/dirty"
  printf 'two\n' > file
  "$verdict" write "$("$here/passed.bash" tree)" check:clippy-arch 2> /dev/null
  git for-each-ref --count=1 refs/verdicts/ | wc -l | tr -d ' '
)
[[ $got == 0 ]] || fail "#7684: work that is not the tree of HEAD writes no record" "$got"

# A merge group on a newer base reads the record of a base that the trunk
# holds. The group's own `GATE_BASE` does not enter the key.
got=$(setup "$scratch/trunk" && gate && GATE_BASE=0000000000000000000000000000000000000000 reads)
[[ $got == held ]] || fail "#7684: a merge group reads a record whose base the trunk holds" "$got"

got=$(setup "$scratch/off-trunk" && gate && GATE_VERDICT_TRUNK_OK=none reads)
[[ $got == runs ]] || fail "#7684: a record whose base the trunk does not hold is refused" "$got"

# A record whose signature does not verify, as in an image with no
# `ssh-keygen`. The read states the reason, and the job runs the check.
got=$(
  setup "$scratch/unverified"
  gate
  GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=gpg.ssh.program GIT_CONFIG_VALUE_0="$scratch/no-ssh-keygen" \
    "$verdict" read check:clippy-arch 2>&1 || true
)
[[ $got == *"of check:clippy-arch does not hold: its signature does not verify: "*"$scratch/no-ssh-keygen"*"No such file or directory"* \
  && $got == *"no record holds check:clippy-arch on "* ]] \
  || fail "#7684: a record whose signature does not verify states why" "$got"

# An edit that keeps the size and the stamp of a file. Before it, git writes
# an index in the same second as the file. Git reads the entry again by
# content only while the copy of the index keeps the index's stamp.
#
# The entry's stamp is of 2010 and the index's of 2000. So the entry is racy
# in the index, and not in a copy stamped now. The edit keeps the entry's
# stamp, so the stat of the file matches the entry.
got=$(
  setup "$scratch/racy"
  touch -t 201001010000 file
  git add file
  touch -t 200001010000 "$scratch/racy.old"
  touch -r "$scratch/racy.old" "$(git rev-parse --path-format=absolute --git-path index)"
  cp -p file "$scratch/racy.stamp"
  printf 'two\n' > file
  touch -r "$scratch/racy.stamp" file
  work=$(GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=core.trustctime GIT_CONFIG_VALUE_0=false "$here/passed.bash" tree)
  if [[ $work == "$(git rev-parse 'HEAD^{tree}')" ]]; then echo head; else echo work; fi
)
[[ $got == work ]] || fail "#7740: an edit that keeps a file's size and stamp is the tree of the work" "$got"

# A scratch workspace of three crates: `b` depends on `a`, and `c` stands
# apart. The task's definition is a fixed text, since the scratch repository
# holds no task.
workspace() {
  local name
  for name in a b c; do
    mkdir -p "crates/$name/src"
    printf '//! %s\n' "$name" > "crates/$name/src/lib.rs"
    printf '[package]\nname = "%s"\nversion = "0.1.0"\nedition = "2024"\n' "$name" > "crates/$name/Cargo.toml"
  done
  printf '\n[dependencies]\na = { path = "../a" }\n' >> crates/b/Cargo.toml
  printf '[workspace]\nmembers = ["crates/a", "crates/b", "crates/c"]\nresolver = "3"\n' > Cargo.toml
  cargo generate-lockfile --offline --quiet
  git add -A
  git commit --quiet --message workspace
  export GATE_INPUTS_TASK=case-task GATE_BASE
  GATE_BASE=$(git rev-parse HEAD)
}

# Gates a change of `a` on a branch over the scope that `$1` names. Then it
# pushes the record of the inputs of the check `$2`, the policy by default.
gate_inputs() {
  git switch --quiet --create change
  commit crates/a/src/lib.rs '//! a, changed' change > /dev/null
  GATE_SCOPE=$1 "$verdict" write "$(git rev-parse 'HEAD^{tree}')" "${2:-check:dylint}" 2> /dev/null
  "$verdict" publish HEAD 2> /dev/null
}

# Merges the change onto a moved base, as a merge group does. The base moves
# by the text `$1` at the path `$2`, and it becomes the group's base.
group() {
  git switch --quiet --detach "$GATE_BASE"
  commit "$2" "$1" moved > /dev/null
  GATE_BASE=$(git rev-parse HEAD)
  git merge --quiet --no-edit change
}

# Whether a read of the check `$2`, the policy by default, holds over the
# scope `$1`, as `held` or `runs`.
reads_inputs() { if GATE_VERDICT_SCOPE=$1 "$verdict" read "${2:-check:dylint}" 2> /dev/null; then echo held; else echo runs; fi; }

got=$(setup "$scratch/inputs-moved" && workspace && gate_inputs --workspace && group notes notes.txt && reads_inputs --workspace)
[[ $got == held ]] || fail "#7684: a group whose base moved holds the record when no input of the check changed" "$got"

got=$(setup "$scratch/inputs-changed" && workspace && gate_inputs --workspace && group '//! b, moved' crates/b/src/lib.rs && reads_inputs --workspace)
[[ $got == runs ]] || fail "#7684: a group whose base changed an input of the check runs it" "$got"

got=$(setup "$scratch/inputs-apart" && workspace && gate_inputs '--workspace --exclude c' \
  && group '//! c, moved' crates/c/src/lib.rs && reads_inputs '--workspace --exclude c')
[[ $got == held ]] || fail "#7684: a change of a crate outside the scope's closure holds the record" "$got"

got=$(setup "$scratch/inputs-manifest" && workspace && gate_inputs '--workspace --exclude c' \
  && group "$(printf '[package]\nname = "c"\nversion = "0.2.0"\nedition = "2024"')" crates/c/Cargo.toml \
  && reads_inputs '--workspace --exclude c')
[[ $got == runs ]] || fail "#7684: a change of a manifest outside the scope's closure runs the check" "$got"

# The plain Clippy pass greps each crate for its pattern. So a file outside
# the closure that gains the pattern runs it, and another change keeps it.
got=$(setup "$scratch/grep-other" && workspace && gate_inputs '--workspace --exclude c' check:clippy-plain-only \
  && group '//! c, moved' crates/c/src/lib.rs && reads_inputs '--workspace --exclude c' check:clippy-plain-only)
[[ $got == held ]] || fail "#7684: a change outside the closure that the plain pass's grep does not find holds its record" "$got"

got=$(setup "$scratch/grep-found" && workspace && gate_inputs '--workspace --exclude c' check:clippy-plain-only \
  && group '#[cfg(not(anodized_panic))] fn plain() {}' crates/c/src/lib.rs \
  && reads_inputs '--workspace --exclude c' check:clippy-plain-only)
[[ $got == runs ]] || fail "#7684: a file outside the closure that gains the plain pass's pattern runs it" "$got"

# A dep-info file of the crate `a` that names a file outside its crate. The
# check refuses it by its path, until the table names it for `a`.
got=$(
  setup "$scratch/depinfo"
  workspace
  mkdir -p notes
  commit notes/outside.txt outside notes > /dev/null
  touch -d '1 hour ago' "$scratch/depinfo.stamp"
  unit=target/case/build/a/0123456789abcdef/out
  mkdir -p "$unit"
  printf 'target/case/liba.rmeta: crates/a/src/lib.rs notes/outside.txt\n\ncrates/a/src/lib.rs:\nnotes/outside.txt:\n' > "$unit/a-0123456789abcdef.d"
  refused=$("$here/inputs.bash" depinfo "$scratch/depinfo.stamp" --workspace target/case 2>&1) && refused=passed
  printf '{"workspace": [], "outside": {"a": ["notes/outside.txt"]}}\n' > "$scratch/depinfo.json"
  declared=$(GATE_INPUTS_TABLE=$scratch/depinfo.json "$here/inputs.bash" depinfo "$scratch/depinfo.stamp" --workspace target/case 2>&1) || declared=refused
  printf '%s|%s' "$refused" "$declared"
)
[[ $got == "inputs: a read notes/outside.txt, which the inputs of its scope do not hold; name it under \`outside.a\` in .config/gate-scope/inputs.json (#7684)|inputs: each file of the tree that the run read is an input of its scope" ]] \
  || fail "#7684: the dep-info check refuses a file outside the inputs by its path" "$got"

(( failed == 0 )) || exit 1
echo "verdict OK: 22 cases read, refuse and write records as recorded"
