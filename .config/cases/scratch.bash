# shellcheck shell=bash
# The scratch repository that a case harness builds (#5262), sourced by each
# harness that commits in one. It holds the setup alone, never a rule that a
# harness checks: the identity a scratch commit carries, and a commit of one
# file. One copy serves every harness, so a Git setting that each scratch
# commit needs changes in one place.

# Sets the scratch identity on the repository `$1`, or on the repository in
# the working directory. The identity has a name and an address that no
# server reads. It does not sign by default.
#
# Some commands ask for a signature, such as `rebase --gpg-sign` in
# `chain_replay` or an annotated tag under a host's `tag.gpgsign`. Such a
# command signs with a key of the scratch repository's own, through
# `ssh-keygen`. So a host's signing key, and the agent that holds it, never
# touch a scratch commit. Each host and the CI image hold `ssh-keygen`.
# - see: #7159, #7684
#
# `check:cases` refuses a case harness that commits with no call of it.
identity() {
  local repo=${1:-.} key
  git -C "$repo" config user.name case
  git -C "$repo" config user.email case@example.invalid
  git -C "$repo" config commit.gpgsign false
  git -C "$repo" config tag.gpgsign false
  key=$(git -C "$repo" rev-parse --absolute-git-dir)/scratch-signing-key
  [[ -e $key ]] || ssh-keygen -q -t ed25519 -N '' -C case -f "$key"
  git -C "$repo" config gpg.format ssh
  git -C "$repo" config gpg.ssh.program ssh-keygen
  git -C "$repo" config user.signingkey "$key"
}

# Writes `$2` as the whole of the file `$1`, stages it and commits it with the
# message `$3`.
commit() { printf '%s\n' "$2" > "$1" && git add "$1" && git commit --quiet --message "$3"; }
