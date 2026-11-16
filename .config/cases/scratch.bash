# shellcheck shell=bash
# The scratch repository that a case harness builds (#5262), sourced by each
# harness that commits in one. It holds the setup alone, never a rule that a
# harness checks: the identity a scratch commit carries, and a commit of one
# file. One copy serves every harness, so a Git setting that each scratch
# commit needs changes in one place.

# Sets the scratch identity on the repository `$1`, or on the repository in
# the working directory: a name and an address that no server reads, and no
# signing by default. A command that asks for a signature (`rebase
# --gpg-sign` in `chain_replay`, an annotated tag under a host's
# `tag.gpgsign`) signs with a key of the scratch repository's own, through
# `ssh-keygen`. So a host's signing key, and the agent that holds it, never
# touches a scratch commit (#7159). A host with no `ssh-keygen`, such as the
# image of the format job, holds no signing key either, so the scratch
# repository gets no key there and no case there signs (#5469).
# `check:cases` refuses a case harness that commits with no call of it.
identity() {
  local repo=${1:-.} key
  git -C "$repo" config user.name case
  git -C "$repo" config user.email case@example.invalid
  git -C "$repo" config commit.gpgsign false
  git -C "$repo" config tag.gpgsign false
  command -v ssh-keygen > /dev/null || return 0
  key=$(git -C "$repo" rev-parse --absolute-git-dir)/scratch-signing-key
  [[ -e $key ]] || ssh-keygen -q -t ed25519 -N '' -C case -f "$key"
  git -C "$repo" config gpg.format ssh
  git -C "$repo" config gpg.ssh.program ssh-keygen
  git -C "$repo" config user.signingkey "$key"
}

# Writes `$2` as the whole of the file `$1`, stages it and commits it with the
# message `$3`.
commit() { printf '%s\n' "$2" > "$1" && git add "$1" && git commit --quiet --message "$3"; }
