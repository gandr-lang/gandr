#!/usr/bin/env bash
# Hash what the image is built from: the ordered tracked pin bytes, including
# npm sidecars, the image sources, and the parts of the CI files that the
# build reads. Both publication and lookup call this script, so a tag cannot
# drift between them. The build reads three parts of files that hold more:
# landing-checks.yml's `MISE_DISABLE_TOOLS` line, the install action's mise version and
# the task files' tool pins. The script hashes those parts alone, so an edit
# to a step or to a task's script keeps the tag, and an edit to a pin changes
# it. The install action is hashed whole.
set -euo pipefail
# `sort` orders the paths by the locale's collation. A runner whose locale is
# `en_US.UTF-8` orders them another way than one whose locale is `C`, and so
# hashes another tag for the same bytes. The order is the byte order.
export LC_ALL=C
disabled=$(grep -E '^  MISE_DISABLE_TOOLS: ' .github/workflows/landing-checks.yml) \
  || { echo "image-tag.sh: landing-checks.yml holds no MISE_DISABLE_TOOLS line, which the image build reads" >&2; exit 1; }
printf 'tag='
{
  git ls-files -z -- mise.toml mise.lock rust-toolchain.toml .mise/locks \
    .github/docker .github/actions/install-tools .github/workflows/build-ci-image.yml \
    | sort -z | xargs -0 sha256sum
  printf 'landing-checks.yml %s\n' "$disabled"
  for tasks in .config/mise/tasks/mise-tasks-fmt.toml .config/mise/tasks/mise-tasks-check.toml \
    .config/mise/tasks/mise-tasks-mutants.toml; do
    grep -E '^tools[.= ]' "$tasks" | sort -u | sed "s|^|$tasks |"
  done
} | sha256sum | cut -d ' ' -f 1
