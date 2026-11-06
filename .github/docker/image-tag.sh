#!/usr/bin/env bash
# Hash the ordered tracked pin bytes, including npm sidecars, and image sources.
# Both publication and lookup call this script, so a tag cannot drift between
# them. ci.yml supplies the CI subset and the install action the baked mise
# version; both are inputs.
set -euo pipefail
# `sort` orders the paths by the locale's collation. A runner whose locale is
# `en_US.UTF-8` orders them another way than one whose locale is `C`, and so
# hashes another tag for the same bytes. The order is the byte order.
export LC_ALL=C
printf 'tag='
git ls-files -z -- mise.toml mise.lock rust-toolchain.toml .mise/locks \
    .config/mise/tasks/mise-tasks-fmt.toml .config/mise/tasks/mise-tasks-check.toml \
    .config/mise/tasks/mise-tasks-mutants.toml \
    .github/docker .github/actions/install-tools .github/workflows/ci-image.yml .github/workflows/ci.yml \
    | sort -z | xargs -0 sha256sum | sha256sum | cut -d ' ' -f 1
