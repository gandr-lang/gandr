#!/usr/bin/env bash
# Whether `check:vscode-smoke` may start a real VS Code here (#3696):
#   admits.bash [<kernel>]
# exits 0 on Linux in GitHub Actions and 1 anywhere else. The kernel is
# `uname -s` unless given. Chromium honours `--ozone-platform=headless` on
# Linux alone, so elsewhere the editor opens a window and takes the seated
# user's focus. `GITHUB_ACTIONS=true` is set by the hosted runner and by
# `act`. `CI` is not read, for a seat's own shell may set it.
set -euo pipefail
kernel=${1:-$(uname -s)}
[[ $kernel == Linux && ${GITHUB_ACTIONS:-} == true ]]
