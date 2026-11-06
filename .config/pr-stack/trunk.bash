# shellcheck shell=bash
# The branch the lanes land on (#5443), under the landing model of #5438.
# Each task that stacks, lands, waits, watches or reads the fork of a change
# sources this file. Thus the lanes and the gate read one name.
#
# The trunk is `landing`. Each pull request opens on it, and the queue of
# `landing` lands it. `main` stays GitHub's default branch, so the workflows
# run from it. It takes only the integration cycle's fast-forward
# (`.github/workflows/integration.yml`). A run that must read another trunk
# sets `GANDR_TRUNK` in its environment, outside the tree.
trunk=${GANDR_TRUNK:-landing}
# The branches that outlive every unit: the default branch, the landing
# branch, the integration cycle's branch and the orphan branch of the
# coverage badge (`ci:coverage-badge`). No branch listing names them for
# deletion.
kept_branches=(main landing integration badges)
