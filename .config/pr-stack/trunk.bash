# shellcheck shell=bash
# The branch the lanes land on (#5443), under the landing model of #5438.
# Each task that stacks, lands, waits, watches or reads the fork of a change
# sources this file. Thus the lanes and the gate read one name.
#
# The trunk is `main` until the cutover (#5443, step 4). A lane that tries
# the model first sets `GANDR_TRUNK=landing` in its environment, outside the
# tree. Its pull requests then open on `landing`, and the queue of `landing`
# lands them. The cutover makes `landing` the value here for every lane.
# `main` stays GitHub's default branch, so the workflows run from it, and it
# then takes only the integration cycle's fast-forward
# (`.github/workflows/integration.yml`).
trunk=${GANDR_TRUNK:-main}
# The branches that outlive every unit: the default branch, the landing
# branch, the integration cycle's branch and the orphan branch of the
# coverage badge (`ci:coverage-badge`). No branch listing names them for
# deletion.
kept_branches=(main landing integration badges)
