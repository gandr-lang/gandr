# The build directories a deploy of `toolchain:follow` removes (#4499): every
# build under `$XDG_DATA_HOME/gandr/builds` but the current one, the one
# before it, and any build a live process still runs. A live build goes at
# the first deploy that finds it no longer running.
#
# Input: `{builds, current, previous, live}`: the commits of the build
# directories on disk, the deployed commit, the commit deployed before it
# (`null` at the first deploy), and the commits whose `gandr` a process runs.
# Output: the commits to remove, sorted.

. as $in
| [$in.current, $in.previous, ($in.live // [])[]] as $kept
| [$in.builds[] | select(. as $build | $kept | index($build) | not)]
| unique
