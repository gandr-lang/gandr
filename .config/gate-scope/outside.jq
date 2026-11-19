# The paths of a change that lie in no package directory (#6976). A scope of
# the whole workspace names them on stderr (`scope.bash`), so the log of a
# queue's group says which path widened the lints. The queue of `landing`
# read the whole workspace for a group whose change the same rule reads as
# three packages outside the queue, and its log named no path.
#
# Input:
#   changed   the paths the change touches
#   packages  the workspace's packages: [{name, dir, deps: [name]}], `dir`
#             the package's directory relative to the root, with no
#             trailing `/`
#
# Output: the paths in no package directory, in the order of `changed`.

.packages as $packages
| [.changed[] | . as $path | select(all($packages[]; .dir as $dir | $path | startswith($dir + "/") | not))]
