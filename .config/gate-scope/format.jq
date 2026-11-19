# The paths the shared formatters read for a change (#6883). The whole
# treefmt pass took 48.5 s on a quiet host and 50 s on a runner. The gate ran
# it before each pull request opened, and no check of the queue read the tree
# that the queue then built. A formatter's verdict on a tree is the meet of
# its verdicts on the files, so the check reads the files that the change
# touches, and the rest of the tree keeps the verdict of the base.
#
# Three things read more than one file. The configuration and the pins of
# the formatters decide the verdict on every file: a change that touches a
# path of the table's `formatting.configuration` reads the whole tree. A
# program of `formatting.programs` reads more files than it formats: the
# type-aware lint of TypeScript reads the whole program. A change that
# touches a path of a program's `reads` adds every tracked path of its
# `sources`. A link of a source in `formatting.links` names another path, and
# MD057 refuses a link to a path that the tree lacks. A change that deletes a
# path, a move among them, adds every tracked path of its `sources`. A row is
# a path as `rows.jq` reads it: a file, a directory that ends in `/`, or a
# glob.
#
# Input:
#   changed   the paths the change touches that the tree holds
#   deleted   the paths the change deletes; absent, none
#   tracked   every path the index holds
#   table     the table to read; absent, `table.json`
#
# Output: `"tree"`, or the paths to format, sorted and unique. A change that
# touches no path gives `[]`.

import "table" as $table;

include "rows";

def touches($rows): any(.[]; . as $path | any($rows[]; mapped({path: .}; $path)));

(.table // $table::table[0]).formatting as $formatting
| .changed as $changed
| (.deleted // []) as $deleted
| .tracked as $tracked
| if $changed | touches($formatting.configuration) then "tree"
  else
    [$changed[],
     ($formatting.programs[]
      | .reads as $reads
      | .sources as $sources
      | select($changed | touches($reads))
      | $tracked[] | select([.] | touches($sources))),
     ($formatting.links // empty
      | .sources as $sources
      | select($deleted != [])
      | $tracked[] | select([.] | touches($sources)))]
    | unique
  end
