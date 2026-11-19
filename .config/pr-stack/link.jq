# The arguments of `gh stack link` for an open chain (#1275), one per line.
#
# Input: {chain: [number], stacks: [number | null]}, the open chain bottom to
# top and the server stack each member already belongs to.
#
# GitHub keeps a stack's merged members, and `gh stack link` refuses a list
# that leaves one out. A chain already in a stack is therefore linked by the
# stack's number: members already in it are skipped and the new ones appended
# on top. A chain in no stack is linked by its numbers alone. `gh stack link`
# takes at least two, so a chain of one in no stack takes no link: its pull
# request stands alone on the trunk, as one whose stack top merged while it
# opened does (#3817).

(.stacks | map(select(. != null)) | first) as $stack
| if $stack != null then $stack, .chain[]
  elif (.chain | length) >= 2 then .chain[]
  else empty end
