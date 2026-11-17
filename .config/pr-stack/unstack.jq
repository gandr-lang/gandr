# Whether `stack_link` unstacks a server stack before it links the chain
# (#2094, #7142): true or false.
#
# Input: [chain, entries], the chain's numbers bottom to top, and the
# stack's entries `{number, state, isInMergeQueue}` bottom to top.
#
# GitHub refuses every link onto a stack that holds a member closed unmerged
# (#2094). `link.jq` appends each new member of the chain above every member
# of the stack. So an open member that the chain leaves out ends below the
# new members. `pr:open` leaves out the held draft that it stacks past, and
# GitHub then bases the new pull request on the branch of the draft (#7142).
# The unstack drops that member. A queued member stays stacked through the
# unstack, and the chain links above it as before, so it asks for no unstack.
# A chain that adds no member appends nothing, so it unstacks nothing for an
# open member.

.[0] as $chain
| .[1] as $entries
| ($entries | map(.number)) as $held
| any($entries[]; .state == "CLOSED")
  or (any($chain[]; IN($held[]) | not)
    and any($entries[]; .state == "OPEN" and (.isInMergeQueue | not) and (.number | IN($chain[]) | not)))
