# The host that runs a gate of `gate:remote` (#6996), read by `remote.bash`.
#
# The probe of #6996 reads the gate records and the cycle's runs of three
# days. The wait for a slot is 0 s at p90 on each host, while a gate beside
# the cycle takes 298 s at p50 against 159 s with no cycle. So the load
# chooses the host, and a free slot only admits it. A host whose gh gives no
# token of the reader fails the gate's reads of GitHub, so it is passed over.
#
# Input: one reading for each host that answered its probe, `{host, load,
# cores, free, token}`: its load over one minute, its cores, its free gate
# slots and whether a gate there reads with a token. Output: the name of the
# host with the least load for each core among the hosts with a free slot
# and a token, or null when no host has both. Of two hosts with one load for
# each core, the one with more free slots goes first, then the first by name.
map(select(.free > 0 and .cores > 0 and .token != false))
| sort_by([.load / .cores, -.free, .host])
| if length == 0 then null else first.host end
