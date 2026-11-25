# What `pr:watch`'s landing trigger keeps after `land_prefix` ran (#1988):
# `<landed head>|<retry at>`, the head it will not land again and the
# earliest second it tries again.
#
# Input: {status, head, landed_head, now, retry_at}, `status` `land_prefix`'s
# exit status, `now` the watch's `SECONDS`.
#
# Only a landing that ran (0) records the head. A stack that waits (3) and a
# landing that failed, a rate-limited read among them (#2746), keep the head
# unlanded and try again two minutes on.
if .status == 0 then "\(.head)|\(.retry_at)" else "\(.landed_head)|\(.now + 120)" end
