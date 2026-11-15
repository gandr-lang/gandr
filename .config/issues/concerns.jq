# The concerns `unit.jq` asks after (#3113), read from the rows of
# `ledger/concerns.sql` as text, so the issues workflow needs no sqlite on its
# runner. `check:issues` holds it to sqlite's reading of the same file.
#
# Input: the file, a string. Output: each concern as `{id, issue}`, in the
# file's order. The issue is the row's last field, so `findings.jq` asks no
# row of an issue filed before the concern (#5308).

[scan("INSERT INTO concern VALUES\\('([a-z_-]+)',.*,'(#[0-9]+)'\\);") | {id: .[0], issue: .[1]}]
