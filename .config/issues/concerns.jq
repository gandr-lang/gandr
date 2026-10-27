# The concerns `unit.jq` asks after (#3113), read from the rows of
# `ledger/concerns.sql` as text, so the issues workflow needs no sqlite on its
# runner. `check:issues` holds it to sqlite's reading of the same file.
#
# Input: the file, a string. Output: the concern ids, in the file's order.

[scan("INSERT INTO concern VALUES\\('([a-z_-]+)',") | .[0]]
