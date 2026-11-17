-- The findings of `check:purposes` over the purposes ledger, the concerns
-- ledger, the entries that `purposes:items` lists (`entry`), the crates it
-- lists (`checked`) and the host's system (`host`, one row). A host reads a
-- row whose entry `held_by` names against its listing only when a `held_by`
-- row names the host's system: rustdoc lists no entry that a `cfg` of the
-- host leaves out. Each finding is one line.
WITH named(crate, path, kind, shown) AS (
  SELECT crate, path, kind, crate || CASE path WHEN '' THEN '' ELSE '::' || path END FROM purpose
),
listed(crate, path, kind, location, shown) AS (
  SELECT crate, path, kind, location, crate || CASE path WHEN '' THEN '' ELSE '::' || path END FROM entry
),
held(crate, path, kind) AS (
  SELECT h.crate, h.path, h.kind FROM held_by h, host WHERE h.system = host.system
),
elsewhere(crate, path, kind) AS (
  SELECT crate, path, kind FROM held_by EXCEPT SELECT crate, path, kind FROM held
),
tags(crate, path, kind, shown, tag) AS (
  SELECT n.crate, n.path, n.kind, n.shown, t.value
  FROM purpose p JOIN named n USING (crate, path, kind), json_each('["' || replace(p.concerns, ' ', '","') || '"]') t
  WHERE p.concerns IS NOT NULL
)
SELECT crate || ': rows for no crate with a library under crates/; correct the crate or delete its rows'
FROM (SELECT DISTINCT crate FROM purpose WHERE crate IN (SELECT crate FROM checked) AND crate NOT IN (SELECT crate FROM entry))
UNION ALL
SELECT l.shown || ' (' || l.kind || ', ' || l.location || '): a public item with no row; add'
  || ' INSERT INTO purpose VALUES(' || quote(l.crate) || ',' || quote(l.path) || ',' || quote(l.kind)
  || ',''<purpose>'',<concerns>,''<naming>'',''<doc>'',<finding>);'
  || ' to ledger/purposes.sql, each column as its schema there states, then run `mise run ledger:purposes`'
FROM listed l
WHERE l.kind NOT IN ('crate', 'module')
  AND NOT EXISTS (SELECT 1 FROM purpose p WHERE (p.crate, p.path, p.kind) = (l.crate, l.path, l.kind))
UNION ALL
SELECT n.shown || ' (' || n.kind || '): a row naming no entry of `mise run purposes:list ' || n.crate || '`; correct its path or kind, or delete it'
FROM named n
WHERE n.crate IN (SELECT crate FROM entry)
  AND NOT EXISTS (SELECT 1 FROM entry e WHERE (e.crate, e.path, e.kind) = (n.crate, n.path, n.kind))
  AND NOT EXISTS (SELECT 1 FROM elsewhere o WHERE (o.crate, o.path, o.kind) = (n.crate, n.path, n.kind))
UNION ALL
SELECT l.shown || ' (' || l.kind || ', ' || l.location || '): listed on ' || (SELECT system FROM host)
  || ', and its held_by rows name other systems alone; add'
  || ' INSERT INTO held_by VALUES(' || quote(l.crate) || ',' || quote(l.path) || ',' || quote(l.kind) || ',' || quote((SELECT system FROM host)) || ');'
  || ' to ledger/purposes.sql, or delete its held_by rows'
FROM listed l
WHERE EXISTS (SELECT 1 FROM elsewhere o WHERE (o.crate, o.path, o.kind) = (l.crate, l.path, l.kind))
UNION ALL
SELECT h.crate || '::' || h.path || ' (' || h.kind || '): a held_by row for ' || h.system || ' with no purpose row; add its purpose row, or delete it'
FROM held_by h
WHERE NOT EXISTS (SELECT 1 FROM purpose p WHERE (p.crate, p.path, p.kind) = (h.crate, h.path, h.kind))
UNION ALL
SELECT l.shown || ' (module, ' || l.location || '): no row, and its crate has the crate row; the crate row lands with a row for every module'
FROM listed l
WHERE l.kind = 'module'
  AND EXISTS (SELECT 1 FROM purpose c WHERE c.crate = l.crate AND c.kind = 'crate')
  AND NOT EXISTS (SELECT 1 FROM purpose p WHERE (p.crate, p.path, p.kind) = (l.crate, l.path, l.kind))
UNION ALL
SELECT n.shown || ' (module): a module row, and its crate has no crate row; module rows land with the crate row'
FROM named n
WHERE n.kind = 'module' AND NOT EXISTS (SELECT 1 FROM purpose c WHERE c.crate = n.crate AND c.kind = 'crate')
UNION ALL
SELECT shown || ' (' || kind || '): concern ' || tag || ' is no key of ledger/concerns.sql'
FROM tags WHERE tag NOT IN (SELECT id FROM concern)
UNION ALL
SELECT shown || ' (' || kind || '): concern ' || tag || ' is tagged more than once'
FROM tags GROUP BY crate, path, kind, tag HAVING count(*) > 1;
