-- The citation refresh's record (#4532, #4533): each site the `fidelity`
-- table records is held to what the refresh read there. Run by
-- `check:references` over a database holding
--   cite      the lines `cites.awk` prints over the crates and the corpus;
--   corpus    each corpus source's path;
--   fidelity  the references ledger's rows the refresh writes by hand.
-- It prints one finding a line, in a fixed order, and nothing when every
-- recorded site keeps its record.
--
-- A crate's site is its crate and module, written `crate::module`, or the
-- crate alone at its root; a corpus source's is its path. A recorded crate
-- site cites each work by a key line whose role says what the site takes
-- from it: `lineage`, `background` and a bare locator, which name nothing
-- it takes, are refused there. A corpus source cites by locator alone, so
-- only the record itself is held there.

CREATE TEMP VIEW recorded AS
SELECT f.*,
  CASE f.crate WHEN 'corpus' THEN 'corpus/' || f.module
    ELSE f.crate || CASE f.module WHEN '' THEN '' ELSE '::' || f.module END END AS site
FROM fidelity f;

CREATE TEMP VIEW held AS
SELECT r.*,
  CASE r.crate WHEN 'corpus' THEN EXISTS (SELECT 1 FROM corpus c WHERE c.path = 'corpus/' || r.module)
    ELSE EXISTS (SELECT 1 FROM cite c WHERE c.kind = 'file' AND (c.crate, c.module) = (r.crate, r.module)) END AS present,
  (SELECT count(DISTINCT c.key) FROM cite c
    WHERE (c.crate, c.module) = (r.crate, r.module)
      AND c.kind IN ('cite', 'locator', 'corpus')) AS works
FROM recorded r;

CREATE TEMP VIEW sites AS
SELECT DISTINCT crate, module, site FROM recorded WHERE crate <> 'corpus';

SELECT line FROM (
  SELECT 0 AS rank, site AS place, 'ledger/references.sql: the fidelity row of ' || site || ' and `' || old
    || '` names a site the tree no longer holds; delete the row' AS line
  FROM held WHERE NOT present
  UNION ALL
  SELECT 1, site, 'ledger/references.sql: ' || site || ' is historical against `' || old
    || '` with no follow-up; file the refactor that brings it to the newest work''s framing, and write its number in `follow_up`'
  FROM held WHERE present AND verdict = 'historical' AND follow_up IS NULL
  UNION ALL
  SELECT 2, site, 'ledger/references.sql: ' || site || ' cites one work and its `followed` is empty; trace every work the newest one cites and write them there'
  FROM held WHERE present AND works = 1 AND coalesce(trim(followed), '') = ''
  UNION ALL
  SELECT 3, site, 'ledger/references.sql: ' || site || '''s newest work is narrower than the site, and the row names no anchor; cite the central statement it specialises as `anchor`, or state in `unanchored` that the citation window holds none'
  FROM held WHERE present AND scope = 'narrower' AND anchor IS NULL AND unanchored IS NULL
  UNION ALL
  SELECT 4, site, 'ledger/references.sql: ' || site || ' names `' || anchor || '` its anchor, and cites it as no `anchor`; give its key line the role `anchor`'
  FROM held h WHERE present AND crate <> 'corpus' AND anchor IS NOT NULL
    AND NOT EXISTS (SELECT 1 FROM cite c WHERE c.kind = 'cite' AND (c.crate, c.module, c.key, c.role) = (h.crate, h.module, h.anchor, 'anchor'))
  UNION ALL
  SELECT 5, c.location, c.location || ': ' || h.site || ' still cites `' || h.old || '`, the work the refresh replaced; delete the citation'
  FROM held h JOIN cite c ON (c.crate, c.module, c.key) = (h.crate, h.module, h.old)
  WHERE h.present AND c.kind IN ('cite', 'locator', 'corpus')
  UNION ALL
  SELECT 6, c.location, c.location || ': `' || c.key || '` is cited as ' || c.role || ' at ' || s.site
    || ', which the refresh records; give it the role the site takes from it, newest, dependency, anchor or exemplar'
  FROM sites s JOIN cite c ON (c.crate, c.module) = (s.crate, s.module)
  WHERE c.kind = 'cite' AND c.role IN ('lineage', 'background')
  UNION ALL
  SELECT 7, c.location, c.location || ': `' || c.key || '` is a bare locator at ' || s.site
    || ', which the refresh records; cite it by a key line with its role, or delete it'
  FROM sites s JOIN cite c ON (c.crate, c.module) = (s.crate, s.module)
  WHERE c.kind = 'locator'
)
ORDER BY rank, place, line;
