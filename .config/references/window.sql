-- The citation window: a cited work older than the cutoff year, at a site the
-- allowlist does not cover, is refused. Run by `check:references` over a
-- database holding
--   cite    the lines `cites.awk` prints over the crates and the corpus;
--   work    the references ledger's years and newer works;
--   allow   the allowlist `window.jq` reads from `window.toml`: kind, crate,
--           subject, site, work, why and the entry as written;
--   window  the cutoff year, one row.
-- It prints one finding a line, in a fixed order, and nothing when the
-- citations keep the window.
--
-- A work's year is its `work` row's, else the year its citation key carries
-- (`Author-YYYY-…`), else its arXiv identifier's. A crate's site is its crate
-- and module, written `crate::module`, or the crate alone at its root; a
-- corpus source's is its path, and its subject the directory holding it.

CREATE TEMP VIEW cited AS
SELECT key, location,
  CASE kind WHEN 'corpus' THEN 'corpus/' || module
    ELSE crate || CASE module WHEN '' THEN '' ELSE '::' || module END END AS site,
  CASE kind WHEN 'corpus' THEN NULL ELSE crate END AS crate,
  CASE kind WHEN 'corpus' THEN rtrim(rtrim(module, replace(module, '/', '')), '/') END AS subject
FROM cite
WHERE kind IN ('cite', 'locator', 'corpus') AND key NOT GLOB 'vault:*';

CREATE TEMP VIEW dated AS
SELECT c.key, c.location, c.site, c.crate, c.subject, w.newer,
  coalesce(w.year, CASE
    WHEN c.key GLOB 'arXiv:[0-9][0-9][0-9][0-9].*' THEN 2000 + CAST(substr(c.key, 7, 2) AS INTEGER)
    WHEN c.key GLOB 'arXiv:*/[0-9][0-9]*' THEN
      CASE WHEN CAST(substr(c.key, instr(c.key, '/') + 1, 2) AS INTEGER) >= 90 THEN 1900 ELSE 2000 END
        + CAST(substr(c.key, instr(c.key, '/') + 1, 2) AS INTEGER)
    WHEN c.key NOT GLOB 'doi:*' AND c.key NOT GLOB 'arXiv:*'
      AND substr(c.key, instr(c.key, '-')) GLOB '-[12][0-9][0-9][0-9]-*'
      THEN CAST(substr(c.key, instr(c.key, '-') + 1, 4) AS INTEGER)
  END) AS year
FROM cited c LEFT JOIN work w USING (key);

CREATE TEMP VIEW old AS
SELECT d.* FROM dated d, window WHERE d.year < window.cutoff;

CREATE TEMP VIEW covered AS
SELECT o.location, o.key, a.entry
FROM old o JOIN allow a ON (a.kind = 'crate' AND a.crate = o.crate)
  OR (a.kind = 'corpus' AND a.subject = o.subject)
  OR (a.kind = 'site' AND a.site = o.site AND a.work = o.key);

SELECT line FROM (
  SELECT 0 AS rank, entry AS place, 'window.toml: ' || entry || ' ' || why AS line
  FROM allow WHERE kind = 'refused'
  UNION ALL
  SELECT 1, location, location || ': `' || key || '` states no year: add its row to `work` in ledger/references.sql, the year the work appeared'
  FROM dated WHERE year IS NULL
  UNION ALL
  SELECT 2, o.location, o.location || ': `' || o.key || '` appeared in ' || o.year || ', before the citation window opens in ' || window.cutoff
    || '; cite the newest work that states what ' || o.site || ' builds'
    || coalesce(', such as `' || o.newer || '`', '')
    || ', or allow the site in .config/references/window.toml with why no newer work states it'
  FROM old o, window WHERE NOT EXISTS (SELECT 1 FROM covered c WHERE (c.location, c.key) = (o.location, o.key))
  UNION ALL
  SELECT 3, a.entry, 'window.toml: ' || a.entry || ' covers no citation older than ' || window.cutoff || '; delete it'
  FROM allow a, window WHERE a.kind <> 'refused' AND NOT EXISTS (SELECT 1 FROM covered c WHERE c.entry = a.entry)
)
ORDER BY rank, place, line;
