PRAGMA foreign_keys=OFF;
BEGIN TRANSACTION;
CREATE TABLE purpose(
  -- The crate's directory under crates/.
  crate    TEXT NOT NULL CONSTRAINT "crate is a directory under crates/" CHECK(crate GLOB '[a-z]*-[a-z]*' AND crate NOT GLOB '*[^a-z0-9-]*'),
  -- The entry's path as `mise run purposes:list <crate>` prints it: empty for
  -- the crate row, a module's path, an item's path at the module defining it.
  path     TEXT NOT NULL CONSTRAINT "path is segments joined by ::, empty for the crate row" CHECK(path NOT GLOB '*[^A-Za-z0-9_:]*'),
  -- `crate`, `module`, or the item's rustdoc kind, as the listing prints it.
  kind     TEXT NOT NULL CONSTRAINT "kind is crate, module, struct, union, enum, function, type_alias, constant, static, trait, trait_alias, extern_type, macro, proc_attribute or proc_derive" CHECK(kind IN ('crate', 'module', 'struct', 'union', 'enum', 'function', 'type_alias', 'constant', 'static', 'trait', 'trait_alias', 'extern_type', 'macro', 'proc_attribute', 'proc_derive')),
  -- What the entry is for, read from its code, in one sentence. A crate row's
  -- names the crate's layer and its wall.
  purpose  TEXT NOT NULL CONSTRAINT "purpose is one sentence on one line: a capital first, a full stop last" CHECK(purpose GLOB '[A-Z]*.' AND instr(purpose, char(10)) = 0),
  -- The concerns the entry carries: keys of ledger/concerns.sql joined by
  -- single spaces, each once; NULL for none.
  concerns TEXT CONSTRAINT "concerns is NULL or keys of ledger/concerns.sql joined by single spaces" CHECK(concerns GLOB '[a-z]*[a-z]' AND concerns NOT GLOB '*[^a-z -]*' AND concerns NOT GLOB '*  *'),
  -- The entry's name, the first verdict that holds:
  --   misleading  promises something the entry does not do;
  --   collides    names a different thing elsewhere in the workspace, or an
  --               overloaded term;
  --   vague       tells a reader nothing to act on: a Data, Info, Manager,
  --               Helper or Util name, a bare generic word;
  --   mechanism   names how the entry works rather than what it is for;
  --   fits        says what the entry is for, in the vocabulary of the
  --               surface that owns it.
  naming   TEXT NOT NULL CONSTRAINT "naming is fits, mechanism, vague, collides or misleading" CHECK(naming IN ('fits', 'mechanism', 'vague', 'collides', 'misleading')),
  -- The entry's own documentation, an item's `///`, a module's `//!`, the
  -- crate root's `//!` with the crate's README, the first verdict that holds:
  --   inaccurate  states what the code does not do, or leaves out a failure,
  --               a panic or an effect it has;
  --   record      carries a decision record, history or state prose, or an
  --               issue number as an origin;
  --   unplaced    a crate row's: its lead paragraph leaves out the crate's
  --               layer (its category in crates/README.md) or its wall
  --               (integrity, validity, or neither);
  --   verbose     says more than the entry needs: restates its code, a
  --               workspace rule or another entry's documentation;
  --   sound       none of these.
  doc      TEXT NOT NULL CONSTRAINT "doc is sound, verbose, unplaced, record or inaccurate" CHECK(doc IN ('sound', 'verbose', 'unplaced', 'record', 'inaccurate')),
  -- Each defect the two verdicts stand for, a sentence each, on one line;
  -- NULL when the name fits and the documentation is sound.
  finding  TEXT CONSTRAINT "finding is sentences on one line, a full stop last" CHECK(finding GLOB '[A-Z`]*.' AND instr(finding, char(10)) = 0),
  PRIMARY KEY(crate, path, kind),
  CONSTRAINT "the crate row alone has the empty path" CHECK((kind = 'crate') = (path = '')),
  CONSTRAINT "unplaced judges a crate row" CHECK(doc <> 'unplaced' OR kind = 'crate'),
  CONSTRAINT "a finding is written exactly when naming is not fits or doc is not sound" CHECK((finding IS NULL) = (naming = 'fits' AND doc = 'sound'))
) WITHOUT ROWID;
INSERT INTO purpose VALUES('kernel-check-memo','','crate','Lets a checker skip a goal it already decided in this process: the kernel layer''s check-memo seam, inside the validity wall, generic in support and outcome so it names no kernel type.','sharing','fits','unplaced','The lead paragraph names neither the kernel layer nor the validity wall. The # Boundaries hit paragraph repeats CheckMemo''s, the #[non_exhaustive] paragraph restates the workspace rule rather than this crate''s code, and # Witnesses narrates the specification facade''s evaluation order.');
INSERT INTO purpose VALUES('kernel-check-memo','accounting','module','Counts a memo''s entries per plane and in total with checked arithmetic, so a measurement never reads a wrapped count.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','accounting::MemoBucketCount','struct','Counts the distinct digests a memo''s entries are bucketed under; read against the entry count, a smaller number shows a collision.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','accounting::MemoEntryCount','struct','Counts a memo''s entries on one plane or across all, advanced only by a successor that refuses at the ceiling.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','accounting::MemoError','enum','Refuses a recording whose entry count is at its ceiling, the one way a memo fails.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','digest','module','Holds the content digest that picks a memo bucket and the agreement verdict that decides within it.','sharing','fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','digest::ContentAgreement','enum','Says whether two supports have the same content, the verdict a memo serves a hit on.','sharing','fits','inaccurate','Claims a memo implementation that never consults it cannot type check; `NullMemo` never does, and nothing in `CheckMemo` obliges a call to `MemoKey::agreement`.');
INSERT INTO purpose VALUES('kernel-check-memo','digest::ContentDigest','struct','Carries a support''s two-word content digest, which picks a memo bucket and never decides agreement.','sharing','fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','digest::DigestWord','struct','Carries one opaque 64-bit word of a content digest, ordered by its raw value.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','key','module','Holds what a consumer''s support supplies to key a memo.','sharing','fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','key::MemoKey','trait','States what a support supplies to key a memo: its accounting plane, its content digest and the agreement that decides.','sharing','fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','memo','module','Holds the seam and its two memos, the one that never answers and the one that stores.','sharing','fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','memo::CheckMemo','trait','Lets a checker recall an outcome it already computed in this process for an agreeing support and record a new one, its activity known at compile time.','sharing','fits','record','Grounds the in-process lifetime on no kernel-checked support discipline existing, state prose that goes stale when one lands, and calls that the two-wall rule, which is not the integrity and validity walls the kernel names. Its hit paragraph is repeated in the crate root''s # Boundaries.');
INSERT INTO purpose VALUES('kernel-check-memo','memo::MemoActivity','enum','Says at compile time whether a memo ever answers, so the branch around an inactive memo folds away.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','memo::MemoHit','struct','Hands back a recalled outcome borrowed together with the support it was recorded under, for pointwise adoption.','sharing','fits','inaccurate','Says a support is an output of the judgement rather than a scan beside it; `kernel-core` builds each support by a reach walk beside the check (`NodeSupport::build`).');
INSERT INTO purpose VALUES('kernel-check-memo','memo::MemoRecord','enum','Reports what a recording did: stored a fresh entry, replaced an agreeing entry''s outcome, or stored nothing.',NULL,'misleading','sound','Reads as a record the memo holds; it is what `remember` did, which a name such as `Remembered` says.');
INSERT INTO purpose VALUES('kernel-check-memo','memo::NullMemo','struct','Stands for the memoless path as a type parameter: it never answers, never counts, and compiles to the code with no memo.','sharing','fits','sound',NULL);
INSERT INTO purpose VALUES('kernel-check-memo','memo::OrderedMemo','struct','Stores outcomes by support: buckets them by content digest in ordered maps, decides within a bucket by agreement, and counts entries per plane.','sharing','mechanism','verbose','Named for its ordered maps, a mechanism a hashed store would replace, rather than for being the memo that stores. Its first-entry-inline paragraph repeats the private `Bucket`''s documentation and the crate root''s.');
COMMIT;
