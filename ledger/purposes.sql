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
COMMIT;
