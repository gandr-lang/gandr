PRAGMA foreign_keys=OFF;
BEGIN TRANSACTION;
CREATE TABLE shared(
  -- The source that declares the field: a source of a kernel crate or of the
  -- fork crate, outside the tests.
  file  TEXT NOT NULL CONSTRAINT "file is a source of a kernel crate or of the fork crate" CHECK((file GLOB 'crates/kernel-*/src/*.rs' OR file GLOB 'crates/core-fork/src/*.rs') AND file NOT GLOB '*[^A-Za-z0-9_/.-]*'),
  -- The field as `.config/shared/hits.jq` reads it: `<Type>.<field>`, a tuple
  -- variant's `<Type>.<Variant>`, or a tuple struct's `<Type>.0`.
  name  TEXT NOT NULL CONSTRAINT "name is a type and a field" CHECK(name GLOB '[A-Z]*.[A-Za-z0-9_]*' AND name NOT GLOB '*[^A-Za-z0-9_.]*' AND name NOT GLOB '*.*.*'),
  -- What a write does to what the field shares once a freeze, a fork or a
  -- hand-on clones it, the first that holds:
  --   chunked                a write copies at most one chunk of a bound size
  --                          and shares the rest;
  --   layered                a fork adds a layer, a read walks the layers, and
  --                          a compaction keeps them few;
  --   copied whole           a write copies all that the field shares;
  --   grows with the module  no write copies it, but what each clone, check or
  --                          join holds or reads grows with the module;
  --   read only              no write comes after the share: a payload that its
  --                          node writes once, a source, or a token of a count.
  class TEXT NOT NULL CONSTRAINT "class is chunked, layered, copied whole, grows with the module or read only" CHECK(class IN ('chunked', 'layered', 'copied whole', 'grows with the module', 'read only')),
  -- The issue whose unit moves a copied whole or a grows with the module row
  -- to chunked or to layered; NULL for every other class.
  unit  TEXT CONSTRAINT "unit is an issue number" CHECK(unit GLOB '#[1-9]*' AND unit NOT GLOB '#*[^0-9]*'),
  -- Why the row holds its class, in one sentence.
  why   TEXT NOT NULL CONSTRAINT "why is one sentence on one line: a capital first, a full stop last" CHECK(why GLOB '[A-Z]*.' AND instr(why, char(10)) = 0),
  CONSTRAINT "a copied whole or a grows with the module row names its unit, and no other row names one" CHECK((class IN ('copied whole', 'grows with the module')) = (unit IS NOT NULL)),
  PRIMARY KEY(file, name)
) WITHOUT ROWID;
INSERT INTO shared VALUES('crates/kernel-check-memo/src/overlay.rs','ForkPoint.open','read only',NULL,'A token whose count says that a fork point is open, which no write changes.');
INSERT INTO shared VALUES('crates/kernel-check-memo/src/overlay.rs','Frozen.memo','layered',NULL,'A frozen layer of the memo, which each fork shares and a compaction folds into the layer below, so a read walks the open layers.');
INSERT INTO shared VALUES('crates/kernel-check-memo/src/overlay.rs','OverlaidMemo.point','read only',NULL,'The token of the fork point that the overlay holds open, which no write changes.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/encoding.rs','LayerView.layer','layered',NULL,'A layer of the content table''s placements, which each fork shares and a compaction absorbs into the layer below, so a read walks the open layers.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/env.rs','Entries.log','chunked',NULL,'A write copies the log''s shell of a bound size, and its family, its maps and its presented table each hold a row of their own.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/env.rs','Entries.spares','grows with the module','#7406','Each spare support holds one stamp for each position of the module.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/env.rs','Entries.support','grows with the module','#7406','The support of the running check holds one stamp for each position of the module, which its reads write in place.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/fork.rs','SharedFork.0','read only',NULL,'A handle to the pool that runs the forked goals, which no write changes.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/presented.rs','Presentations.table','copied whole','#7407','A write beside an open view copies the map of presented types and the map of words whole.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/presented.rs','PresentedType.arities','read only',NULL,'The field counts of a presented type, which its admission writes once.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/presented.rs','PresentedType.sort_arities','read only',NULL,'The field counts of a presented type''s sort, which its admission writes once.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/support.rs','Owed.0','read only',NULL,'The keys that a formation owes, which its record writes once.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/verdict.rs','Verdicts.chain','copied whole','#7408','The first key of a handed-on state copies the encoder''s own maps whole, and they grow with the admissions since its base.');
INSERT INTO shared VALUES('crates/kernel-core-base/src/verdict.rs','Verdicts.source','read only',NULL,'The source of the recorded verdicts, which no write changes.');
INSERT INTO shared VALUES('crates/kernel-core/src/check.rs','Frame.dialogues','read only',NULL,'The dialogues of a frame''s goal, which its term writes once, so a frame holds a count and copies none.');
INSERT INTO shared VALUES('crates/kernel-core/src/environment.rs','Environment.commits','copied whole','#7404','A write while a handed-on state holds the commit log copies it whole, with its rows for each admitted position.');
INSERT INTO shared VALUES('crates/kernel-core/src/environment.rs','Names.shared','copied whole','#4369','The first check of a handed-on environment copies the shared session''s content table and kept memo whole.');
INSERT INTO shared VALUES('crates/kernel-term/src/arena.rs','Family.frozen','copied whole','#7405','A write or a freeze beside a clone copies the list of chunks whole, one pointer for each 64 nodes.');
INSERT INTO shared VALUES('crates/kernel-term/src/arena.rs','Family.tail','chunked',NULL,'A write copies one segment of fewer than 64 nodes, and the tail keeps at most five segments.');
INSERT INTO shared VALUES('crates/kernel-term/src/arena.rs','TermArena.unrelated','read only',NULL,'The empty dialogues that each unrelated node shares, which no write changes.');
INSERT INTO shared VALUES('crates/kernel-term/src/chunked.rs','Chunk.entries','chunked',NULL,'A write copies the one chunk of at most 64 entries that it writes.');
INSERT INTO shared VALUES('crates/kernel-term/src/chunked.rs','ChunkedMap.chunks','copied whole','#7405','A write beside a clone copies the list of chunks whole, one entry for each chunk of the map.');
INSERT INTO shared VALUES('crates/kernel-term/src/encode.rs','EncodedPrefix.assigned','read only',NULL,'The frozen assignments of an encoded prefix, which each encoding that resumes it reads and none writes.');
INSERT INTO shared VALUES('crates/kernel-term/src/encode.rs','Interner.base','layered',NULL,'The frozen assignments that an interner continues, below the maps of what it assigns itself.');
INSERT INTO shared VALUES('crates/kernel-term/src/encode.rs','Places.0','read only',NULL,'The admission place of each position, which its encoding writes once.');
INSERT INTO shared VALUES('crates/kernel-term/src/operation_rules.rs','OperationRules.0','read only',NULL,'The rules of an operation, which its declaration writes once.');
INSERT INTO shared VALUES('crates/kernel-term/src/presented.rs','Presentation.cells','read only',NULL,'The free cells of a presentation, which its declaration writes once.');
INSERT INTO shared VALUES('crates/kernel-term/src/presented.rs','Presentation.rules','read only',NULL,'The rules of a presentation, which its declaration writes once.');
INSERT INTO shared VALUES('crates/kernel-term/src/term.rs','Value.dialogues','read only',NULL,'A payload of a value node, which its node writes once.');
INSERT INTO shared VALUES('crates/kernel-term/src/term.rs','Value.evidence','read only',NULL,'A payload of a value node, which its node writes once.');
INSERT INTO shared VALUES('crates/kernel-term/src/term.rs','Value.program','read only',NULL,'A payload of a value node, which its node writes once.');
INSERT INTO shared VALUES('crates/kernel-term/src/term.rs','Value.steps','read only',NULL,'A payload of a value node, which its node writes once.');
INSERT INTO shared VALUES('crates/kernel-term/src/types.rs','ValueType.graph','read only',NULL,'A payload of a value type node, which its node writes once.');
CREATE TABLE stated(
  -- The source that declares the item.
  file    TEXT NOT NULL CONSTRAINT "file is a source of a crate" CHECK(file GLOB 'crates/*/src/*.rs' AND file NOT GLOB '*[^A-Za-z0-9_/.-]*'),
  -- The item: a struct, an enum, a union, a type, a constant or a static that
  -- the file declares.
  item    TEXT NOT NULL CONSTRAINT "item is an identifier" CHECK(item GLOB '[A-Z]*' AND item NOT GLOB '*[^A-Za-z0-9_]*'),
  -- What a device needs of the item that no field of the pattern shows:
  --   width   an id that a device holds, `usize` today, which takes a stated
  --           width;
  --   region  a structure whose memory a device bounds, which takes the
  --           arena's region as its allocator;
  --   window  a bound of the schedule on the open checks.
  concern TEXT NOT NULL CONSTRAINT "concern is width, region or window" CHECK(concern IN ('width', 'region', 'window')),
  -- The issue whose unit meets the concern; NULL for a window that stays the
  -- capacity of the lanes that exist, with its reason at the window.
  unit    TEXT CONSTRAINT "unit is an issue number" CHECK(unit GLOB '#[1-9]*' AND unit NOT GLOB '#*[^0-9]*'),
  -- Why the row holds, in one sentence.
  why     TEXT NOT NULL CONSTRAINT "why is one sentence on one line: a capital first, a full stop last" CHECK(why GLOB '[A-Z]*.' AND instr(why, char(10)) = 0),
  CONSTRAINT "a width or a region row names its unit" CHECK(concern = 'window' OR unit IS NOT NULL),
  PRIMARY KEY(file, item, concern)
) WITHOUT ROWID;
INSERT INTO stated VALUES('crates/core-term/src/definition.rs','ScopeId','width','#7409','A scope''s id, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/core-term/src/session.rs','RecursionIndex','width','#7409','A recursion''s id, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/kernel-core/src/higher_field.rs','HigherId','width','#7409','A higher field''s id, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/kernel-term/src/presented.rs','CellIndex','width','#7409','A free cell''s id, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/kernel-term/src/presented.rs','RuleIndex','width','#7409','A presented rule''s id, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/kernel-term/src/term.rs','ConstantIndex','width','#7409','A constant''s admission position, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/kernel-term/src/term.rs','ConstructorTag','width','#7409','A constructor''s tag, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/kernel-term/src/term.rs','SourceRank','width','#7409','A declaration''s rank in its source, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/kernel-term/src/term.rs','StageId','width','#7409','A stage''s id, which a device holds as a `usize`.');
INSERT INTO stated VALUES('crates/surface-dispatcher/src/pool/lane.rs','DEPTH','window','#7410','The capacity of each lane''s rings, and the schedule''s window of one more release for each lane, which bound the open checks with a reason and no measure.');
COMMIT;
