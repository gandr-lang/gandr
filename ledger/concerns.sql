PRAGMA foreign_keys=OFF;
BEGIN TRANSACTION;
CREATE TABLE concern(
  id        TEXT PRIMARY KEY CHECK(id GLOB '[a-z]*' AND id NOT GLOB '*[^a-z-]*'),
  name      TEXT NOT NULL,
  line      TEXT NOT NULL CHECK(line <> ''),
  interface TEXT CHECK(interface GLOB '[a-z]*::*[A-Z]*'),
  issue     TEXT NOT NULL CHECK(issue GLOB '#[0-9]*'),
  CHECK(instr(name || line, char(10)) = 0)
) WITHOUT ROWID;
INSERT INTO concern VALUES('fork','Fork','Work split across a pool: the checker states the trait and a driver hands it a pool.','core-checker::fork::Fork','#1250');
INSERT INTO concern VALUES('oracle','Oracle','A decision the kernel asks of a module that answers with evidence the kernel checks. A metaprogram stands as one: `Eq.generic`''s derived core is judged and readmitted as if written, so the derivation itself is never trusted.',NULL,'#313');
INSERT INTO concern VALUES('sharing','Sharing','A descent datum: positions, a coverage of which positions share, a compatibility, a gluing done once, and a certificate the kernel replays. A cell''s per-hole occurrence count is the size of one such coverage: the positions of its right side that share the subterm its left side matched at the hole. An effect theory''s law shares requests: the requests a scope''s subject makes in a run its left side covers, nothing but returns between them, are glued into its right side''s fewer, the law''s orientation the certificate the kernel replays with the theory and the handler''s check as a model the reason the gluing changes no answer.',NULL,'#2291');
CREATE TABLE descent(
  mechanism     TEXT PRIMARY KEY CHECK(mechanism GLOB '[a-z]*' AND mechanism NOT GLOB '*[^a-z-]*'),
  status        TEXT NOT NULL CHECK(status IN ('built','gated','banned')),
  positions     TEXT NOT NULL,
  cover         TEXT NOT NULL,
  compatibility TEXT NOT NULL,
  gluing        TEXT NOT NULL,
  certificate   TEXT NOT NULL,
  CHECK(instr(positions || cover || compatibility || gluing || certificate, char(10)) = 0)
) WITHOUT ROWID;
INSERT INTO descent VALUES('courant-leroy','built','comparison subproblems ordered by the wait graph','the memo''s keys with support edges','permutation equivalence of reduction choices: the trace monoid','one channel per key, one process per pair','the conversion trace');
INSERT INTO descent VALUES('hash-consing','banned','every subterm','syntactic identity','equality','a table','none: the degenerate coverage, asserted rather than computed');
INSERT INTO descent VALUES('incremental-memo','built','the decomposition''s parts, across edits','per-part data','interface agreement','the assembly','the memo''s keys');
INSERT INTO descent VALUES('spinal','gated','occurrences under a binder','the spine, each maximal rib a leg','the spinal calculus''s two permutation quotients','a leg evaluated once per configuration','the spinal catalogue and ladder trace');
INSERT INTO descent VALUES('superposition','built','members of a family indexed by guard points','the schema','agreement away from the guarded points, a member a guard vector','one schema check, rows by exact identity','the schema and its rows');
CREATE TABLE site(
  concern   TEXT NOT NULL REFERENCES concern(id),
  crate     TEXT NOT NULL CHECK(crate GLOB '[a-z]*-[a-z]*' AND crate NOT GLOB '*[^a-z0-9-]*'),
  module    TEXT NOT NULL CHECK(module NOT GLOB '*[^a-z0-9_:]*'),
  role      TEXT NOT NULL CHECK(role IN ('defines','implements','consumes')),
  mechanism TEXT REFERENCES descent(mechanism),
  line      TEXT NOT NULL CHECK(line <> '' AND instr(line, char(10)) = 0),
  PRIMARY KEY(concern, crate, module),
  CHECK((concern = 'sharing') = (mechanism IS NOT NULL))
) WITHOUT ROWID;
INSERT INTO site VALUES('fork','core-checker','fork','defines',NULL,'The `Fork` trait and `Serial`, the pool of one the checker runs on alone.');
INSERT INTO site VALUES('fork','surface-dispatcher','pool','implements',NULL,'`Pooled`, the driver-held pool a session hands the checker.');
INSERT INTO site VALUES('oracle','kernel-strata','level','implements',NULL,'The universe-level algebra in its always-canonical form.');
INSERT INTO site VALUES('oracle','kernel-strata','order','implements',NULL,'The order oracle, answering with evidence a validator recomputes.');
INSERT INTO site VALUES('sharing','core-incremental','','implements','incremental-memo','Incremental checking: validated resume and content-addressed checkpoints.');
INSERT INTO site VALUES('sharing','core-nbe','duplicate','implements','spinal','Spinal atomic duplication, refused by the policy until its differential lands.');
INSERT INTO site VALUES('sharing','core-nbe','machine','implements','courant-leroy','The lazy concurrent convertibility search and its memo.');
INSERT INTO site VALUES('sharing','core-nbe','overlay','implements','spinal','The overlay a spinal leg''s evaluation is shared through.');
INSERT INTO site VALUES('sharing','core-nbe','resharing','implements','courant-leroy','The memo''s resharing of a comparison already decided.');
INSERT INTO site VALUES('sharing','kernel-check-memo','','implements','incremental-memo','The check-memo seam a checker consults.');
INSERT INTO site VALUES('sharing','kernel-core','admission','implements','superposition','Guarded-superposition admission: one schema check for a family of members.');
COMMIT;
