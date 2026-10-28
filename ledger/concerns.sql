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
INSERT INTO concern VALUES('oracle','Oracle','A decision the kernel asks of a module that answers with evidence the kernel checks. A metaprogram stands as one: `Eq.generic`''s derived core is judged and readmitted as if written, so the derivation itself is never trusted. A foreign semantics stands as one: a Rust function''s THIR, written as data, has each weakest precondition computed by a fold the kernel replays, so only the data''s fidelity to rustc is trusted (`rust-semantics-thir`). A trusted kernel''s receipt stands as one: a recorded verdict is believed on a signature the kernel verifies, under the operator''s policy, so only the signer is trusted, and `--recheck` re-derives every verdict (`attested-verdict-cache`).',NULL,'#313');
INSERT INTO concern VALUES('sharing','Sharing','A descent datum: positions, a coverage of which positions share, a compatibility, a gluing done once, and a certificate the kernel replays. A cell''s per-hole occurrence count is the size of one such coverage: the positions of its right side that share the subterm its left side matched at the hole. An effect theory''s law shares requests: the requests a scope''s subject makes in a run its left side covers, nothing but returns between them, are glued into its right side''s fewer, the law''s orientation the certificate the kernel replays with the theory and the handler''s check as a model the reason the gluing changes no answer. A kernel memo key names a plain definition''s reference by its declared type and body, not its admission position, so two environments that admitted the same declarations in another order build one key for one question. Sharing points are local or global: a location-addressable heap shares a cell by its index, a wrapping indirection inside one world, and the content-addressable store shares a chunk by its digest, a boundary any world dereferences; what a duplication costs is the boundary and alias classification''s to say.',NULL,'#2291');
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
INSERT INTO descent VALUES('cell-holes','built','a cell''s right-side occurrences of one hole','the subterm its left side matched at the hole','one match per hole, the same subterm at each occurrence','the match bound once and written at each occurrence','none: the count is the hole''s Lipschitz constant, which the derivation reports and refuses nowhere');
INSERT INTO descent VALUES('content-chunks','built','a value''s subtrees at its boundary constructors','the chunk digest over canonical bytes','deep equality of the chunk''s value','one chunk stored per digest, read by every pointer to it, in any world','the manifest''s boundary and alias classification and the deep-equality round trip');
INSERT INTO descent VALUES('courant-leroy','built','comparison subproblems ordered by the wait graph','the memo''s keys with support edges','permutation equivalence of reduction choices: the trace monoid','one channel per key, one process per pair','the conversion trace');
INSERT INTO descent VALUES('effect-laws','built','the requests a scope''s subject makes in one run','an instance of a law''s oriented left side','nothing but returns between the requests, each payload checked at its type','the right side''s fewer requests, each dropped request replaced by returning its reply','the law''s orientation, replayed by the kernel with the theory; the handler''s check as a model is why the gluing changes no answer');
INSERT INTO descent VALUES('exact-records','built','the one-level records an arena holds: a tag, a payload and the children''s ids','exact syntactic identity of the record','equality of every field, confirmed by comparison and never by a hash','one id per record, read wherever the record recurs','none: an id decides syntactic identity and nothing more, computed rather than asserted, so this is not hash-consing');
INSERT INTO descent VALUES('hash-consing','banned','every subterm','syntactic identity','equality','a table','none: the degenerate coverage, asserted rather than computed');
INSERT INTO descent VALUES('heap-reuse','built','a run''s heap cells','the references to one cell by its index, counted','one value per index, an index never recycled','one cell read through every reference; a cell whose count is one rebuilt in place by the constructor its match pairs with','none: the reference count, local to the run and never replayed');
INSERT INTO descent VALUES('incremental-memo','built','the decomposition''s parts, across edits','per-part data','interface agreement','the assembly','the memo''s keys');
INSERT INTO descent VALUES('record-leaves','built','a sorted record sequence''s runs, cut between records','the node hash over a leaf''s canonical encoding','equal runs cut alike, a boundary a function of the records alone','one node per hash in the block store, read by every root whose leaves reach it','none: a membership, absence or range proof checked against the root shows what a root commits, never that a record is valid');
INSERT INTO descent VALUES('spinal','built','occurrences under a binder','the spine, each maximal rib a leg','the spinal calculus''s two permutation quotients','a leg evaluated once per configuration','the property against the copying stance, and the conversion trace a traced verdict records');
INSERT INTO descent VALUES('subterm-table','built','every subterm of an exported artifact','structural equality, computed bottom-up by the writer','equality of tag, child indices and inline payload','one table entry, referenced by every parent','the reader''s re-encode-compare: the writer is untrusted and feeds no judgement, so this is not hash-consing');
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
INSERT INTO site VALUES('fork','workflow-lane-budget','github','implements',NULL,'`read_all`: a report''s `gh` reads split across scoped threads of its own, outside the checker''s `Fork` pool.');
INSERT INTO site VALUES('oracle','kernel-core','verdict','defines',NULL,'The trusted receipt: a recorded verdict believed on a signature the kernel verifies, under the operator''s policy.');
INSERT INTO site VALUES('oracle','kernel-strata','level','implements',NULL,'The universe-level algebra in its always-canonical form.');
INSERT INTO site VALUES('oracle','kernel-strata','order','implements',NULL,'The order oracle, answering with evidence a validator recomputes.');
INSERT INTO site VALUES('sharing','core-checker','staging','consumes','exact-records','The merge: each worker''s classifiers and terms interned into the program''s arena in source order, a held one found and compared, only a miss appended.');
INSERT INTO site VALUES('sharing','core-checker','template','implements','superposition','Guarded families of staging equations: one template drafted and priced for a family of one producer''s equations, ordinary replay the authority.');
INSERT INTO site VALUES('sharing','core-incremental','','implements','incremental-memo','Incremental checking: validated resume and content-addressed checkpoints.');
INSERT INTO site VALUES('sharing','core-nbe','duplicate','implements','spinal','Spinal atomic duplication, admitted under the testing stance on its agreement with the copying stance.');
INSERT INTO site VALUES('sharing','core-nbe','eval','implements','spinal','The machine''s leg sharing: a leg''s first weak head in one configuration remembered, and taken by every later occurrence read in it.');
INSERT INTO site VALUES('sharing','core-nbe','machine','implements','courant-leroy','The lazy concurrent convertibility search and its memo.');
INSERT INTO site VALUES('sharing','core-nbe','overlay','implements','spinal','The overlay a spinal leg''s evaluation is shared through.');
INSERT INTO site VALUES('sharing','core-nbe','resharing','implements','courant-leroy','The memo''s resharing of a comparison already decided.');
INSERT INTO site VALUES('sharing','core-nbe','traced','implements','spinal','The spinal stance on the certifying path: a root evaluated through its own duplicate, its shared legs handed to the machine, its conversions recorded for replay.');
INSERT INTO site VALUES('sharing','core-term','handler::subject','implements','effect-laws','A theory''s laws as rewrites of a scope''s subject: a run of requests a law''s left side covers glued into its right side''s fewer before the scope runs.');
INSERT INTO site VALUES('sharing','kernel-check-memo','','implements','incremental-memo','The check-memo seam a checker consults.');
INSERT INTO site VALUES('sharing','kernel-conversion-trace','','defines','courant-leroy','The conversion-decision seam: the trace an engine emits for a comparison it decided once, which the kernel replays without search.');
INSERT INTO site VALUES('sharing','kernel-core','admission','implements','superposition','Guarded-superposition admission: one schema check for a family of members.');
INSERT INTO site VALUES('sharing','kernel-core','admission::content','implements','exact-records','The consumer-owned arena a binding''s rows look their records up in, an id deciding syntactic identity with no hash premise.');
INSERT INTO site VALUES('sharing','kernel-core','encoding','implements','incremental-memo','The memo key, naming a plain definition''s reference by its content, over a content table that names each node once for its environment''s life.');
INSERT INTO site VALUES('sharing','kernel-core','replay','implements','spinal','The replay''s weak-head reduction under an environment: the value a binder stands for held once in a cell for every occurrence and closed once at the unload, admitted on its agreement with the substituting reduction.');
INSERT INTO site VALUES('sharing','kernel-core','support','implements','incremental-memo','The support of one node check: the complete input a memo key names, so equal supports force equal answers.');
INSERT INTO site VALUES('sharing','kernel-core','verdict','implements','incremental-memo','The verdict key, chaining the kernel''s build and each admitted declaration, read by every later run over the same prefix.');
INSERT INTO site VALUES('sharing','kernel-term','decode','consumes','subterm-table','The reader''s re-encode-compare: an artifact accepted only when the maximal-sharing encoder reproduces its bytes.');
INSERT INTO site VALUES('sharing','kernel-term','encode','implements','subterm-table','The writer''s subterm table: nodes interned bottom-up by their entry bytes, two structurally equal subterms one entry across declarations.');
INSERT INTO site VALUES('sharing','kernel-term','stage','implements','exact-records','The staging arena: classifiers and terms interned by exact syntactic equality, a held descriptor found by hash and confirmed by comparison.');
INSERT INTO site VALUES('sharing','kernel-term','support','implements','incremental-memo','The support column every node carries: the free indices a memo key reads off a node without walking its term.');
INSERT INTO site VALUES('sharing','runtime-emitter','crossing','consumes','content-chunks','`crossing::commit`: a store''s value written to the value plane however the store shares it, a subtree written twice stored once by content; `crossing::deref` lays a tree.');
INSERT INTO site VALUES('sharing','runtime-emitter','lower','implements','heap-reuse','The reuse token: a scrutinee whose fields an arm took is rebuilt in place by the constructor the ownership reading pairs with it.');
INSERT INTO site VALUES('sharing','runtime-emitter','world','consumes','content-chunks','A migration''s captures and answer crossing by content through the process''s one chunk store; `arrive` runs one another host shipped here.');
INSERT INTO site VALUES('sharing','runtime-net','chunks','consumes','content-chunks','The chunk wire: a fetch naming the values its asker holds carries only the chunks their closures lack, so a chunk two sends share crosses once.');
INSERT INTO site VALUES('sharing','storage-artifact','record::value','implements','content-chunks','A kernel artifact on the value plane: each declaration segment''s constructor holds the one before it, so an edit to a declaration shares every chunk before it, across edits and across the packages one store holds.');
INSERT INTO site VALUES('sharing','storage-chunker','typed','implements','content-chunks','The typed scanner: a value''s chunk cut where a residue divides kappa or the cap fires, at a boundary constructor''s exit.');
INSERT INTO site VALUES('sharing','storage-records','','implements','record-leaves','The keyed plane''s tree: a sorted record sequence cut into leaves at content-defined boundaries, each node stored once by its hash.');
INSERT INTO site VALUES('sharing','storage-values','commit','defines','content-chunks','`cam_commit`: a value cut at its boundary constructors into chunks named by digest, the boundary and alias classification deciding where a cut falls.');
INSERT INTO site VALUES('sharing','surface-dispatcher','evaluate::worlds','consumes','content-chunks','A migration''s captures fetched by the host that runs it, skipping each it holds whole and naming every value it holds, so a value it made itself crosses back to it as nothing.');
INSERT INTO site VALUES('sharing','surface-dispatcher','verdicts','consumes','incremental-memo','The verdict cache a driver installs: each readmission recalls the receipt its verdict key names, and one that crossed whole keeps the kernel''s.');
INSERT INTO site VALUES('sharing','surface-lowering','table','implements','incremental-memo','A suspended lowering''s per-node cells, shared behind one `Arc` with every lowering resumed from it, a cell copied only when written.');
INSERT INTO site VALUES('sharing','surface-parser','meld','implements','incremental-memo','The resumable melder: a checkpoint at a declaration boundary, resumed to parse what follows as a fresh parse would.');
INSERT INTO site VALUES('sharing','surface-session','session','consumes','incremental-memo','Each revision offered to the incremental checker, which adopts every checkpoint that still answers and persists the set.');
INSERT INTO site VALUES('sharing','theory-cell-complexes','sequent','consumes','cell-holes','A cell''s per-hole contractum use: how many times a step writes the subterm its left side matched at each hole, the size of that hole''s coverage.');
INSERT INTO site VALUES('sharing','theory-deep-inference','template','implements','superposition','Guarded templates: one certificate for a family firing the same cells at the same positions, an arm per distinct member subterm, each arm''s inheritance check memoized.');
COMMIT;
