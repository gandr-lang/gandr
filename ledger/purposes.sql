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
INSERT INTO purpose VALUES('core-checker','access::AccessDefect','enum','How a held value or a view broke the access discipline.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::ArtifactAudit','struct','What a readmitted artifact rests on: the union of its declarations'' audits.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::Crossed','struct','The environment once the leading declarations crossed, beside the declarations that crossed and their boundary.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::LeadingCount','struct','Counts the leading declarations a readmission crosses before the rest.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::Outcome','enum','What became of one declaration at the kernel boundary.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::Readmission','struct','A module''s readmission: the kernel environment it built, one outcome per declaration, the artifact''s audit, and the declarations the kernel admitted.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::Readmitted','struct','One declaration''s outcome, beside the position and origin the judgement echoed and the certificates its erasure replayed.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::Readmitting','type_alias','The declarations a readmitting run crossed before it, as a polled readmission beside what retired it.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::Refusal','enum','Whose fact a readmission''s refusal records.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::Replayed','struct','One certificate the kernel replayed for a declaration: what its step unfolded, the content of the instance it fired at, and the kernel''s verdict on its trace.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::readmit','function','Readmits a module''s report to the kernel.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::readmit_resuming','function','Readmits a module''s report, resuming at the boundary it crossed.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','bridge::readmit_retiring','function','Readmits a module''s report, resuming at the boundary it crossed and polling a retirement.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','capability::Grants','enum','The authority the host grants a module''s held capabilities at the checker''s entry.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','capability::HostGrant','struct','The host operations a run grants and the entry it enters every declaration at, by name.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','codata::CodataFault','enum','Why a codata declaration or application is refused.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','codata::form_signature','function','Checks a codata declaration''s kind, parameter telescope and observations before admission.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','codata::kind_level','function','Reads a codata kind''s computation-universe level.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','codata::read','function','Reads a codata application''s observations as one lazy product.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Certificate','struct','The normaliser''s certificate that a code converts to the reduct of one step at its head.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::CodeDefinitions','struct','The definitions a code may unfold, in admission order.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Derivation','enum','How the kernel re-derives a certified step.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::EndpointRelation','struct','The normaliser''s reading of one pair of path endpoints a type conversion met: the derivation relating the left endpoint to the right.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Evaluation','struct','The normaliser''s reading of one closed evaluation claim.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Lift','struct','A code checked at a universe above its own level: the readmission writes the kernel''s explicit lift where it stands.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::OpenBinders','struct','How many binders a claim stands under, each read as a rigid variable.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Reading','enum','The normaliser''s reading of one closed claim, returning or stuck.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Reduction','struct','One step of reduction at a code''s head: what it unfolds, the code it fires at and the reduct, minted.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Reflexivity','struct','The normaliser''s reading of one reflexivity: the derivation relating its point to each endpoint of the path type it was checked against.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Stalled','struct','The normaliser''s reading of one closed claim whose normal form does not return.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','code::Unfolded','enum','What one certified step unfolds: the name a certificate is filed under.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','context::CheckBudget','struct','The work one judgement may spend before it refuses.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','context::CheckingContext','struct','The checking context: the core context the judgement goes under binders in, wrapped with what the core context does not hold.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','context::Checkpoint','struct','A checkpoint of the checking context: its binders, signature table and admissions.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','context::Formations','enum','Which formations a judgement runs.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','conversion::ConversionCount','struct','Counts the conversions a run made, the declared projection of its crossings of the conversion boundary.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','coverage::Coverage','struct','A match''s coverage: the match''s exhaustiveness and each arm''s redundancy.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','coverage::CoverageFault','enum','Why a match''s coverage has no answer.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','coverage::Exhaustiveness','enum','Whether a match covers every value of its scrutinee''s type.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','coverage::Redundancy','enum','Whether an arm matches some value no arm above it matches.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','coverage::cover','function','Answers arms'' coverage of a scrutinee: exhaustiveness and each arm''s redundancy, three-valued over the holes the patterns hold.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','declaration::AbstractType','struct','A sealed abstract type: an atom of a universe, the representation it stands for inside its seal, the reach of that seal, and the interface its elements are related by, when stated.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','declaration::AtomInterface','struct','What a sealed atom''s elements are related by: a relation, its reflexivity and, when stated, the law that makes the relation its identity.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','declaration::Declaration','struct','One declaration: its admission position, its origin, its content and its stages.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','declaration::DeclarationContent','enum','A declaration''s content.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','declaration::OriginToken','struct','A declaration''s origin, the location a driver resolves a refusal to.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','elaboration::Entry','struct','One declaration''s current answer and cumulative judgement count.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','elaboration::Judgements','struct','The number of declaration judgements actually executed.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','elaboration::Outcome','enum','A term-producing run''s answer for one declaration.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','elaboration::Output','struct','A checked, emitted core term and its original judgement evidence.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','elaboration::ResumeError','enum','An invalid request to fill or resume a module declaration.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','elaboration::Session','struct','A module elaboration, admitting only checked hole fillings as mutations.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','elaboration::Suspension','struct','What a suspended declaration waits on.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','elaboration::constraints::Equation','struct','One conversion obligation on a bare module hole.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','eliminator::DerivationRefusal','enum','Why the fold derives no eliminator.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','eliminator::Eliminator','struct','A derived eliminator: the declaration the fold writes.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','eliminator::derive','function','Derives the eliminator a recursive data declaration has, per motive.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','equiv::Equivalence','struct','A universe equivalence the judgement decided: the native classifier the bridge erases it at, and the evidence of its round trips.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','failure::Failure','struct','A refused run''s state: the refusal, the obligations pending outermost first, the goal under way, the hypotheses the run had opened and the endpoints its linear zone held.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','failure::FoldPremise','enum','The premise of a List fold that a fold frame awaits.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','failure::FrameRole','enum','The rule a pending frame stands for, one per frame of the machine.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','failure::Obligation','struct','One rule pending when a run refused: a frame of the machine.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','failure::Pursuit','struct','The goal a run was pursuing when it refused.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','failure::Stage','enum','Where the machine stood when its run refused.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','flow::Statement','struct','A session statement the judgement decided: the relation, the two quotes, the classifier the bridge erases it at, the engine''s evidence and the payload pairs its paths are owed for.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','fork::Fork','trait','Runs independent jobs on the workers the driver provides.','fork','fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','fork::Serial','struct','Every job on the calling thread, in order: the serial reference.','fork','fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','formation::FormedCompType','struct','A computation type known formed because it is a sub-node of a formed type or a rewrite of one.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','formation::FormedValueType','struct','A value type known formed because it is a sub-node of a formed type or a rewrite of one.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','formation::classify_comp_type','function','The classifier of the formed computation type formed: the computation universe at its natural level.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','formation::classify_value_type','function','The classifier of the formed value type formed: the value universe at its natural level.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','formation::form_comp_type','function','Forms the computation type comp_type in the context''s binders.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','formation::form_value_type','function','Forms the value type value_type in the context''s binders.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','formation::level_of','function','The natural level of root: the level of the universe it inhabits.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','forward::Directed','enum','A directed statement the judgement decided, by its former.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','forward::Forward','struct','A forward flow the judgement decided: its classifier, and an image and a dialogue at every pattern of its source code''s coverage.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','funext::Funext','struct','A function extensionality the judgement decided: per input the domain''s coverage reaches, in the kernel''s order, its tree of steps in pre-order.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','funext::Step','enum','One step of a function extensionality''s decision, in the kernel''s pre-order.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::Checked','struct','A value or computation the judgement checked against its expected type, with the conversions the run made.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::Direction','enum','The direction a judgement runs in.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::Synthesised','struct','A value or computation the judgement synthesised the type of, with the conversions the run made.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::check_comp','function','Checks computation against expected.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::check_value','function','Checks value against expected.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::elaboration::Elaboration','struct','A total run''s result: the term with its marks, its type and the marks'' refusals.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::elaboration::Formed','struct','A type formation a typed run finished: the type and the level it formed at, read under the binders it was formed under.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::elaboration::MarkEntry','struct','One refusal a total run marked, at the term it stands on.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::elaboration::Typing','struct','A term judgement a typed run finished: the term, the type it was judged at, and how many intuitionistic binders were open where it was judged.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::elaboration::Typings','struct','A typed run''s record of what it judged.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::elaboration::elaborate_comp','function','Elaborates computation totally: judges it in direction, marking every refusal short of an engine fault where it stands.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::elaboration::elaborate_value','function','Elaborates value totally: judges it in direction, marking every refusal short of an engine fault where it stands.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::elaboration::type_value','function','Every term judgement the judgement of value in direction finishes, with the type it was judged at, and the refusals it marks.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::synthesise_comp','function','Synthesises the type of computation.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','judgement::synthesise_value','function','Synthesises the type of value.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ledger::Absence','struct','A hole met in checking position: the declaration it stands for, the type it owes, and the declaration''s origin.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ledger::ObligationCount','struct','How many obligations a ledger holds.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ledger::ObligationEntry','struct','One obligation a ledger holds: the absence it records.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ledger::ObligationLedger','struct','The obligations a run owes, in the order their holes were met.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::Judged','struct','One declaration''s verdict, beside the position and origin it was offered with.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::ModuleReport','struct','A module''s verdicts, in the order given, and the obligations they owe.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::ModuleRun','struct','A module run part way: the verdicts of the declarations judged so far and the schedule''s state after the last of them, so that judging the rest later continues the run.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::TypedModule','struct','What type_module keeps of a module''s typed run: the types each declaration''s run formed and judged, the declared type each judgement filled, and the refusal of each declaration the run refused.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::Verdict','enum','A declaration''s verdict.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::check_declaration','function','Judges one declaration in context.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::check_declaration_supported','function','Judges one declaration in context, and reports the signature answers the judgement consulted.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::check_module','function','Judges every declaration of a module, in the order given.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::elaborated_report','function','The report a term-producing run''s entries stand for, over the batch report base.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','module::type_module','function','Judges declarations in order, as check_module does, keeping the type of every term each judged body judges and the refusal of every declaration refused.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','nested::NestedElaboration','struct','What elaborating one declaration''s body did: every decision the judgement made, every node the rebuild carried over from one it was built from, and every bind minted beside the run it was minted for.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','nested::Nesting','enum','A nested computation''s nesting.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::ArgumentPosition','struct','The position of an argument among a static application''s arguments, counted from zero at the argument nearest the head.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::CheckRefusal','enum','Why the judgement refused a term, a type or a declaration.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::CheckingForm','enum','A checking-only form, met where a type had to be synthesised.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::Compared','struct','The types a refusal compares: the expected and the found.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::CoreNode','enum','Any node of the core arena: a term or a type.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::ExpectedShape','enum','The former a rule required of the type it met.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::LoopRespect','enum','Why a case over a looped sort is not shown to respect one of its loops.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::Mismatch','enum','A synthesised type that does not convert to the type it was checked against.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::RunFault','enum','Why a session refuses a recorded run.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::RunStep','struct','A zero-based position among a recorded run''s moves; a count past u32 saturates.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::StaticArity','struct','A count of static arguments: how many a static application passes, or how many static Pis a head''s type opens.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::TermNode','enum','A term node of the core arena.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::TypeNode','enum','A type node of the core arena.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::UnadmittedFormer','enum','A former of the core vocabulary the judgement has no rule for.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','refusal::Unsolved','enum','Why the solver bound no solution to the hole a call nominated for an implicit it omits.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','retire::Demand','enum','The demand for a run''s work: still wanted, or retired by something.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','retire::Polled','enum','What a run that polls retirement answers: its whole answer, or what retired it beside what it held then.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','retire::Retirement','trait','The poll a run reads before each of its steps.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','retire::Unretired','struct','The poll of work nobody retires.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','seal::ComponentOrdinal','struct','An abstract component''s place among its signature''s components.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','seal::SealError','enum','Why a minting or a re-minting check failed.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','seal::SealId','struct','One minted atom: its serial and the site that minted it.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','seal::SealSerial','struct','A minted atom''s place in minting order.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','seal::SealSite','struct','One sealing site: an opaque ascription and the abstract component of its signature it seals.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','seal::SealTable','struct','The atoms one elaboration minted, in minting order, with the sites that minted them.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','seal::SealingSite','struct','The opaque ascription a site belongs to, as its producer numbers it.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','session::Capture','enum','What may run an endpoint''s use other than exactly once.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','session::Endpoint','struct','An endpoint, named by the fork or the receive that bound it and its side.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','session::ForkSide','enum','Which binder of an endpoint bound it: a half of a fork, or a receive.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','session::LinearityDefect','enum','How an endpoint escaped its one linear use.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','session::LiveEndpoint','struct','An endpoint the linear zone held when a run refused.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','session::ProtocolDefect','enum','What an endpoint''s session state refuses of an action on it.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','stage::Admitted','struct','The checked definition and the explicit primitive signature it may use.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','stage::Instruction','enum','First-order instructions; operands always precede their result.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','stage::Program','struct','A replayed, closed first-order natural function.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','stage::ReadmissionError','enum','A residual readmission failure, retaining the layer that refused it.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','stage::Register','struct','One register in a closure-free, straight-line residual.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','stage::compile','function','Replays a staged result and compiles its closed first-order residual.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','staging::Allowance','struct','The work each job of a check may spend, granted afresh to every job so no job''s allowance depends on how the jobs were scheduled.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','staging::Checked','struct','A staged program, checked: its arena, its certificates, readmissions, harvested families and admissions, and the time each stage took.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','staging::Program','struct','A staged meta-program, ready to check.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','staging::ProgramError','enum','Why a staged program could not be checked: the first failure in source order, with the stage and source it belongs to.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','staging::Readmission','enum','The kernel''s verdict on one certificate.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','staging::SourceIndex','struct','A source''s position in its program.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','staging::Stages','struct','Time spent at each stage of a check, read from the caller''s clock.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','staging::check','function','Checks a staged program: normalizes every source, merges the syntax, harvests the families, then readmits every certificate beside admitting every family through the memo.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','support::CodataConsulted','struct','One codata-signature answer, including a missing declaration.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','support::Consulted','struct','One answer a judgement read from the signature table.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','support::DataConsulted','struct','One nominal-signature answer, including a missing declaration.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','support::Support','struct','The answers one declaration''s judgement consulted, ascending by position, each position once.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','support::Supported','struct','A supported judgement: the support it consulted and the verdict it returned.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::Analysis','enum','Preparation without replay, preserving malformed-family refusals.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::Candidate','struct','An untrusted candidate and its transient discovery columns, before inheritance.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::FamilyPrices','struct','Both prices, computed before any inheritance check.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::PriceGate','enum','Which independently reported strict price authorizes an inheritance attempt.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::Production','enum','A producer result; ordinary replay is selected whenever compression declines.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::ProgramId','struct','Producer identity within one readmission run; unrelated programs never merge.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::Substitution','struct','The member''s choices, selected only by matching its own source.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::Template','struct','A priced and inheritance-checked equation family, retaining no members.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::admission::AdmissionCandidate','struct','A kernel proposal and independent point-ordered rows for harvested members.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::analyze','function','Anti-unifies and prices a uniform family without replay or admission authority.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::draft::ArmCount','struct','How many arms a draft added to its template''s.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::draft::DraftKind','enum','How a draft departs from its template.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::draft::Miss','enum','Why a walk left a member unmatched.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::draft::RepairCount','struct','How many binders a rebase replaced.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::draft::Unfit','enum','Why a draft that matched every member is not offered to the kernel.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::harvest::Family','struct','One recurring decision region from a single meta-program.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::harvest::harvest','function','Harvests every equation, partitioning by decision and shallow source shape.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::image::plain_image','function','Builds the independent serial image of one plain equation, excluding arena garbage.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::Clock','trait','A monotone clock the caller supplies; the checker reads no clock of its own.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::Decline','enum','Why the controller did not draft a family whose key holds a template.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::Drafting','enum','What the drafter did with one family.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::FamilyAdmission','enum','What became of one family.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::FamilyReport','struct','One family''s outcome, the drafter''s part in it, and the time spent.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::Memo','struct','Each harvest key''s last template, the controller''s state, and the buffers drafting and admission reuse, carried by the caller across programs.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::Origin','enum','Where an admitted schema came from.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::Spent','struct','Time spent on one family, by stage.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::memo::Unheld','enum','Why the memo holds no template for a family.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::produce','function','Prepares a family and emits it only under the selected price and inheritance.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','template::readmit','function','Replays a complete certificate, exercising paying equation templates first.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::StratumDefect','enum','Why the stratum a ua statement names is not certified.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::Translators','struct','The two translators an equivalence gives at one corolla.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::UaDefect','enum','Why a ua statement''s translators are no equivalence of its species at its stratum.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::UaRefusal','enum','Why an equivalence has no path at the stratum.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::Universal','struct','An equivalence of species as a path of the certificate universe.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::Way','enum','Which way a translator record reads.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::code','function','The code of a species at a corolla''s profile: one unit summand per element, in the stratum''s enumeration order.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::derive','function','The certificate-universe path the equivalence the translators give is, at a certified stratum.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','ua::tabulate','function','The canonical translator of a table: a thunk of a lambda casing on its argument and returning, at the i-th summand, the injection of the unit at the i-th image.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','view::FragmentRefusal','enum','Why a type node has no view.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::Bound','enum','Whether a stated entry lies within the host''s.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::Crossed','enum','What crosses at a refused crossing.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::Crossing','enum','The decision on whether a type crosses.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::Entry','struct','A declaration''s entry: the world it is judged at and the capabilities the host hands it, one migration each.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::HostEntry','enum','The entry the host names for every declaration of a run.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::LocatedDefect','enum','How a located judgement breaks.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::Mobility','enum','Whether a sealed abstract type crosses outside its seal.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::Predicate','enum','Which of the two crossing predicates a former fails.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::WorldMove','enum','One move of the world register a typed run keeps: a migration''s push, with the linear zone before and after its capability was spent, and its pop.',NULL,'fits','sound',NULL);
INSERT INTO purpose VALUES('core-checker','worlds::WorldName','struct','The name of a world, as a host names one before any source declares it.',NULL,'fits','sound',NULL);
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
