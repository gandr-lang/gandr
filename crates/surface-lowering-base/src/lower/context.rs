//! The lowering's context: the state that every family of the lowering reads
//! and writes.
//!
//! `gandr-surface-lowering` holds each family as a wrapper that owns this
//! context. A family reads a field as `self.cx.field`. The
//! context and the types of its fields read nothing of the families, so they
//! compile here, before the families and beside their code generation.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CodataSignature;
use gandr_core_term::DataSignature;
use gandr_core_term::Renaming;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::Summand;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::LayoutBlock;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use super::AskedRuns;
use super::Block;
use super::Bridge;
use super::Current;
use super::Exit;
use super::HoleGroups;
use super::InPayload;
use super::InstanceType;
use super::LabelSite;
use super::Lowered;
use super::Parameter;
use super::Plan;
use super::Reading;
use super::Returned;
use super::Site;
use super::Statement;
use super::TextSegment;
use super::access;
use super::capability;
use super::classified;
use super::exits;
use super::generic;
use super::implicit;
use super::loops;
use super::lowered;
use super::method;
use super::model;
use super::native;
use super::opening;
use super::scoped;
use super::session;
use crate::budget::Fuel;
use crate::by_form::ByForm;
use crate::by_form::FormPlace;
use crate::error::LoweringRefusal;
use crate::form::Pieces;
use crate::form::Placed;
use crate::module::CodataIndex;
use crate::module::Collected;
use crate::module::ComponentScope;
use crate::module::DataIndex;
use crate::module::DeclarationOutcome;
use crate::module::InstanceIndex;
use crate::module::Sealing;
use crate::module::SlotIndex;
use crate::module::TypeComponent;
use crate::namespace::NamePath;
use crate::namespace::Recognition;
use crate::resolve::Frame;
use crate::resolve::Resolution;
use crate::resolve::Scope;
use crate::resolve::ScopeId;
use crate::resolve::Shadow;
use crate::resolve::SurfaceName;
use crate::table::NodeTable;
use crate::unit::SourceIndex;
use crate::unit::Unit;
use crate::unit::UnitKey;
/// The lowering's working state, shared by both sweeps.
///
/// # Specification
/// - requires: The grammar, tree and collected declarations describe one
///   lowering run.
/// - ensures: Per-node tables share the tree’s coordinate space; planned
///   flat-store ranges and declaration ownership are interpreted only in that
///   run.
/// - provides: The state linking collection, classification, minting and
///   assembly.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Type-level invariant expansion is unavailable in the
///   enabled specification facade; new and the phase boundaries carry
///   executable table and state relations.
///
/// # Adequacy
/// - hypothesis: L3 — declaration isolation, manifest dependencies, origins and
///   attribute retention are observed through parsed multi-declaration modules,
///   not inferred from table lengths alone.
/// - witness: `gandr-surface-lowering::lower::tests::a_refused_declaration_leaves_the_others_lowered`
/// - witness: `gandr-surface-lowering::tests::modules::a_manifest_type_component_expands_in_later_components`
/// - witness: `gandr-surface-lowering::lower::tests::every_minted_node_has_an_origin`
/// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
#[derive(Clone)]
pub struct Context<'run, 'source>
{
    /// The grammar the tree was molded under.
    pub pbg: &'run Pbg,
    /// The tree being lowered.
    pub tree: &'run SyntaxTree<'source>,
    /// The module's declarations and the slot each node belongs to.
    pub collected: Collected<'source>,
    /// How each node's position reads it.
    pub readings: NodeTable<Reading>,
    /// What the mint sweep does for each node, kept once it is done: a later
    /// source's classification reads an earlier source's plans.
    pub plans: NodeTable<Plan>,
    /// Each written name resolved, with what it names, in the order resolved:
    /// a name of a declaration refused later is kept.
    pub resolutions: Vec<(ByteSpan, Resolution)>,
    /// Each written binder whose name an outer scope binds, with the binding
    /// it hides, in the form of the node that wrote the binder: a binder of a
    /// declaration refused later is kept.
    pub shadows: ByForm<Shadow>,
    /// Whether the mint sweep has carried out each node's plan, which it does
    /// once.
    pub taken: NodeTable<bool>,
    /// What the mint sweep writes over each node's own core node.
    pub bridges: NodeTable<Bridge>,
    /// Each node's lowered core node.
    pub lowered: NodeTable<Maybe<Lowered, lowered::Absent>>,
    /// Which nodes lie inside an attribute payload.
    pub payload: NodeTable<InPayload>,
    /// The manifest type components each node sees, where it lies in a
    /// module signature.
    pub scopes: NodeTable<Maybe<ComponentScope, scoped::Absent>>,
    /// Each type head that named a manifest type component, with the held
    /// slot owning that component's type.
    pub manifests: Vec<(SlotIndex, NodeIndex)>,
    /// Each application of a type member with parameters, by its node, with
    /// its span and the frame it is read under: the application answers as
    /// the type it expands to, which the member's own body mints.
    pub expansions: BTreeMap<NodeIndex, (ByteSpan, Frame)>,
    /// Each type member's definition, by its node, that is a computation
    /// type (`Lowerer::member_reading`): a name or an application reaching
    /// the member stands where a computation type is read.
    pub computation_members: BTreeSet<NodeIndex>,
    /// Each top-level type member that takes no parameters, by the node of
    /// its definition, with the name tile the member declares. The value
    /// type that definition mints is recorded under the name, so the printer
    /// writes the name where the type is shared (#5826).
    pub defining: BTreeMap<NodeIndex, NodeIndex>,
    /// Each exported value component's full path, with the member's slot.
    pub exported: BTreeMap<NamePath, SlotIndex>,
    /// Each exported type component's full path, with what it reads.
    pub exported_types: BTreeMap<NamePath, TypeComponent<'source>>,
    /// Each witness's body, by slot.
    pub witnessed: BTreeMap<SlotIndex, ValueId>,
    /// Each abstract slot's declaration, once its kind and representation
    /// lowered.
    pub sealings: BTreeMap<SlotIndex, Sealing>,
    /// Each kind witness's declared kind and body, the code of the type
    /// member it checks.
    pub kind_checks: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// Each slot whose signature a model derives, with the type minted for
    /// it.
    pub modelled: BTreeMap<SlotIndex, ValueTypeId>,
    /// Each slot a check after minting refused: a derived component that
    /// names one that did not lower, or a family whose parameters disagree
    /// with its indices.
    pub faults: BTreeMap<SlotIndex, LoweringRefusal<'source>>,
    /// Each flow's instance over an import's source that the import's match
    /// refuses: it declares nothing.
    pub untranslated: BTreeSet<InstanceIndex>,
    /// The arguments every planned application reads, stretch by stretch.
    pub operands: ByForm<NodeIndex>,
    /// The rungs every planned conditional reads, stretch by stretch.
    pub else_ifs: ByForm<(
        NodeIndex,
        Block,
        Maybe<native::Answer, native::answered::Absent>,
    )>,
    /// The segments every planned interpolated string reads, stretch by
    /// stretch.
    pub segments: ByForm<TextSegment>,
    /// The statements every planned block reads, stretch by stretch.
    pub statements: ByForm<Statement>,
    /// The parameters every planned function reads, stretch by stretch.
    pub parameters: ByForm<Parameter>,
    /// The binder frames the lambdas, the parameters and the statements
    /// extended.
    pub scope: Scope<'source>,
    /// The outermost scope every declared name is declared in and every
    /// binder is reported against.
    pub recognition: Recognition,
    /// The remaining allowance.
    pub fuel: Fuel,
    /// The scratch reading of the form being classified.
    pub pieces: Pieces,
    /// The scratch reading of a written universe a decode reads its sort and
    /// level from.
    pub scratch: Pieces,
    /// Each constructor written under an annotation, with the annotation's
    /// type.
    pub classifiers: BTreeMap<NodeIndex, NodeIndex>,
    /// Each annotation `(e : T)` over the whole value of a definition no
    /// signature types, with the `T` that signs it.
    pub annotated_definitions: BTreeMap<NodeIndex, NodeIndex>,
    /// Each annotation `(e : T)` an ascription carries, with its `T`: the
    /// whole operand of a `return`, or a tail, each returning at `-F T`. An
    /// annotated constructor or injection is not among them: `T` is already
    /// its classifier.
    pub ascribed: BTreeMap<NodeIndex, NodeIndex>,
    /// Each call standing as one value whose callee returns a group of
    /// outputs, with its outputs' labels in order, none for an unnamed one:
    /// the call stands as the record of its outputs.
    pub packed: BTreeMap<NodeIndex, Vec<Option<FieldLabel>>>,
    /// Each tuple pattern over a call returning a group of outputs, with the
    /// binder it writes for each output, in the order the callee writes them:
    /// a labelled pattern's binders stand in its labels' order otherwise.
    pub output_binders: BTreeMap<NodeIndex, Vec<NodeIndex>>,
    /// Each lambda's binder written with a type, `x` in `fun (x : A) { … }`,
    /// with `A`, the frame it was read under, which the lambda stands in, and
    /// the lambda's own frame, which binds `x`.
    pub typed_parameters: BTreeMap<NodeIndex, (NodeIndex, Frame, Frame)>,
    /// Each value argument of a data family's application, with its place.
    pub argued: BTreeMap<NodeIndex, native::Argued>,
    /// Each argument of a call naming a declaration, with the type the
    /// declaration writes for the parameter at its place and the call's
    /// arguments that type reads.
    pub parameter_typed: BTreeMap<NodeIndex, native::CalledAt>,
    /// Each constructor classified by its place in a data family's
    /// application or a call's, or by a field, not yet minted: its classifier
    /// reads the arguments or the fields before it, which the mint sweep
    /// reaches after it, so the application, the call or the constructor
    /// around it mints it.
    pub awaiting: BTreeSet<NodeIndex>,
    /// Each constructor classified by the field it stands in, with where the
    /// mint names the wildcards of the classifier it inserts when the
    /// constructor around reads as no family's application (#6113).
    pub fielded: BTreeMap<NodeIndex, native::Fielded>,
    /// Each thunk a definition is, with the answer its signature states for
    /// its body: `C` for `+U C`, `-F B` for `() -> B`.
    pub thunked: BTreeMap<NodeIndex, native::Answer>,
    /// Each thunk or bare lambda passed for a parameter whose type names a
    /// parameter written before it, with the answer that type gives, read
    /// under the callee's binders: the lambda's binder takes the answer's
    /// domain, and nothing answers its body where the call stands (#3921).
    pub dependent_answers: BTreeMap<NodeIndex, native::Answer>,
    /// Each node a type classifies without annotating it: a definition whose
    /// signature writes a type no thunk is, and a field of a constructor with
    /// a classifier, with the classifier it takes.
    pub inherited: BTreeMap<NodeIndex, native::Classifier>,
    /// Each operand a grouping wraps, `(e)`, `(T)` or `type(T)`, with the
    /// outermost grouping around it: a form of the wrong sort there is refused
    /// at the grouping, the form that stands in the position (#2341).
    pub grouped: BTreeMap<NodeIndex, Placed>,
    /// Each label written against an entry, in the order planned.
    pub labels: Vec<LabelSite>,
    /// Each prefix minus folded onto a number, the operator span beside the
    /// operand span, in the order planned.
    pub covers: Vec<(ByteSpan, ByteSpan)>,
    /// Each type and stated index a data declaration writes, with the frame
    /// of the binders it is read under: a parameter's type under the
    /// parameters before it, an index's under the parameters and the indices
    /// before it, a field's under the parameters and its constructor's fields
    /// before it, and a stated index under the parameters and all its
    /// constructor's fields.
    pub data_frames: Vec<(NodeIndex, Frame)>,
    /// Each type head that stands for a type minted elsewhere: a manifest
    /// component's or a functor instance's, which the head adopts.
    pub stand_ins: BTreeSet<NodeIndex>,
    /// Each type written as a kind, a type's own classifier, with each
    /// codomain of an arrow it heads: an arrow there is the static Pi, never
    /// the box.
    pub kinds: BTreeSet<NodeIndex>,
    /// Each written type's answer to [`crate::form::classifies_codes`], kept
    /// so each node of an arrow chain is classified once.
    pub classified: BTreeMap<NodeIndex, crate::form::Kinded>,
    /// Each `Model(T)` application a manifest type closes, with the sorts it
    /// fixes: each sort's name beside the type it is, in written order.
    pub fixed_sorts: BTreeMap<NodeIndex, Vec<(Placed, Placed)>>,
    /// Each type a manifest sort is fixed to that a reading of the sort off
    /// its binder, `a.C`, stands for: minted before the sweep reaches the
    /// reading, which can sit deeper in the tree than the type.
    pub fixed_carriers: Vec<Placed>,
    /// The nodes the form being classified asks classified next, before the
    /// sweep moves on: a manifest type's `Model(T)` application, whose bundle
    /// a reading of its sorts can stand before.
    pub ahead: Vec<NodeIndex>,
    /// Each node classified ahead of the sweep, which the sweep then passes
    /// over.
    pub classified_ahead: BTreeSet<NodeIndex>,
    /// The node and span of each name the sweep refuses as unresolved, in the
    /// order the sweep reaches them, whether or not its declaration keeps
    /// that refusal: the names `Lowerer::place_misspelt_operator` may read as
    /// an operator misspelt.
    pub unresolved: Vec<(NodeIndex, ByteSpan)>,
    /// The type each computation position answers, where a function's result
    /// or a match's answer states it, or the block a statement's local ends
    /// continue answers.
    pub answers: BTreeMap<NodeIndex, native::Answer>,
    /// The body of every copattern clause: the arms a productive self-call
    /// `f[>](…)` may stand as.
    pub cocased: BTreeSet<NodeIndex>,
    /// Each derived operation standing where no type is answered, its motive
    /// synthesised from its operands: the innermost first once
    /// `Lowerer::refuse_unsynthesised` has read them, for the mint sweep.
    pub synthesised: Vec<Site>,
    /// The terms standing inside a type: a path type's endpoints and every
    /// node under one, whose bound names count only the frames that bind in
    /// the type's telescope and make the arrow binding them dependent.
    pub in_type: BTreeSet<NodeIndex>,
    /// The nodes of a type a body quotes, the quote included: their binder
    /// reads count in the quote's own telescope, which the quote is carried
    /// out of into the body's context, and never make the signature's arrows
    /// dependent (#547).
    pub in_quote: BTreeSet<NodeIndex>,
    /// The body of each static lambda, the type its operator denotes: a
    /// dynamic call written there unquotes the code it returns, and the body
    /// quotes that type (#3786).
    pub static_bodies: BTreeSet<NodeIndex>,
    /// Each lambda whose position reads it as a static lambda, with the
    /// static classifier `K -> J` the position states when it states one: a
    /// transport's or a ride's motive, which states none, an argument at a
    /// static application's parameter, and a static lambda's body under the
    /// arrow its own classifier answers (#4508).
    pub static_lambdas: BTreeMap<NodeIndex, Maybe<NodeIndex, classified::Absent>>,
    /// The span of each static lambda's body: a call written there is the
    /// static application a type spells (#4508).
    pub static_spans: Vec<ByteSpan>,
    /// Each call read as a value inside a static lambda's body, which
    /// `Lowerer::static_call` plans as a static application (#4508).
    pub static_calls: BTreeSet<NodeIndex>,
    /// The terms standing at an endpoint: a path type's endpoints,
    /// reflexivity's point and every node under one, where a computation
    /// standing as a value is the value it returns.
    pub at_endpoint: BTreeSet<NodeIndex>,
    /// Each abstraction whose binder ranges over the points of a path, with
    /// the carrier the path's written type states (#3773). A lambda `cong`
    /// maps by types its binder with it, is minted as its thunk, and the
    /// transport's motive reads its body. A static motive of `transport`
    /// records its binder in [`Self::binders_over_points`].
    pub over_points: BTreeMap<NodeIndex, NodeIndex>,
    /// The binder of each static motive [`Self::over_points`] records, with
    /// that carrier: an operation over the binder reads its path type off it.
    pub binders_over_points: BTreeMap<ScopeId, NodeIndex>,
    /// The binder of each lambda passed for a parameter that writes no type
    /// of its own, with the parameter, the domain node its binder is typed
    /// by and the frame the call stands in: an operation over the binder
    /// reads its path type off the domain at the call's arguments (#3921).
    pub argued_binders: BTreeMap<ScopeId, (native::CalledAt, NodeIndex, Frame)>,
    /// What every node's paths do with the body it stands in, surveyed before
    /// the classification reads it.
    pub leaves: NodeTable<exits::Leaves>,
    /// The computation positions where a path through a body ends: the last
    /// computation of a function's, a lambda's or a thunk's body, and what
    /// stands in tail position of one — a block's last computation, a match's
    /// arm, a grouping's operand. A form there that is not an exit takes the
    /// one its polarity names.
    pub exits: BTreeSet<NodeIndex>,
    /// The computation positions a path through a body passes, where an exit
    /// may stand: every position where a path ends, and every statement's
    /// computation in a block on a path, with what stands in tail position of
    /// one.
    pub exitable: BTreeSet<NodeIndex>,
    /// The computation positions whose local ends continue a block: the
    /// computation of a statement that holds an exit, and what stands in tail
    /// position of one.
    pub joined: BTreeSet<NodeIndex>,
    /// The exits read: every `return` and `become`, written or inferred, and
    /// every `continue`, whose minted computation the commuting keeps where
    /// it stands.
    pub leaving: BTreeSet<NodeIndex>,
    /// The computation positions where a path through a loop's body ends: the
    /// body's last computation, and what stands in tail position of one. A
    /// form there that is no exit runs the loop again.
    pub iterated: BTreeSet<NodeIndex>,
    /// The computation positions a path through a loop's body passes, where
    /// a `break` or a `continue` may stand.
    pub looping: BTreeSet<NodeIndex>,
    /// The `break`s read, whose minted returner the commuting continues with
    /// what follows their loop.
    pub breaking: BTreeSet<NodeIndex>,
    /// The loop ends written without an exit, each run again: where its loop
    /// runs again from under the binder of the result it discards.
    pub reentered: BTreeMap<NodeIndex, loops::Reentry>,
    /// The conditions of `while` loops, read where a computation is: a value
    /// written there is returned, so the loop binds what it tests.
    pub tested: BTreeSet<NodeIndex>,
    /// The linear binders that hold a slot: each `var` statement's, and each
    /// slot a threading loop holds again for its passes and for what follows
    /// it.
    pub held: BTreeSet<ScopeId>,
    /// The parameters at a session type each function body places, stretch
    /// by stretch.
    pub endpoints: ByForm<session::PlacedEndpoint>,
    /// The loops that thread held slots or endpoints, by the loop's node: each
    /// slot's linear index where the loop stands, its name and what it is,
    /// outermost first.
    pub threading: BTreeMap<NodeIndex, Vec<(DeBruijnIndex, SurfaceName<'source>, loops::Carry)>>,
    /// The slots each threading loop holds or places again for its passes, by
    /// the loop's own binder, outermost first.
    pub reheld: BTreeMap<ScopeId, Vec<ScopeId>>,
    /// The slots each threading loop's first pass takes, by the loop body's
    /// last computation: their linear indices where the loop stands and what
    /// each is, outermost first.
    pub carries: BTreeMap<NodeIndex, Vec<(DeBruijnIndex, loops::Carry)>>,
    /// The computation positions where a path through a handled subject
    /// ends: the subject's last computation, and what stands in tail position
    /// of one. A value there is returned to the handler's return clause, as
    /// the subject's result; neither it nor a computation there is an exit.
    pub results: BTreeSet<NodeIndex>,
    /// The operand of each block's `module m = p ;`, with the type node `p`
    /// is declared at, which must plan as a model type's bundle.
    pub opened_models: BTreeMap<NodeIndex, NodeIndex>,
    /// The value positions a `let` binding a name binds: a computation there
    /// is carried nested at
    /// [`Insertion::Bound`](crate::origin::Insertion::Bound), the run the `let`
    /// writes.
    pub let_bound: BTreeSet<NodeIndex>,
    /// The computation positions a path through a handled subject passes: a
    /// `return` there leaves its body past every handler frame around it, and
    /// a `become` there is refused.
    pub framed: BTreeSet<NodeIndex>,
    /// The positions of `framed` whose nearest loop stands outside a
    /// handler's frame: a `break` or a `continue` there is refused.
    pub looped_past: BTreeSet<NodeIndex>,
    /// The body every position a path passes belongs to, by that body's last
    /// computation.
    pub bodies: BTreeMap<NodeIndex, NodeIndex>,
    /// The `return`s written at a position of `framed`, each minted as a
    /// capture its body's delimiter discards.
    pub crossing: BTreeSet<NodeIndex>,
    /// The bodies, by their last computation, that hold a `return` of
    /// `crossing`: each is minted under a delimiter.
    pub delimited: BTreeSet<NodeIndex>,
    /// The tails the source wrote without an exit, each exited by the one its
    /// polarity names: a value by an inserted `return`, a computation by
    /// running it in tail position.
    pub inferred: BTreeSet<NodeIndex>,
    /// Every inferred exit the mint sweep minted, with its tail's position.
    pub elided: Vec<(NodeIndex, Exit)>,
    /// Every written `return` the mint sweep minted that the lowering would
    /// infer were it left out, with its position, its operand's and what the
    /// operand is.
    pub elidable: Vec<(NodeIndex, NodeIndex, Returned)>,
    /// The slots an `explicit_exits` attribute asks written exits of: a
    /// declaration it decorates, and every member of a module it decorates.
    pub asked: BTreeSet<SlotIndex>,
    /// Which runs an `explicit_runs` attribute asks written of each slot it
    /// reaches: a declaration it decorates, and every member of a module it
    /// decorates, the wider ask where both reach.
    pub asked_runs: BTreeMap<SlotIndex, AskedRuns>,
    /// Each block's last computation written as a statement, `c ;` before the
    /// closing brace, with the statement's span.
    pub stated: BTreeMap<NodeIndex, ByteSpan>,
    /// Each module a block's `import P ;` opens, by the statement's span.
    pub opened: BTreeMap<ByteSpan, opening::Opened>,
    /// The positions in tail position of a block's last computation written
    /// as a statement, `c ;`: an exit there keeps `c` the block's end, so the
    /// sugared form keeps it written.
    pub stated_tails: BTreeSet<NodeIndex>,
    /// Each block's last statement that is not an exit and that does not
    /// leave on every path: the block runs it, discards its result and
    /// returns the unit.
    pub trailing: BTreeSet<NodeIndex>,
    /// The matches, each compiled to its decision tree.
    pub cases: ByForm<native::CaseForm, native::CaseIndex>,
    /// Each constructor arm a match passed its answer into, with what the arm
    /// reads the match's scrutinee as.
    pub arms: ByForm<native::ArmReading, native::ArmIndex>,
    /// The fields read off data values by name, each the case returning it.
    pub projected: ByForm<native::Projected, native::ProjectedIndex>,
    /// The position each lowered data declaration's signature takes, by its
    /// position in the collection's data list.
    pub signatures: BTreeMap<usize, DataIndex>,
    /// The position each words' signature takes, by its position in the
    /// collection's words list.
    pub worded: BTreeMap<usize, DataIndex>,
    /// The position each theory's terms' signature takes, by their position
    /// in the collection's terms list.
    pub termed: BTreeMap<usize, DataIndex>,
    /// The path type at each minted words' point and the type at each wrapping
    /// of the point, the family first, by its position in the collection's
    /// words list: what a later source's letters and empty words are labelled
    /// at.
    pub word_types: BTreeMap<usize, (ValueTypeId, Vec<ValueTypeId>)>,
    /// Each loop's binding, the path type at its point and the word of its
    /// one letter, by slot.
    pub looped: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// Each letter written before a cons, the name an inverse letter applies
    /// `back` to, and the loop a loop arm names, with the words it spells a
    /// letter of: no core node holds it, so it answers at the path type at
    /// the words' point.
    pub lettered: Vec<(ByteSpan, usize)>,
    /// Each node of a point `here` names when it is the empty word, and each
    /// `Path.here` call around the point, with the words at that point and how
    /// many calls stand at and inside it: no core node holds it, so it answers
    /// at the words' family wrapped as many times.
    pub pointed: Vec<(ByteSpan, usize, gandr_kernel_term::Reflexivities)>,
    /// The position each described family's decoded signature takes, by its
    /// slot: a family the native data reading does not own.
    pub described: BTreeMap<SlotIndex, DataIndex>,
    /// The data declarations' signatures, by [`DataIndex`].
    pub data: Vec<Arc<DataSignature>>,
    /// The names of each data declaration's constructors in tag order, by
    /// [`DataIndex`].
    pub constructors: Vec<Vec<String>>,
    /// The position each codata declaration's decoded signature takes, by its
    /// slot.
    pub codata_described: BTreeMap<SlotIndex, CodataIndex>,
    /// The codata declarations' signatures, by [`CodataIndex`].
    pub codata: Vec<Arc<CodataSignature>>,
    /// Each recursive function's own name, by the frame that binds it.
    pub recursions: BTreeMap<ScopeId, native::Recursion>,
    /// Each recursive function's parameter, by the frame it binds: the
    /// function and the parameter's position, which a match on it stages.
    pub staged_parameters: BTreeMap<ScopeId, native::Scrutiny>,
    /// Each staged type a quantified function's signature writes, by its
    /// node: the stage its binder's ordinal names.
    pub stage_marks: BTreeMap<NodeIndex, gandr_kernel_term::Stage>,
    /// The bound of each stage binder of each quantified function, in
    /// written order, by the function's declaration key.
    pub stage_bounds: BTreeMap<UnitKey, Vec<gandr_kernel_term::StageBound>>,
    /// Each region binder of each definition abstracted over regions, by its
    /// name, at its ordinal among them, by the slot of the definition: every
    /// node the definition owns reads them there.
    pub region_binders: BTreeMap<
        SlotIndex,
        BTreeMap<SurfaceName<'source>, gandr_core_term::effect::capability::RegionBinder>,
    >,
    /// Each mode binder of each method a deduced mode receives through, by
    /// its name, by the slot of the method.
    pub mode_binders: BTreeMap<SlotIndex, BTreeSet<SurfaceName<'source>>>,
    /// The body a method answering a view ends in, by its node: the place of
    /// the receiver the body answers, `self.#[e]`.
    pub view_places: BTreeMap<NodeIndex, method::ViewPlace>,
    /// The place assignments a block read, by the place's node: the place
    /// stands as the access that writes it.
    pub assignments: BTreeMap<NodeIndex, access::Assignment>,
    /// The view types, `View[m](a)`, a method answering a place declares its
    /// result at, by node: each stands as the place's index.
    pub view_types: BTreeSet<NodeIndex>,
    /// The linear binders a `resume` or an `abort` ends: a view a block ends
    /// asks its call for an exclusive lend.
    pub ended_views: BTreeSet<ScopeId>,
    /// The stages a call supplies its callee's binders at, `f[.i = s]`, by the
    /// node of the callee's name, beside the declaration making the call.
    pub planned_supplies: BTreeMap<
        NodeIndex,
        (
            ConstantIndex,
            Vec<(gandr_kernel_term::StageBinder, gandr_kernel_term::Stage)>,
        ),
    >,
    /// Each stage a call supplies, at the value it forces, by the declaration
    /// whose body makes the call.
    pub supplies: BTreeMap<ConstantIndex, Vec<gandr_core_term::staged::Supply>>,
    /// The laws each capability scope over a theory owes it, read through the
    /// scope's clauses, by the declaration whose body holds the scope.
    pub handler_laws: BTreeMap<ConstantIndex, Vec<gandr_core_term::handler::HandlerLaw>>,
    /// The model slots a call omits, by the node of the call, each with the
    /// declaration making the call, its holes and its candidates.
    pub planned_models: BTreeMap<NodeIndex, Vec<model::PlannedModel<'source>>>,
    /// The names of an omitted model slot's candidates, in place order, by
    /// each hole the slot nominated.
    pub model_candidates: BTreeMap<gandr_core_term::hole::HoleId, Vec<String>>,
    /// Each model slot a call omits, its candidates minted, by the
    /// declaration whose body makes the call.
    pub models: BTreeMap<ConstantIndex, Vec<gandr_core_term::model::ModelSlot>>,
    /// Each `let` binder written with no type, by the frame it binds: the
    /// frame its computation reads under and the computation, whose callee's
    /// written result states the binder's type to a match on it.
    pub ran: BTreeMap<ScopeId, (Frame, Placed)>,
    /// Every hole of the tree, by its form's block and where its text starts,
    /// read once the first hole is lowered: a hole is named by its block's
    /// group and its place among the group's holes here
    /// (`Lowerer::hole_group`).
    pub holes: Vec<(LayoutBlock, ByteOffset, NodeIndex)>,
    /// The group of each block that a hole names, read as far as a hole asks
    /// ([`HoleGroups`]): the forms of one declaration share one group
    /// (#5469).
    pub hole_groups: HoleGroups,
    /// Each pattern variable whose position a written type states, by the
    /// name's syntax node: the node of that type, which the arm binds the
    /// variable at.
    pub pattern_stated: BTreeMap<NodeIndex, NodeIndex>,
    /// Each node under an arm of a match on a recursive function's
    /// parameter: the innermost such match's function and position.
    pub scrutinised: BTreeMap<NodeIndex, native::Scrutiny>,
    /// Each recursive call, by its head: the instantiation whose claim checks
    /// it.
    pub descents: BTreeMap<NodeIndex, native::Descent>,
    /// Each recursive call through a joint fixpoint, by its head: the summand
    /// of the member it calls, which injects its argument.
    pub injected: BTreeMap<NodeIndex, Summand>,
    /// Each recursive call through a joint fixpoint to a sibling member: the
    /// call, the members it stands in and calls, and the arguments it passes,
    /// held until every member's parameters are read.
    pub sibling_calls: Vec<native::SiblingCall>,
    /// The reading of the form being classified, or unread between forms: a
    /// value a type reads is filed in [`Self::type_read`].
    pub reader: Reading,
    /// Every position read as a value by a type — a type-position call's
    /// argument, and its own operands in turn — whose quote stays in the
    /// enclosing type's telescope rather than carried into a term's context.
    pub type_read: BTreeSet<NodeIndex>,
    /// Each telescope type written where a value is read inside a type, at a
    /// constructor's field, a call's parameter or a tuple's component whose
    /// type is no universe, with that type when it is written: it is the
    /// tuple of its entries, not the quote of their product (#5208, #5500).
    pub valued_telescopes: BTreeMap<NodeIndex, Option<NodeIndex>>,
    /// Each head of a call of no arguments, beside the call: such a call is
    /// its head's force, so the force carries the call's origin.
    pub nullary: BTreeMap<NodeIndex, NodeIndex>,
    /// Each head of a call standing where a type is read, beside the call:
    /// the call is the type application it spells, and the head, a node of
    /// its own, carries the function the unquote calls.
    pub typed_heads: BTreeMap<NodeIndex, NodeIndex>,
    /// The head of each call that applies a function with implicits, each
    /// supplied by name, `f[.a = T](…)`, or nominated where the call omits it
    /// (`Self::nominated`): the one place such a function is named without
    /// refusal.
    pub supplied: BTreeSet<NodeIndex>,
    /// Each operand an application passes for an implicit its call omits, by
    /// its coordinate in the operand store, with the hole nominated for it:
    /// the operand's node is the call's own, which no value lowers at, and
    /// the application mints the hole there.
    pub nominated: BTreeMap<FormPlace, gandr_core_term::hole::HoleId>,
    /// Each operand a standing supply passes for an explicit parameter its
    /// merged telescope places before a supplied implicit, by its coordinate
    /// in the operand store, with the variable of the lambda the supply opens
    /// for it: the operand's node is the supply's own, which no value lowers
    /// at, and the application mints the variable there, under one lambda per
    /// such operand.
    pub abstracted: BTreeMap<FormPlace, DeBruijnIndex>,
    /// Each operand a call passes for an instance it omits, by its coordinate
    /// in the operand store, with the variable of the instance resolved for
    /// it where the call stands: the operand's node is the call's own, which
    /// no value lowers at, and the application mints the variable there.
    pub instanced: BTreeMap<FormPlace, DeBruijnIndex>,
    /// Each operand an application passes for a component of a model
    /// implicit its call supplies, by its coordinate in the operand store,
    /// with the supply and the component's place in the slot: the operand's
    /// node is the call's own, which no value lowers at, and the application
    /// mints the component's value there (`Lowerer::mint_supplied`).
    pub components: BTreeMap<FormPlace, (Arc<model::Supplied>, model::ComponentPlace)>,
    /// Each operand a recursive call passes for an implicit it omits before
    /// its fixpoint, by its coordinate in the operand store: the function's
    /// own implicit, which the fixpoint binds outside and the call leaves out
    /// of its application. The operand's node is the call's own, which no
    /// value lowers at.
    pub kept_implicits: BTreeSet<FormPlace>,
    /// Each model implicit flattened into one parameter per component, by the
    /// frame its name resolves to.
    pub flattened: BTreeMap<ScopeId, model::Flattened>,
    /// Each model implicit a function's telescope writes, by the slot of the
    /// function, beside the entry of its merged telescope that writes it.
    pub written_slots: BTreeMap<SlotIndex, Vec<(usize, model::WrittenSlot<'source>)>>,
    /// Each hole nominated for an omitted implicit or a written wildcard, in
    /// the order nominated, with what it stands for.
    pub nominations: BTreeMap<gandr_core_term::hole::HoleId, implicit::Nomination<'source>>,
    /// How many holes each form nominated, by the form and the origin the
    /// holes' names say: a nominated hole's name counts its form's holes of
    /// its origin.
    pub nominated_places: BTreeMap<
        (
            gandr_core_term::hole::HoleForm,
            gandr_core_term::hole::HoleOrigin,
        ),
        u32,
    >,
    /// Each callable operation's minted type and body, by slot.
    pub operated: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// Each derived rule's minted type and proof, by slot: a derived rule
    /// declaration's statement and each lemma its proof rests on.
    pub derivations: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// The prelude's `Eq.generic`, once the prelude is declared.
    pub generic: Option<SlotIndex>,
    /// The laws the prelude admits of the host's equalities, by base type and
    /// law, once the prelude is declared.
    pub hosted: alloc::vec::Vec<(
        gandr_kernel_term::BaseType,
        gandr_core_term::generic::law::Statement,
        ConstantIndex,
    )>,
    /// Each definition written `Eq.generic(T)` or one of its laws, by its
    /// slot, with the data declaration `T` names.
    pub requested: BTreeMap<SlotIndex, generic::Requested<'source>>,
    /// Each derived equality's or law's minted type and body, by slot.
    pub generics: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// The sorts each minted forgetting map puts back, in signature order, by
    /// its slot.
    pub forgotten: BTreeMap<SlotIndex, Vec<gandr_theory_levitation::Name>>,
    /// Each `theory` block's definition, `S : Theory`, as its minted type and
    /// value, by slot.
    pub presented: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// The frame of every capability a capability scope binds.
    pub capabilities: BTreeSet<ScopeId>,
    /// The theory each capability scope over one reads as its interface, by
    /// the frame of the capability it binds.
    pub theory_capabilities: BTreeMap<ScopeId, Arc<capability::TheoryInterface>>,
    /// The interface each capability a capability scope binds answers, by its
    /// frame: what a call resolving an instance reads.
    pub answered: BTreeMap<ScopeId, gandr_core_term::effect::EffectName>,
    /// Each instance a label of a function's result row binds, by its frame,
    /// with its interface and the region binder it lives at.
    pub labelled: BTreeMap<
        ScopeId,
        (
            gandr_core_term::effect::EffectName,
            gandr_core_term::effect::capability::RegionBinder,
        ),
    >,
    /// The row each world requires, `world w requires [ … ] ;`, its
    /// interfaces named whole each held, by the world's position. A world
    /// that requires none of them has no entry.
    pub world_rows: BTreeMap<ConstantIndex, gandr_core_term::effect::EffectRow>,
    /// The interface and region binder of each instance parameter, by its
    /// binder tile: what the declared type mints its capability type from.
    pub instance_parameters: BTreeMap<
        NodeIndex,
        (
            gandr_core_term::effect::EffectName,
            gandr_core_term::effect::capability::RegionBinder,
        ),
    >,
    /// The theory at the sorts its row entry fixes, of each instance parameter
    /// whose label names a theory, by its binder tile: what its capability
    /// type mints its signature from.
    pub instance_theories: BTreeMap<NodeIndex, Arc<capability::TheoryInterface>>,
    /// The region each capability type written at a scope, a hold or a
    /// region binder lives in, by the capability type's node.
    pub regions: BTreeMap<NodeIndex, gandr_core_term::effect::capability::Region>,
    /// Each application's renaming, in source order, or the refusal of the
    /// argument type it could not read: built during the mint sweep, before
    /// the first type written after the application mints.
    pub renamings: Vec<Result<Renaming, LoweringRefusal<'source>>>,
    /// Each manifest type an instance exports, by its application and the
    /// template's type: that type, renamed by the application, at the
    /// template's sort.
    pub instance_types: BTreeMap<(InstanceIndex, NodeIndex), InstanceType>,
    /// Each slot of an application — a witness or an image of its functor's
    /// body — with the declaration it amounts to.
    pub instantiated: BTreeMap<SlotIndex, DeclarationOutcome<'source>>,
    /// Each function and each round trip of a path, with the declaration it
    /// amounts to.
    pub pathed: BTreeMap<SlotIndex, DeclarationOutcome<'source>>,
    /// The frame of every continuation an operation clause binds.
    pub resumptions: BTreeSet<ScopeId>,
    /// Every described family decoded so far, by its description's name: a
    /// later description, in its own source or one importing it, reads it.
    pub described_types:
        BTreeMap<gandr_theory_levitation::Name, gandr_core_term::description::TypeBinding>,
    /// Each node's source: the source its top-level form starts in.
    pub source_of: NodeTable<SourceIndex>,
    /// The source the passes are lowering, and where its share of each list
    /// they read begins.
    pub current: Current,
    /// The current source's own positions, in ascending order.
    pub own: Vec<NodeIndex>,
}

impl<'run, 'source> Context<'run, 'source>
{
    /// The state for lowering `tree`, everything unread.
    ///
    /// # Specification
    /// - requires: the collected names and ownership positions describe this
    ///   tree.
    /// - ensures: one unread, unplanned, unminted, unbridged and unscoped cell
    ///   is allocated per syntax node; scratch stores and export indexes start
    ///   empty.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty working state is consumed by paired
    ///   declarations, nested modules and attributed refusals without leaking
    ///   prior node state.
    /// - witness: `gandr-surface-lowering::lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `gandr-surface-lowering::lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `gandr-surface-lowering::tests::modules::deeply_nested_modules_lower_and_resolve_at_every_depth`
    #[spec(
        ensures: |ret| {
            let count = usize::from(tree.node_count());
            usize::from(ret.readings.count()) == count
                && ret
                    .readings
                    .iter()
                    .all(|(_, reading)| matches!(*reading, Reading::Unread))
                && usize::from(ret.plans.count()) == count
                && ret
                    .plans
                    .iter()
                    .all(|(_, plan)| matches!(*plan, Plan::Unplanned))
                && usize::from(ret.bridges.count()) == count
                && ret.bridges.iter().all(|(_, bridge)| *bridge == Bridge::Bare)
                && usize::from(ret.lowered.count()) == count
                && ret
                    .lowered
                    .iter()
                    .all(|(_, node)| matches!(*node, Maybe::Absent(lowered::Absent::Unminted)))
                && usize::from(ret.payload.count()) == count
                && ret.payload.iter().all(|(_, flag)| !flag.0)
                && usize::from(ret.scopes.count()) == count
                && ret
                    .scopes
                    .iter()
                    .all(|(_, scope)| matches!(*scope, Maybe::Absent(_)))
                && ret.manifests.is_empty()
                && ret.exported.is_empty()
                && ret.witnessed.is_empty()
                && ret.operands.entries().is_empty()
                && ret.statements.entries().is_empty()
                && ret.parameters.entries().is_empty()
                && ret.classifiers.is_empty()
                && ret.thunked.is_empty()
                && ret.inherited.is_empty()
                && ret.answers.is_empty()
                && ret.in_type.is_empty()
                && ret.at_endpoint.is_empty()
                && ret.cases.entries().is_empty()
                && ret.arms.entries().is_empty()
                && ret.signatures.is_empty()
                && ret.data.is_empty()
                && ret.fuel == fuel
        },
    )]
    #[must_use]
    #[inline]
    pub fn new(
        pbg: &'run Pbg,
        tree: &'run SyntaxTree<'source>,
        collected: Collected<'source>,
        fuel: Fuel,
        recognition: Recognition,
    ) -> Self
    {
        let readings = NodeTable::filled(tree.blocks(), Reading::Unread);
        let plans = NodeTable::filled(tree.blocks(), Plan::Unplanned);
        let taken = NodeTable::filled(tree.blocks(), false);
        let bridges = NodeTable::filled(tree.blocks(), Bridge::Bare);
        let lowered = NodeTable::filled(tree.blocks(), Maybe::Absent(lowered::Absent::Unminted));
        let payload = NodeTable::filled(tree.blocks(), InPayload(false));
        let scopes = NodeTable::filled(tree.blocks(), Maybe::Absent(scoped::Absent::Unscoped));
        let leaves = NodeTable::filled(tree.blocks(), exits::Leaves::Never);
        let source_of = sources_of(tree, &collected.unit);
        let own = own_positions(&source_of, SourceIndex::default());

        Self {
            pbg,
            tree,
            collected,
            readings,
            plans,
            taken,
            bridges,
            lowered,
            payload,
            scopes,
            manifests: Vec::new(),
            expansions: BTreeMap::new(),
            computation_members: BTreeSet::new(),
            defining: BTreeMap::new(),
            exported: BTreeMap::new(),
            exported_types: BTreeMap::new(),
            witnessed: BTreeMap::new(),
            sealings: BTreeMap::new(),
            kind_checks: BTreeMap::new(),
            modelled: BTreeMap::new(),
            faults: BTreeMap::new(),
            untranslated: BTreeSet::new(),
            operands: ByForm::default(),
            else_ifs: ByForm::default(),
            segments: ByForm::default(),
            statements: ByForm::default(),
            parameters: ByForm::default(),
            scope: Scope::new(),
            recognition,
            fuel,
            pieces: Pieces::new(),
            scratch: Pieces::new(),
            classifiers: BTreeMap::new(),
            annotated_definitions: BTreeMap::new(),
            ascribed: BTreeMap::new(),
            packed: BTreeMap::new(),
            output_binders: BTreeMap::new(),
            typed_parameters: BTreeMap::new(),
            argued: BTreeMap::new(),
            parameter_typed: BTreeMap::new(),
            awaiting: BTreeSet::new(),
            fielded: BTreeMap::new(),
            thunked: BTreeMap::new(),
            dependent_answers: BTreeMap::new(),
            inherited: BTreeMap::new(),
            grouped: BTreeMap::new(),
            labels: Vec::new(),
            covers: Vec::new(),
            data_frames: Vec::new(),
            stand_ins: BTreeSet::new(),
            kinds: BTreeSet::new(),
            classified: BTreeMap::new(),
            fixed_sorts: BTreeMap::new(),
            fixed_carriers: Vec::new(),
            ahead: Vec::new(),
            classified_ahead: BTreeSet::new(),
            unresolved: Vec::new(),
            answers: BTreeMap::new(),
            cocased: BTreeSet::new(),
            synthesised: Vec::new(),
            in_type: BTreeSet::new(),
            in_quote: BTreeSet::new(),
            static_bodies: BTreeSet::new(),
            static_lambdas: BTreeMap::new(),
            static_spans: Vec::new(),
            static_calls: BTreeSet::new(),
            at_endpoint: BTreeSet::new(),
            over_points: BTreeMap::new(),
            binders_over_points: BTreeMap::new(),
            argued_binders: BTreeMap::new(),
            leaves,
            exits: BTreeSet::new(),
            exitable: BTreeSet::new(),
            joined: BTreeSet::new(),
            leaving: BTreeSet::new(),
            iterated: BTreeSet::new(),
            looping: BTreeSet::new(),
            breaking: BTreeSet::new(),
            reentered: BTreeMap::new(),
            tested: BTreeSet::new(),
            held: BTreeSet::new(),
            endpoints: ByForm::default(),
            threading: BTreeMap::new(),
            reheld: BTreeMap::new(),
            carries: BTreeMap::new(),
            results: BTreeSet::new(),
            opened_models: BTreeMap::new(),
            let_bound: BTreeSet::new(),
            framed: BTreeSet::new(),
            looped_past: BTreeSet::new(),
            bodies: BTreeMap::new(),
            crossing: BTreeSet::new(),
            delimited: BTreeSet::new(),
            inferred: BTreeSet::new(),
            elided: Vec::new(),
            elidable: Vec::new(),
            asked: BTreeSet::new(),
            asked_runs: BTreeMap::new(),
            stated: BTreeMap::new(),
            opened: BTreeMap::new(),
            stated_tails: BTreeSet::new(),
            trailing: BTreeSet::new(),
            cases: ByForm::default(),
            arms: ByForm::default(),
            projected: ByForm::default(),
            signatures: BTreeMap::new(),
            worded: BTreeMap::new(),
            termed: BTreeMap::new(),
            word_types: BTreeMap::new(),
            looped: BTreeMap::new(),
            lettered: Vec::new(),
            pointed: Vec::new(),
            described: BTreeMap::new(),
            data: Vec::new(),
            constructors: Vec::new(),
            codata_described: BTreeMap::new(),
            codata: Vec::new(),
            resolutions: Vec::new(),
            shadows: ByForm::default(),
            recursions: BTreeMap::new(),
            staged_parameters: BTreeMap::new(),
            stage_marks: BTreeMap::new(),
            stage_bounds: BTreeMap::new(),
            region_binders: BTreeMap::new(),
            mode_binders: BTreeMap::new(),
            view_places: BTreeMap::new(),
            assignments: BTreeMap::new(),
            view_types: BTreeSet::new(),
            ended_views: BTreeSet::new(),
            planned_supplies: BTreeMap::new(),
            supplies: BTreeMap::new(),
            handler_laws: BTreeMap::new(),
            planned_models: BTreeMap::new(),
            model_candidates: BTreeMap::new(),
            models: BTreeMap::new(),
            ran: BTreeMap::new(),
            holes: Vec::new(),
            hole_groups: HoleGroups::default(),
            pattern_stated: BTreeMap::new(),
            scrutinised: BTreeMap::new(),
            descents: BTreeMap::new(),
            injected: BTreeMap::new(),
            sibling_calls: Vec::new(),
            reader: Reading::Unread,
            type_read: BTreeSet::new(),
            valued_telescopes: BTreeMap::new(),
            nullary: BTreeMap::new(),
            typed_heads: BTreeMap::new(),
            supplied: BTreeSet::new(),
            nominated: BTreeMap::new(),
            abstracted: BTreeMap::new(),
            instanced: BTreeMap::new(),
            components: BTreeMap::new(),
            kept_implicits: BTreeSet::new(),
            flattened: BTreeMap::new(),
            written_slots: BTreeMap::new(),
            nominations: BTreeMap::new(),
            nominated_places: BTreeMap::new(),
            operated: BTreeMap::new(),
            derivations: BTreeMap::new(),
            generic: None,
            hosted: alloc::vec::Vec::new(),
            requested: BTreeMap::new(),
            generics: BTreeMap::new(),
            forgotten: BTreeMap::new(),
            presented: BTreeMap::new(),
            renamings: Vec::new(),
            instance_types: BTreeMap::new(),
            instantiated: BTreeMap::new(),
            pathed: BTreeMap::new(),
            capabilities: BTreeSet::new(),
            theory_capabilities: BTreeMap::new(),
            answered: BTreeMap::new(),
            labelled: BTreeMap::new(),
            world_rows: BTreeMap::new(),
            instance_parameters: BTreeMap::new(),
            instance_theories: BTreeMap::new(),
            regions: BTreeMap::new(),
            resumptions: BTreeSet::new(),
            described_types: BTreeMap::new(),
            source_of,
            current: Current::default(),
            own,
        }
    }
}

/// Each node's source: a root's and a top-level node's is the source its span
/// starts in, and every other node's is its parent's.
///
/// # Specification
/// - requires: `unit` lays out the text `tree` was parsed from.
/// - ensures: one source per node; each root holds the source it starts in, and
///   every node under a top-level form holds that form's source.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a two-source unit's nodes split at the second source's
///   first form, whether its tree is one parse or a closure's with the
///   document's laid after it.
/// - witness: `gandr-surface-lowering::tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
/// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[spec(ensures: |ret| ret.count() == tree.node_count())]
#[must_use]
#[inline]
pub fn sources_of(
    tree: &SyntaxTree<'_>,
    unit: &Unit,
) -> NodeTable<SourceIndex>
{
    let mut of = NodeTable::filled(core::iter::empty(), SourceIndex::default());
    extend_sources(&mut of, tree, unit);
    of
}

/// Extend `of`, the sources of `tree`'s first blocks, with those of the blocks
/// after them, as [`sources_of`] reads them.
///
/// # Specification
/// - requires: `of` is [`sources_of`] of a tree whose blocks `tree`'s first
///   blocks are, at the same positions over the same text, under a unit whose
///   sources `unit`'s first sources are; empty for a whole tree.
/// - ensures: `of` is [`sources_of`] of `tree` under `unit`.
/// - fails: never.
/// - panics: none.
/// - intension: only the blocks after `of`'s are visited. Under the layout by
///   form each of their nodes is a root added after the first blocks or a node
///   of a form added after them, and every node of a first block's form lies in
///   a first block, so a document resumed after its closure reads its own
///   nodes.
///
/// # Adequacy
/// - hypothesis: L3 — as [`sources_of`].
/// - witness: `gandr-surface-lowering::tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[spec(ensures: of.count() == tree.node_count())]
#[inline]
pub fn extend_sources(
    of: &mut NodeTable<SourceIndex>,
    tree: &SyntaxTree<'_>,
    unit: &Unit,
)
{
    let read = of.blocks();
    of.widen(tree.blocks(), SourceIndex::default());
    let roots = tree.roots();
    let added = roots
        .get(roots.partition_point(|&root| root.block() < read) ..)
        .unwrap_or_default();
    for &root in added {
        let Some(node) = tree.node(root)
        else {
            continue;
        };
        let rooted = unit.source_at(node.span().start());
        if let Some(held) = of.get_mut(root) {
            *held = rooted;
        }
        for child in tree.children(root) {
            let source = tree
                .node(child)
                .map_or(rooted, |node| unit.source_at(node.span().start()));
            if let Some(held) = of.get_mut(child) {
                *held = source;
            }
            // The child's descendants are one block, read whole.
            if let Some(first) = tree.children(child).next() {
                of.fill(first.block(), source);
            }
        }
    }
}

/// The positions `source_of` gives to `source`, in ascending order.
///
/// # Specification
/// - ensures: exactly the positions whose source is `source`, ascending.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`sources_of`].
/// - witness: `gandr-surface-lowering::tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
#[spec(ensures: |ret| ret.is_sorted() && ret.iter().all(|&position| source_of.get(position) == Some(&source)))]
#[must_use]
#[inline]
pub fn own_positions(
    source_of: &NodeTable<SourceIndex>,
    source: SourceIndex,
) -> Vec<NodeIndex>
{
    source_of
        .iter()
        .filter(|&(_, &held)| held == source)
        .map(|(position, _)| position)
        .collect()
}
