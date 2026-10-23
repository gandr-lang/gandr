//! Identities at run time: a flow runs as the translator it moves values
//! with, and a path between types as its two maps.
//!
//! The command IL carries no identity types, so neither family has an image
//! of its own. What it does carry is functions, and every identity the
//! checker admits has an action on values that functions compute: the
//! kernel's ride table and its transport table, read at a motive, are
//! programs. The focusing therefore sends each flow to a thunk of one
//! argument, its translator; each path between types to the pair of its two
//! maps, forward then backward; and each ride and each transport to the
//! motive's action applied to the identity's image and the moved value.
//!
//! # Flows
//!
//! | Core | Producer |
//! |---|---|
//! | `forward(f)` | `𝓥⟦f⟧`, the translator itself |
//! | `stay(a)`, a session simulation | the identity thunk |
//! | `p then q` | `thunk(force(compose) 𝓥⟦p⟧ 𝓥⟦q⟧)` |
//! | `arrow(d, c)` | `thunk(force(wrap) 𝓥⟦d⟧ 𝓥⟦c⟧)` |
//! | `flowProduct(p, q)` | `thunk(force(pair) 𝓥⟦p⟧ 𝓥⟦q⟧)` |
//! | `ride(P, p, v)` | `force(ride_P) 𝓥⟦p⟧ 𝓥⟦v⟧` |
//!
//! `compose` is `thunk(λp. λq. λx. y ← force p x; force q y)`, `wrap` is
//! `thunk(λd. λc. λg. return thunk(λa'. a ← force d a'; b ← force g a; force
//! c b))` — the kernel's function-flow row with the boundaries as functions —
//! `pair` is `thunk(λp. λq. λx. a ← x.0; b ← x.1; a' ← force p a; b' ← force
//! q b; return (a', b'))` — the kernel's flow-product row, the components in
//! order — and `ride_P` is `thunk(λt. λv. M_P)`, built over the motive's
//! syntax by the kernel's rows in their order: at the decode of the motive's
//! own binder `M` is `force t v`; a product rides each component by its own
//! action, a sum its payload under its summand, a list each element by a
//! native fold; the singleton `y. Flow(D, l, y)` composes the ridden flow with
//! `t`; any other motive — one that ignores its binder, a run type, a family
//! over an element carrier — returns the value unchanged. That last row is
//! exact: the checker refuses at a universe carrier every motive no row
//! computes, and over an element carrier every closed flow is a stay or a
//! composite of stays, whose action is the identity.
//!
//! # Paths between types
//!
//! A path `p : Path(Type, A, B)` runs as the pair `(to, from)` of `to : U (A →
//! F B)` and `from : U (B → F A)`. A pair of two functions is a value the IL
//! already has, so a path adds no former to it.
//!
//! | Core | Producer |
//! |---|---|
//! | `ua(e)`, carrying its forward map `f` | `(𝓥⟦f⟧, thunk(force(inverse) 𝓥⟦e⟧))` |
//! | `here(a)`, a native reflexivity | `(identity, identity)` |
//! | `equiv(f, g)`, a native equivalence of `f` and `g` | `(𝓥⟦f⟧, 𝓥⟦g⟧)` |
//! | the native product of `p` and `q` | `(thunk(force(both₀) 𝓥⟦p⟧ 𝓥⟦q⟧), thunk(force(both₁) 𝓥⟦p⟧ 𝓥⟦q⟧))` |
//! | `transport(p, v)` along a native path | `force(forward) 𝓥⟦p⟧ 𝓥⟦v⟧` |
//! | `tr(P, here(a), v)` | `return 𝓥⟦v⟧`, or `𝓒⟦c⟧` for `v = ⟨c⟩`, whatever `P` is |
//! | `tr(P, p, v)`, `p` or `v` a returned value | `force(transport_from_P) 𝓞⟦p⟧ 𝓞⟦v⟧` |
//! | `tr(P, p, v)` | `force(transport_P) 𝓥⟦p⟧ 𝓥⟦v⟧` |
//!
//! `inverse` is `thunk(λe. λy. i ← e.1; l ← i.0; g ← l.0; force g y)`: the
//! record `e : A ≃ B` is `(to, ((g, sect), (h, retr)))`, and its map back is
//! the left inverse `g`. Its laws are evidence the kernel checked; they ride
//! inside `e` and nothing forces them. `both_d` is `thunk(λp. λq. λx. a ← x.0;
//! b ← x.1; f ← p.d; g ← q.d; a' ← force f a; b' ← force g b; return (a',
//! b'))`, the componentwise map in the direction `d`, and `forward` is
//! `thunk(λp. λv. f ← p.0; force f v)`. Transport along reflexivity keeps the
//! value before the motive is read, as the kernel's first transport row
//! does. A returned value `⟨c⟩` — `back(p)` and `p then q` are the transports
//! that compute them — has no producer of its own, so as a transport's
//! operand it is passed as `𝓞⟦⟨c⟩⟧ = thunk(𝓒⟦c⟧)` and run first, any other
//! operand as `𝓞⟦v⟧ = 𝓥⟦v⟧`: `transport_from_P` is `thunk(λp. λv. p' ←
//! force p; v' ← force v; force(transport_P) p' v')`, forcing only the
//! operands passed suspended, as the kernel reads `E[c]` as `c to x. E[x]`.
//!
//! `transport_P` is `thunk(λp. λv. M_P)`, built over the motive's syntax by
//! the kernel's transport rows in their order: a motive that never reads its
//! binder returns `v`; at the decode of the binder `M` is `f ← p.0; force f
//! v`, as `forward`'s; a product moves each component by its own action, a
//! sum its payload under its summand, a list each element by a native fold,
//! and a function `U(A → F B)` into a returner that performs no effect
//! becomes `return thunk(λa. s ← (g ← p.1; f ← p.0; return (g, f)); x ←
//! force(M_A) s a; y ← force v x; force(M_B) p y)`: the argument moves back
//! by its own action at the reversed pair, the function applies, and the
//! result moves forward. A path between types whose moving endpoints are the
//! binder, `y. Path(Type, y, c)`, `y. Path(Type, a, y)` or `y. Path(Type, y,
//! y)`, composes the moved path's maps with `p`'s on the ends that move:
//! the new forward map runs `p.1` first when the left end moves, then the
//! moved path's forward map, then `p.0` when the right end moves, and the
//! new backward map runs `p.1` first when the right end moves, then the
//! moved path's backward map, then `p.0` when the left end moves. A run of a
//! quoted session with no recursion, `y. Run(S)`, moves each payload by its
//! payload type's action and keeps the moves and labels: the core has no
//! eliminator for a run, so the action's body is the IL's match on the run,
//! one arm per complete run the protocol admits ([`RunCase`]); a recursive
//! session admits unboundedly many and is refused by name. Any other motive
//! has no row the normaliser computes, and focusing refuses its transport by
//! the head of the first part no row reads ([`MotiveHead`]); a telescope
//! transport is refused the same way.
//!
//! **Choice.** A path as the pair of its maps and transport as the motive's
//! action on it, rather than a path former of the IL's own with transport its
//! destructor: the IL would carry an identity type only to compute what two
//! functions compute, and the emitter and the readback would each grow a case
//! for it. The left inverse rather than the right one: the two agree up to a
//! path, the record names `g` first, and no conversion rule picks either, so
//! the choice is the record's order. **Certification.** The kernel admitted
//! the program, the record's laws checked as its fields, and the run
//! computes the rows the normaliser's and the kernel's transport compute on
//! the same motive, so a transported first-order value reads back through the
//! ordinary readback as the value conversion gives: every corpus `runs` row
//! on a transport stands beside the `checks` row it agrees with. **Reversal.**
//! A motive the corpus runs that no row reads earns its row in the normaliser
//! and the kernel first, so its `runs` row has a `checks` row to agree with,
//! and then here.
//!
//! # Combinators are closed
//!
//! Every combinator is closed, so the focusing builds it in a scratch core
//! arena and focuses it into the same command arena; it is applied to the
//! identity's parts rather than closing over them, so no producer is shifted
//! under a binder it did not have. A ride of an open flow and a transport
//! along an open path run the same way: the image is whatever value the
//! variable is bound to at run time.
//!
//! The alternative was a core-to-core pass replacing identities before
//! focusing, rejected because the replacement must rebuild every ancestor of a
//! ride or a transport to name the new node, where the focusing already visits
//! each node once. The choice reverses if the command IL gains an identity
//! former of its own.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::session::ProtocolNode;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionType;
use gandr_core_term::session::Step;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::ProducerArity;
use crate::focus::FocusRefusal;
use crate::il::Selector;

/// A closed program an identity's image, or a call whose argument is a
/// returned value, applies to its parts.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Combinator
{
    /// `thunk(λx. return x)`: the translator of a stay and of a session
    /// simulation, and both maps of a reflexivity.
    Identity,
    /// `thunk(λp. λq. λx. y ← force p x; force q y)`: sequential composition.
    Compose,
    /// `thunk(λd. λc. λg. return thunk(λa'. a ← force d a'; b ← force g a;
    /// force c b))`: the arrow's action on its boundaries.
    Wrap,
    /// `thunk(λp. λq. λx. a ← x.0; b ← x.1; a' ← force p a; b' ← force q b;
    /// return (a', b'))`: the flow product's action, componentwise.
    Pair,
    /// `thunk(λt. λv. M_P)`: the action of the ride motive `P`, a value type
    /// under one binder in the arena being focused.
    Ride(ValueTypeId),
    /// `thunk(λe. λy. i ← e.1; l ← i.0; g ← l.0; force g y)`: a bi-invertible
    /// record's map back, its left inverse.
    Inverse,
    /// `thunk(λp. λq. λx. a ← x.0; b ← x.1; f ← p.d; g ← q.d; a' ← force f
    /// a; b' ← force g b; return (a', b'))`: one map of a native product of
    /// two paths, componentwise.
    Both(Direction),
    /// `thunk(λp. λv. f ← p.0; force f v)`: transport along a native path.
    Forward,
    /// `thunk(λp. λv. M_P)`: the action of the transport motive `P`, a value
    /// type under one binder in the arena being focused.
    Transport(ValueTypeId),
    /// `thunk(λp. λv. p' ← force p; v' ← force v; force(M_P) p' v')`: the
    /// transport motive `P`'s action where the path, the moved value or both
    /// are returned values, each passed suspended and run first; an operand
    /// that is not one is passed as it is and not forced.
    TransportFrom
    {
        /// The motive, a value type under one binder in the arena being
        /// focused.
        motive: ValueTypeId,
        /// Whether the path is passed suspended.
        path: bool,
        /// Whether the moved value is passed suspended.
        value: bool,
    },
    /// `thunk(λf. λa. x ← force a; force f x)`: a call whose argument is a
    /// returned value, `⟨c⟩`, the call and `c` each passed suspended and `c`
    /// run first, as the kernel reads `E[c]` as `c to x. E[x]`.
    RunArgument,
}

impl Combinator
{
    /// How many of an identity's parts its image applies the combinator to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `0` for the identity, which is a part itself; `1` for the
    ///   inverse, applied to its record; `2` for every other combinator,
    ///   applied to two parts or to an image and a moved value.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reflexivity, a `ua` and a transport each focus and
    ///   run to the value the kernel's rows compute, which an image applying
    ///   the wrong number of parts would not.
    /// - witness: `tests::run::transports_run_by_the_motives_action`
    #[spec(ensures: |ret| usize::from(ret) == match self {
        Self::Identity => 0_usize,
        Self::Inverse => 1_usize,
        Self::Compose | Self::Wrap | Self::Pair | Self::Ride(_) | Self::Both(_) | Self::Forward | Self::Transport(_) | Self::TransportFrom { .. } | Self::RunArgument => 2_usize,
    })]
    #[must_use]
    pub(crate) fn applied(self) -> ProducerArity
    {
        ProducerArity::from(match self {
            Self::Identity => 0_usize,
            Self::Inverse => 1_usize,
            Self::Compose
            | Self::Wrap
            | Self::Pair
            | Self::Ride(_)
            | Self::Both(_)
            | Self::Forward
            | Self::Transport(_)
            | Self::TransportFrom { .. }
            | Self::RunArgument => 2_usize,
        })
    }
}

/// Which of a path's two maps a combinator reads.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Direction
{
    /// The forward map, component `0` of the image.
    Forward,
    /// The backward map, component `1` of the image.
    Backward,
}

impl Direction
{
    /// The component of a path's image that holds this map.
    ///
    /// # Specification
    /// trivial.
    fn component(self) -> gandr_kernel_term::Component
    {
        gandr_kernel_term::Component::from(match self {
            Self::Forward => 0_usize,
            Self::Backward => 1_usize,
        })
    }
}

/// The head of a transport motive's part that no transport row reads: what a
/// refused element transport names.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MotiveHead
{
    /// A datatype applied to arguments that read the binder.
    Data,
    /// A record type.
    Record,
    /// A universe of native paths.
    PathUniverse,
    /// A path type: the family `back`, `then` and `cong` transport in.
    Path,
    /// A flow type.
    Flow,
    /// A run type whose code is not a quoted session.
    Run,
    /// A run of a recursive session: it admits unboundedly many shapes, and
    /// the IL's match names each shape it answers.
    RecursiveRun,
    /// A prefix type: an open play does not transport.
    Prefix,
    /// A dialogue type: a dialogue does not transport.
    Dialogue,
    /// A base type.
    Base,
    /// A dependent pair type.
    Sigma,
    /// A thunk type, a function's among them.
    Thunk,
    /// A universe.
    Universe,
    /// A lifted type.
    Lift,
    /// The decode of a code other than the moving one.
    Element,
    /// An abstract type.
    Abstract,
    /// A staged type.
    Staged,
    /// The classifier of a type operator.
    StaticPi,
    /// The unknown type.
    Unknown,
    /// A stack type.
    Stack,
    /// A session type.
    Session,
    /// A capability type.
    Capability,
    /// The opaque buffer type a receive places live.
    Buffer,
    /// A value kept in a region.
    Kept,
    /// A world type.
    World,
    /// A telescope: the motive of a telescope transport.
    Telescope,
}

impl fmt::Display for MotiveHead
{
    /// Names the head.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the head's name, each head's apart from every other's.
    /// - provides: the head a refused element transport names.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every head reads apart from every other, a prefix
    ///   type's among them.
    /// - witness: `tests::refusals::motive_heads_read_apart`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Data => "a datatype",
            Self::Record => "a record type",
            Self::PathUniverse => "a universe of native paths",
            Self::Path => "a path type",
            Self::Flow => "a flow type",
            Self::Run => "a run type",
            Self::RecursiveRun => "a run of a recursive session",
            Self::Prefix => "a prefix type",
            Self::Dialogue => "a dialogue type",
            Self::Base => "a base type",
            Self::Sigma => "a dependent pair type",
            Self::Thunk => "a thunk type",
            Self::Universe => "a universe",
            Self::Lift => "a lifted type",
            Self::Element => "the decode of a code other than the moving one",
            Self::Abstract => "an abstract type",
            Self::Staged => "a staged type",
            Self::StaticPi => "the classifier of a type operator",
            Self::Unknown => "the unknown type",
            Self::Stack => "a stack type",
            Self::Session => "a session type",
            Self::Capability => "a capability type",
            Self::Buffer => "the buffer type",
            Self::Kept => "a type kept in a region",
            Self::World => "a world type",
            Self::Telescope => "a telescope",
        })
    }
}

/// Why a transport motive has no action the IL computes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Unread
{
    /// A part reads the binder and no row reads its head.
    Head(MotiveHead),
    /// A part names no value type of the core arena.
    Dangling,
}

/// The identity family a motive's action moves along.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Family
{
    /// A flow, whose image is its translator.
    Flow,
    /// A path between types, whose image is the pair of its maps.
    Path,
}

/// The row a motive's action takes at one part.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Row<'core>
{
    /// The value is returned unchanged.
    Unchanged,
    /// The decode of the moving binder: the image's forward map applies.
    Decode,
    /// A product: each component moves by its own action.
    Product(&'core [ValueTypeId]),
    /// A record: each field moves by its own action, in label order.
    Record(&'core BTreeMap<gandr_core_term::FieldLabel, ValueTypeId>),
    /// A sum: the payload moves under its summand.
    Sum(&'core [ValueTypeId]),
    /// A list: each element moves, in order.
    List(ValueTypeId),
    /// The flow singleton `y. Flow(D, l, y)`: the ridden flow composes with
    /// the image.
    Singleton,
    /// A function `U(A → F B)` into a returner that performs no effect: the
    /// argument moves back by its own action at the reversed pair, the
    /// function applies, and the result moves forward.
    Function
    {
        /// The argument's type `A`.
        argument: ValueTypeId,
        /// The result's type `B`.
        result: ValueTypeId,
    },
    /// A suspension `U(F B)` whose returner performs no effect: forced, it
    /// runs and its result moves forward.
    Suspended(ValueTypeId),
    /// A path between types whose moving endpoints are the binder and whose
    /// other parts read no binder: the moved path's maps compose with the
    /// image's on the ends that move.
    Ends(Moving),
    /// A run of a session with no recursion: each payload moves by its
    /// payload type's action, one match arm per complete run the protocol
    /// admits.
    Run(&'core SessionType),
}

/// Which endpoints of a path between types the moving binder is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Moving
{
    /// The left endpoint alone, as in `y. Path(Type, y, c)`.
    Left,
    /// The right endpoint alone, as in `y. Path(Type, a, y)`.
    Right,
    /// Both endpoints, as in `y. Path(Type, y, y)`.
    Both,
}

/// Whether a motive part reads its binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Occurrence
{
    /// No occurrence names the binder: the part is the same at every point.
    Absent,
    /// Some occurrence names the binder.
    Present,
}

/// Whether the motive part `node` reads its binder.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Occurrence::Absent`] exactly when the part, read under one
///   binder, strengthens out from under it: no occurrence names the binder.
/// - provides: the transport table's first row, decided on the part's syntax in
///   a scratch arena of its own, which is dropped.
/// - fails: [`Unread::Dangling`] for a part that does not import.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a constant motive returns the value unchanged, and a
///   motive at the decode of its binder applies the forward map: answering
///   either for the other changes the run's value.
/// - witness: `tests::run::transports_run_by_the_motives_action`
#[spec(ensures: |ret| ret != Err(Unread::Head(MotiveHead::Unknown)))]
fn occurrence(
    core: &CoreArena,
    node: ValueTypeId,
) -> Result<Occurrence, Unread>
{
    let mut scratch = CoreArena::new();
    let imported = gandr_core_term::TypeImporter::new(core, &mut scratch)
        .value_type(node)
        .map_err(|gandr_core_term::ImportFault| Unread::Dangling)?;
    Ok(
        match gandr_core_term::strengthen_value_type(&mut scratch, imported, Binders::ONE) {
            Maybe::Present(_) => Occurrence::Absent,
            Maybe::Absent(_) => Occurrence::Present,
        },
    )
}

/// The head of a value type no transport row reads.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the head of `node`'s former; a base type, a web, a product, a sum
///   and a list share [`MotiveHead::Base`].
/// - provides: the head a refused transport names.
/// - panics: none.
/// - executable: none — a clause would restate the match arm by arm.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive run, a run of no quoted session and a prefix
///   type, each a motive that reads its binder, are refused by their own heads.
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
fn head(node: &ValueType) -> MotiveHead
{
    match *node {
        ValueType::Data { .. } => MotiveHead::Data,
        ValueType::Record(_) => MotiveHead::Record,
        ValueType::PathUniverse(..) => MotiveHead::PathUniverse,
        ValueType::Path { .. } => MotiveHead::Path,
        ValueType::Flow { .. } => MotiveHead::Flow,
        ValueType::Run(_) => MotiveHead::Run,
        ValueType::Prefix(_) => MotiveHead::Prefix,
        ValueType::Dialogue(_) => MotiveHead::Dialogue,
        ValueType::Base(_)
        | ValueType::Web
        | ValueType::Product(_)
        | ValueType::Sum(_)
        | ValueType::List(_) => MotiveHead::Base,
        ValueType::Sigma { .. } => MotiveHead::Sigma,
        ValueType::Thunk(_) => MotiveHead::Thunk,
        ValueType::Universe { .. } => MotiveHead::Universe,
        ValueType::Lift { .. } => MotiveHead::Lift,
        ValueType::Element { .. } => MotiveHead::Element,
        ValueType::Abstract(_) => MotiveHead::Abstract,
        ValueType::Staged { .. } => MotiveHead::Staged,
        ValueType::StaticPi { .. } => MotiveHead::StaticPi,
        ValueType::Unknown => MotiveHead::Unknown,
        ValueType::Stack { .. } => MotiveHead::Stack,
        ValueType::Session(_) => MotiveHead::Session,
        ValueType::Capability { .. } => MotiveHead::Capability,
        ValueType::Buffer => MotiveHead::Buffer,
        ValueType::Kept { .. } => MotiveHead::Kept,
        ValueType::World(_) => MotiveHead::World,
    }
}

/// The session a run motive's code quotes, when it has no recursion.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the session type `code` quotes, as written, when its protocol
///   holds no `mu`.
/// - fails: [`Unread::Head`] with [`MotiveHead::Run`] for a code that is not a
///   quoted session, the session a motive's binder names among them; with
///   [`MotiveHead::RecursiveRun`] for a recursive session.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a run of a fixed protocol and a run of a choice move
///   their payloads; a run of a recursive protocol is refused by name.
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
#[spec(ensures: |ret| ret.as_ref().is_err() || matches!(core.value(code), Some(&Value::Quote(_))))]
fn run_session(
    core: &CoreArena,
    code: ValueId,
) -> Result<&SessionType, Unread>
{
    let unquoted = Unread::Head(MotiveHead::Run);
    let Some(&Value::Quote(quoted)) = core.value(code)
    else {
        return Err(unquoted);
    };
    let Some(&ValueType::Session(ref session)) = core.value_type(quoted)
    else {
        return Err(unquoted);
    };
    if session
        .protocol()
        .nodes()
        .iter()
        .any(|node| matches!(*node, ProtocolNode::Mu(_)))
    {
        return Err(Unread::Head(MotiveHead::RecursiveRun));
    }
    Ok(session)
}

/// The row `family`'s action takes at the motive part `node`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a flow, the module table's ride rows in their order, any
///   other part unchanged; for a path, [`Row::Unchanged`] for a part that never
///   reads its binder, then the decode of the binder, a non-empty product, a
///   record, a sum, a list and a run of a quoted session with no recursion.
/// - provides: the one reading the focusing's refusal and the combinator's
///   build share.
/// - fails: [`Unread::Dangling`] for a part naming no value type;
///   [`Unread::Head`] for a path motive's part that reads its binder under a
///   head no row reads, [`MotiveHead::RecursiveRun`] for a run of a recursive
///   session.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — rides and transports at the decode, through a product, a
///   sum and a list, transports through a record, and at a constant part run to
///   the kernel rows' values; a transport in a path family is refused by its
///   head.
/// - witness: `tests::run::rides_run_by_the_motives_action`
/// - witness: `tests::run::transports_run_by_the_motives_action`
/// - witness: `tests::run::a_transport_no_row_reads_is_refused_by_its_head`
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
#[spec(ensures: |ret| family == Family::Path || matches!(ret, Ok(_) | Err(Unread::Dangling)))]
fn row(
    core: &CoreArena,
    node: ValueTypeId,
    family: Family,
) -> Result<Row<'_>, Unread>
{
    let read = core.value_type(node).ok_or(Unread::Dangling)?;
    if family == Family::Path && occurrence(core, node)? == Occurrence::Absent {
        return Ok(Row::Unchanged);
    }
    // Whether `code` is the moving binder: the innermost intuitionistic
    // variable.
    let moving = |code: ValueId| matches!(core.value(code), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if index == DeBruijnIndex::from(0_u32));
    Ok(match *read {
        ValueType::Element { code, .. } if moving(code) => Row::Decode,
        ValueType::Product(ref parts) if !parts.is_empty() => Row::Product(parts),
        ValueType::Record(ref fields) if family == Family::Path => Row::Record(fields),
        ValueType::Sum(ref parts) => Row::Sum(parts),
        ValueType::List(element) => Row::List(element),
        ValueType::Flow { target, .. } if family == Family::Flow && moving(target) => {
            Row::Singleton
        },
        ValueType::Thunk(function) if family == Family::Path => {
            if let Some((argument, result)) = function_row(core, function) {
                Row::Function { argument, result }
            }
            else if let Some(result) = pure_result(core, function) {
                Row::Suspended(result)
            }
            else {
                return Err(Unread::Head(head(read)));
            }
        },
        ValueType::Path {
            carrier,
            left,
            right,
        } if family == Family::Path => match ends(core, node, (carrier, left, right))? {
            Some(row) => row,
            None => return Err(Unread::Head(head(read))),
        },
        ValueType::Run(code) if family == Family::Path => Row::Run(run_session(core, code)?),
        ValueType::Data { .. }
        | ValueType::Record(_)
        | ValueType::PathUniverse(..)
        | ValueType::Path { .. }
        | ValueType::Flow { .. }
        | ValueType::Run(_)
        | ValueType::Prefix(_)
        | ValueType::Dialogue(_)
        | ValueType::Web
        | ValueType::Base(_)
        | ValueType::Product(_)
        | ValueType::Sigma { .. }
        | ValueType::Thunk(_)
        | ValueType::Universe { .. }
        | ValueType::Lift { .. }
        | ValueType::Element { .. }
        | ValueType::Abstract(_)
        | ValueType::Staged { .. }
        | ValueType::StaticPi { .. }
        | ValueType::Unknown
        | ValueType::Stack { .. }
        | ValueType::Session(_)
        | ValueType::Capability { .. }
        | ValueType::Buffer
        | ValueType::Kept { .. }
        | ValueType::World(_) => match family {
            Family::Flow => Row::Unchanged,
            Family::Path => return Err(Unread::Head(head(read))),
        },
    })
}

/// The argument and result types of the function motive part `U(function)`
/// when `function` is an arrow into a returner that performs no effect.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some((A, B))` exactly for `A → F B` whose returner's effect row
///   is empty; `None` for a dependent arrow, any other codomain or an effectful
///   returner, whose call a transport cannot hand on as the value it returns.
/// - provides: the function row's guard, as the normaliser's `function_parts`
///   reads the same type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function carried along `ua` runs as the kernel's
///   function row computes it; refusing the arrow, or admitting an effectful
///   one, changes which transports focus.
/// - witness: `tests::run::a_function_runs_along_a_path_by_its_maps`
#[spec(ensures: |ret| ret.is_none_or(|(argument, _)| matches!(core.comp_type(function), Some(&CompType::Arrow { domain, .. }) if domain == argument)))]
fn function_row(
    core: &CoreArena,
    function: CompTypeId,
) -> Option<(ValueTypeId, ValueTypeId)>
{
    let &CompType::Arrow { domain, codomain } = core.comp_type(function)?
    else {
        return None;
    };
    Some((domain, pure_result(core, codomain)?))
}

/// The result type of `returner` when it is a returner that performs no
/// effect.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some(B)` exactly for `F B` whose effect row is empty; `None` for
///   any other computation type, or an effectful returner, whose run a
///   transport cannot hand on as the value it returns.
/// - provides: the guard the function row's result and the suspension row
///   share.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function and a suspension carried along a path run as
///   the kernel's rows compute them; admitting an effectful returner changes
///   which transports focus.
/// - witness: `tests::run::a_function_runs_along_a_path_by_its_maps`
#[spec(ensures: |ret| ret.is_none_or(|result| matches!(core.comp_type(returner), Some(&CompType::Returner { result: held, .. }) if held == result)))]
fn pure_result(
    core: &CoreArena,
    returner: CompTypeId,
) -> Option<ValueTypeId>
{
    let &CompType::Returner {
        result,
        ref effects,
    } = core.comp_type(returner)?
    else {
        return None;
    };
    effects.signatures().next().is_none().then_some(result)
}

/// The row of the path motive part `node`, `Path(carrier, left, right)`,
/// when it is a path between types whose moving endpoints are the binder.
///
/// # Specification
/// - requires: `node` is the part `Path(carrier, left, right)` of `core`.
/// - ensures: [`Row::Ends`] naming the endpoints that are the moving binder
///   when the carrier is a universe, at least one endpoint moves and the part
///   with each moving endpoint replaced by a closed value reads no binder;
///   `None` for an element carrier, whose paths are not pairs of maps, and for
///   an endpoint built from the binder.
/// - provides: the rows `back` and `then` transport along, the families `y.
///   Path(U, y, c)` and `y. Path(U, a, y)`.
/// - fails: [`Unread::Dangling`] for a part that does not import.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — `back(p)` and `p then q` along `ua` run to the maps the
///   kernel's rows compose; moving the wrong end, or composing in the wrong
///   order, changes the run's value.
/// - witness: `tests::run::derived_paths_run_as_their_composed_maps`
#[spec(ensures: |ret| matches!(ret, Ok(Some(Row::Ends(_)) | None) | Err(Unread::Dangling)))]
fn ends(
    core: &CoreArena,
    node: ValueTypeId,
    (carrier, left, right): (ValueTypeId, ValueId, ValueId),
) -> Result<Option<Row<'static>>, Unread>
{
    if !matches!(core.value_type(carrier), Some(&ValueType::Universe { .. })) {
        return Ok(None);
    }
    let is_binder = |code: ValueId| matches!(core.value(code), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if index == DeBruijnIndex::from(0_u32));
    let moving = match (is_binder(left), is_binder(right)) {
        (true, true) => Moving::Both,
        (true, false) => Moving::Left,
        (false, true) => Moving::Right,
        (false, false) => return Ok(None),
    };
    let left_moves = matches!(moving, Moving::Left | Moving::Both);
    let right_moves = matches!(moving, Moving::Right | Moving::Both);
    let mut scratch = CoreArena::new();
    let imported = gandr_core_term::TypeImporter::new(core, &mut scratch)
        .value_type(node)
        .map_err(|gandr_core_term::ImportFault| Unread::Dangling)?;
    let Some(&ValueType::Path {
        carrier,
        left,
        right,
    }) = scratch.value_type(imported)
    else {
        return Err(Unread::Dangling);
    };
    let closed_end = scratch.value_unit();
    let fixed = scratch.value_type_path(
        carrier,
        if left_moves { closed_end } else { left },
        if right_moves { closed_end } else { right },
    );
    Ok(
        match gandr_core_term::strengthen_value_type(&mut scratch, fixed, Binders::ONE) {
            Maybe::Present(_) => Some(Row::Ends(moving)),
            Maybe::Absent(_) => None,
        },
    )
}

/// Whether every part of the transport motive `motive` has a row.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok(())` exactly when [`Combinator::Transport`] at `motive`
///   builds: every part its rows reach reads under a row.
/// - provides: the focusing's refusal of a transport by its motive, before any
///   combinator is wanted.
/// - fails: the first part's [`Unread`], walking the motive from its root, each
///   product's components and each sum's summands in order.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a motive at a path type is refused by that head, a
///   product holding a thunk type by the thunk's, and the motives the rows read
///   focus and run.
/// - witness: `tests::run::a_transport_no_row_reads_is_refused_by_its_head`
/// - witness: `tests::run::transports_run_by_the_motives_action`
#[spec(ensures: |ret| ret.is_err() || row(core, motive, Family::Path).is_ok())]
pub fn readable(
    core: &CoreArena,
    motive: ValueTypeId,
) -> Result<(), Unread>
{
    let mut pending = Vec::from([motive]);
    while let Some(node) = pending.pop() {
        match row(core, node, Family::Path)? {
            Row::Product(parts) | Row::Sum(parts) => pending.extend(parts.iter().rev()),
            Row::Record(fields) => pending.extend(fields.values().rev()),
            Row::Run(session) => pending.extend(session.payloads().iter().rev()),
            Row::List(element) => pending.push(element),
            Row::Function { argument, result } => pending.extend([result, argument]),
            Row::Suspended(result) => pending.push(result),
            Row::Unchanged | Row::Decode | Row::Singleton | Row::Ends(_) => {},
        }
    }
    Ok(())
}

/// The variable `index` binders out, in the intuitionistic zone.
///
/// # Specification
/// trivial.
fn variable(
    scratch: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    scratch.value_variable(Zone::Intuitionistic, index)
}

/// `force(head) first second`: a closed combinator applied to two values.
///
/// # Specification
/// trivial.
fn applied(
    scratch: &mut CoreArena,
    head: ValueId,
    (first, second): (ValueId, ValueId),
) -> ComputationId
{
    let forced = scratch.computation_force(head);
    let once = scratch.computation_application(forced, first);
    scratch.computation_application(once, second)
}

/// The IL's match on a recorded run, which a run part's action needs and the
/// core cannot write: the core has no eliminator for a run, so the action's
/// body is a placeholder, and the focusing mints this match in its place.
#[derive(Clone, Debug)]
pub struct RunCase
{
    /// The run matched.
    pub scrutinee: ValueId,
    /// One arm per complete run the session admits.
    pub arms: RunArms,
}

/// A run match's arms: each run's moves, and the body run under its
/// payloads, the last innermost.
pub type RunArms = Arc<[(Arc<[RecordedMove<()>]>, ComputationId)]>;

/// The run matches a combinator's build leaves for the focusing, by the
/// placeholder each stands at.
pub type RunCases = BTreeMap<ComputationId, RunCase>;

/// Build `combinator` as a closed value of `scratch`.
///
/// # Specification
/// - requires: a [`Combinator::Ride`] or [`Combinator::Transport`] motive names
///   a value type of `core`, a transport motive one [`readable`] reads.
/// - ensures: a closed thunk of `scratch` computing the combinator, as the
///   module tables state; the match of every run part the combinator moves
///   through is left in `cases`, at the placeholder that stands for it.
/// - provides: what the focusing focuses and applies to an identity's parts, or
///   to a call and its returned argument.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a motive naming no type
///   of `core`, a transport motive no row reads, or an index overflow.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a composite, a function flow, rides at the decode of the
///   binder, a product, a sum, a list and a run type, and transports along
///   `ua`, a reflexivity, a native equivalence and a native product run to the
///   values the kernel's rows compute; a call whose argument is a returned
///   transport runs to what its bind spelling runs to.
/// - witness: `tests::run::rides_run_by_the_motives_action`
/// - witness: `tests::run::a_function_flow_runs_in_variance_order`
/// - witness: `tests::run::a_flow_product_runs_componentwise`
/// - witness: `tests::run::transports_run_by_the_motives_action`
/// - witness: `tests::run::native_paths_run_as_their_maps`
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
/// - witness: `tests::run::a_returned_argument_runs_before_its_call_2129`
#[spec(ensures: |ret| match ret {
    | Ok(id) => matches!(scratch.value(id), Some(&Value::Thunk(_))),
    | Err(_) => true,
})]
pub fn build(
    core: &CoreArena,
    combinator: Combinator,
    (scratch, cases): (&mut CoreArena, &mut RunCases),
) -> Result<ValueId, FocusRefusal>
{
    match combinator {
        Combinator::Identity => {
            let bound = variable(scratch, DeBruijnIndex::from(0_u32));
            let body = scratch.computation_return(bound);
            let lambda = scratch.computation_lambda(body);
            Ok(scratch.value_thunk(lambda))
        },
        Combinator::Compose => Ok(compose(scratch)),
        Combinator::Wrap => {
            // Under λd. λc. λg. λa': a' = 0, g = 1, c = 2, d = 3.
            let domain = variable(scratch, DeBruijnIndex::from(3_u32));
            let argument = variable(scratch, DeBruijnIndex::from(0_u32));
            let forced = scratch.computation_force(domain);
            let moved = scratch.computation_application(forced, argument);
            // Under a: a = 0, a' = 1, g = 2.
            let function = variable(scratch, DeBruijnIndex::from(2_u32));
            let argument = variable(scratch, DeBruijnIndex::from(0_u32));
            let forced = scratch.computation_force(function);
            let result = scratch.computation_application(forced, argument);
            // Under b: b = 0, a = 1, a' = 2, g = 3, c = 4.
            let codomain = variable(scratch, DeBruijnIndex::from(4_u32));
            let produced = variable(scratch, DeBruijnIndex::from(0_u32));
            let forced = scratch.computation_force(codomain);
            let onward = scratch.computation_application(forced, produced);
            let tail = scratch.computation_bind(result, onward);
            let body = scratch.computation_bind(moved, tail);
            let inner = scratch.computation_lambda(body);
            let wrapped = scratch.value_thunk(inner);
            let returned = scratch.computation_return(wrapped);
            Ok(closed(scratch, returned, Binders::from(3_u32)))
        },
        Combinator::Pair => {
            // Under λp. λq. λx: x = 0, q = 1, p = 2.
            let whole = variable(scratch, DeBruijnIndex::from(0_u32));
            let left = scratch
                .computation_tuple_projection(whole, gandr_kernel_term::Component::from(0_usize));
            // Under a: a = 0, x = 1.
            let whole = variable(scratch, DeBruijnIndex::from(1_u32));
            let right = scratch
                .computation_tuple_projection(whole, gandr_kernel_term::Component::from(1_usize));
            // Under b: b = 0, a = 1, x = 2, q = 3, p = 4.
            let first = variable(scratch, DeBruijnIndex::from(4_u32));
            let component = variable(scratch, DeBruijnIndex::from(1_u32));
            let moved_left = applied_once(scratch, first, component);
            // Under a': a' = 0, b = 1, a = 2, x = 3, q = 4.
            let second = variable(scratch, DeBruijnIndex::from(4_u32));
            let component = variable(scratch, DeBruijnIndex::from(1_u32));
            let moved_right = applied_once(scratch, second, component);
            let tail = paired_after(scratch, (moved_left, moved_right));
            let tail = scratch.computation_bind(right, tail);
            let body = scratch.computation_bind(left, tail);
            Ok(closed(scratch, body, Binders::from(3_u32)))
        },
        Combinator::Ride(motive) => action(core, motive, Family::Flow, (scratch, cases)),
        Combinator::Inverse => {
            // Under λe. λy: y = 0, e = 1.
            let record = variable(scratch, DeBruijnIndex::from(1_u32));
            let inverses = scratch
                .computation_tuple_projection(record, gandr_kernel_term::Component::from(1_usize));
            // Under i: i = 0, y = 1.
            let both = variable(scratch, DeBruijnIndex::from(0_u32));
            let left = scratch
                .computation_tuple_projection(both, gandr_kernel_term::Component::from(0_usize));
            // Under l: l = 0, i = 1, y = 2.
            let pair = variable(scratch, DeBruijnIndex::from(0_u32));
            let map = scratch
                .computation_tuple_projection(pair, gandr_kernel_term::Component::from(0_usize));
            // Under g: g = 0, l = 1, i = 2, y = 3.
            let inverse = variable(scratch, DeBruijnIndex::from(0_u32));
            let point = variable(scratch, DeBruijnIndex::from(3_u32));
            let moved = applied_once(scratch, inverse, point);
            let tail = scratch.computation_bind(map, moved);
            let tail = scratch.computation_bind(left, tail);
            let body = scratch.computation_bind(inverses, tail);
            Ok(closed(scratch, body, Binders::from(2_u32)))
        },
        Combinator::Both(direction) => {
            // Under λp. λq. λx: x = 0, q = 1, p = 2.
            let whole = variable(scratch, DeBruijnIndex::from(0_u32));
            let left = scratch
                .computation_tuple_projection(whole, gandr_kernel_term::Component::from(0_usize));
            // Under a: a = 0, x = 1.
            let whole = variable(scratch, DeBruijnIndex::from(1_u32));
            let right = scratch
                .computation_tuple_projection(whole, gandr_kernel_term::Component::from(1_usize));
            // Under b: b = 0, a = 1, x = 2, q = 3, p = 4.
            let first = variable(scratch, DeBruijnIndex::from(4_u32));
            let first_map = scratch.computation_tuple_projection(first, direction.component());
            // Under f: f = 0, b = 1, a = 2, x = 3, q = 4.
            let second = variable(scratch, DeBruijnIndex::from(4_u32));
            let second_map = scratch.computation_tuple_projection(second, direction.component());
            // Under g: g = 0, f = 1, b = 2, a = 3.
            let map = variable(scratch, DeBruijnIndex::from(1_u32));
            let component = variable(scratch, DeBruijnIndex::from(3_u32));
            let moved_left = applied_once(scratch, map, component);
            // Under a': a' = 0, g = 1, f = 2, b = 3.
            let map = variable(scratch, DeBruijnIndex::from(1_u32));
            let component = variable(scratch, DeBruijnIndex::from(3_u32));
            let moved_right = applied_once(scratch, map, component);
            let tail = paired_after(scratch, (moved_left, moved_right));
            let tail = scratch.computation_bind(second_map, tail);
            let tail = scratch.computation_bind(first_map, tail);
            let tail = scratch.computation_bind(right, tail);
            let body = scratch.computation_bind(left, tail);
            Ok(closed(scratch, body, Binders::from(3_u32)))
        },
        Combinator::Forward => {
            let body = forward_body(scratch);
            Ok(closed(scratch, body, Binders::from(2_u32)))
        },
        Combinator::Transport(motive) => action(core, motive, Family::Path, (scratch, cases)),
        Combinator::TransportFrom {
            motive,
            path,
            value,
        } => {
            let transport = action(core, motive, Family::Path, (scratch, cases))?;
            // Under λp. λv: v = 0, p = 1. The path is forced first, then the
            // value, each binding its result; the action reads both where
            // the binds leave them.
            let (path_at, value_at) = match (path, value) {
                (true, true) | (false, false) => (1_u32, 0_u32),
                (true, false) => (0, 1),
                (false, true) => (2, 0),
            };
            let image = variable(scratch, DeBruijnIndex::from(path_at));
            let moved = variable(scratch, DeBruijnIndex::from(value_at));
            let mut body = applied(scratch, transport, (image, moved));
            if value {
                // Under the forced path, if any, the value is one further out.
                let held = variable(scratch, DeBruijnIndex::from(u32::from(path)));
                let forced = scratch.computation_force(held);
                body = scratch.computation_bind(forced, body);
            }
            if path {
                let held = variable(scratch, DeBruijnIndex::from(1_u32));
                let forced = scratch.computation_force(held);
                body = scratch.computation_bind(forced, body);
            }
            Ok(closed(scratch, body, Binders::from(2_u32)))
        },
        Combinator::RunArgument => {
            // Under λf. λa: a = 0, f = 1.
            let held = variable(scratch, DeBruijnIndex::from(0_u32));
            let run = scratch.computation_force(held);
            // Under x: x = 0, a = 1, f = 2.
            let call = variable(scratch, DeBruijnIndex::from(2_u32));
            let returned = variable(scratch, DeBruijnIndex::from(0_u32));
            let applied = applied_once(scratch, call, returned);
            let body = scratch.computation_bind(run, applied);
            Ok(closed(scratch, body, Binders::from(2_u32)))
        },
    }
}

/// `body` closed by `binders` abstractions and suspended.
///
/// # Specification
/// trivial.
fn closed(
    scratch: &mut CoreArena,
    body: ComputationId,
    binders: Binders,
) -> ValueId
{
    let mut abstraction = body;
    for _binder in 0 .. u32::from(binders) {
        abstraction = scratch.computation_lambda(abstraction);
    }
    scratch.value_thunk(abstraction)
}

/// `a' ← left; b' ← right; return (a', b')`, `right` read under `a'`.
///
/// # Specification
/// trivial.
fn paired_after(
    scratch: &mut CoreArena,
    (left, right): (ComputationId, ComputationId),
) -> ComputationId
{
    // Under b': b' = 0, a' = 1.
    let first = variable(scratch, DeBruijnIndex::from(1_u32));
    let second = variable(scratch, DeBruijnIndex::from(0_u32));
    let pair = scratch.value_tuple(&[first, second]);
    let returned = scratch.computation_return(pair);
    let tail = scratch.computation_bind(right, returned);
    scratch.computation_bind(left, tail)
}

/// `f ← p.0; force f v` under `p` (index 1) and `v` (index 0): a path's
/// forward map applied.
///
/// # Specification
/// trivial.
fn forward_body(scratch: &mut CoreArena) -> ComputationId
{
    let image = variable(scratch, DeBruijnIndex::from(1_u32));
    let map = scratch.computation_tuple_projection(image, Direction::Forward.component());
    // Under f: f = 0, v = 1.
    let forward = variable(scratch, DeBruijnIndex::from(0_u32));
    let value = variable(scratch, DeBruijnIndex::from(1_u32));
    let moved = applied_once(scratch, forward, value);
    scratch.computation_bind(map, moved)
}

/// `force(head) argument`.
///
/// # Specification
/// trivial.
fn applied_once(
    scratch: &mut CoreArena,
    head: ValueId,
    argument: ValueId,
) -> ComputationId
{
    let forced = scratch.computation_force(head);
    scratch.computation_application(forced, argument)
}

/// `compose`, closed.
///
/// # Specification
/// trivial.
fn compose(scratch: &mut CoreArena) -> ValueId
{
    // Under λp. λq. λx: x = 0, q = 1, p = 2; under y, q = 2 again.
    let first = variable(scratch, DeBruijnIndex::from(2_u32));
    let argument = variable(scratch, DeBruijnIndex::from(0_u32));
    let head = applied_once(scratch, first, argument);
    let second = variable(scratch, DeBruijnIndex::from(2_u32));
    let middle = variable(scratch, DeBruijnIndex::from(0_u32));
    let tail = applied_once(scratch, second, middle);
    let body = scratch.computation_bind(head, tail);
    closed(scratch, body, Binders::from(3_u32))
}

/// The action `thunk(λt. λv. M_P)` of the motive `motive` for `family`,
/// built bottom up over the parts its rows reach so each part's action is a
/// closed value its parent applies.
///
/// # Specification
/// - requires: `motive` names a value type of `core`, under one binder.
/// - ensures: the module tables' `ride_P` for a flow and `transport_P` for a
///   path; a node shared by two parts is built once; a run part's match is left
///   in `cases` at the placeholder its action's body stands at.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a dangling motive part,
///   a path motive's part no row reads, or an index overflow.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — rides and transports at the decode of the binder, through
///   a pair, a sum and a list, and at a constant part run to the kernel rows'
///   values.
/// - witness: `tests::run::rides_run_by_the_motives_action`
/// - witness: `tests::run::transports_run_by_the_motives_action`
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
#[spec(ensures: |ret| match ret {
    | Ok(id) => matches!(scratch.value(id), Some(&Value::Thunk(_))),
    | Err(_) => true,
})]
fn action(
    core: &CoreArena,
    motive: ValueTypeId,
    family: Family,
    (scratch, cases): (&mut CoreArena, &mut RunCases),
) -> Result<ValueId, FocusRefusal>
{
    let read = |node: ValueTypeId| {
        row(core, node, family).map_err(|_unread| FocusRefusal::TranslationInvariant)
    };
    let mut order = Vec::new();
    let mut pending = Vec::from([(motive, false)]);
    while let Some((node, expanded)) = pending.pop() {
        if expanded {
            order.push(node);
            continue;
        }
        pending.push((node, true));
        match read(node)? {
            Row::Product(parts) | Row::Sum(parts) => {
                pending.extend(parts.iter().map(|&part| (part, false)));
            },
            Row::Record(fields) => {
                pending.extend(fields.values().map(|&part| (part, false)));
            },
            Row::List(element) => pending.push((element, false)),
            Row::Function { argument, result } => {
                pending.extend([(result, false), (argument, false)]);
            },
            Row::Suspended(result) => pending.push((result, false)),
            Row::Run(session) => {
                pending.extend(session.payloads().iter().map(|&payload| (payload, false)));
            },
            Row::Unchanged | Row::Decode | Row::Singleton | Row::Ends(_) => {},
        }
    }
    let mut built: BTreeMap<ValueTypeId, ValueId> = BTreeMap::new();
    for node in order {
        if built.contains_key(&node) {
            continue;
        }
        let body = action_body(core, (node, read(node)?), family, (&built, cases), scratch)?;
        let action = closed(scratch, body, Binders::from(2_u32));
        built.insert(node, action);
    }
    built
        .get(&motive)
        .copied()
        .ok_or(FocusRefusal::TranslationInvariant)
}

/// `M_P` for one motive node read under `row`, under the image `t` (index 1)
/// and the moved value `v` (index 0), its parts' actions already in `built`.
///
/// # Specification
/// - requires: every product, record, sum or list part of `node` has its action
///   in `built`.
/// - ensures: the row of the module tables `node` falls under for `family`.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a part without an
///   action, an annotation that does not import, or an index overflow.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — each row runs to its kernel value, and a run's to the
///   normaliser's.
/// - witness: `tests::run::rides_run_by_the_motives_action`
/// - witness: `tests::run::transports_run_by_the_motives_action`
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
#[spec(ensures: |ret| match ret {
    | Ok(id) => scratch.computation(id).is_some(),
    | Err(_) => true,
})]
fn action_body(
    core: &CoreArena,
    (node, row): (ValueTypeId, Row<'_>),
    family: Family,
    (built, cases): (&BTreeMap<ValueTypeId, ValueId>, &mut RunCases),
    scratch: &mut CoreArena,
) -> Result<ComputationId, FocusRefusal>
{
    let part_action = |part: ValueTypeId| -> Result<ValueId, FocusRefusal> {
        built
            .get(&part)
            .copied()
            .ok_or(FocusRefusal::TranslationInvariant)
    };
    let image = DeBruijnIndex::from(1_u32);
    let moved = DeBruijnIndex::from(0_u32);
    match row {
        Row::Decode => Ok(match family {
            Family::Flow => {
                let translator = variable(scratch, image);
                let ridden = variable(scratch, moved);
                applied_once(scratch, translator, ridden)
            },
            Family::Path => forward_body(scratch),
        }),
        Row::Product(parts) => {
            let mut fields = Vec::with_capacity(parts.len());
            for (position, &part) in parts.iter().enumerate() {
                fields.push((
                    Selector::Component(gandr_kernel_term::Component::from(position)),
                    part_action(part)?,
                ));
            }
            fieldwise(scratch, &fields)
        },
        Row::Record(parts) => {
            let mut fields = Vec::with_capacity(parts.len());
            for (label, &part) in parts {
                fields.push((Selector::Label(label.clone()), part_action(part)?));
            }
            fieldwise(scratch, &fields)
        },
        Row::Sum(parts) => {
            // Each branch binds its payload: z = 0, v = 1, t = 2.
            let mut branches = Vec::with_capacity(parts.len());
            for (position, &part) in parts.iter().enumerate() {
                let action = part_action(part)?;
                let held = variable(scratch, DeBruijnIndex::from(2_u32));
                let payload = variable(scratch, DeBruijnIndex::from(0_u32));
                let step = applied(scratch, action, (held, payload));
                let result = variable(scratch, DeBruijnIndex::from(0_u32));
                let injected =
                    scratch.value_injection(gandr_kernel_term::Summand::from(position), result);
                let returned = scratch.computation_return(injected);
                branches.push(scratch.computation_bind(step, returned));
            }
            let scrutinee = variable(scratch, moved);
            Ok(scratch.computation_case(scrutinee, &branches))
        },
        Row::List(element) => {
            let action = part_action(element)?;
            let (element, result) = {
                let mut importer = gandr_core_term::TypeImporter::new(core, scratch);
                let element = importer
                    .value_type(element)
                    .map_err(|gandr_core_term::ImportFault| FocusRefusal::TranslationInvariant)?;
                let result = importer
                    .value_type(node)
                    .map_err(|gandr_core_term::ImportFault| FocusRefusal::TranslationInvariant)?;
                (element, result)
            };
            let nil = scratch.value_list_nil();
            let on_nil = scratch.computation_return(nil);
            // The cell branch binds the head, then the folded tail: tail = 0,
            // head = 1, v = 2, t = 3; under the element's result y, tail = 1.
            let held = variable(scratch, DeBruijnIndex::from(3_u32));
            let head = variable(scratch, DeBruijnIndex::from(1_u32));
            let step = applied(scratch, action, (held, head));
            let first = variable(scratch, DeBruijnIndex::from(0_u32));
            let rest = variable(scratch, DeBruijnIndex::from(1_u32));
            let cell = scratch.value_list_cons(first, rest);
            let returned = scratch.computation_return(cell);
            let on_cons = scratch.computation_bind(step, returned);
            let list = variable(scratch, moved);
            Ok(scratch.computation_list_fold(element, result, list, on_nil, on_cons))
        },
        Row::Singleton => {
            let composer = compose(scratch);
            let ridden = variable(scratch, moved);
            let translator = variable(scratch, image);
            let composite = applied(scratch, composer, (ridden, translator));
            let suspended = scratch.value_thunk(composite);
            Ok(scratch.computation_return(suspended))
        },
        Row::Unchanged => {
            let ridden = variable(scratch, moved);
            Ok(scratch.computation_return(ridden))
        },
        Row::Function { argument, result } => Ok(function_action(
            scratch,
            (part_action(argument)?, part_action(result)?),
        )),
        Row::Suspended(result) => Ok(suspended_action(scratch, part_action(result)?)),
        Row::Ends(moving) => Ok(ends_action(scratch, moving)),
        Row::Run(session) => {
            let complete = shapes(session)?;
            let mut arms = Vec::with_capacity(complete.len());
            for (moves, payloads) in complete {
                let body = run_arm(scratch, &moves, (&payloads, built))?;
                arms.push((moves, body));
            }
            let mark = u32::try_from(cases.len())
                .map_err(|_overflow| FocusRefusal::TranslationInvariant)?;
            let placeholder = scratch.computation_hole(HoleId::from(mark));
            let scrutinee = variable(scratch, moved);
            let _fresh = cases.insert(placeholder, RunCase {
                scrutinee,
                arms: Arc::from(arms),
            });
            Ok(placeholder)
        },
    }
}

/// `M_P` at a product or a record, under the image `t` and the moved value
/// `v`: each field projected from `v` and moved by its own action under `t`,
/// in order, and the moved fields returned in the same former.
///
/// # Specification
/// - requires: `fields` holds one selector and one closed action per field,
///   every selector a component or every one a label.
/// - ensures: `x₀ ← v.s₀; y₀ ← a₀ t x₀; …; return (y₀, …)` for components and
///   `return #{s₀ = y₀, …}` for labels, binders from the outermost `t`, `v`,
///   then `xᵢ` and `yᵢ` per field.
/// - fails: [`FocusRefusal::TranslationInvariant`] for an index overflow or a
///   label among components.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a product motive and a record motive each move every
///   field by its own action and keep their former and their order.
/// - witness: `tests::run::transports_run_by_the_motives_action`
#[spec(ensures: |ret| match ret {
    | Ok(id) => scratch.computation(id).is_some(),
    | Err(_) => true,
})]
fn fieldwise(
    scratch: &mut CoreArena,
    fields: &[(Selector, ValueId)],
) -> Result<ComputationId, FocusRefusal>
{
    let count = fields.len();
    let depth = count
        .checked_mul(2)
        .and_then(|pairs| pairs.checked_add(2))
        .ok_or(FocusRefusal::TranslationInvariant)?;
    // The index of the binder at `position` from the outermost, read at
    // `depth` binders.
    let index_at = |depth: usize, position: usize| {
        depth
            .checked_sub(1)
            .and_then(|outermost| outermost.checked_sub(position))
            .and_then(|distance| u32::try_from(distance).ok())
            .map(DeBruijnIndex::from)
            .ok_or(FocusRefusal::TranslationInvariant)
    };
    let mut moved = Vec::with_capacity(count);
    for position in 0 .. count {
        let entry = position
            .checked_mul(2)
            .and_then(|offset| offset.checked_add(3))
            .ok_or(FocusRefusal::TranslationInvariant)?;
        moved.push(variable(scratch, index_at(depth, entry)?));
    }
    let assembled = if fields
        .iter()
        .all(|&(ref selector, _)| matches!(*selector, Selector::Component(_)))
    {
        scratch.value_tuple(&moved)
    }
    else {
        let mut record = BTreeMap::new();
        for (&(ref selector, _), &value) in fields.iter().zip(&moved) {
            let Selector::Label(ref label) = *selector
            else {
                return Err(FocusRefusal::TranslationInvariant);
            };
            let _fresh = record.insert(label.clone(), value);
        }
        scratch.value_record(record)
    };
    let mut body = scratch.computation_return(assembled);
    for (position, &(ref selector, action)) in fields.iter().enumerate().rev() {
        let entry = position
            .checked_mul(2)
            .and_then(|offset| offset.checked_add(2))
            .ok_or(FocusRefusal::TranslationInvariant)?;
        let inside = entry
            .checked_add(1)
            .ok_or(FocusRefusal::TranslationInvariant)?;
        let held = variable(scratch, index_at(inside, 0)?);
        let field = variable(scratch, DeBruijnIndex::from(0_u32));
        let step = applied(scratch, action, (held, field));
        body = scratch.computation_bind(step, body);
        let whole = variable(scratch, index_at(entry, 1)?);
        let projected = match *selector {
            Selector::Component(component) => {
                scratch.computation_tuple_projection(whole, component)
            },
            Selector::Label(ref label) => {
                scratch.computation_record_projection(whole, label.clone())
            },
        };
        body = scratch.computation_bind(projected, body);
    }
    Ok(body)
}

/// One complete run a session admits: its moves, and the payload type of each
/// send and receive among them, in order.
type Shape = (Arc<[RecordedMove<()>]>, Vec<ValueTypeId>);

/// A run part way through a session: where it stands, its moves so far, and
/// their payload types.
type Partial = (SessionType, Vec<RecordedMove<()>>, Vec<ValueTypeId>);

/// Every complete run a session with no recursion admits.
///
/// # Specification
/// - requires: `session`'s protocol holds no `mu`.
/// - ensures: one shape per `end` the protocol reaches, each choice taking
///   every label; the moves end with the close.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a protocol that breaks
///   its own invariant.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Termination
/// - reason: a protocol with no `mu` is a tree, and each step pushes its
///   children once.
/// - measure: the protocol nodes not yet stepped.
///
/// # Adequacy
/// - hypothesis: L3 — a choice's two runs each match their own arm, which a
///   missing or merged arm would not.
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |all| all.iter().all(|&(ref moves, _)| matches!(moves.last(), Some(&RecordedMove::Closed)))))]
fn shapes(session: &SessionType) -> Result<Vec<Shape>, FocusRefusal>
{
    let broken =
        |_broken: gandr_core_term::session::ProtocolError| FocusRefusal::TranslationInvariant;
    let mut complete = Vec::new();
    let mut pending: Vec<Partial> = Vec::from([(session.clone(), Vec::new(), Vec::new())]);
    while let Some((standing, mut moves, mut payloads)) = pending.pop() {
        match standing.step().map_err(broken)? {
            Step::Send { payload, next } => {
                moves.push(RecordedMove::Sent(()));
                payloads.push(payload);
                pending.push((next, moves, payloads));
            },
            Step::Receive { payload, next } => {
                moves.push(RecordedMove::Received(()));
                payloads.push(payload);
                pending.push((next, moves, payloads));
            },
            Step::Select(ref branches) => {
                branch(
                    branches,
                    (&moves, &payloads),
                    RecordedMove::Selected,
                    &mut pending,
                )?;
            },
            Step::Offer(ref branches) => {
                branch(
                    branches,
                    (&moves, &payloads),
                    RecordedMove::Offered,
                    &mut pending,
                )?;
            },
            Step::End => {
                moves.push(RecordedMove::Closed);
                complete.push((Arc::from(moves), payloads));
            },
        }
    }
    Ok(complete)
}

/// Push one partial run per label of a choice, each with the choice's move.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `pending` gains one entry per label of `branches`, standing at
///   that label's branch, with `moves` and `chosen(label)` and `payloads`.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a label whose branch the
///   protocol does not resolve.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a choice's two runs each match their own arm.
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
#[spec(captures: before = pending.len(), ensures: |ret| ret.is_err() || before.checked_add(branches.labels().len()) == Some(pending.len()))]
fn branch(
    branches: &gandr_core_term::session::Branches<'_>,
    (moves, payloads): (&[RecordedMove<()>], &[ValueTypeId]),
    chosen: fn(gandr_core_term::FieldLabel) -> RecordedMove<()>,
    pending: &mut Vec<Partial>,
) -> Result<(), FocusRefusal>
{
    for label in branches.labels() {
        let Maybe::Present(standing) = branches
            .get(label)
            .map_err(|_broken| FocusRefusal::TranslationInvariant)?
        else {
            return Err(FocusRefusal::TranslationInvariant);
        };
        let mut taken = moves.to_vec();
        taken.push(chosen(label.clone()));
        pending.push((standing, taken, payloads.to_vec()));
    }
    Ok(())
}

/// One arm of a run's match: `y₀ ← force(M₀) t x₀; …; return run(y₀, …)`
/// under the image `t`, the run `v` and the arm's payloads `x₀ … xₙ₋₁`, the
/// last innermost, with `Mᵢ` the action of payload `i`'s type.
///
/// # Specification
/// - requires: `payloads` holds the payload type of each send and receive of
///   `moves`, in order, and `built` the closed action of each.
/// - ensures: each payload moves by its own type's action, bound before the
///   next, and the run returns with `moves`' actions and labels.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a payload count that
///   differs from the moves', a payload type with no built action, or an index
///   overflow.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — swapping two payloads or skipping one's action changes
///   the run the machine returns.
/// - witness: `tests::run::a_run_moves_its_payloads_along_a_path`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&body| scratch.computation(body).is_some()))]
fn run_arm(
    scratch: &mut CoreArena,
    moves: &[RecordedMove<()>],
    (payloads, built): (&[ValueTypeId], &BTreeMap<ValueTypeId, ValueId>),
) -> Result<ComputationId, FocusRefusal>
{
    let invariant = |_overflow| FocusRefusal::TranslationInvariant;
    let count = u32::try_from(payloads.len()).map_err(invariant)?;
    // Under all `count` binds, `yᵢ` is `count - 1 - i` binders out.
    let mut index = count;
    let mut moved = Vec::with_capacity(moves.len());
    for movement in moves {
        moved.push(movement.try_map(|()| -> Result<ValueId, FocusRefusal> {
            index = index
                .checked_sub(1)
                .ok_or(FocusRefusal::TranslationInvariant)?;
            Ok(variable(scratch, DeBruijnIndex::from(index)))
        })?);
    }
    if index != 0 {
        return Err(FocusRefusal::TranslationInvariant);
    }
    let run = scratch.value_recorded(Arc::from(moved));
    let mut body = scratch.computation_return(run);
    // Under `j` binds, `t` is `j + count + 1` out and `xⱼ` stays `count - 1`
    // out: each bind steps past one payload and adds one binder.
    let payload = count.checked_sub(1);
    for (position, payload_type) in payloads.iter().enumerate().rev() {
        let action = built
            .get(payload_type)
            .copied()
            .ok_or(FocusRefusal::TranslationInvariant)?;
        let binds = u32::try_from(position).map_err(invariant)?;
        let image = binds
            .checked_add(count)
            .and_then(|outer| outer.checked_add(1))
            .ok_or(FocusRefusal::TranslationInvariant)?;
        let held = variable(scratch, DeBruijnIndex::from(image));
        let current = variable(
            scratch,
            DeBruijnIndex::from(payload.ok_or(FocusRefusal::TranslationInvariant)?),
        );
        let step = applied(scratch, action, (held, current));
        body = scratch.computation_bind(step, body);
    }
    Ok(body)
}

/// `return thunk(y ← force v; force(M_B) t y)` under the image `t` (index 1)
/// and the moved suspension `v` (index 0): the suspension row, with `M_B` the
/// result's action.
///
/// # Specification
/// - requires: `result` is a closed action in `scratch`.
/// - ensures: forced, the suspension runs and its result moves forward.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a suspension carried along a path runs to the kernel's
///   `thunk(tr(B, p, ⟨force v⟩))`; returning it unforced, or its result
///   unmoved, would not.
/// - witness: `tests::run::a_function_runs_along_a_path_by_its_maps`
#[spec(ensures: |ret| scratch.computation(ret).is_some())]
fn suspended_action(
    scratch: &mut CoreArena,
    result: ValueId,
) -> ComputationId
{
    // Inside the thunk, as outside it: v = 0, t = 1.
    let suspension = variable(scratch, DeBruijnIndex::from(0_u32));
    let forced = scratch.computation_force(suspension);
    // Under y: y = 0, v = 1, t = 2.
    let image = variable(scratch, DeBruijnIndex::from(2_u32));
    let produced = variable(scratch, DeBruijnIndex::from(0_u32));
    let moved_forward = applied(scratch, result, (image, produced));
    let body = scratch.computation_bind(forced, moved_forward);
    let suspended = scratch.value_thunk(body);
    scratch.computation_return(suspended)
}

/// `return thunk(λa. s ← (g ← t.1; f ← t.0; return (g, f)); x ← force(M_A)
/// s a; y ← force v x; force(M_B) t y)` under the image `t` (index 1) and
/// the moved function `v` (index 0): the function row, with `M_A` the
/// argument's action and `M_B` the result's.
///
/// # Specification
/// - requires: `argument` and `result` are closed actions in `scratch`.
/// - ensures: the argument moves back by its own action at the image's maps
///   swapped, the function applies to it, and its result moves forward.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function carried along `ua` runs to the kernel's `λa.
///   tr(B, p, ⟨force f (back a)⟩)`; moving the argument forward, or the result
///   back, would not.
/// - witness: `tests::run::a_function_runs_along_a_path_by_its_maps`
#[spec(ensures: |ret| scratch.computation(ret).is_some())]
fn function_action(
    scratch: &mut CoreArena,
    (argument, result): (ValueId, ValueId),
) -> ComputationId
{
    // Under λa: a = 0, v = 1, t = 2.
    let image = variable(scratch, DeBruijnIndex::from(2_u32));
    let backward = scratch.computation_tuple_projection(image, Direction::Backward.component());
    // Under g: g = 0, a = 1, v = 2, t = 3.
    let image = variable(scratch, DeBruijnIndex::from(3_u32));
    let forward = scratch.computation_tuple_projection(image, Direction::Forward.component());
    // Under f: f = 0, g = 1.
    let first = variable(scratch, DeBruijnIndex::from(1_u32));
    let second = variable(scratch, DeBruijnIndex::from(0_u32));
    let swapped = scratch.value_tuple(&[first, second]);
    let returned = scratch.computation_return(swapped);
    let swapped = scratch.computation_bind(forward, returned);
    let swapped = scratch.computation_bind(backward, swapped);
    // Under s: s = 0, a = 1, v = 2, t = 3.
    let pair = variable(scratch, DeBruijnIndex::from(0_u32));
    let point = variable(scratch, DeBruijnIndex::from(1_u32));
    let moved_back = applied(scratch, argument, (pair, point));
    // Under x: x = 0, s = 1, a = 2, v = 3, t = 4.
    let function = variable(scratch, DeBruijnIndex::from(3_u32));
    let point = variable(scratch, DeBruijnIndex::from(0_u32));
    let called = applied_once(scratch, function, point);
    // Under y: y = 0, x = 1, s = 2, a = 3, v = 4, t = 5.
    let image = variable(scratch, DeBruijnIndex::from(5_u32));
    let produced = variable(scratch, DeBruijnIndex::from(0_u32));
    let moved_forward = applied(scratch, result, (image, produced));
    let tail = scratch.computation_bind(called, moved_forward);
    let tail = scratch.computation_bind(moved_back, tail);
    let body = scratch.computation_bind(swapped, tail);
    let lambda = scratch.computation_lambda(body);
    let suspended = scratch.value_thunk(lambda);
    scratch.computation_return(suspended)
}

/// The path-end row under the image `t` (index 1) and the moved path `v`
/// (index 0): `tf ← t.0; tb ← t.1; rf ← v.0; rb ← v.1; return (to, from)`,
/// where `to` runs `tb` first when the left end moves, then `rf`, then `tf`
/// when the right end moves, and `from` runs `tb` first when the right end
/// moves, then `rb`, then `tf` when the left end moves.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the moved path's maps composed with the image's on the ends that
///   move, each composite a suspended [`Combinator::Compose`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `back(p)` runs to `p`'s maps swapped and `p then q` to
///   `q`'s after `p`'s, as the kernel's rows compose them; composing in the
///   other order would not.
/// - witness: `tests::run::derived_paths_run_as_their_composed_maps`
#[spec(ensures: |ret| scratch.computation(ret).is_some())]
fn ends_action(
    scratch: &mut CoreArena,
    moving: Moving,
) -> ComputationId
{
    let left = matches!(moving, Moving::Left | Moving::Both);
    let right = matches!(moving, Moving::Right | Moving::Both);
    let image = variable(scratch, DeBruijnIndex::from(1_u32));
    let image_forward = scratch.computation_tuple_projection(image, Direction::Forward.component());
    // Under tf: tf = 0, v = 1, t = 2.
    let image = variable(scratch, DeBruijnIndex::from(2_u32));
    let image_backward =
        scratch.computation_tuple_projection(image, Direction::Backward.component());
    // Under tb: tb = 0, tf = 1, v = 2.
    let path = variable(scratch, DeBruijnIndex::from(2_u32));
    let path_forward = scratch.computation_tuple_projection(path, Direction::Forward.component());
    // Under rf: rf = 0, tb = 1, tf = 2, v = 3.
    let path = variable(scratch, DeBruijnIndex::from(3_u32));
    let path_backward = scratch.computation_tuple_projection(path, Direction::Backward.component());
    // Under rb: rb = 0, rf = 1, tb = 2, tf = 3.
    let composer = compose(scratch);
    let [moved_back, moved_on, image_back, image_on] =
        [0_u32, 1, 2, 3].map(|index| variable(scratch, DeBruijnIndex::from(index)));
    let mut then = |first: ValueId, second: ValueId| {
        let composite = applied(scratch, composer, (first, second));
        scratch.value_thunk(composite)
    };
    let mut to = moved_on;
    if left {
        to = then(image_back, to);
    }
    if right {
        to = then(to, image_on);
    }
    let mut from = moved_back;
    if right {
        from = then(image_back, from);
    }
    if left {
        from = then(from, image_on);
    }
    let maps = scratch.value_tuple(&[to, from]);
    let body = scratch.computation_return(maps);
    let body = scratch.computation_bind(path_backward, body);
    let body = scratch.computation_bind(path_forward, body);
    let body = scratch.computation_bind(image_backward, body);
    scratch.computation_bind(image_forward, body)
}
