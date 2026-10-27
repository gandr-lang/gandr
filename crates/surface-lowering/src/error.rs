//! The crate's typed refusal vocabulary, [`LoweringRefusal`], and the payloads
//! that say where a form left the fragment or how it was malformed.
//!
//! Every refusal about the source names the span it rejected, because the
//! diagnostic a driver renders has to point somewhere. Nothing here panics,
//! repairs a malformed form, or admits a node it could not read.
//!
//! # Names and forms are different mistakes
//!
//! An identifier no table answers is an unresolved *name* — the author wrote a
//! spelling nothing binds. A node whose *form* has no reading where it stands
//! is out of fragment — the author wrote something the core has no node for at
//! that position. Keeping them apart is what lets a misspelled type head carry
//! a suggestion-shaped repair while a lambda in value position carries a
//! statement about the polarity discipline instead.
//!
//! # Out of fragment covers four boundaries, and names which
//!
//! A reserved form is parsed so it can be declined by name; an unadmitted form
//! is one the grammar parses and the fragment has no reading for at all; a form
//! of the wrong sort is a well-formed former in the wrong place; a form offered
//! the wrong number of operands is a shape the core cannot build. All four are
//! the lowering declining to represent what was written, so they share a
//! class, and [`FragmentBoundary`] is the discriminating payload that keeps
//! their witnesses apart.
//!
//! # A malformed form is the parser's repair, read back
//!
//! When recovering from malformed source, the parser inserts grout or a
//! closing tile, and where juxtaposition puts two forms in a hole that takes
//! one it keeps both. The lowering reads every
//! such shape back as [`LoweringRefusal::MalformedForm`], naming the form, the
//! fault and the bytes the fault stands at, so a repaired tree is never
//! lowered as if the source had written it.
//!
//! # Repairs are refused where they stand
//!
//! When the parser repairs a form, its tree can hold grout where the source
//! wrote no term and closing tiles the source never wrote. The first repair
//! among a form's children refuses the form as `MalformedForm` with the
//! `Repaired` fault, at the repair's own span. A hole holding no operand, a
//! hole holding a juxtaposition, and a tile out of its place are refused the
//! same way, as `MissingOperand`, `ExtraOperand` and `MisplacedTile`.
//!
//! The alternative was to lower around a repair, reading grout as a hole term.
//! It was declined because the core fragment has no hole, and a hole would be
//! an obligation the classifier forbids a refusal to become. Reversal: when the
//! core gains typed holes, grout lowers to one and the repair stops refusing.
//!
//! A minted close is usually an effect, not a cause: the parser closes an outer
//! form at its opening because an inner form swallowed the closer the outer one
//! needed. So when a form's first repair is a minted close and a form inside it
//! holds a repair too, the refusal names the deepest such inner form, at its
//! repair — the first in source order among equals. A source that ends after a
//! case's last arm, the case and its definition both open, is refused as the
//! case at the end of the arm rather than as the definition at its opening
//! brace.
//!
//! The alternative was to report the outer close where the parser minted it,
//! which is faithful to the tree but points at the one place the author did not
//! err. Reversal: when the parser places a minted close at the bytes that
//! caused it, the outer repair is the cause and the walk inward goes.
//!
//! # Four ways out of the fragment
//!
//! `OutOfFragment` names the boundary a form crossed. `Reserved`: the form
//! parses and is declined by name — a recursive call's claim other than `<` —
//! and classifies as unimplemented, naming its tracking issue.
//! `Unadmitted`: the grammar reads the form and this fragment does not
//! — a statement other than `run`, an annotated or patterned `run` binder, a
//! recursive function with no parameter to recurse on, a claim on a name that
//! is not a recursive function or that heads no call, an explicit parameter
//! block, a parameter named as a type variable, an annotation, a grade on a
//! returner, a capitalised name nothing answers, a
//! selection no module governs, a level wider than a level constant, a type
//! abstraction, a typed lambda parameter, a number at a width other than
//! `f64`, and every kind outside the dispatch table. `WrongSort`: the form
//! produces another sort than its position demands. `Arity`: a lambda with
//! other than one parameter, a block with no last computation, a recursive call
//! with other than one argument per parameter. `NotInTail`: a `return`,
//! `become`, `break` or `continue`, or a loop, standing where no path through
//! a body passes (the `lower` module's § A function exits where its body
//! ends). `JoinsBlock`: a written answer on a match whose arms continue the
//! block after it.
//!
//! # Loops refuse by their own names
//!
//! A `break` or a `continue` on a path through a body but not through a
//! loop's body is [`LoweringRefusal::OutsideLoop`]: the source wrote a loop
//! exit where no loop is iterated, which is a mistake, not a form the
//! fragment lacks.
//!
//! # Exits across a handler's frame refuse by their own name
//!
//! A `become` in a handled subject, and a `break` or a `continue` there whose
//! loop holds the scope, are [`LoweringRefusal::AcrossHandler`]: each would
//! run code in place of a live handler's frame, which no tail can do. A
//! `return` there leaves its body past every frame, and needs no refusal.
//!
//! `Unadmitted` and `Arity` exist because the grammar is the whole surface and
//! the fragment is a small part of it; without them every form the surface has
//! and the core lacks would be misreported as a sort error.

use core::error::Error;
use core::fmt;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::MoldId;
use gandr_theory_levitation::WfKind;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeSchema;
use crate::attribute::PayloadForm;
use crate::attribute::RegisteredAttribute;
use crate::attribute::suggestion;
use crate::form::FormName;
use crate::form::Repair;
use crate::import::ONE_SOURCE;
use crate::lower::LoweringBudget;
use crate::resolve::CandidateCount;
use crate::resolve::HeadArity;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;
use crate::unbuilt::Unbuilt;

quenchant_shape::reason_enum! {
    /// Why a refusal names no span of the source.
    pub mod refusal_span {
        /// The refusal is about the run, not about a position in the source.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The refusal concerns the lowering run as a whole.
            Run,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an ill-formed description's refusal holds no name in a subject's
    /// place.
    pub mod description_subject {
        /// The reason the name is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The description check's reason names fewer names.
            Unnamed,
            /// The declaration spells no name the check gives: a name the
            /// description derived rather than read.
            Unwritten,
        }
    }
}

/// The sort a node was read at, which its position in its parent fixes.
///
/// # Specification
/// - requires: a producer selects the sort demanded by the rejected position.
/// - ensures: the tag reports the expected sort, not the rejected form's sort.
/// - provides: the polarity and position at which representation was requested.
/// - fails: not applicable to the tag itself.
/// - panics: none.
/// - executable: none — the tag holds no parent, grammar or position from which
///   the required sort could be derived.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration at the root and a number as a run's operand
///   report module and computation respectively, separating expected sort from
///   the form's own sort. These witnesses bound the claim to those positions.
/// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
/// - witness: `lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
/// - witness: `lower::session::tests::a_malformed_protocol_is_refused_where_it_is_written`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentSort
{
    /// The root of a source: a module's declarations.
    Module,
    /// A module's own child: a declaration.
    Declaration,
    /// A value type, the sort a declaration is declared at.
    ValueType,
    /// A computation type, reached under `+U` and `-F` and to an arrow's right.
    CompType,
    /// A value, the sort a definition's body is at.
    Value,
    /// A computation, reached under a thunk and to an application's left.
    Computation,
    /// A pattern, the binder of a `run` statement.
    Pattern,
    /// A session type's continuation: a session form, or a variable a `mu`
    /// around it binds.
    Continuation,
}

impl fmt::Display for FragmentSort
{
    /// Writes the sort's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Module => f.write_str("a module"),
            Self::Declaration => f.write_str("a declaration"),
            Self::ValueType => f.write_str("a value type"),
            Self::CompType => f.write_str("a computation type"),
            Self::Value => f.write_str("a value"),
            Self::Computation => f.write_str("a computation"),
            Self::Pattern => f.write_str("a pattern"),
            Self::Continuation => f.write_str("a session continuation"),
        }
    }
}

/// Which way a form left the fragment at the position it was written.
///
/// # Specification
/// - requires: the producer identifies the boundary crossed by the source form.
/// - ensures: reserved, unadmitted, wrong-sort, wrong-arity, indexed,
///   unannotated, not-a-function, non-uniform, foreign-claim, not-in-tail,
///   joins-block, empty-list, endpoint, non-contractive, held and view reports
///   remain distinct; an arity report carries the number of operands offered.
/// - provides: why a parsed form has no representation at this position.
/// - fails: not applicable to the report itself.
/// - panics: none.
/// - executable: none — the tag and offered count do not hold the grammar,
///   admission policy or actual operands needed to verify the report.
///
/// # Adequacy
/// - hypothesis: L3 — reserved recursion claims, unadmitted forms, a wrong-sort
///   run operand and zero/two-operand refusals distinguish the four boundaries
///   by exact typed payloads. The fixtures do not enumerate every grammar form.
/// - witness: `lower::native::tests::a_productive_call_is_the_whole_arm_of_a_copattern_block`
/// - witness: `lower::native::tests::a_descent_claim_names_its_own_function_873`
/// - witness: `lower::native::tests::an_indexed_generator_is_declined`
/// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
/// - witness: `lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
/// - witness: `lower::tests::the_empty_parentheses_are_never_the_unit`
/// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
/// - witness: `lower::exits::tests::a_match_continuing_its_block_answers_what_the_block_does`
/// - witness: `lower::session::tests::an_action_on_no_endpoint_is_refused`
/// - witness: `lower::session::tests::a_malformed_protocol_is_refused_where_it_is_written`
/// - witness: `lower::access::tests::an_access_names_a_held_value_and_an_eliminator_its_view`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentBoundary
{
    /// The form is reserved: parsed so it can be declined by name, at the
    /// feature it stops at.
    Reserved(Unbuilt),
    /// The form is parsed by the grammar and has no reading in the fragment
    /// for the feature it stops at.
    Unadmitted(Unbuilt),
    /// The form is admitted at one position only and written at another:
    /// the universe of representable sorts, which classifies a theory's sort
    /// member, read anywhere else; the mark `pub`, read before anything but a
    /// root declaration.
    Misplaced,
    /// The form is a row written before a type, `[E] B`, standing anywhere
    /// but a definition's result: only there is a returner inserted for the
    /// row to belong to.
    NotAtResult,
    /// The form is a former of the fragment, but not of the sort its position
    /// demands.
    WrongSort,
    /// The form is an expression written at a source's top level, where only
    /// declarations stand: an expression runs inside a declaration, and a
    /// program runs the `main` it declares.
    TopLevel,
    /// The form is a former of this sort, offered a number of operands it does
    /// not take.
    Arity(OperandCount),
    /// The form reads a family at an index where the fragment does not: a
    /// generator whose result applies its family to anything but its own
    /// parameters, in order, then one term per index its kind states; a cell
    /// on an indexed family; univalence at an indexed sort.
    Indexed,
    /// The form needs a type the source does not state: a match over nominal
    /// data with no answer type written or known from its function, a
    /// constructor of a parameterized family with no classifier or answering
    /// the decode of a binder or of a constant no top-level definition writes,
    /// `back`, `then` or `cong` standing where no written path type is
    /// answered and its path's type is not read off a word or an operation
    /// over one, `cong` so standing at a map that is no function definition
    /// with a closed written result that lowers, `then` where no written flow
    /// type is either, a transport or ride whose motive is no static
    /// abstraction, or a number with a fraction or an exponent written with
    /// neither the `f64` suffix nor an annotation.
    Unannotated,
    /// The form is a recursive call passing, where one of the definition's
    /// unchanging parameters stands, something other than that parameter: the
    /// parameters before the one the definition descends on stay unchanged.
    NonUniform,
    /// The form is a descent claim, `f[<]`, whose head names a function
    /// other than the recursive one it is written in: a descent claim heads a
    /// call of the function being defined or of a member of its mutual block.
    ForeignClaim,
    /// The form is `cong` at a constructor, which is not a function: `cong`
    /// maps a path by a function definition.
    NotAFunction,
    /// The form is a function exit, `return` or `become`, a loop exit,
    /// `break` or `continue`, or a loop, standing where no path through a
    /// function's, a lambda's or a thunk's body passes: a call's head, an
    /// operand, or outside any body.
    NotInTail,
    /// The form is a match written with an answer, `case e -> T { … }`,
    /// whose arms continue the block after the statement it is bound by,
    /// because one of them exits: each arm then answers what the block
    /// answers, so the written answer is not the match's.
    JoinsBlock,
    /// The form is the empty parentheses `()` standing as a value or a type:
    /// an empty list, which is never the unit.
    EmptyList,
    /// The form stands where a session action names its endpoint and is not
    /// a name a fork binds as one of its ends: a value, a declaration or an
    /// ordinary binder.
    Endpoint,
    /// The form is a `mu` whose body is a `mu` or a recursion variable, so
    /// the protocol recurses before any action: not contractive.
    NonContractive,
    /// The name an access lends is no linear slot: a value, a declaration
    /// or an ordinary binder, where only a name a `hold` holds can be lent.
    Held,
    /// The name a `resume` or an `abort` ends is no linear slot: a value, a
    /// declaration or an ordinary binder, where only the view an `access`
    /// binds can be ended.
    View,
}

/// Why a source does not export a declaration an importer names.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unexported
{
    /// No `pub` mark precedes the declaration.
    Private,
    /// The declaration has a signature and no definition.
    Undefined,
}

impl fmt::Display for FragmentBoundary
{
    /// Writes the way the form left the fragment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Reserved(_) => f.write_str("is reserved and declined"),
            Self::Unadmitted(_) => f.write_str("is not admitted by the fragment"),
            Self::Misplaced => {
                f.write_str("is admitted only where it classifies a theory's sort member")
            },
            Self::NotAtResult => f.write_str(
                "is a row before a type, admitted only at a definition's result, where the \
                 returner it rows is inserted",
            ),
            Self::WrongSort => f.write_str("is not a former of this sort"),
            Self::TopLevel => f.write_str(
                "stands at a source's top level, where only declarations stand; a program runs \
                 the `main` it declares",
            ),
            Self::Arity(operands) => write!(f, "does not take {operands} operands"),
            Self::Indexed => {
                f.write_str("applies its family to an index, which the fragment does not read")
            },
            Self::Unannotated => f.write_str("needs a type the source does not state"),
            Self::NonUniform => f.write_str(
                "passes something other than the parameter itself where an earlier parameter \
                 stands; only the parameter the definition descends on and the ones after it \
                 vary",
            ),
            Self::ForeignClaim => f.write_str(
                "names a function other than the recursive one it is written in: a descent \
                 claim heads a call of the function being defined",
            ),
            Self::NotAFunction => {
                f.write_str("maps a path by a constructor, which is not a function")
            },
            Self::NotInTail => f.write_str(
                "stands where no path through a function, a lambda, a thunk or a copattern \
                 clause body passes; an exit leaves, and a loop runs, only on such a path",
            ),
            Self::JoinsBlock => f.write_str(
                "has arms that continue the block after it, which answer what the block \
                 answers, so a written answer is not read",
            ),
            Self::EmptyList => f.write_str(
                "is spelled `()`, an empty list and never the unit: the unit value is `unit` and \
                 its type `Unit`",
            ),
            Self::Endpoint => f.write_str(
                "is no endpoint: a session action acts on a name a fork binds as one of its \
                 ends",
            ),
            Self::NonContractive => f.write_str(
                "recurses before any action: a `mu` body that is a `mu` or a variable unfolds \
                 to itself",
            ),
            Self::Held => {
                f.write_str("is no held value: an access lends a name a `hold` statement holds")
            },
            Self::View => f.write_str(
                "is no view: `resume` and `abort` end the name an `access` binds after `as`",
            ),
        }
    }
}

/// How a form's pieces fell short of its rule.
///
/// # Specification
/// - requires: a producer reports the fault observed in the form's children.
/// - ensures: parser repair, missing operand, extra operand, misplaced tile,
///   extra closer, extra opener, missing opener and misspelt keyword reports
///   retain distinct meanings; a repair retains its shape, a bracket fault its
///   family, and a misspelling the keyword it nearly spells.
/// - provides: the structural reason a form could not be read.
/// - fails: not applicable to the report itself.
/// - panics: none.
/// - executable: none — a fault holds neither the syntax node nor the rule and
///   children needed to establish that the reported fault occurred.
///
/// # Adequacy
/// - hypothesis: L3 — repaired, juxtaposed, misplaced-tile, doubled-closer,
///   doubled-opener and left-out-opener fixtures carry different exact faults
///   and spans. The raw missing-operand variant is included in the span
///   projection fixture; the source examples are not a complete enumeration of
///   malformed child sequences.
/// - witness: `lower::tests::a_repaired_declaration_is_refused`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
/// - witness: `lower::tests::a_tile_out_of_place_is_refused`
/// - witness: `module::tests::a_doubled_closer_is_refused_where_it_was_written_2047`
/// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
/// - witness: `lower::tests::a_keyword_misspelt_is_refused_at_the_word_2259`
/// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FormFault
{
    /// The parser repaired the form where the source fell short.
    Repaired(Repair),
    /// A hole the form's rule requires holds nothing.
    MissingOperand,
    /// A hole holds more forms than the rule takes, or an operand stands where
    /// the rule has no hole.
    ExtraOperand,
    /// One of the form's own tiles stands where the rule does not place it.
    MisplacedTile,
    /// A closer of this family written once more than its openers: it closes
    /// the form early, and a closer after it closes nothing.
    ExtraClose(ClosingClass),
    /// An opener of this family written once more than its closers: the
    /// layout gives its line one closer fewer than it opens.
    ExtraOpen(ClosingClass),
    /// The opener a closer of this family answers, left out: the closer begins
    /// a line indented past every opener still waiting for one.
    MissingOpen(ClosingClass),
    /// A word one edit from this keyword, standing where the form then holds
    /// an operand it does not take: the keyword misspelt, read as a name.
    Misspelt(crate::form::TileName),
}

impl fmt::Display for FormFault
{
    /// Writes how the form fell short.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Repaired(repair) => write!(f, "holds {repair}"),
            Self::MissingOperand => f.write_str("leaves an operand unwritten"),
            Self::ExtraOperand => f.write_str("has an operand where it takes none"),
            Self::MisplacedTile => f.write_str("has a tile out of place"),
            Self::ExtraClose(close) => {
                write!(f, "is closed early by one `{}` too many", Closer(close))
            },
            Self::ExtraOpen(close) => {
                write!(f, "is left open by one `{}` too many", Opener(close))
            },
            Self::MissingOpen(close) => {
                write!(
                    f,
                    "is missing the `{}` its `{}` closes",
                    Opener(close),
                    Closer(close)
                )
            },
            Self::Misspelt(keyword) => write!(f, "misspells `{}`", keyword.as_ref()),
        }
    }
}

/// The closer of a family, written as it is spelled.
#[repr(transparent)]
struct Closer(ClosingClass);

impl fmt::Display for Closer
{
    /// Writes the closer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            ClosingClass::Paren => ")",
            ClosingClass::Bracket => "]",
            ClosingClass::Brace => "}",
        })
    }
}

/// The plain opener of a family, written as it is spelled.
#[repr(transparent)]
struct Opener(ClosingClass);

impl fmt::Display for Opener
{
    /// Writes the opener.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match self.0 {
            ClosingClass::Paren => "(",
            ClosingClass::Bracket => "[",
            ClosingClass::Brace => "{",
        })
    }
}

/// A module ascription form the fragment does not read.
///
/// # Specification
/// - requires: a producer selects the ascription form actually written.
/// - ensures: an opaque family or operator, a kinded or parameterized component
///   of a functor's parameter, and a parameter list before a kind do not become
///   an abstract or manifest interpretation.
/// - provides: which unread ascription obligation prevented admission.
/// - fails: not applicable to the report itself.
/// - panics: none.
/// - executable: none — the tag does not hold an ascription tree or its
///   components, so it cannot validate the producer's classification.
///
/// # Adequacy
/// - hypothesis: L3 — an opaque operator component is asserted as a typed
///   refusal; a transparent one and a manifest component are admitted instead
///   of conflated with it.
/// - witness: `tests::modules::a_kinded_type_component_forms_at_its_classifier`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AscriptionForm
{
    /// A type component whose kind is a family's or an operator's, `type T :
    /// (a : A) => U` or `type T : A -> U`, where its meaning would be an
    /// abstract family: under an opaque ascription, or in a functor's
    /// parameter, whether written or derived from an indexed sort of a
    /// `Model(S)` parameter's theory.
    Kinded,
    /// A type component binding parameters, `type T(a : A) …`, before a kind
    /// or in a functor's parameter.
    Parameterized,
}

impl fmt::Display for AscriptionForm
{
    /// Writes the form and what it waits on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Kinded => f.write_str("is a kinded type component, a type family"),
            Self::Parameterized => f.write_str("is a type component that binds parameters"),
        }
    }
}

/// A loop exit: the keyword a [`LoweringRefusal::OutsideLoop`] names.
///
/// # Specification
/// - requires: a producer selects the keyword actually written.
/// - ensures: one variant per loop exit.
/// - provides: which exit stood outside every loop.
/// - fails: not applicable to the tag itself.
/// - panics: none.
/// - executable: none — the tag holds no tree to check the keyword against.
///
/// # Adequacy
/// - hypothesis: L3 — a `break` and a `continue` outside every loop are each
///   refused with their own keyword.
/// - witness: `lower::loops::tests::a_loop_exit_off_every_loop_body_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LoopExit
{
    /// `break` or `break(v)`, leaving the nearest loop.
    Break,
    /// `continue`, running the nearest loop's body again.
    Continue,
}

impl fmt::Display for LoopExit
{
    /// Writes the keyword between backticks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Break => "`break`",
            Self::Continue => "`continue`",
        })
    }
}

/// An exit refused in a handled subject: the keyword a
/// [`LoweringRefusal::AcrossHandler`] names.
///
/// # Specification
/// - requires: a producer selects the keyword actually written.
/// - ensures: one variant per exit a live handler frame refuses.
/// - provides: which exit would have run code in place of the frame.
/// - fails: not applicable to the tag itself.
/// - panics: none.
/// - executable: none — the tag holds no tree to check the keyword against.
///
/// # Adequacy
/// - hypothesis: L3 — a `become`, a `break` and a `continue` in a subject are
///   each refused with their own keyword.
/// - witness: `lower::capability::tests::an_exit_that_would_run_in_a_live_frame_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CrossedExit
{
    /// `become c`, running `c` in the subject's place.
    Become,
    /// `break` or `break(v)`, leaving a loop around the scope.
    Break,
    /// `continue`, running a loop around the scope again.
    Continue,
}

impl fmt::Display for CrossedExit
{
    /// Writes the keyword between backticks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Become => "`become`",
            Self::Break => "`break`",
            Self::Continue => "`continue`",
        })
    }
}

/// Where a type family's parameters part from the index telescope its
/// component states.
///
/// # Specification
/// - requires: a producer compares a family member's parameters with the
///   indices its component states.
/// - ensures: a count mismatch names both counts; a type mismatch names the
///   first parameter, counted from one, whose type is not its index's.
/// - provides: which part of the telescope a refusal is about.
/// - fails: not applicable to the report itself.
/// - panics: none.
/// - executable: none — the fault holds neither telescope.
///
/// # Adequacy
/// - hypothesis: L3 — a family binding too few parameters and one binding a
///   parameter at another sort are refused with their faults.
/// - witness: `tests::modules::models::a_family_of_the_wrong_telescope_is_refused`
/// - witness: `tests::modules::models::a_written_family_of_the_wrong_telescope_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TelescopeFault
{
    /// The member binds another number of parameters than the component
    /// states indices.
    Arity
    {
        /// The indices the component states.
        stated: OperandCount,
        /// The parameters the member binds.
        written: OperandCount,
    },
    /// The parameter at this place, counted from one, has a type its index
    /// does not state.
    Index(OperandCount),
}

impl fmt::Display for TelescopeFault
{
    /// Writes where the telescopes part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Arity { stated, written } => write!(
                f,
                "binds {} parameters where its component states {} indices",
                usize::from(written),
                usize::from(stated)
            ),
            Self::Index(place) => write!(
                f,
                "binds parameter {} at a type its component's index does not state",
                usize::from(place)
            ),
        }
    }
}

/// The crate's global and declaration-local refusals.
///
/// The vocabulary is closed and every refusal carries a class, which the
/// classifier reads from the variant alone.
///
/// # Specification
/// - requires: producers supply the identities and positions of the reported
///   failure; callers may also construct unvalidated diagnostic records.
/// - ensures: the variant identifies the failure kind and retains its payload;
///   span projection selects the rejected occurrence, not an earlier duplicate.
/// - provides: structured diagnostic data, not a certificate that the failure
///   occurred or that the payload belongs to a particular syntax tree.
/// - fails: not applicable to the stored report itself.
/// - panics: none.
/// - executable: none — the report does not own the syntax tree, lexical scope,
///   grammar or budget execution needed to authenticate its payload. Projection
///   and classification have their own executable predicates.
///
/// # Adequacy
/// - hypothesis: L3 — all current variants have exact span observations,
///   including earlier-versus-rejected duplicates and the two run absences.
///   Classification is observed independently of payload; this does not prove
///   that an arbitrary constructed report describes a real lowering failure.
/// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
/// - witness: `classify::tests::every_refusal_carries_its_pinned_class`
/// - witness: `classify::tests::the_classification_ignores_position_and_name`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum LoweringRefusal<'source>
{
    /// A term name no binder or earlier declaration answers.
    UnresolvedName
    {
        /// The bytes the name covers.
        span: ByteSpan,
        /// The identifier as it was written.
        name: SurfaceName<'source>,
    },

    /// A documentation link to a name the module does not declare.
    UnresolvedDocLink
    {
        /// The bytes the linked name covers.
        span: ByteSpan,
        /// The name as the link wrote it.
        name: SurfaceName<'source>,
    },

    /// A type head no table entry answers at the arity it was written with.
    UnresolvedTypeHead
    {
        /// The bytes the head covers.
        span: ByteSpan,
        /// The identifier as it was written.
        name: SurfaceName<'source>,
        /// How many arguments the head was written with, which selects the
        /// table that failed to answer it.
        arity: HeadArity,
    },

    /// A second signature for one name.
    DuplicateSignature
    {
        /// The bytes the second signature covers.
        span: ByteSpan,
        /// The name declared twice.
        name: SurfaceName<'source>,
        /// The bytes the first signature covers.
        first: ByteSpan,
    },

    /// A second definition for one name.
    DuplicateDefinition
    {
        /// The bytes the second definition covers.
        span: ByteSpan,
        /// The name defined twice.
        name: SurfaceName<'source>,
        /// The bytes the first definition covers.
        first: ByteSpan,
    },

    /// A second import binding an alias an earlier import already binds.
    DuplicateImportAlias
    {
        /// The bytes the second import covers.
        span: ByteSpan,
        /// The alias imported twice.
        alias: SurfaceName<'source>,
        /// The bytes the first import covers.
        first: ByteSpan,
    },

    /// A declaration of a source whose path import names no source the run
    /// lowers: nothing at the path, a path outside the importer's root, or a
    /// source refused as a whole.
    ImportUnresolved
    {
        /// The bytes the import covers.
        span: ByteSpan,
        /// The bytes of the refused declaration's name.
        refused: ByteSpan,
    },

    /// A declaration of a source whose imports lead back to it.
    ImportCycle
    {
        /// The bytes of the import that is an edge of the cycle.
        span: ByteSpan,
        /// The bytes of the refused declaration's name.
        refused: ByteSpan,
    },

    /// A name two sources bind for one source: an unqualified import binding
    /// a name the importer declares, or two unqualified imports binding one
    /// name.
    ImportShadows
    {
        /// The bytes refused: the importer's declaration of the name, or a
        /// use of a name two imports bind.
        span: ByteSpan,
        /// The name bound twice.
        name: SurfaceName<'source>,
        /// The bytes of the import binding it.
        import: ByteSpan,
        /// The bytes of the other binding: the importer's declaration, or
        /// the other import.
        other: ByteSpan,
    },

    /// A name an unqualified import answers with a declaration its source
    /// does not export: one no `pub` mark precedes, or one with a signature
    /// and no definition.
    UnexportedName
    {
        /// The bytes the use covers.
        span: ByteSpan,
        /// The name as it was written.
        name: SurfaceName<'source>,
        /// The bytes of the declaration's name in its own source.
        declared: ByteSpan,
        /// Why its source does not export it.
        reason: Unexported,
    },

    /// A declared name or a binder over a builtin, under the policy that
    /// forbids shadowing one; or a family named as a builtin type the grammar
    /// spells as a tile of its own, under either policy.
    ShadowedBuiltin
    {
        /// The bytes of the name that shadows.
        span: ByteSpan,
        /// The name as it was written.
        name: SurfaceName<'source>,
    },

    /// A form the fragment does not admit where it was written.
    OutOfFragment
    {
        /// The bytes the form covers.
        span: ByteSpan,
        /// The form that was written.
        form: FormName,
        /// The sort the position demanded.
        sort: FragmentSort,
        /// Which way the form left the fragment.
        boundary: FragmentBoundary,
    },

    /// A circuit rule's fed-back port that no observation reads: every
    /// occurrence of it in the body is bare, so the loop the feed closes is
    /// not guarded.
    BareFeedback
    {
        /// The bare occurrence of the port.
        span: ByteSpan,
        /// The rule's name tile.
        rule: ByteSpan,
    },

    /// A description the description check refuses: a `data`, `codata` or
    /// `theory` declaration whose sorts, ports, shape or rules are not well
    /// formed, though its syntax is complete.
    IllFormedDescription
    {
        /// The bytes the check located the failure at: the rule or face at
        /// fault, or the whole declaration where the check records none.
        span: ByteSpan,
        /// Why the check refuses it.
        kind: WfKind,
        /// The names the check's reason names, in its order, as the
        /// declaration spells them: the sort, port, rule, face, symbol or
        /// variable at fault.
        subjects: [Maybe<SurfaceName<'source>, description_subject::Absent>; 2],
    },

    /// A thunk type written with a grade other than the default `ω`, which
    /// the core has no bridge for.
    GradedBridge
    {
        /// The bytes the grade covers.
        span: ByteSpan,
        /// The grade as it was written.
        grade: SurfaceName<'source>,
    },

    /// A literal node whose own text is not a lexeme of its kind.
    MalformedLiteral
    {
        /// The bytes the literal covers.
        span: ByteSpan,
        /// The literal form whose lexeme shape was not met.
        form: FormName,
    },

    /// A universe level at or past the greatest the levels count: the
    /// greatest has no universe above it, so `Type[s, n]` names none.
    NoUniverseAbove
    {
        /// The bytes the level's numeral covers.
        span: ByteSpan,
        /// The level as it was written.
        level: SurfaceName<'source>,
    },

    /// A form whose pieces fall short of its rule, the parser's repairs
    /// included.
    MalformedForm
    {
        /// The bytes the fault stands at: the repair, the empty hole, the
        /// extra operand or the misplaced tile.
        span: ByteSpan,
        /// The form whose rule was not met.
        form: FormName,
        /// How the pieces fell short.
        fault: FormFault,
    },

    /// An attribute name the registry does not hold.
    UnknownAttribute
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
        /// The name as it was written.
        name: SurfaceName<'source>,
        /// The nearest registered name within the suggestion bound.
        suggestion: Maybe<RegisteredAttribute, suggestion::Absent>,
    },

    /// One attribute written twice for one declared name.
    DuplicateAttribute
    {
        /// The bytes the second attribute covers.
        span: ByteSpan,
        /// The attribute name written twice.
        name: SurfaceName<'source>,
        /// The bytes the first attribute covers.
        first: ByteSpan,
    },

    /// An attribute whose schema takes a payload, written with none.
    MissingPayload
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
        /// The registered name whose schema went unsatisfied.
        name: RegisteredAttribute,
        /// The schema that takes a payload.
        expected: AttributeSchema,
    },

    /// An attribute payload that is not a value of the fragment.
    NonValuePayload
    {
        /// The bytes the payload covers.
        span: ByteSpan,
        /// The registered name whose payload was written.
        name: RegisteredAttribute,
        /// The form the payload was written as.
        form: FormName,
    },

    /// An attribute payload whose form its schema does not admit.
    IllTypedPayload
    {
        /// The bytes the payload covers, or the attribute's own bytes when the
        /// schema takes no payload and one was written.
        span: ByteSpan,
        /// The registered name whose schema was contradicted.
        name: RegisteredAttribute,
        /// The schema the name carries.
        expected: AttributeSchema,
        /// The form the payload was written as.
        written: PayloadForm,
    },

    /// A module member named at or after the position of the member that
    /// names it.
    ForwardMemberReference
    {
        /// The bytes the reference covers.
        span: ByteSpan,
        /// The member's name as the reference wrote it.
        name: SurfaceName<'source>,
        /// The bytes of the member's own name, where it is declared.
        declared: ByteSpan,
    },

    /// A static member — a type member, or a type a signature states — whose
    /// type reads a dynamic member, a module's value or a parameter's: a type
    /// depends only on types.
    PhaseDependence
    {
        /// The bytes the reference covers.
        span: ByteSpan,
        /// The static member whose type the reference is written in.
        member: SurfaceName<'source>,
        /// The dynamic member it reads.
        reached: SurfaceName<'source>,
    },

    /// A declaration reading a model's inert component, a field its theory's
    /// operation marks `@[ inert ]`, when it is no inert component itself:
    /// only the manifest step reads an inert field, so no other content
    /// depends on it.
    InertRead
    {
        /// The bytes the read covers.
        span: ByteSpan,
        /// The declaration the read is written in.
        member: SurfaceName<'source>,
        /// The inert component it reads.
        reached: SurfaceName<'source>,
    },

    /// A module that exports no member of this name: a path selecting a
    /// member the module hid or never declared, or a signature component no
    /// member supplies.
    UnknownMember
    {
        /// The bytes the selection or the component covers.
        span: ByteSpan,
        /// The module, as the path or the declaration spelled it.
        module: SurfaceName<'source>,
        /// The member's name.
        member: SurfaceName<'source>,
    },

    /// A law of a module's model the module does not prove: no member answers
    /// it.
    UnprovenLaw
    {
        /// The bytes of the law's name.
        span: ByteSpan,
        /// The module, as the declaration spelled it.
        module: SurfaceName<'source>,
        /// The law's name.
        law: SurfaceName<'source>,
    },

    /// A field read off a data value by its name, `e.l`, where a constructor
    /// of the value's family declares no field of that name: the value it
    /// builds has none to read.
    PartialField
    {
        /// The bytes of the field's name.
        span: ByteSpan,
        /// The field's name.
        field: SurfaceName<'source>,
        /// The first constructor declaring no such field.
        constructor: SurfaceName<'source>,
    },

    /// A module binding `module A = F(X) ;` whose `F` names no functor
    /// declared before it.
    NotAFunctor
    {
        /// The bytes of the name applied.
        span: ByteSpan,
        /// The name as the binding wrote it.
        name: SurfaceName<'source>,
    },

    /// A path projected from a functor application, `F(X).T` or `F(X).x`: an
    /// application names its instance only once a module binding binds it,
    /// `module A = F(X) ;`, so `A.T` is the spelling.
    ProjectionFromApplication
    {
        /// The bytes of the application projected from.
        span: ByteSpan,
        /// The functor applied.
        functor: SurfaceName<'source>,
    },

    /// A module ascription form the fragment does not read yet.
    UnreadAscription
    {
        /// The bytes of the component's name.
        span: ByteSpan,
        /// The type component the form ascribes.
        name: SurfaceName<'source>,
        /// The form.
        form: AscriptionForm,
    },

    /// A component of a derived model signature the derivation cannot state,
    /// kept on the component of its name rather than dropped from the
    /// signature.
    UnstatedComponent
    {
        /// The bytes of the theory the signature is derived from, as the
        /// ascription names it.
        span: ByteSpan,
        /// The component's name.
        name: SurfaceName<'source>,
        /// Why it cannot be stated.
        fault: crate::model::ModelFault,
    },

    /// A member of a theory a capability scope handles that cannot stand in
    /// the effect interface the scope reads the theory as.
    UninterfacedMember
    {
        /// The bytes of the theory, as the scope names it.
        span: ByteSpan,
        /// The member's name.
        name: SurfaceName<'source>,
        /// Why it cannot stand.
        fault: crate::model::InterfaceFault,
    },

    /// A member of a description declaration the description route or its
    /// cell layer does not read, kept at its own span under the family's
    /// name.
    UndescribedMember
    {
        /// The bytes of the member.
        span: ByteSpan,
        /// Why it is not read.
        fault: crate::description::MemberFault,
    },

    /// A type family member whose parameters disagree with the index
    /// telescope its component states.
    FamilyTelescope
    {
        /// The bytes of the family member's name.
        span: ByteSpan,
        /// The family's name.
        name: SurfaceName<'source>,
        /// Where the parameters and the indices part.
        fault: TelescopeFault,
    },

    /// A top-level module named with a lowercase initial, a spelling the
    /// grammar admits so it is declined here by name, and reserves for nested
    /// modules.
    LowercaseModuleName
    {
        /// The bytes the declaration covers.
        span: ByteSpan,
        /// The name as it was written.
        name: SurfaceName<'source>,
    },

    /// A declaration whose header binds parameters in an implicit telescope
    /// `@[…]` an entry of which is out of shape: an entry is a lower-case name
    /// and its sort, `a : Type` or the stage binder `i : Size`, or a stage's
    /// bound `i < n`, and a telescope binding a value stands before a
    /// function's parameters.
    ImplicitTelescope
    {
        /// The bytes the declaration covers.
        span: ByteSpan,
    },

    /// A function whose merged telescope has no order: two parameters each
    /// mention the other in their types, directly or through the telescope.
    TelescopeCycle
    {
        /// The bytes the declaration covers.
        span: ByteSpan,
        /// A parameter the merge could not place.
        first: SurfaceName<'source>,
        /// A parameter its type waits on.
        second: SurfaceName<'source>,
    },

    /// A use of a function with an implicit parameter that supplies none for
    /// it: an implicit is supplied by name in the instantiation slot, `f[a =
    /// T](…)`, never inferred in this fragment and never written among the
    /// parentheses.
    ImplicitUnsupplied
    {
        /// The bytes of the use.
        span: ByteSpan,
        /// The function's name.
        function: SurfaceName<'source>,
        /// The first implicit the use leaves unsupplied.
        implicit: SurfaceName<'source>,
    },

    /// A call writing a function's implicit argument among its parentheses:
    /// it passes one argument per parameter, the implicits with the explicit
    /// ones, where an implicit is supplied by name.
    ImplicitInParentheses
    {
        /// The bytes of the call.
        span: ByteSpan,
        /// The function's name.
        function: SurfaceName<'source>,
        /// The first implicit of the function.
        implicit: SurfaceName<'source>,
    },

    /// A call omitting an instance a label of the callee's row names, `f()`
    /// for `def f() -> [a : I] B`, where no instance of `I` stands: a call
    /// resolves an omitted instance among the instances of its interface in
    /// scope, a capability scope's capability and a label of the caller's own
    /// row.
    InstanceUnanswered
    {
        /// The bytes of the call.
        span: ByteSpan,
        /// The function's name.
        function: SurfaceName<'source>,
        /// The instance the call omits.
        instance: SurfaceName<'source>,
        /// The instance's interface.
        interface: SurfaceName<'source>,
    },

    /// A call omitting an instance where several instances of its interface
    /// are in scope: the call names the one it means, `f[a = c](…)`.
    InstanceAmbiguous
    {
        /// The bytes of the call.
        span: ByteSpan,
        /// The function's name.
        function: SurfaceName<'source>,
        /// The instance the call omits.
        instance: SurfaceName<'source>,
        /// The instance's interface.
        interface: SurfaceName<'source>,
        /// The innermost instance of the interface in scope.
        first: SurfaceName<'source>,
        /// Another instance of the interface in scope.
        second: SurfaceName<'source>,
    },

    /// A model implicit standing as a value: named alone where a value is
    /// read, or supplied by what names neither a module nor a model implicit.
    /// A model implicit is its components, each read as `s.x`, and a slot
    /// takes a module's name or a model implicit's, `f[s = M]`.
    ModelImplicitValue
    {
        /// The bytes of the name or the supply.
        span: ByteSpan,
        /// The model implicit's name.
        implicit: SurfaceName<'source>,
    },

    /// A definition's region binder, bound `r : Region` in its telescope,
    /// named as a value: a region is erased and never computed, so the body
    /// reads one only in a kept type `A at r`.
    RegionAsValue
    {
        /// The bytes of the name.
        span: ByteSpan,
        /// The region binder's name.
        name: SurfaceName<'source>,
    },

    /// A source's top-level `main`, its program's entry, declared at a type no
    /// entry has: an entry is a computation returning the exit code, `-F
    /// Integer`, or the unit, `-F Unit`, taking the arguments as one
    /// `List(String)` when it takes any.
    EntryType
    {
        /// The bytes of the name.
        span: ByteSpan,
    },

    /// A receiver's mode word, `shared` or `consumed`, written on a parameter
    /// that is no method's receiver: only a module member's first parameter,
    /// `self`, takes one.
    StrayReceiverMode
    {
        /// The bytes of the mode word.
        span: ByteSpan,
        /// The mode word as written.
        mode: SurfaceName<'source>,
    },

    /// A call `s.f(…)` whose `f` is a method of more than one module in
    /// scope.
    AmbiguousMethod
    {
        /// The bytes of the method's name at the call.
        span: ByteSpan,
        /// The method's name.
        method: SurfaceName<'source>,
        /// The first module declaring it, in collection order.
        first: SurfaceName<'source>,
        /// The second module declaring it.
        second: SurfaceName<'source>,
        /// How many more modules declare it.
        more: CandidateCount,
    },

    /// A method whose receiver is at a mode its telescope binds, `self : m T`,
    /// whose result is no `-F View[m](a)` over that mode, or whose body is no
    /// place of its receiver, `{ self[i] }`; or a view type `View[m](a)`
    /// anywhere but such a method's result.
    ViewNotPlace
    {
        /// The bytes of the result, the body or the view type out of shape.
        span: ByteSpan,
    },

    /// A view block `e as w { … }` whose `e` is no call of a method answering
    /// a place.
    ViewOfNoPlace
    {
        /// The bytes of the call, or of the method's name at it.
        span: ByteSpan,
    },

    /// A match some scrutinee reaches no arm of: a constructor, or an integer
    /// or boolean value, that every arm's pattern refuses.
    NonExhaustiveMatch
    {
        /// The bytes the match covers.
        span: ByteSpan,
    },

    /// A match pattern of another kind than the first pattern tested at its
    /// place: a constructor of another data type, or a literal, a tuple, a
    /// record, an injection or a list pattern where the first is of another
    /// of those kinds.
    MismatchedPattern
    {
        /// The bytes of the pattern.
        span: ByteSpan,
        /// The bytes of the first pattern tested at its place.
        first: ByteSpan,
    },

    /// A recursive definition's own name written without a claim of how it
    /// recurses.
    UnmarkedSelfReference
    {
        /// The bytes the name covers.
        span: ByteSpan,
        /// The definition's name.
        name: SurfaceName<'source>,
    },

    /// A productivity claim `f[>](…)` standing anywhere but as the whole arm
    /// of a copattern block.
    UnguardedCorecursion
    {
        /// The bytes the claim covers.
        span: ByteSpan,
        /// The definition's name.
        name: SurfaceName<'source>,
    },

    /// A recursive definition whose claims descend on two parameters: one
    /// stands under a match on one parameter, another under a match on a
    /// different one, and a definition stages one.
    DescentOnSeveralParameters
    {
        /// The bytes the claim that disagrees covers.
        span: ByteSpan,
        /// The parameter the earlier claims descend on.
        staged: SurfaceName<'source>,
        /// The parameter this claim descends on.
        claimed: SurfaceName<'source>,
    },

    /// The rest of a block after a statement whose every path exits: no path
    /// reaches it.
    Unreachable
    {
        /// The bytes from the first statement no path reaches to the block's
        /// last computation.
        span: ByteSpan,
    },

    /// A `break` or a `continue` on no path through a loop's body: outside
    /// every loop, or inside a function, a lambda, a thunk or a copattern
    /// clause a loop holds, whose body is its own.
    OutsideLoop
    {
        /// The bytes the exit covers.
        span: ByteSpan,
        /// Which exit was written.
        exit: LoopExit,
    },

    /// A `become` in a handled subject, or a `break` or a `continue` there
    /// whose loop holds the scope: each would run code in place of a live
    /// handler's frame, which is no tail. A `return` there leaves its body
    /// past every frame instead.
    AcrossHandler
    {
        /// The bytes the exit covers.
        span: ByteSpan,
        /// Which exit was written.
        exit: CrossedExit,
    },

    /// A pattern matching a path against reflexivity, `here`: axiom K where
    /// the endpoints are fixed, and in every case a second eliminator beside
    /// transport, which is the only way a path is used.
    WithoutK
    {
        /// The bytes the pattern covers.
        span: ByteSpan,
    },

    /// A `data` block's member `name : a --> b` between two terms: a directed
    /// cell, which builds no word a path type reads, so only the invertible
    /// `<->` is a cell between terms.
    DirectedCell
    {
        /// The bytes the arrow covers.
        span: ByteSpan,
    },

    /// A `data` block's cell `name : a <-> b` between two distinct terms:
    /// only a loop, a cell from a point to itself, mints the words of the
    /// path type at that point.
    CellNotALoop
    {
        /// The bytes the cell covers.
        span: ByteSpan,
    },

    /// A rule of a `data` or `theory` block whose right-hand side the path
    /// order does not put below its left-hand side, so the block's rules
    /// are not known to terminate.
    RulesUnoriented
    {
        /// The bytes the rule covers.
        span: ByteSpan,
    },

    /// A rule of a `data` or `theory` block whose left side names one
    /// variable twice: a rule matches each variable once, because a copy of
    /// a matched value needs a comonoid its sort may not have.
    RulesNonLinear
    {
        /// The bytes the rule covers.
        span: ByteSpan,
        /// The bytes of the variable's second occurrence on the left side.
        copy: ByteSpan,
    },

    /// Two rules of a block whose left sides overlap, one of which
    /// instantiates a variable a binding port binds, and whose critical pair
    /// does not join in the second-order reading: the block's rules are not
    /// confluent.
    RulesOverlapSecondOrder
    {
        /// The bytes the later rule covers.
        span: ByteSpan,
        /// The bytes the earlier rule covers.
        first: ByteSpan,
    },

    /// Two rules of a block whose left sides overlap, one of which fires under
    /// a row, states a freshness condition or moves a variable across an
    /// abstraction where a term can name an atom, and whose critical pair does
    /// not join under the condition the overlap composes: the block's rules
    /// are not confluent.
    RulesOverlapCondition
    {
        /// The bytes the later rule covers.
        span: ByteSpan,
        /// The bytes the earlier rule covers.
        first: ByteSpan,
    },

    /// Two rules of a block that match one term and rewrite it to two normal
    /// forms headed by constructors: no rule joins two values, so the block's
    /// first-match reading and its equational reading part.
    RulesDiverge
    {
        /// The bytes the later rule covers.
        span: ByteSpan,
        /// The bytes the earlier rule covers.
        first: ByteSpan,
    },

    /// Two rules of a block that match one term and rewrite it to two normal
    /// forms the path order does not orient into a rule from an operation
    /// call, so completion derives no rule joining them.
    RulesUncompleted
    {
        /// The bytes the later rule covers.
        span: ByteSpan,
        /// The bytes the earlier rule covers.
        first: ByteSpan,
    },

    /// Two rules of a block whose completion never ends: the rule it derives
    /// from them wraps an earlier derived rule at one point, and no rule
    /// rewrites any further wrapping, so every round derives a longer rule.
    RulesNeverComplete
    {
        /// The bytes the later rule covers.
        span: ByteSpan,
        /// The bytes the earlier rule covers.
        first: ByteSpan,
    },

    /// Two rules of a block that match one term the coincidence check did not
    /// decide within its budget: a rewrite reaching no normal form within its
    /// steps, or a pair still parting once completion derived its most rules.
    RulesUndecided
    {
        /// The bytes the later rule covers.
        span: ByteSpan,
        /// The bytes the earlier rule covers.
        first: ByteSpan,
    },

    /// A `derive` declaration whose statement its theory's completed rules
    /// do not prove.
    UnderivedRule
    {
        /// The bytes of the declaration.
        span: ByteSpan,
        /// The rule's name.
        rule: SurfaceName<'source>,
        /// The theory's name.
        theory: SurfaceName<'source>,
        /// Why the theory does not derive it.
        fault: crate::derive::DeriveFault,
    },

    /// `Eq.generic` read anywhere but as the whole body of a definition,
    /// `def m = Eq.generic(T)`, applied to one data type.
    GenericMisplaced
    {
        /// The bytes of the read.
        span: ByteSpan,
    },

    /// A definition `def m = Eq.generic(T)` whose data type the derivation
    /// writes no equality for.
    GenericUncovered
    {
        /// The bytes of the application.
        span: ByteSpan,
        /// The data type, as written.
        data: SurfaceName<'source>,
        /// What stopped the derivation.
        fault: gandr_core_term::generic::Uncovered,
    },

    /// A splice `~t` whose operand writes no tactic: `assumption`, or
    /// `intro(t)` of a tactic, under fewer than 32 introductions.
    UnknownTactic
    {
        /// The bytes of the operand.
        span: ByteSpan,
    },

    /// The lowering's work allowance ran out.
    BudgetExceeded
    {
        /// The allowance the caller set.
        budget: LoweringBudget,
    },

    /// The tree was molded under a grammar other than the one it was lowered
    /// with, so its molds would be read against the wrong table.
    GrammarMismatch
    {
        /// The fingerprint the tree carries.
        tree: GrammarFingerprint,
        /// The fingerprint of the grammar the lowering was given.
        grammar: GrammarFingerprint,
    },

    /// A node carries a mold the grammar's table does not hold.
    UnknownMold
    {
        /// The bytes the node covers.
        span: ByteSpan,
        /// The mold the node carries.
        mold: MoldId,
    },

    /// A capability form whose names the host's table cannot answer, the
    /// table being in conflict with itself: a fault of the engine's own
    /// table, never of the source.
    HostConflict
    {
        /// The bytes of the capability form.
        span: ByteSpan,
    },

    /// A declaration the lowering collected and refused nothing in, whose
    /// type and body it minted neither of: a gap in the lowering, never a
    /// fault of the source.
    Unminted
    {
        /// The bytes of the declaration.
        span: ByteSpan,
        /// The declared name.
        name: SurfaceName<'source>,
    },
}

/// A subject of an ill-formed description's refusal: the name as the
/// declaration spells it.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Subject<'source>(Maybe<SurfaceName<'source>, description_subject::Absent>);

impl fmt::Display for Subject<'_>
{
    /// Writes the name between backticks, or says the declaration does not
    /// spell it.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            Maybe::Present(name) => write!(f, "`{name}`"),
            Maybe::Absent(_) => f.write_str("a name it does not spell"),
        }
    }
}

/// Writes why the description check refuses a description, naming the
/// `subjects` its reason names, in their order.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — every kind the check gives, over the same two subjects,
///   renders a reason no other kind renders, so an empty or fixed text shows.
/// - witness: `error::tests::each_ill_formed_description_reads_as_its_own_reason`
fn ill_formed(
    kind: WfKind,
    subjects: [Maybe<SurfaceName<'_>, description_subject::Absent>; 2],
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result
{
    let [first, second] = subjects;
    let (one, other) = (Subject(first), Subject(second));
    match kind {
        WfKind::OutOfSignatureRule => match second {
            Maybe::Present(_) => write!(
                f,
                "the rule {one} applies {other}, which the signature does not declare"
            ),
            Maybe::Absent(_) => write!(
                f,
                "a rule applies {one}, which the signature does not declare"
            ),
        },
        WfKind::UnboundRhsVariable => write!(
            f,
            "a rule's right-hand side introduces {one}, which its left-hand side does not bind"
        ),
        WfKind::ArityDoesNotCompose => {
            write!(
                f,
                "the bridge arity of the operation {one} does not compose"
            )
        },
        WfKind::DeclaresDerivedMetadata => write!(
            f,
            "{one} declares {other}, which is derived from the rules, never declared"
        ),
        WfKind::DerivedBoundaryMismatch => write!(
            f,
            "the wiring of the rule {one} derives a boundary its declared sphere does not fix"
        ),
        WfKind::CyclicCircuitWiring => write!(
            f,
            "the wiring of the rule {one} reaches the port {other} from itself"
        ),
        WfKind::UnknownRewritePort => write!(
            f,
            "the rule {one} applies the rewrite {other}, which its telescope does not declare"
        ),
        WfKind::CircuitDerivationBudget => write!(
            f,
            "the wiring of the rule {one} unfolds past the derivation's node budget"
        ),
        WfKind::DuplicateSortName => write!(f, "the sort {one} is declared more than once"),
        WfKind::UnknownResultSort => write!(
            f,
            "the constructor {one} targets {other}, which is not a declared sort"
        ),
        WfKind::UnknownVarSort => write!(
            f,
            "the constructor {one} recurses at {other}, which is not a declared sort"
        ),
        WfKind::UnknownPortSort => write!(
            f,
            "the operation {one} has a port at {other}, which is neither a sort the signature \
             declares nor a builtin type"
        ),
        WfKind::SortPolarityDisagreement => write!(
            f,
            "the sort {one} declares a polarity its declaration does not"
        ),
        WfKind::MisplacedResults => f.write_str(
            "a rule writes a results tuple away from its right-hand root, the one place it \
             stands",
        ),
        WfKind::NonRepresentableBinder => write!(
            f,
            "the port {other} binds a variable of the sort {one}, which is not representable"
        ),
        WfKind::NonAtomAbstraction => write!(
            f,
            "the port {other} abstracts an atom of the sort {one}, which is not an atom sort"
        ),
        WfKind::SplitCircuitOutputs => write!(
            f,
            "the wiring of the rule {one} reads the port {other}, one output of a many-out \
             node, on its own"
        ),
        WfKind::DuplicateFaceName => write!(f, "the shape {one} names the face {other} twice"),
        WfKind::FaceOutsideShape => {
            write!(f, "the face {one} holds a point outside the shape {other}")
        },
        WfKind::UnsortedBinding => write!(
            f,
            "a rule uses {one} where no port binds it over the same sorts"
        ),
        WfKind::AtomResult => write!(
            f,
            "the operation {one} returns {other}, an atom sort, which is compared and swapped, \
             never produced"
        ),
        WfKind::MisplacedAbstraction => f.write_str(
            "a rule abstracts names where no operation's port abstracts or binds as many; an \
             abstraction stands only as an argument at a port that binds its names",
        ),
        WfKind::UnknownFreshness => write!(
            f,
            "the freshness condition on the atom {one} and {other} names an atom no abstraction \
             of the rule abstracts, or a variable its left side does not bind"
        ),
        WfKind::Capture => write!(
            f,
            "{one} stands under an abstraction of {other} on one side of the rule and outside it \
             on the other, so an instance naming {other} would be captured or escape"
        ),
        WfKind::MisplacedAtom => write!(
            f,
            "a rule names the atom {one} under no abstraction of it, or where no port of its sort \
             stands; an atom is named only inside `bind {one} . t`, at a port of the sort it \
             abstracts"
        ),
        WfKind::UndecidedCondition => write!(
            f,
            "the rule holds only of an instance of {one} that does not name the atom it \
             crosses, and the operation {other} takes an atom, so a term can name one: no \
             rewriting step decides that condition yet"
        ),
    }
}

impl fmt::Display for LoweringRefusal<'_>
{
    /// Writes the refusal without the positions it names: a diagnostic
    /// locates those through [`LoweringRefusal::span`] and the payload's own
    /// spans, so the message never repeats them as byte offsets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::UnresolvedName { name, .. } => {
                write!(f, "no declaration or binder answers `{name}`")
            },
            Self::UnresolvedDocLink { name, .. } => {
                write!(
                    f,
                    "the documentation links to `{name}`, which nothing declares"
                )
            },
            Self::UnresolvedTypeHead { name, arity, .. } => {
                write!(f, "no type head answers `{name}` {arity}")
            },
            Self::DuplicateSignature { name, .. } => {
                write!(f, "`{name}` already has a signature")
            },
            Self::DuplicateDefinition { name, .. } => {
                write!(f, "`{name}` already has a definition")
            },
            Self::DuplicateImportAlias { alias, .. } => write!(
                f,
                "the import alias `{alias}` is already bound by an earlier import: {ONE_SOURCE}"
            ),
            Self::ImportUnresolved { .. } => f.write_str(
                "this source's import names no source its root holds that lowers, so none of its declarations is read",
            ),
            Self::ImportCycle { .. } => f.write_str(
                "this source's import is an edge of an import cycle, so none of its declarations is read",
            ),
            Self::ImportShadows { name, .. } => write!(
                f,
                "`{name}` is bound by an import and by another binding of this source"
            ),
            Self::UnexportedName {
                name,
                reason: Unexported::Undefined,
                ..
            } => write!(
                f,
                "`{name}` is declared by an imported source without a definition, so it is not exported"
            ),
            Self::UnexportedName {
                name,
                reason: Unexported::Private,
                ..
            } => write!(
                f,
                "`{name}` is private to the imported source that declares it; `pub` before its declaration exports it"
            ),
            Self::ShadowedBuiltin { name, .. } => write!(
                f,
                "`{name}` shadows a builtin name, which the active policy forbids"
            ),
            Self::OutOfFragment {
                form,
                sort,
                boundary,
                ..
            } => write!(f, "{form}, read as {sort}, {boundary}"),
            Self::BareFeedback { .. } => f.write_str(
                "a fed-back port is read bare: the rule's body reads it under no observation of \
                 its sort",
            ),
            Self::IllFormedDescription { kind, subjects, .. } => ill_formed(kind, subjects, f),
            Self::GradedBridge { grade, .. } => write!(
                f,
                "the bridge's grade `{grade}` is not the default `ω`, the only grade the \
                 fragment admits"
            ),
            Self::MalformedLiteral { form, .. } => {
                write!(f, "the text is not the lexeme of {form}")
            },
            Self::NoUniverseAbove { level, .. } => write!(
                f,
                "the universe level `{level}` is at or past the greatest, which has no universe \
                 above it"
            ),
            Self::MalformedForm { form, fault, .. } => write!(f, "{form} {fault}"),
            Self::UnknownAttribute {
                name, suggestion, ..
            } => match suggestion {
                Maybe::Present(nearest) => write!(
                    f,
                    "no attribute is registered as `{name}`; the nearest is `{nearest}`"
                ),
                Maybe::Absent(_) => write!(f, "no attribute is registered as `{name}`"),
            },
            Self::DuplicateAttribute { name, .. } => {
                write!(f, "the attribute `{name}` is already written")
            },
            Self::MissingPayload { name, expected, .. } => {
                write!(f, "`{name}` takes {expected} and was given none")
            },
            Self::NonValuePayload { name, form, .. } => {
                write!(f, "the payload of `{name}` is {form}, not a value")
            },
            Self::IllTypedPayload {
                name,
                expected,
                written,
                ..
            } => write!(f, "`{name}` takes {expected} and was given {written}"),
            Self::ForwardMemberReference { name, .. } => write!(
                f,
                "the member `{name}` is declared at or after the member naming it; a member \
                 names only the members before it"
            ),
            Self::PhaseDependence { member, reached, .. } => write!(
                f,
                "the type `{member}` depends on the value `{reached}`; a type is static and \
                 depends only on static members, never on a module's or a parameter's values"
            ),
            Self::InertRead { member, reached, .. } => write!(
                f,
                "`{member}` reads `{reached}`, a field its theory marks inert; only the \
                 manifest step and another inert field read an inert field"
            ),
            Self::UnknownMember { module, member, .. } => {
                write!(f, "the module `{module}` exports no member `{member}`")
            },
            Self::UnprovenLaw { module, law, .. } => write!(
                f,
                "the module `{module}` neither proves nor admits its model's law `{law}`"
            ),
            Self::PartialField {
                field, constructor, ..
            } => write!(
                f,
                "the constructor `{constructor}` declares no field `{field}`, so a value it \
                 builds has no `{field}` to read"
            ),
            Self::NotAFunctor { name, .. } => write!(
                f,
                "`{name}` is applied as a functor, and no functor `{name}` is declared before \
                 the binding"
            ),
            Self::ProjectionFromApplication { functor, .. } => write!(
                f,
                "a path is read off an application of `{functor}`; bind the application first, \
                 `module A = {functor}(…) ;`, and read the path off `A`"
            ),
            Self::UnreadAscription { name, form, .. } => {
                write!(f, "`{name}` {form}; the fragment does not read it yet")
            },
            Self::UnstatedComponent { name, fault, .. } => write!(
                f,
                "the model signature cannot state `{name}`, which {fault}"
            ),
            Self::UninterfacedMember { name, fault, .. } => write!(
                f,
                "the theory cannot stand as the interface its handler reads at `{name}`, which {fault}"
            ),
            Self::UndescribedMember { fault, .. } => write!(f, "this member {fault}"),
            Self::FamilyTelescope { name, fault, .. } => {
                write!(f, "the type family `{name}` {fault}")
            },
            Self::LowercaseModuleName { name, .. } => write!(
                f,
                "the module `{name}` is named with a lowercase initial; a top-level module's \
                 name starts with an uppercase letter"
            ),
            Self::ImplicitTelescope { .. } => f.write_str(
                "this declaration's implicit telescope `@[…]` has an entry out of shape: an entry \
                 is a lower-case name and its sort, `a : Type` or a stage `i : Size`, or a \
                 stage's bound `i < n`, and a telescope binding a value stands before a \
                 function's parameters",
            ),
            Self::TelescopeCycle { first, second, .. } => write!(
                f,
                "the parameters `{first}` and `{second}` mention each other through their types, \
                 so no order of the telescope binds each after what its type names"
            ),
            Self::ImplicitUnsupplied {
                function, implicit, ..
            } => write!(
                f,
                "`{function}` takes the implicit `{implicit}`, which this use does not supply; \
                 supply it by name, `{function}[{implicit} = …](…)`"
            ),
            Self::ImplicitInParentheses {
                function, implicit, ..
            } => write!(
                f,
                "this call writes `{function}`'s implicit arguments among its parentheses; \
                 supply `{implicit}` by name, `{function}[{implicit} = …](…)`, and pass the \
                 explicit arguments alone"
            ),
            Self::InstanceUnanswered {
                function,
                instance,
                interface,
                ..
            } => write!(
                f,
                "`{function}` performs `{interface}` through its instance `{instance}`, and no \
                 instance of `{interface}` is handled where this call stands: handle one around \
                 the call, `handle c : {interface} {{ … }}`, or supply one by name, \
                 `{function}[{instance} = c](…)`"
            ),
            Self::InstanceAmbiguous {
                function,
                instance,
                interface,
                first,
                second,
                ..
            } => write!(
                f,
                "`{function}`'s instance `{instance}` could be `{first}` or `{second}`, each an \
                 instance of `{interface}` handled where this call stands: name the one it \
                 means, `{function}[{instance} = {first}](…)`"
            ),
            Self::ModelImplicitValue { implicit, .. } => write!(
                f,
                "the model implicit `{implicit}` is its components and stands as no value: read \
                 each as `{implicit}.x`, and supply the slot by a module's name or a model \
                 implicit's, `f[{implicit} = M]`"
            ),
            Self::EntryType { .. } => f.write_str(
                "`main` is the program's entry: it is a computation returning the exit code or the \
                 unit, `() -> -F Integer` or `() -> -F Unit`, or one taking the arguments, `(args \
                 : List(String)) -> -F Integer`",
            ),
            Self::RegionAsValue { name, .. } => write!(
                f,
                "`{name}` binds a region, which is no value: it is read only where a type keeps a \
                 value in it, `A at {name}`"
            ),
            Self::StrayReceiverMode { mode, .. } => write!(
                f,
                "`{mode}` is a receiver's mode: only a module member's first parameter, `self`, \
                 is written with it"
            ),
            Self::AmbiguousMethod {
                method,
                first,
                second,
                more,
                ..
            } => {
                if usize::from(more) == 0_usize {
                    write!(
                        f,
                        "`{method}` is a method of both `{first}` and `{second}`, and a call \
                         selects exactly one"
                    )
                }
                else {
                    write!(
                        f,
                        "`{method}` is a method of `{first}`, `{second}` and {more} more modules, \
                         and a call selects exactly one"
                    )
                }
            },
            Self::ViewNotPlace { .. } => f.write_str(
                "a method whose receiver's mode is deduced answers a place of its receiver: its \
                 result is `-F View[m](a)` at the receiver's mode `m`, and its body is that \
                 place, `{ self[i] }`",
            ),
            Self::ViewOfNoPlace { .. } => f.write_str(
                "`e as w { … }` lends a view only of the place a method whose receiver's mode is \
                 deduced answers, `s.f(…) as w { … }`",
            ),
            Self::NonExhaustiveMatch { .. } => {
                f.write_str("the match leaves a value of its scrutinee that no arm matches")
            },
            Self::MismatchedPattern { .. } => f.write_str(
                "the pattern matches another type than the first pattern tested at its place",
            ),
            Self::UnmarkedSelfReference { name, .. } => write!(
                f,
                "`{name}` names its own recursive definition without a claim; write \
                 `{name}[<](…)` to recurse on a field of the parameter its match scrutinises"
            ),
            Self::UnguardedCorecursion { name, .. } => write!(
                f,
                "`{name}[>](…)` stands outside a copattern arm; a productive self-call is the \
                 whole arm of a copattern block, so every observation yields before it recurses"
            ),
            Self::DescentOnSeveralParameters {
                staged, claimed, ..
            } => write!(
                f,
                "this claim descends on `{claimed}`, and an earlier one on `{staged}`; a \
                 recursive definition descends on one parameter"
            ),
            Self::Unreachable { .. } => f.write_str(
                "no path reaches this code: every path through the statement before it exits",
            ),
            Self::OutsideLoop { exit, .. } => write!(
                f,
                "{exit} stands on no path through a loop's body; a function, a lambda, a \
                 thunk or a copattern clause inside a loop has a body of its own"
            ),
            Self::AcrossHandler { exit, .. } => write!(
                f,
                "{exit} would run in place of a live handler's frame; a handled subject \
                 leaves its body only by `return`, past every frame around it"
            ),
            Self::WithoutK { .. } => f.write_str(
                "a path is matched against `here`, which is axiom K; a path is used by \
                 transport, and `back`, `then` and `cong` derive what a match would",
            ),
            Self::DirectedCell { .. } => f.write_str(
                "a directed cell `-->` between two terms builds no word of a path type; a cell \
                 between terms is the invertible `<->`",
            ),
            Self::CellNotALoop { .. } => f.write_str(
                "this cell joins two distinct terms; a cell `<->` is a loop at one point, \
                 written with the same term on both sides",
            ),
            Self::RulesUnoriented { .. } => f.write_str(
                "this rule's right-hand side is not below its left-hand side in the path order, \
                 so the block's rules may never end",
            ),
            Self::RulesNonLinear { .. } => f.write_str(
                "this rule's left-hand side names one variable twice: a rule matches each \
                 variable once, since copying a matched value needs a comonoid its sort may not \
                 have, so the rule is refused",
            ),
            Self::RulesOverlapSecondOrder { .. } => f.write_str(
                "this rule and an earlier one rewrite overlapping terms, one of them instantiates \
                 a variable, and the overlap rewrites to two different normal forms in the \
                 second-order reading, so the block's rules are refused",
            ),
            Self::RulesOverlapCondition { .. } => f.write_str(
                "this rule and an earlier one rewrite overlapping terms, one of them fires only \
                 under a row or where its instance names no atom it may not, and under the \
                 condition the overlap composes it rewrites to two different normal forms, so the \
                 block's rules are refused",
            ),
            Self::RulesDiverge { .. } => f.write_str(
                "this rule and an earlier one rewrite one term to two different constructor \
                 terms, so the rule written first decides what runs and the equations do not",
            ),
            Self::RulesUncompleted { .. } => f.write_str(
                "this rule and an earlier one rewrite one term to two normal forms the path order \
                 orients neither way, so no rule derived from them joins the two",
            ),
            Self::RulesNeverComplete { .. } => f.write_str(
                "this rule and an earlier one rewrite one term to two normal forms, and each \
                 rule completion derives to join them wraps the one before, so completion never \
                 ends",
            ),
            Self::RulesUndecided { .. } => write!(
                f,
                "this rule and an earlier one rewrite one term, and whether they agree is not \
                 decided within {} steps a rewrite and {} derived rules",
                crate::coincide::JOIN_STEPS,
                crate::coincide::DERIVED_RULES
            ),
            Self::UnderivedRule {
                rule,
                theory,
                fault,
                ..
            } => write!(f, "the theory `{theory}` does not derive `{rule}`: {fault}"),
            Self::UnknownTactic { .. } => f.write_str(
                "a splice runs a tactic: `assumption`, or `intro(t)` of a tactic `t`, under \
                 fewer than 32 introductions",
            ),
            Self::GenericMisplaced { .. } => f.write_str(
                "`Eq.generic` stands only as a definition's whole body, applied to one data \
                 type: `def eq = Eq.generic(T)`",
            ),
            Self::GenericUncovered { data, fault, .. } => {
                write!(f, "`Eq.generic` derives no equality for `{data}`: ")?;
                uncovered(f, fault)
            },
            Self::BudgetExceeded { budget } => {
                write!(f, "the lowering outran its allowance of {budget} steps")
            },
            Self::GrammarMismatch { tree, grammar } => write!(
                f,
                "the tree was molded under grammar {:#018x}, not the grammar {:#018x} it was lowered with",
                u64::from(tree),
                u64::from(grammar)
            ),
            Self::UnknownMold { mold, .. } => write!(
                f,
                "the mold {} is not in the grammar's table",
                u32::from(mold)
            ),
            Self::HostConflict { .. } => f.write_str(
                "the host's capability table is in conflict with itself, so it answers no \
                 capability's names",
            ),
            Self::Unminted { name, .. } => write!(
                f,
                "the lowering minted neither a type nor a body for `{name}`, and refused nothing \
                 in it"
            ),
        }
    }
}

/// Write why the derivation of `Eq.generic` stopped, `fault`, to `f`.
///
/// # Specification
/// - ensures: one clause per alternative; a field's names its constructor and
///   field by their positions, counted from zero.
/// - fails: what `f` fails with.
/// - panics: none.
/// - executable: none — what it writes goes to the formatter's sink, which no
///   predicate over the return reads.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — every refusal renders its own message.
/// - witness: `error::tests::every_tag_renders_its_own_message`
fn uncovered(
    f: &mut fmt::Formatter<'_>,
    fault: gandr_core_term::generic::Uncovered,
) -> fmt::Result
{
    use gandr_core_term::generic::Uncovered;
    let at = |site: gandr_kernel_term::OccurrenceSite| match site {
        gandr_kernel_term::OccurrenceSite::Field { tag, field } => {
            (usize::from(tag), usize::from(field))
        },
        gandr_kernel_term::OccurrenceSite::Parameter(parameter) => (0, usize::from(parameter)),
    };
    match fault {
        Uncovered::Unknown(_) => f.write_str("it is no data declaration"),
        Uncovered::Applied(_) => f.write_str("it takes parameters or indices"),
        Uncovered::Presented(_) => f.write_str(
            "its terms are presented by rules, a quotient structural equality does not respect",
        ),
        Uncovered::Field(_, site) => {
            let (tag, field) = at(site);
            write!(
                f,
                "field {field} of constructor {tag} has no equality the program decides: a \
                 function, a universe, a path, a list or a float"
            )
        },
        Uncovered::Dependent(_, site) => {
            let (tag, field) = at(site);
            write!(
                f,
                "field {field} of constructor {tag} reads a field before it"
            )
        },
        Uncovered::Uncoded(_, site) => {
            let (tag, field) = at(site);
            write!(
                f,
                "field {field} of constructor {tag} has a type its levitated code does not carry, \
                 so it has no code to derive from"
            )
        },
        Uncovered::Cycle(_, site) => {
            let (tag, field) = at(site);
            write!(
                f,
                "field {field} of constructor {tag} reaches a declaration whose equality is \
                 derived through it"
            )
        },
        Uncovered::Nested(_, site) => {
            let (tag, field) = at(site);
            write!(
                f,
                "field {field} of constructor {tag} holds the type under a product or a sum"
            )
        },
        Uncovered::DependentCase(_, site) => {
            let (tag, field) = at(site);
            write!(
                f,
                "field {field} of constructor {tag} is a sum or a tuple, whose law cases on it under \
                 a motive core's case does not carry (#2374)"
            )
        },
        Uncovered::Inductive(_, site) => {
            let (tag, field) = at(site);
            write!(
                f,
                "field {field} of constructor {tag} holds the type itself, whose law is an \
                 induction the derivation does not write"
            )
        },
        Uncovered::BinderCeiling => {
            f.write_str("its constructors open more binders than a term holds")
        },
    }
}

impl Error for LoweringRefusal<'_>
{
}

impl LoweringRefusal<'_>
{
    /// The bytes of the source this refusal is about.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: the span the variant rejected, which for a duplicate is the
    ///   second occurrence rather than the first, so the reported position is
    ///   the one an author would delete; the run absence for the allowance
    ///   refusal and the grammar mismatch, which are about the run rather than
    ///   about a position in the source.
    /// - provides: the position a diagnostic renders the refusal at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the const predicate separates source spans from the
    ///   two run absences. The current finite vocabulary is enumerated with
    ///   exact spans, including distinct earlier and rejected occurrences; this
    ///   witness catches returning the wrong span within a variant.
    /// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
    #[spec(
        ensures: |ret| {
            matches!(ret, Maybe::Absent(refusal_span::Absent::Run))
                == matches!(
                    *self,
                    Self::BudgetExceeded { .. } | Self::GrammarMismatch { .. }
                )
        },
    )]
    #[inline]
    pub const fn span(&self) -> Maybe<ByteSpan, refusal_span::Absent>
    {
        match *self {
            Self::UnresolvedName { span, .. }
            | Self::UnresolvedDocLink { span, .. }
            | Self::UnresolvedTypeHead { span, .. }
            | Self::DuplicateSignature { span, .. }
            | Self::DuplicateDefinition { span, .. }
            | Self::DuplicateImportAlias { span, .. }
            | Self::ImportUnresolved { span, .. }
            | Self::ImportCycle { span, .. }
            | Self::ImportShadows { span, .. }
            | Self::UnexportedName { span, .. }
            | Self::ShadowedBuiltin { span, .. }
            | Self::OutOfFragment { span, .. }
            | Self::BareFeedback { span, .. }
            | Self::IllFormedDescription { span, .. }
            | Self::GradedBridge { span, .. }
            | Self::MalformedLiteral { span, .. }
            | Self::NoUniverseAbove { span, .. }
            | Self::MalformedForm { span, .. }
            | Self::UnknownAttribute { span, .. }
            | Self::DuplicateAttribute { span, .. }
            | Self::MissingPayload { span, .. }
            | Self::NonValuePayload { span, .. }
            | Self::IllTypedPayload { span, .. }
            | Self::ForwardMemberReference { span, .. }
            | Self::PhaseDependence { span, .. }
            | Self::InertRead { span, .. }
            | Self::UnknownMember { span, .. }
            | Self::UnprovenLaw { span, .. }
            | Self::PartialField { span, .. }
            | Self::NotAFunctor { span, .. }
            | Self::ProjectionFromApplication { span, .. }
            | Self::UnreadAscription { span, .. }
            | Self::UnstatedComponent { span, .. }
            | Self::UninterfacedMember { span, .. }
            | Self::UndescribedMember { span, .. }
            | Self::FamilyTelescope { span, .. }
            | Self::LowercaseModuleName { span, .. }
            | Self::ImplicitTelescope { span }
            | Self::TelescopeCycle { span, .. }
            | Self::ImplicitUnsupplied { span, .. }
            | Self::ImplicitInParentheses { span, .. }
            | Self::InstanceUnanswered { span, .. }
            | Self::InstanceAmbiguous { span, .. }
            | Self::ModelImplicitValue { span, .. }
            | Self::RegionAsValue { span, .. }
            | Self::EntryType { span }
            | Self::StrayReceiverMode { span, .. }
            | Self::AmbiguousMethod { span, .. }
            | Self::ViewNotPlace { span }
            | Self::ViewOfNoPlace { span }
            | Self::NonExhaustiveMatch { span }
            | Self::MismatchedPattern { span, .. }
            | Self::UnmarkedSelfReference { span, .. }
            | Self::UnguardedCorecursion { span, .. }
            | Self::DescentOnSeveralParameters { span, .. }
            | Self::Unreachable { span }
            | Self::OutsideLoop { span, .. }
            | Self::AcrossHandler { span, .. }
            | Self::WithoutK { span }
            | Self::DirectedCell { span }
            | Self::CellNotALoop { span }
            | Self::RulesUnoriented { span }
            | Self::RulesNonLinear { span, .. }
            | Self::RulesDiverge { span, .. }
            | Self::RulesOverlapSecondOrder { span, .. }
            | Self::RulesOverlapCondition { span, .. }
            | Self::RulesUncompleted { span, .. }
            | Self::RulesNeverComplete { span, .. }
            | Self::RulesUndecided { span, .. }
            | Self::UnderivedRule { span, .. }
            | Self::GenericMisplaced { span }
            | Self::UnknownTactic { span }
            | Self::GenericUncovered { span, .. }
            | Self::UnknownMold { span, .. }
            | Self::HostConflict { span }
            | Self::Unminted { span, .. } => Maybe::Present(span),
            Self::BudgetExceeded { .. } | Self::GrammarMismatch { .. } => {
                Maybe::Absent(refusal_span::Absent::Run)
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ClosingClass;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use quenchant_shape::shape::Maybe;

    use super::AscriptionForm;
    use super::CrossedExit;
    use super::FormFault;
    use super::FragmentBoundary;
    use super::FragmentSort;
    use super::LoopExit;
    use super::LoweringRefusal;
    use super::TelescopeFault;
    use super::Unexported;
    use super::refusal_span;
    use crate::attribute::AttributeSchema;
    use crate::attribute::PayloadForm;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::form::Repair;
    use crate::lower::LoweringBudget;
    use crate::resolve::CandidateCount;
    use crate::resolve::HeadArity;
    use crate::resolve::OperandCount;
    use crate::resolve::SurfaceName;
    use crate::unbuilt::Unbuilt;

    /// One inhabitant of every variant, each with its own rejected span.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the fixture has no repeated variant tag; source-bearing
    ///   variants carry separately observable rejected spans.
    /// - provides: a finite domain for the exact span projection witness.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the predicate checks pairwise tag distinctness, while
    ///   the span witness separates payload selection and run absence. Coverage
    ///   is for the current vocabulary; a new variant requires extending this
    ///   fixture.
    /// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
    #[spec(
        ensures: |ret| {
            ret.iter().enumerate().all(|(index, left)| {
                ret.iter()
                    .skip(index.saturating_add(1_usize))
                    .all(|right| core::mem::discriminant(left) != core::mem::discriminant(right))
            })
        },
    )]
    fn every_variant() -> [LoweringRefusal<'static>; 73_usize]
    {
        let owes = registered(SurfaceName::from("owes"));
        let s = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        [
            LoweringRefusal::UnresolvedName {
                span: s(1_usize, 2_usize),
                name: SurfaceName::from("x"),
            },
            LoweringRefusal::UnresolvedTypeHead {
                span: s(3_usize, 4_usize),
                name: SurfaceName::from("Intgr"),
                arity: HeadArity::Nullary,
            },
            LoweringRefusal::DuplicateSignature {
                span: s(5_usize, 6_usize),
                name: SurfaceName::from("x"),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::DuplicateDefinition {
                span: s(7_usize, 8_usize),
                name: SurfaceName::from("x"),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::OutOfFragment {
                span: s(9_usize, 10_usize),
                form: FormName::from(NamedKind("lazy_product_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::Reserved(Unbuilt::UnknownType),
            },
            LoweringRefusal::MalformedLiteral {
                span: s(11_usize, 12_usize),
                form: FormName::from(NamedKind("number")),
            },
            LoweringRefusal::MalformedForm {
                span: s(23_usize, 23_usize),
                form: FormName::DECLARATION,
                fault: FormFault::MissingOperand,
            },
            LoweringRefusal::UnknownAttribute {
                span: s(13_usize, 14_usize),
                name: SurfaceName::from("check"),
                suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
            },
            LoweringRefusal::DuplicateAttribute {
                span: s(15_usize, 16_usize),
                name: SurfaceName::from("checks"),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::MissingPayload {
                span: s(17_usize, 18_usize),
                name: owes,
                expected: AttributeSchema::Integer,
            },
            LoweringRefusal::NonValuePayload {
                span: s(19_usize, 20_usize),
                name: owes,
                form: FormName::from(NamedKind("pure_expression")),
            },
            LoweringRefusal::IllTypedPayload {
                span: s(21_usize, 22_usize),
                name: owes,
                expected: AttributeSchema::Integer,
                written: PayloadForm::Text,
            },
            LoweringRefusal::BudgetExceeded {
                budget: LoweringBudget::from(4_usize),
            },
            LoweringRefusal::GrammarMismatch {
                tree: GrammarFingerprint::from(1_u64),
                grammar: GrammarFingerprint::from(2_u64),
            },
            LoweringRefusal::UnknownMold {
                span: s(24_usize, 25_usize),
                mold: MoldId::from(9_u32),
            },
            LoweringRefusal::DuplicateImportAlias {
                span: s(26_usize, 27_usize),
                alias: SurfaceName::from("parse"),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::ShadowedBuiltin {
                span: s(28_usize, 29_usize),
                name: SurfaceName::from("list"),
            },
            LoweringRefusal::GradedBridge {
                span: s(30_usize, 31_usize),
                grade: SurfaceName::from("1"),
            },
            LoweringRefusal::ForwardMemberReference {
                span: s(32_usize, 33_usize),
                name: SurfaceName::from("second"),
                declared: s(40_usize, 46_usize),
            },
            LoweringRefusal::PhaseDependence {
                span: s(83_usize, 84_usize),
                member: SurfaceName::from("Q"),
                reached: SurfaceName::from("n"),
            },
            LoweringRefusal::InertRead {
                span: s(90_usize, 94_usize),
                member: SurfaceName::from("named"),
                reached: SurfaceName::from("name"),
            },
            LoweringRefusal::UnknownMember {
                span: s(34_usize, 35_usize),
                module: SurfaceName::from("Facts"),
                member: SurfaceName::from("hidden"),
            },
            LoweringRefusal::UnreadAscription {
                span: s(36_usize, 37_usize),
                name: SurfaceName::from("T"),
                form: AscriptionForm::Kinded,
            },
            LoweringRefusal::LowercaseModuleName {
                span: s(38_usize, 39_usize),
                name: SurfaceName::from("natAdd"),
            },
            LoweringRefusal::UnmarkedSelfReference {
                span: s(41_usize, 42_usize),
                name: SurfaceName::from("length"),
            },
            LoweringRefusal::UnguardedCorecursion {
                span: s(77_usize, 78_usize),
                name: SurfaceName::from("nats"),
            },
            LoweringRefusal::UnresolvedDocLink {
                span: s(43_usize, 44_usize),
                name: SurfaceName::from("gone"),
            },
            LoweringRefusal::Unreachable {
                span: s(45_usize, 46_usize),
            },
            LoweringRefusal::UnstatedComponent {
                span: s(47_usize, 48_usize),
                name: SurfaceName::from("assoc"),
                fault: crate::model::ModelFault::Circuit,
            },
            LoweringRefusal::FamilyTelescope {
                span: s(49_usize, 50_usize),
                name: SurfaceName::from("Hom"),
                fault: TelescopeFault::Arity {
                    stated: OperandCount::from(2_usize),
                    written: OperandCount::from(1_usize),
                },
            },
            LoweringRefusal::NotAFunctor {
                span: s(51_usize, 52_usize),
                name: SurfaceName::from("MkTally"),
            },
            LoweringRefusal::ProjectionFromApplication {
                span: s(53_usize, 54_usize),
                functor: SurfaceName::from("MkCounter"),
            },
            LoweringRefusal::OutsideLoop {
                span: s(55_usize, 56_usize),
                exit: LoopExit::Continue,
            },
            LoweringRefusal::AcrossHandler {
                span: s(59_usize, 60_usize),
                exit: CrossedExit::Become,
            },
            LoweringRefusal::RulesUnoriented {
                span: s(61_usize, 62_usize),
            },
            LoweringRefusal::RulesNonLinear {
                span: s(91_usize, 92_usize),
                copy: s(0_usize, 1_usize),
            },
            LoweringRefusal::RulesDiverge {
                span: s(63_usize, 64_usize),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::RulesUndecided {
                span: s(65_usize, 66_usize),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::Unminted {
                span: s(67_usize, 68_usize),
                name: SurfaceName::from("windHom"),
            },
            LoweringRefusal::ImportUnresolved {
                span: s(69_usize, 70_usize),
                refused: s(0_usize, 1_usize),
            },
            LoweringRefusal::ImportCycle {
                span: s(71_usize, 72_usize),
                refused: s(0_usize, 1_usize),
            },
            LoweringRefusal::ImportShadows {
                span: s(73_usize, 74_usize),
                name: SurfaceName::from("Circle"),
                import: s(0_usize, 1_usize),
                other: s(2_usize, 3_usize),
            },
            LoweringRefusal::UnexportedName {
                span: s(75_usize, 76_usize),
                name: SurfaceName::from("pending"),
                declared: s(0_usize, 1_usize),
                reason: Unexported::Undefined,
            },
            LoweringRefusal::RulesUncompleted {
                span: s(77_usize, 78_usize),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::BareFeedback {
                span: s(79_usize, 80_usize),
                rule: s(0_usize, 1_usize),
            },
            LoweringRefusal::ImplicitTelescope {
                span: s(81_usize, 82_usize),
            },
            LoweringRefusal::TelescopeCycle {
                span: s(83_usize, 84_usize),
                first: SurfaceName::from("a"),
                second: SurfaceName::from("b"),
            },
            LoweringRefusal::ImplicitUnsupplied {
                span: s(85_usize, 86_usize),
                function: SurfaceName::from("same"),
                implicit: SurfaceName::from("a"),
            },
            LoweringRefusal::ImplicitInParentheses {
                span: s(87_usize, 88_usize),
                function: SurfaceName::from("same"),
                implicit: SurfaceName::from("a"),
            },
            LoweringRefusal::RegionAsValue {
                span: s(89_usize, 90_usize),
                name: SurfaceName::from("r"),
            },
            LoweringRefusal::StrayReceiverMode {
                span: s(91_usize, 92_usize),
                mode: SurfaceName::from("shared"),
            },
            LoweringRefusal::AmbiguousMethod {
                span: s(93_usize, 94_usize),
                method: SurfaceName::from("len"),
                first: SurfaceName::from("Str"),
                second: SurfaceName::from("Bytes"),
                more: CandidateCount::from(0_usize),
            },
            LoweringRefusal::ViewNotPlace {
                span: s(95_usize, 96_usize),
            },
            LoweringRefusal::ViewOfNoPlace {
                span: s(97_usize, 98_usize),
            },
            LoweringRefusal::IllFormedDescription {
                span: s(99_usize, 100_usize),
                kind: crate::WfKind::NonRepresentableBinder,
                subjects: [
                    Maybe::Present(SurfaceName::from("Tm")),
                    Maybe::Absent(crate::description_subject::Absent::Unwritten),
                ],
            },
            LoweringRefusal::RulesNeverComplete {
                span: s(101_usize, 102_usize),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::RulesOverlapSecondOrder {
                span: s(103_usize, 104_usize),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::NonExhaustiveMatch {
                span: s(105_usize, 106_usize),
            },
            LoweringRefusal::DescentOnSeveralParameters {
                span: s(107_usize, 108_usize),
                staged: SurfaceName::from("n"),
                claimed: SurfaceName::from("m"),
            },
            LoweringRefusal::UndescribedMember {
                span: s(109_usize, 110_usize),
                fault: crate::description::MemberFault::Reversible,
            },
            LoweringRefusal::WithoutK {
                span: s(111_usize, 112_usize),
            },
            LoweringRefusal::DirectedCell {
                span: s(113_usize, 114_usize),
            },
            LoweringRefusal::CellNotALoop {
                span: s(115_usize, 116_usize),
            },
            LoweringRefusal::RulesOverlapCondition {
                span: s(117_usize, 118_usize),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::EntryType {
                span: s(119_usize, 120_usize),
            },
            LoweringRefusal::MismatchedPattern {
                span: s(121_usize, 122_usize),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::PartialField {
                span: s(123_usize, 124_usize),
                field: SurfaceName::from("start"),
                constructor: SurfaceName::from("Dot"),
            },
            LoweringRefusal::ModelImplicitValue {
                span: s(125_usize, 126_usize),
                implicit: SurfaceName::from("s"),
            },
            LoweringRefusal::GenericMisplaced {
                span: s(127_usize, 128_usize),
            },
            LoweringRefusal::GenericUncovered {
                span: s(129_usize, 130_usize),
                data: SurfaceName::from("Shape"),
                fault: gandr_core_term::generic::Uncovered::Field(
                    gandr_kernel_term::ConstantIndex::from(0_usize),
                    gandr_kernel_term::OccurrenceSite::Field {
                        tag: gandr_kernel_term::ConstructorTag::from(1_usize),
                        field: gandr_kernel_term::FieldPosition::from(0_usize),
                    },
                ),
            },
            LoweringRefusal::NoUniverseAbove {
                span: s(131_usize, 132_usize),
                level: SurfaceName::from("18446744073709551615"),
            },
            LoweringRefusal::HostConflict {
                span: s(133_usize, 134_usize),
            },
            LoweringRefusal::UnknownTactic {
                span: s(135_usize, 136_usize),
            },
        ]
    }

    #[test]
    fn every_refusal_names_the_span_it_rejected()
    {
        let s = |start: usize, end: usize| {
            Maybe::Present(span(ByteOffset::from(start), ByteOffset::from(end)))
        };
        let run = Maybe::Absent(refusal_span::Absent::Run);
        let expected = [
            s(1_usize, 2_usize),
            s(3_usize, 4_usize),
            s(5_usize, 6_usize),
            s(7_usize, 8_usize),
            s(9_usize, 10_usize),
            s(11_usize, 12_usize),
            s(23_usize, 23_usize),
            s(13_usize, 14_usize),
            s(15_usize, 16_usize),
            s(17_usize, 18_usize),
            s(19_usize, 20_usize),
            s(21_usize, 22_usize),
            run,
            run,
            s(24_usize, 25_usize),
            s(26_usize, 27_usize),
            s(28_usize, 29_usize),
            s(30_usize, 31_usize),
            s(32_usize, 33_usize),
            s(83_usize, 84_usize),
            s(90_usize, 94_usize),
            s(34_usize, 35_usize),
            s(36_usize, 37_usize),
            s(38_usize, 39_usize),
            s(41_usize, 42_usize),
            s(77_usize, 78_usize),
            s(43_usize, 44_usize),
            s(45_usize, 46_usize),
            s(47_usize, 48_usize),
            s(49_usize, 50_usize),
            s(51_usize, 52_usize),
            s(53_usize, 54_usize),
            s(55_usize, 56_usize),
            s(59_usize, 60_usize),
            s(61_usize, 62_usize),
            s(91_usize, 92_usize),
            s(63_usize, 64_usize),
            s(65_usize, 66_usize),
            s(67_usize, 68_usize),
            s(69_usize, 70_usize),
            s(71_usize, 72_usize),
            s(73_usize, 74_usize),
            s(75_usize, 76_usize),
            s(77_usize, 78_usize),
            s(79_usize, 80_usize),
            s(81_usize, 82_usize),
            s(83_usize, 84_usize),
            s(85_usize, 86_usize),
            s(87_usize, 88_usize),
            s(89_usize, 90_usize),
            s(91_usize, 92_usize),
            s(93_usize, 94_usize),
            s(95_usize, 96_usize),
            s(97_usize, 98_usize),
            s(99_usize, 100_usize),
            s(101_usize, 102_usize),
            s(103_usize, 104_usize),
            s(105_usize, 106_usize),
            s(107_usize, 108_usize),
            s(109_usize, 110_usize),
            s(111_usize, 112_usize),
            s(113_usize, 114_usize),
            s(115_usize, 116_usize),
            s(117_usize, 118_usize),
            s(119_usize, 120_usize),
            s(121_usize, 122_usize),
            s(123_usize, 124_usize),
            s(125_usize, 126_usize),
            s(127_usize, 128_usize),
            s(129_usize, 130_usize),
            s(131_usize, 132_usize),
            s(133_usize, 134_usize),
            s(135_usize, 136_usize),
        ];

        for (refusal, position) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                refusal.span(),
                position,
                "each refusal reports its own rejected span"
            );
        }
    }

    #[test]
    fn no_message_spells_a_byte_range()
    {
        use alloc::string::ToString as _;

        for refusal in every_variant() {
            let message = refusal.to_string();
            assert!(
                !message.contains(".."),
                "a diagnostic locates the refusal; its message repeats no byte range: {message}"
            );
        }
    }

    #[test]
    fn the_form_names_are_pairwise_distinct()
    {
        for (first, left) in FormName::ALL.into_iter().enumerate() {
            for (second, right) in FormName::ALL.into_iter().enumerate() {
                if first == second {
                    continue;
                }
                assert_ne!(
                    left, right,
                    "two forms sharing a name would render one diagnostic for two mistakes"
                );
            }
        }
    }

    /// Assert that each of `renderings`, the messages of every variant of
    /// one tag, is written and that no two are alike.
    ///
    /// # Specification
    /// trivial.
    fn assert_apart(renderings: &[alloc::string::String])
    {
        for (first, left) in renderings.iter().enumerate() {
            assert!(!left.is_empty(), "every variant writes its message");
            for right in renderings.iter().skip(first.saturating_add(1_usize)) {
                assert_ne!(
                    left, right,
                    "two variants rendering alike read as one mistake"
                );
            }
        }
    }

    #[test]
    fn each_ill_formed_description_reads_as_its_own_reason()
    {
        use alloc::string::String;
        use alloc::string::ToString as _;
        use alloc::vec::Vec;

        use crate::WfKind;

        let messages: Vec<String> = [
            WfKind::OutOfSignatureRule,
            WfKind::UnboundRhsVariable,
            WfKind::ArityDoesNotCompose,
            WfKind::DeclaresDerivedMetadata,
            WfKind::DerivedBoundaryMismatch,
            WfKind::CyclicCircuitWiring,
            WfKind::UnknownRewritePort,
            WfKind::CircuitDerivationBudget,
            WfKind::DuplicateSortName,
            WfKind::UnknownResultSort,
            WfKind::UnknownVarSort,
            WfKind::UnknownPortSort,
            WfKind::SortPolarityDisagreement,
            WfKind::MisplacedResults,
            WfKind::NonRepresentableBinder,
            WfKind::SplitCircuitOutputs,
            WfKind::DuplicateFaceName,
            WfKind::FaceOutsideShape,
            WfKind::UnsortedBinding,
            WfKind::AtomResult,
            WfKind::NonAtomAbstraction,
        ]
        .into_iter()
        .map(|kind| {
            LoweringRefusal::IllFormedDescription {
                span: span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
                kind,
                subjects: [
                    Maybe::Present(SurfaceName::from("first")),
                    Maybe::Present(SurfaceName::from("second")),
                ],
            }
            .to_string()
        })
        .collect();
        for (first, left) in messages.iter().enumerate() {
            for right in messages.iter().skip(first.saturating_add(1)) {
                assert_ne!(left, right, "no two reasons the check gives read alike");
            }
        }
    }

    /// Every variant of each tag a refusal names renders its own message.
    #[test]
    fn every_tag_renders_its_own_message()
    {
        use alloc::string::ToString as _;

        let render = |each: &[&dyn core::fmt::Display]| {
            each.iter()
                .map(alloc::string::ToString::to_string)
                .collect::<alloc::vec::Vec<_>>()
        };
        assert_apart(&render(&[
            &FragmentSort::Module,
            &FragmentSort::Declaration,
            &FragmentSort::ValueType,
            &FragmentSort::CompType,
            &FragmentSort::Value,
            &FragmentSort::Computation,
            &FragmentSort::Pattern,
            &FragmentSort::Continuation,
        ]));
        assert_apart(&render(&[
            &FormFault::Repaired(Repair::GhostClose(ClosingClass::Paren)),
            &FormFault::MissingOperand,
            &FormFault::ExtraOperand,
            &FormFault::MisplacedTile,
            &FormFault::ExtraClose(ClosingClass::Paren),
            &FormFault::ExtraClose(ClosingClass::Bracket),
            &FormFault::ExtraClose(ClosingClass::Brace),
            &FormFault::ExtraOpen(ClosingClass::Paren),
            &FormFault::ExtraOpen(ClosingClass::Bracket),
            &FormFault::ExtraOpen(ClosingClass::Brace),
            &FormFault::MissingOpen(ClosingClass::Paren),
            &FormFault::MissingOpen(ClosingClass::Bracket),
            &FormFault::MissingOpen(ClosingClass::Brace),
            &FormFault::Misspelt(crate::form::TileName::SEMICOLON),
        ]));
        assert_apart(&render(&[
            &FragmentBoundary::Reserved(Unbuilt::Dup),
            &FragmentBoundary::Unadmitted(Unbuilt::Dup),
            &FragmentBoundary::Misplaced,
            &FragmentBoundary::NotAtResult,
            &FragmentBoundary::WrongSort,
            &FragmentBoundary::Arity(OperandCount::from(2_usize)),
            &FragmentBoundary::Indexed,
            &FragmentBoundary::Unannotated,
            &FragmentBoundary::NonUniform,
            &FragmentBoundary::ForeignClaim,
            &FragmentBoundary::NotAFunction,
            &FragmentBoundary::NotInTail,
            &FragmentBoundary::JoinsBlock,
            &FragmentBoundary::EmptyList,
            &FragmentBoundary::Endpoint,
            &FragmentBoundary::NonContractive,
            &FragmentBoundary::Held,
            &FragmentBoundary::View,
        ]));
        let ill_formed = |kind: crate::WfKind, second: Maybe<SurfaceName<'static>, _>| {
            LoweringRefusal::IllFormedDescription {
                span: span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
                kind,
                subjects: [Maybe::Present(SurfaceName::from("a")), second],
            }
            .to_string()
        };
        let named = Maybe::Present(SurfaceName::from("b"));
        assert_apart(
            &[
                crate::WfKind::OutOfSignatureRule,
                crate::WfKind::UnboundRhsVariable,
                crate::WfKind::ArityDoesNotCompose,
                crate::WfKind::DeclaresDerivedMetadata,
                crate::WfKind::DerivedBoundaryMismatch,
                crate::WfKind::CyclicCircuitWiring,
                crate::WfKind::UnknownRewritePort,
                crate::WfKind::CircuitDerivationBudget,
                crate::WfKind::DuplicateSortName,
                crate::WfKind::UnknownResultSort,
                crate::WfKind::UnknownVarSort,
                crate::WfKind::UnknownPortSort,
                crate::WfKind::SortPolarityDisagreement,
                crate::WfKind::MisplacedResults,
                crate::WfKind::NonRepresentableBinder,
                crate::WfKind::SplitCircuitOutputs,
                crate::WfKind::DuplicateFaceName,
                crate::WfKind::FaceOutsideShape,
                crate::WfKind::UnsortedBinding,
                crate::WfKind::MisplacedAbstraction,
                crate::WfKind::AtomResult,
                crate::WfKind::NonAtomAbstraction,
                crate::WfKind::UnknownFreshness,
                crate::WfKind::Capture,
                crate::WfKind::MisplacedAtom,
                crate::WfKind::UndecidedCondition,
            ]
            .map(|kind| ill_formed(kind, named)),
        );
        let unspelled = ill_formed(
            crate::WfKind::OutOfSignatureRule,
            Maybe::Absent(crate::description_subject::Absent::Unnamed),
        );
        assert_apart(&[
            ill_formed(crate::WfKind::OutOfSignatureRule, named),
            unspelled.clone(),
        ]);
        assert!(
            unspelled.contains("`a`") && !unspelled.contains("`b`"),
            "a rule whose applied symbol is unspelled names only the rule: {unspelled}"
        );
        assert_apart(&render(&[
            &AscriptionForm::Kinded,
            &AscriptionForm::Parameterized,
        ]));
        assert_apart(&render(&[&LoopExit::Break, &LoopExit::Continue]));
        assert_apart(&render(&[
            &CrossedExit::Become,
            &CrossedExit::Break,
            &CrossedExit::Continue,
        ]));
        assert_apart(&render(&[
            &TelescopeFault::Arity {
                stated: OperandCount::from(1_usize),
                written: OperandCount::from(2_usize),
            },
            &TelescopeFault::Index(OperandCount::from(1_usize)),
        ]));
        let ambiguous = |more: usize| {
            LoweringRefusal::AmbiguousMethod {
                span: span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
                method: SurfaceName::from("len"),
                first: SurfaceName::from("Str"),
                second: SurfaceName::from("Bytes"),
                more: CandidateCount::from(more),
            }
            .to_string()
        };
        let (two, more) = (ambiguous(0_usize), ambiguous(2_usize));
        assert_apart(&[two.clone(), more.clone()]);
        assert!(
            more.contains('2') && !two.contains('0'),
            "the message counts the further modules only when there are some: {two} / {more}"
        );
        let site = gandr_kernel_term::OccurrenceSite::Field {
            tag: gandr_kernel_term::ConstructorTag::from(1_usize),
            field: gandr_kernel_term::FieldPosition::from(0_usize),
        };
        let at = gandr_kernel_term::ConstantIndex::from(0_usize);
        assert_apart(
            &[
                gandr_core_term::generic::Uncovered::Unknown(at),
                gandr_core_term::generic::Uncovered::Applied(at),
                gandr_core_term::generic::Uncovered::Presented(at),
                gandr_core_term::generic::Uncovered::Field(at, site),
                gandr_core_term::generic::Uncovered::Dependent(at, site),
                gandr_core_term::generic::Uncovered::Uncoded(at, site),
                gandr_core_term::generic::Uncovered::Cycle(at, site),
                gandr_core_term::generic::Uncovered::Nested(at, site),
                gandr_core_term::generic::Uncovered::BinderCeiling,
            ]
            .map(|fault| {
                LoweringRefusal::GenericUncovered {
                    span: span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
                    data: SurfaceName::from("Shape"),
                    fault,
                }
                .to_string()
            }),
        );
    }
}
