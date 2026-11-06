//! What a reader does about a refusal: the third part of the procedural form.
//!
//! # A refusal reads as a procedure
//!
//! A diagnostic states what is wrong in its message, where in its primary
//! label, and what to do in its help: one imperative sentence, the technical
//! vocabulary unrestricted. [`advice`] writes the help, one arm per refusal
//! name, from the refusal alone. A face shows it as the diagnostic's `help:`
//! line. A refusal tracked by an issue already ends with the issue that tracks
//! it.
//!
//! A refusal whose name has no help yet is [`help::Absent::Unworded`]: the
//! names are worded most-seen first, ten at a time, and the prose check's
//! ledger holds each unworded golden until its name is worded.
//!
//! The alternative was a help slot on each producer's refusal, which would put
//! a reader's advice beside the producer's own wording, where no face reads
//! it. Reversal: a producer whose refusal alone cannot word the help, because
//! the advice needs a fact the diagnostic does not hold, moves that name's
//! help to the producer.
//!
//! # References
//!
//! - `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — background: the
//!   directed-univalence design (§ The surface family) — `NotATranslation`'s
//!   help declares the flow its `via` names.
//! - `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — background: the univalence
//!   design (§ The trust story) — that help names who supplies a translation:
//!   the importer, declaring the flow, or the source, publishing it.
//! - `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: the compilation
//!   ruling (§ compilation-recipe-zero-cost) — a member a flow's codomain lacks
//!   is one declaration to write, as `SignatureMismatch.Missing`'s help says.

use alloc::format;
use alloc::string::String;

use gandr_core_checker::CheckRefusal;
use gandr_core_checker::EndpointMiss;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::access::AccessDefect;
use gandr_core_checker::codata::CodataFault;
use gandr_core_checker::session::ForkSide;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::session::ProtocolDefect;
use gandr_core_checker::ua::UaDefect;
use gandr_core_checker::worlds::Crossed;
use gandr_core_checker::worlds::LocatedDefect;
use gandr_core_checker::worlds::Predicate;
use gandr_core_term::compose::Form;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::host;
use gandr_surface_corpus::BoundaryClause;
use gandr_surface_corpus::CorpusRefusal;
use gandr_surface_corpus::Refusal;
use gandr_surface_lowering::Ending;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::FormName;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::MatchFault;
use gandr_surface_lowering::Offer;
use gandr_surface_lowering::Repair;
use gandr_surface_lowering::WfKind;
use gandr_surface_lowering::description::MemberFault;
use gandr_surface_lowering::head_home;
use gandr_surface_lowering::model::ModelFault;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GroutShape;
use quenchant_shape::shape::Maybe;

use crate::locus::Captor;
use crate::message::Spoken;

quenchant_shape::reason_enum! {
    /// Why a diagnostic tells its reader nothing to do.
    pub mod help {
        /// The reason a diagnostic has no help.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The diagnostic reports no refusal: a goal, an unsettled
            /// declaration or a ledger line.
            Statement,
            /// A warning: the edit it proposes, when it proposes one, is its
            /// help.
            Warning,
            /// The refusal is another declaration's: its help is on that
            /// declaration's diagnostic.
            Upstream,
            /// The refusal's name has no help worded yet.
            Unworded,
        }
    }
}

/// The help of `refusal`: what its reader does about it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one imperative sentence for each worded refusal name, naming the
///   source's own names where the refusal holds them; absent as unworded for
///   every other name.
/// - provides: the `help` of every refusal's diagnostic.
/// - fails: never.
/// - panics: none.
/// - executable: none — the sentence's mood is the prose check's to judge.
///
/// # Adequacy
/// - hypothesis: L3 — one refusal of every vocabulary name is either worded,
///   with a one-line help, or unworded; the most-seen names are worded.
/// - witness: `advice::tests::the_most_seen_names_are_worded_on_one_line`
#[inline]
pub fn advice(refusal: Refusal<'_>) -> Maybe<String, help::Absent>
{
    match refusal {
        Refusal::Lowering(refusal) => lowered(refusal),
        Refusal::Checking(refusal) => checked(refusal),
        Refusal::Corpus(CorpusRefusal::BoundaryUnrealised {
            clause: BoundaryClause::Size,
            ..
        }) => Maybe::Present(String::from(
            "make each member type have the size its boundary row states",
        )),
        Refusal::Corpus(CorpusRefusal::BoundaryUnrealised {
            clause: BoundaryClause::Align,
            ..
        }) => Maybe::Present(String::from(
            "make each member type align with its boundary row",
        )),
        Refusal::Corpus(CorpusRefusal::BoundaryUnrealised {
            clause: BoundaryClause::Arity,
            ..
        }) => Maybe::Present(String::from(
            "give each member the number of arguments its boundary row states",
        )),
        Refusal::Corpus(CorpusRefusal::BoundaryUnrealised {
            clause: BoundaryClause::Members,
            ..
        }) => Maybe::Present(String::from(
            "declare the number of members the boundary attribute names",
        )),
        Refusal::Corpus(CorpusRefusal::BoundaryUnrealised {
            clause: BoundaryClause::Niche,
            ..
        }) => Maybe::Present(String::from(
            "make each member type use the niche its boundary row states",
        )),
        Refusal::Corpus(_) => Maybe::Absent(help::Absent::Unworded),
    }
}

/// The help of a lowering refusal.
///
/// # Specification
/// trivial.
fn lowered(refusal: LoweringRefusal<'_>) -> Maybe<String, help::Absent>
{
    Maybe::Present(match refusal {
        LoweringRefusal::UnresolvedName { name, .. } => {
            format!("define `{name}`, or import the module that exports it")
        },
        LoweringRefusal::UnresolvedDocLink { name, .. } => {
            format!("declare `{name}`, or link to a name this source declares")
        },
        LoweringRefusal::DuplicateDefinition { name, .. } => {
            format!("give each definition of `{name}` its own name, or delete one of them")
        },
        LoweringRefusal::UnknownMember { module, member, .. } => {
            format!("use a member that `{module}` declares, or add `{member}` to `{module}`")
        },
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::ForeignClaim,
            ..
        } => String::from("put the descent claim on its recursive function or a mutual member"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Misplaced,
            ..
        } => String::from("write the form as a theory's sort member"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::NonContractive,
            ..
        } => String::from("put a send, receive or choice below `rec`"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::NotAFunction,
            ..
        } => String::from("pass a function to `Path.ap`"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::TopLevel,
            ..
        } => String::from("write the expression in a declaration"),
        LoweringRefusal::OutOfFragment {
            sort,
            boundary: FragmentBoundary::WrongSort,
            ..
        } => format!("write {sort} in this position"),
        LoweringRefusal::OutOfFragment {
            form: FormName::SEND,
            boundary: FragmentBoundary::Arity(_),
            ..
        } => String::from(
            "write the endpoint and the payload after `send`, side by side: `send c v`",
        ),
        LoweringRefusal::OutOfFragment {
            form: FormName::SELECT,
            boundary: FragmentBoundary::Arity(_),
            ..
        } => String::from(
            "write the endpoint and the label after `select`, side by side: `select c l`",
        ),
        LoweringRefusal::OutOfFragment {
            form: FormName::RESUME,
            boundary: FragmentBoundary::Arity(_),
            ..
        } => {
            String::from("write the view and the value after `resume`, side by side: `resume v e`")
        },
        LoweringRefusal::OutOfFragment {
            form: FormName::RECV_EXPRESSION,
            boundary: FragmentBoundary::Arity(_),
            ..
        } => String::from("write one endpoint after `recv`: `recv c`"),
        LoweringRefusal::OutOfFragment {
            form: FormName::CLOSE,
            boundary: FragmentBoundary::Arity(_),
            ..
        } => String::from("write one endpoint after `close`: `close c`"),
        LoweringRefusal::OutOfFragment {
            form: FormName::DROP,
            boundary: FragmentBoundary::Arity(_),
            ..
        } => String::from("write one endpoint after `drop`: `drop c`"),
        LoweringRefusal::OutOfFragment {
            form: FormName::OFFER,
            boundary: FragmentBoundary::Arity(_),
            ..
        } => String::from("write one endpoint after `offer`, then its arms: `offer c { … }`"),
        LoweringRefusal::OutOfFragment {
            form: FormName::ABORT,
            boundary: FragmentBoundary::Arity(_),
            ..
        } => String::from("write one view after `abort`: `abort v`"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Arity(_),
            ..
        } => String::from("give the form its declared number of operands"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Held,
            ..
        } => String::from("write a value held by a `var` statement"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unannotated,
            ..
        } => String::from("write a type annotation for the form"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::Unbound,
            ..
        } => String::from(
            "bind it to a name with `let`: `let x = recv c;` or `let d = fork (c : S) t;`",
        ),
        LoweringRefusal::MalformedForm { form, fault, .. } => malformed(Spoken(form), fault),
        LoweringRefusal::IllFormedDescription { kind, .. } => ill_formed(kind),
        LoweringRefusal::RulesUncompleted { .. } => String::from(
            "add a rule that joins the two normal forms, or remove one of the two rules",
        ),
        LoweringRefusal::NotATranslation { name, .. } => {
            format!(
                "declare `flow {name}` before this import, or import a source that publishes it"
            )
        },
        LoweringRefusal::ImportCycle { .. } => {
            String::from("remove the import that closes the cycle")
        },
        LoweringRefusal::SignatureMismatch {
            signature,
            member,
            fault,
            ..
        } => match fault {
            MatchFault::Missing => format!(
                "drop `{member}` from `{signature}`, or declare `pub {member}` where the import reads it"
            ),
            MatchFault::Sort => {
                format!("give `{member}` one type in `{signature}` and where the import reads it")
            },
            MatchFault::Unstated => format!(
                "give the source's `{member}` a signature, or state only operations in `{signature}`"
            ),
        },
        LoweringRefusal::UnlabelledRequirement { name, .. } => {
            format!("write a label before it, `l : {name} with …`, and perform through `l`")
        },
        LoweringRefusal::UnfixedParameter {
            constructor,
            parameter,
            ..
        } => format!(
            "write the type after the binder, `let x : … = {constructor}(…)`, to fix `{parameter}`"
        ),
        LoweringRefusal::DerivedComponent { member, theory, .. } => format!(
            "delete `{member}`: the model reads it as `{theory}.{member}`, which the derivation fills"
        ),
        // A head a `std` module homes names its listing, and a host interface
        // the import of its module; any other head is declared or imported.
        LoweringRefusal::UnresolvedTypeHead { name, .. } => match head_home(name) {
            Maybe::Present(home) => {
                format!("write `import {home} ({name});`, the listing of `{name}` from its home")
            },
            Maybe::Absent(_) => match host::home(&EffectName::from(name.as_ref())) {
                Maybe::Present(home) => {
                    format!("write `import {home};`, the import of `{name}`'s module")
                },
                Maybe::Absent(_) => {
                    format!("declare a type named `{name}`, or import the module that exports it")
                },
            },
        },
        LoweringRefusal::IllTypedPayload { name, expected, .. } => {
            format!("give `{name}` {expected}")
        },
        LoweringRefusal::NonValuePayload { .. } => {
            String::from("give the attribute a value payload")
        },
        LoweringRefusal::NonExhaustiveMatch { .. } => String::from(
            "add an arm for the values that no arm matches, or a last arm that matches any value",
        ),
        LoweringRefusal::UninterfacedMember { .. } => {
            String::from("give the theory an unfixed carrier sort and operations that return it")
        },
        LoweringRefusal::ViewNotPlace { .. } => {
            String::from("return a place of `self` with type `View[m](a)`")
        },
        LoweringRefusal::RulesUnoriented { .. } => {
            String::from("make the rule's right side smaller than its left in the path order")
        },
        LoweringRefusal::RulesNonLinear { .. } => {
            String::from("use each variable once on the rule's left side")
        },
        LoweringRefusal::RulesOverlapCondition { .. } => {
            String::from("add a rule that joins the overlap under its condition")
        },
        LoweringRefusal::AcrossHandler { .. } => {
            String::from("leave the handled subject with `return`")
        },
        LoweringRefusal::GenericMisplaced { .. } => {
            String::from("write `Eq.generic(T)` as a definition's whole body")
        },
        LoweringRefusal::InertRead { .. } => {
            String::from("read an inert field only from a manifest step or inert field")
        },
        LoweringRefusal::PhaseDependence { .. } => {
            String::from("make the static member's type depend only on static members")
        },
        LoweringRefusal::RulesOverlapSecondOrder { .. } => {
            String::from("add a rule for the second-order overlap")
        },
        LoweringRefusal::UndescribedMember {
            fault: MemberFault::LhsNotOperation,
            ..
        } => String::from("write an operation application on the rule's left side"),
        LoweringRefusal::UndescribedMember {
            fault: MemberFault::IllSorted,
            ..
        } => String::from("state a law at an earlier sort that makes the two sorts one"),
        LoweringRefusal::UnguardedCorecursion { .. } => {
            String::from("write the productive self-call as a copattern arm's whole body")
        },
        LoweringRefusal::ModelImplicitValue { .. } => {
            String::from("select a component from the model implicit")
        },
        LoweringRefusal::StrayReceiverMode { .. } => {
            String::from("write the receiver mode only on a module member's first `self` parameter")
        },
        LoweringRefusal::RulesDiverge { .. } => String::from(
            "change the overlapping rules so that they rewrite to the same constructor term",
        ),
        LoweringRefusal::RulesNeverComplete { .. } => String::from(
            "add a rule that joins the normal forms without wrapping the earlier completion",
        ),
        LoweringRefusal::BareFeedback { .. } => {
            String::from("observe the port's sort before feeding it back")
        },
        LoweringRefusal::AmbiguousMethod { .. } => {
            String::from("call the intended method through its module")
        },
        LoweringRefusal::DescentOnSeveralParameters { .. } => {
            String::from("mark descent on one parameter in each recursive call")
        },
        LoweringRefusal::CellNotALoop { .. } => {
            String::from("write the same term on both sides of the `<->`")
        },
        LoweringRefusal::ForwardMemberReference { .. } => {
            String::from("declare the referenced member before this member")
        },
        LoweringRefusal::FamilyTelescope { .. } => {
            String::from("write a member kind that matches its parameters and result")
        },
        LoweringRefusal::ImplicitUnsupplied { .. }
        | LoweringRefusal::ImplicitInParentheses { .. } => {
            String::from("supply the implicit by name in square brackets")
        },
        LoweringRefusal::DirectedCell { .. } => {
            String::from("write an undirected `<->` cell instead of `-->`")
        },
        LoweringRefusal::GenericUncovered { .. } => {
            String::from("write an equality function for the datatype")
        },
        LoweringRefusal::ImportShadows { .. } => {
            String::from("rename the declaration or its imported binding")
        },
        LoweringRefusal::ImportUnresolved { .. } => {
            String::from("change the import path to a source under the root")
        },
        LoweringRefusal::MissingPayload { .. } => {
            String::from("give the attribute the payload its schema requires")
        },
        LoweringRefusal::InstanceUnanswered { .. } => {
            String::from("handle the interface or supply its instance by name")
        },
        LoweringRefusal::InstanceAmbiguous { .. } => {
            String::from("supply the intended instance by name")
        },
        LoweringRefusal::MismatchedPattern { .. } => {
            String::from("match constructors of the same datatype in every arm")
        },
        LoweringRefusal::ShadowedBuiltin { .. } => {
            String::from("rename the declaration that shadows the builtin")
        },
        LoweringRefusal::ProjectionFromApplication { .. } => {
            String::from("bind the application to a module before selecting its member")
        },
        LoweringRefusal::TelescopeCycle { .. } => {
            String::from("order parameters so each type names only earlier parameters")
        },
        LoweringRefusal::RegionAsValue { .. } => {
            String::from("name the region only in a type such as `A at r`")
        },
        LoweringRefusal::UnknownAttribute { .. } => {
            String::from("replace the attribute with a registered attribute")
        },
        LoweringRefusal::UnstatedComponent {
            fault: ModelFault::Unbound,
            ..
        } => String::from("remove the component the model signature cannot state"),
        LoweringRefusal::UnstatedComponent {
            fault: ModelFault::Arity,
            ..
        } => String::from("give each sort and operation its declared number of arguments"),
        LoweringRefusal::UnstatedComponent {
            fault: ModelFault::IllSorted,
            ..
        } => String::from("write each term at the sort its position reads"),
        LoweringRefusal::UnstatedComponent {
            fault: ModelFault::UnknownHead,
            ..
        } => String::from("declare each sort and operation the component uses"),
        LoweringRefusal::UnstatedComponent {
            fault: ModelFault::Unsorted,
            ..
        } => String::from("use each variable where its sort is known"),
        LoweringRefusal::UnderivedRule { .. } => {
            String::from("write a rule the theory's completed rules derive")
        },
        LoweringRefusal::UnknownTactic { .. } => {
            String::from("replace the tactic with a supported tactic")
        },
        LoweringRefusal::ViewOfNoPlace { .. } => {
            String::from("call a method that returns a place before the view block")
        },
        LoweringRefusal::WithoutK { .. } => {
            String::from("use the path through `Path.walk`, `Path.back`, `Path.step` or `Path.ap`")
        },
        LoweringRefusal::DuplicateSignature { .. } => {
            String::from("write one type signature for the name")
        },
        LoweringRefusal::DuplicateImportAlias { .. } => String::from("rename one import alias"),
        LoweringRefusal::DuplicateAttribute { .. } => String::from("write the attribute only once"),
        LoweringRefusal::EntryType { .. } => String::from("give `main` an allowed entry signature"),
        LoweringRefusal::MalformedLiteral { form, .. } => {
            format!("write a well-formed {}", Spoken(form))
        },
        LoweringRefusal::NoUniverseAbove { .. } => String::from("use a smaller universe level"),
        LoweringRefusal::NotAFunctor { name, .. } => {
            format!("declare `{name}` as a functor before this binding")
        },
        LoweringRefusal::NotAModel { name, .. } => {
            format!("declare `{name}` as a model before opening it")
        },
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::EmptyList,
            ..
        } => String::from("write `unit` for the unit value"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::JoinsBlock,
            ..
        } => String::from("remove the match result annotation"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::NonUniform,
            ..
        } => String::from("pass the recursive call's parameters unchanged"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::NotAtResult,
            ..
        } => String::from("write the row only before a definition's result type"),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::NotInTail,
            ..
        } => String::from(
            "write the return expression in a function, lambda, thunk or copattern clause",
        ),
        LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::View,
            ..
        } => String::from("open a view with `access` before resuming or aborting it"),
        LoweringRefusal::OutsideLoop { .. } => {
            String::from("write `break` or `continue` in its loop body")
        },
        LoweringRefusal::PartialField { .. } => {
            String::from("select a field each constructor declares")
        },
        LoweringRefusal::UndescribedMember {
            fault: MemberFault::ResultArity,
            ..
        } => String::from("give the rule its operation's number of outputs"),
        LoweringRefusal::UnexportedName { name, .. } => {
            format!("export `{name}` from its source")
        },
        LoweringRefusal::UnlockedDependency { alias, .. } => {
            format!("run `gandr lock` before importing `{alias}`")
        },
        LoweringRefusal::UnmarkedSelfReference { name, .. } => {
            format!("mark `{name}` with a descent claim")
        },
        LoweringRefusal::Unreachable { .. } => {
            String::from("remove code after every path leaves the body")
        },
        // Unworded: a later slice words each, most-seen first.
        LoweringRefusal::OutOfFragment { .. }
        | LoweringRefusal::GradedBridge { .. }
        | LoweringRefusal::UnreadAscription { .. }
        | LoweringRefusal::UnreadCells { .. }
        | LoweringRefusal::UnstatedComponent { .. }
        | LoweringRefusal::UndescribedMember { .. }
        | LoweringRefusal::ImplicitTelescope { .. }
        | LoweringRefusal::RulesUndecided { .. }
        | LoweringRefusal::BudgetExceeded { .. }
        | LoweringRefusal::GrammarMismatch { .. }
        | LoweringRefusal::UnknownMold { .. }
        | LoweringRefusal::HostConflict { .. }
        | LoweringRefusal::Unminted { .. } => return Maybe::Absent(help::Absent::Unworded),
    })
}

/// The help of a malformed form, by its fault.
///
/// # Specification
/// trivial.
fn malformed(
    form: Spoken,
    fault: FormFault,
) -> String
{
    let opening = |close: ClosingClass| match close {
        ClosingClass::Paren => "(",
        ClosingClass::Bracket => "[",
        ClosingClass::Brace => "{",
    };
    let closing = |close: ClosingClass| match close {
        ClosingClass::Paren => ")",
        ClosingClass::Bracket => "]",
        ClosingClass::Brace => "}",
    };
    match fault {
        FormFault::Repaired(Repair::Grout(GroutShape::Convex)) => {
            String::from("write the missing term")
        },
        FormFault::Repaired(Repair::Grout(GroutShape::Prefix | GroutShape::Postfix))
        | FormFault::MissingOperand => String::from("write the missing operand"),
        FormFault::Repaired(Repair::Grout(GroutShape::Infix)) => {
            String::from("write an operator between the two terms")
        },
        FormFault::Repaired(Repair::Keyword(stray)) => match stray.offer {
            Offer::Capitalised(offer) => format!("write `{}` instead", offer.as_ref()),
            Offer::Unspelled => {
                format!("write a term in place of `{}`", stray.written.as_ref())
            },
        },
        FormFault::Repaired(Repair::GhostClose(close)) => {
            format!("add the closing `{}`", closing(close))
        },
        FormFault::Repaired(Repair::Unended(Ending::Tile(tile))) => {
            format!("add the closing `{}`", tile.as_ref())
        },
        FormFault::Repaired(Repair::Unended(Ending::Unnamed)) => format!("finish the {form}"),
        FormFault::Repaired(Repair::Diverged(Ending::Tile(tile))) => {
            format!("write `{}` here", tile.as_ref())
        },
        FormFault::Repaired(Repair::Diverged(Ending::Unnamed)) | FormFault::ExtraOperand => {
            String::from("remove the extra operand")
        },
        FormFault::MisplacedTile => {
            format!("move the keyword or symbol to its place in the {form}")
        },
        FormFault::ExtraClose(close) => format!("remove the extra `{}`", closing(close)),
        FormFault::ExtraOpen(close) => {
            format!("remove the extra `{}`, or close it", opening(close))
        },
        FormFault::Misspelt(keyword) => {
            format!(
                "write the keyword `{}` in place of this word",
                keyword.as_ref()
            )
        },
        FormFault::MisspeltOperator(operator) => {
            format!(
                "write the operator `{}` in place of this run",
                operator.as_ref()
            )
        },
        FormFault::Retired(keyword) => {
            format!(
                "write `{}` in place of the retired keyword",
                keyword.as_ref()
            )
        },
        FormFault::NotAName => String::from("write a name before the `@`"),
        FormFault::BareIndex => String::from("write the index as the selector `.#[ … ]`"),
        FormFault::PositionalAfterNamed => {
            String::from("write the positional entries before the named ones")
        },
        FormFault::PositionalPastBlock => {
            String::from("remove the entry, or match it to an implicit of the block")
        },
        FormFault::CompoundPositional => {
            String::from("supply the value by name, as `.n = …` with the implicit's name for `n`")
        },
        FormFault::SuppliedTwice => String::from("remove one of the two entries"),
        FormFault::PositionalCarrier(head) => {
            format!(
                "supply the carrier by name, as `{}[.A = …](…, …)`, or leave it to the endpoints",
                head.as_ref()
            )
        },
        FormFault::MissingOpen(close) => {
            format!(
                "add the `{}` that this `{}` closes",
                opening(close),
                closing(close)
            )
        },
    }
}

/// The help of an ill-formed description, by its kind.
///
/// # Specification
/// trivial.
fn ill_formed(kind: WfKind) -> String
{
    String::from(match kind {
        WfKind::OutOfSignatureRule => {
            "declare the operation in the signature, or write the rule over operations it declares"
        },
        WfKind::UnboundRhsVariable => {
            "bind the variable on the rule's left-hand side, or remove it from the right-hand side"
        },
        WfKind::ArityDoesNotCompose => "make each map of the bridge arity compose with the next",
        WfKind::DeclaresDerivedMetadata => "remove the declaration, which the rules derive",
        WfKind::DerivedBoundaryMismatch => {
            "make the declared sphere fix the boundary that the wiring derives"
        },
        WfKind::CyclicCircuitWiring => "wire the rule so that no port reaches itself",
        WfKind::UnknownRewritePort => {
            "declare the rewrite in the rule's telescope, or apply a rewrite that it declares"
        },
        WfKind::CircuitDerivationBudget => "split the rule's wiring into smaller rules",
        WfKind::DuplicateSortName => "give each sort its own name",
        WfKind::UnknownResultSort => {
            "declare the sort, or target a sort that the signature declares"
        },
        WfKind::UnknownVarSort => {
            "declare the sort, or recurse at a sort that the signature declares"
        },
        WfKind::UnknownPortSort => {
            "declare the sort in the signature, or put a builtin type at the port"
        },
        WfKind::SortPolarityDisagreement => "give the sort the polarity of its declaration",
        WfKind::MisplacedResults => {
            "move the results tuple to the root of the rule's right-hand side"
        },
        WfKind::NonRepresentableBinder => "bind the variable over a declared, representable sort",
        WfKind::SplitCircuitOutputs => "read all the outputs of the many-out node together",
        WfKind::DuplicateFaceName => "give each face of the boundary its own name",
        WfKind::FaceOutsideShape => "put in the face only names that the boundary lists",
        WfKind::UnsortedBinding => {
            "use the variable where a port binds it over the same sorts, with one argument for \
             each variable it binds"
        },
        WfKind::MisplacedAbstraction => {
            "abstract names only in an argument at a port that binds as many"
        },
        WfKind::AtomResult => "return a sort that is not an atom sort",
        WfKind::NonAtomAbstraction => {
            "abstract over an atom sort, or bind the variable with `(x : S) ->` instead"
        },
        WfKind::UnknownFreshness => {
            "name in the condition an atom that the rule abstracts and a variable that its left \
             side binds"
        },
        WfKind::Capture => "state the atom fresh for the variable with `where { | a # q }`",
        WfKind::MisplacedAtom => {
            "name the atom only inside `bind a . t`, at a port of the sort that it abstracts"
        },
        WfKind::UndecidedCondition => {
            "put the variable under the same abstractions at each of its occurrences"
        },
    })
}

/// The help of a checker refusal.
///
/// # Specification
/// trivial.
fn checked(refusal: CheckRefusal) -> Maybe<String, help::Absent>
{
    Maybe::Present(match refusal {
        CheckRefusal::TypeMismatch(_) => String::from(
            "change the term or the type it is checked against, so that the two types agree",
        ),
        CheckRefusal::CapabilityAmplified(_) => String::from("use the required capability"),
        CheckRefusal::EndpointMismatch {
            miss: EndpointMiss::Unshown,
            ..
        } => String::from(
            "give `Path.here` a point that both endpoints convert to, or change the endpoints",
        ),
        CheckRefusal::EndpointMismatch {
            miss: EndpointMiss::Budget,
            ..
        } => String::from(
            "state the equation through lemmas that each unfold less, or split the computation \
             into steps the conversion settles one at a time",
        ),
        CheckRefusal::StageNotBelow { .. } => String::from(
            "recurse on a field of the parameter, which a match takes apart, and not on the \
             parameter itself",
        ),
        CheckRefusal::OutOfFragment {
            former: UnadmittedFormer::Stage,
            ..
        } => String::from("write the kernel-visible type without a stage"),
        CheckRefusal::Access {
            defect: AccessDefect::Escaped { by },
            ..
        } => format!(
            "use the view outside {}, or open the `access` inside it",
            Captor(by)
        ),
        CheckRefusal::Access {
            defect: AccessDefect::Lent,
            ..
        } => String::from("use the held value only after the `access` that lends it ends"),
        CheckRefusal::Access {
            defect: AccessDefect::HeldCopied,
            ..
        } => String::from("wrap the `var[1]` read in `access ... resume`"),
        CheckRefusal::Access {
            defect: AccessDefect::HeldShared,
            ..
        } => String::from("assign an in-place value to the `var[1]` hold"),
        CheckRefusal::Access {
            defect: AccessDefect::KeptEscaped,
            ..
        } => String::from("return a value that the scope's own region does not keep"),
        CheckRefusal::Linearity {
            defect: LinearityDefect::AsValue { .. },
            ..
        } => String::from("use the endpoint only in a session action"),
        CheckRefusal::Linearity {
            defect: LinearityDefect::Residue { endpoint, .. },
            ..
        } => String::from(match endpoint.side {
            ForkSide::Placed => {
                "end the endpoint's protocol before the body of the function that takes it ends"
            },
            ForkSide::Child | ForkSide::Parent | ForkSide::Received => {
                "close the endpoint before the fork half or receive body that bound it ends"
            },
        }),
        CheckRefusal::Linearity {
            defect: LinearityDefect::ArmsDisagree { .. },
            ..
        } => String::from("leave each arm with the same endpoint states"),
        CheckRefusal::RuleNotRespected { .. } => String::from(
            "give the arms equal results on the terms that each of the datatype's rules \
             identifies",
        ),
        CheckRefusal::LoopNotRespected { .. } => {
            String::from("make the case respect each loop of its sort")
        },
        CheckRefusal::NotApart { .. } => {
            String::from("write an arm for the path, because its endpoints can be equal")
        },
        CheckRefusal::CompoundEndpoint { .. } => {
            String::from("return a value without effects from the path endpoint")
        },
        CheckRefusal::NegativeOccurrence(_) => String::from(
            "apply the datatype there only to its own parameters, one stage below its \
             constructor",
        ),
        CheckRefusal::NestedOccurrence(_) => String::from(
            "place the datatype only where each enclosing type holds it strictly positively",
        ),
        CheckRefusal::PointwiseDistinct { .. } => {
            String::from("make both functions return the same value at every input")
        },
        CheckRefusal::UaInequivalent {
            defect: UaDefect::Cardinality { .. },
            ..
        } => String::from("give both descriptions the same number of generators at each corolla"),
        CheckRefusal::UaInequivalent {
            defect: UaDefect::Tables { .. },
            ..
        } => String::from("give each corolla exactly one translator on each side"),
        CheckRefusal::UaInequivalent {
            defect: UaDefect::NotNatural { .. },
            ..
        } => String::from("make each `ua` translator commute with every corolla symmetry"),
        CheckRefusal::RunNotAdmitted { .. } => String::from(
            "change the run so that each move is one that the protocol admits at that point",
        ),
        CheckRefusal::UndecidedCoverage(_) => {
            String::from("replace the pattern hole with a pattern")
        },
        CheckRefusal::AbsentRecordField(_) => String::from("select a declared record field"),
        CheckRefusal::ImplicitUnsolved { .. } => {
            String::from("supply the implicit by name in brackets before the parentheses")
        },
        CheckRefusal::Located {
            defect:
                LocatedDefect::Immobile {
                    crossed: Crossed::Result | Crossed::Constant,
                    predicate: Predicate::Mobile,
                    ..
                },
            ..
        } => String::from(
            "return data or a handle from the migration, or mark the abstract type `mobile` in \
             its signature",
        ),
        CheckRefusal::Located {
            defect:
                LocatedDefect::Immobile {
                    crossed: Crossed::Result | Crossed::Constant,
                    predicate: Predicate::Open,
                    ..
                },
            ..
        } => String::from(
            "hold data in the handle, or an abstract type that its signature marks `mobile`",
        ),
        CheckRefusal::Located {
            defect:
                LocatedDefect::Immobile {
                    crossed: Crossed::Capture,
                    ..
                },
            ..
        } => String::from(
            "capture only data in a thunk the migration returns, or mark the abstract type \
             `mobile` in its signature",
        ),
        CheckRefusal::Located {
            defect:
                LocatedDefect::Immobile {
                    crossed: Crossed::Homed,
                    ..
                },
            ..
        } => String::from(
            "call the declaration before the migration returns, and return what it answers",
        ),
        CheckRefusal::Located {
            defect: LocatedDefect::Elsewhere { .. },
            ..
        } => String::from("open the value at its binder with `let x at w`"),
        CheckRefusal::Located {
            defect: LocatedDefect::OpenedElsewhere { .. },
            ..
        } => String::from("write the handle's own world after `at`"),
        CheckRefusal::Located {
            defect: LocatedDefect::NotAHandle { .. },
            ..
        } => String::from("give `let x at w` a value that has a handle type"),
        CheckRefusal::BridgeAtSealedType { .. } => String::from(
            "give the abstract type an `identity` attribute that names its relation, or relate \
             points of a type that is not sealed",
        ),
        CheckRefusal::ComposeNotAShape { pasting, .. } => String::from(match pasting.form() {
            Form::Chain(_) => {
                "write a stratum of degree at least 2m - 1 and bound at least 2m + 1 for a chain \
                 of m cells"
            },
            Form::Columns(_) => {
                "write a stratum whose bound holds the level-two shape and whose degree reaches \
                 its degree"
            },
            Form::Tree { level, .. } if usize::from(level) <= 4 => {
                "write a stratum whose bound holds the pasting and whose degree reaches its degree"
            },
            Form::Tree { .. } => "write the pasting at level four or below",
        }),
        CheckRefusal::ComposeDoesNotFill {
            seam: gandr_core_term::compose::Seam::Outer,
            ..
        } => String::from("start each cell at the point where the cell before it ends"),
        CheckRefusal::ComposeDoesNotFill {
            seam: gandr_core_term::compose::Seam::Column(_),
            defect: gandr_theory_sites::Unfilled::Profile { .. },
            ..
        } => String::from(
            "write a 2-cell at this place, or give its column the height 0 to hold one 1-cell",
        ),
        CheckRefusal::ComposeDoesNotFill {
            seam: gandr_core_term::compose::Seam::Column(_),
            ..
        } => String::from(
            "start each 2-cell of a column at the 1-cell where the 2-cell before it ends",
        ),
        CheckRefusal::NoFiller { .. } => String::from(
            "ask for the square the generator makes, with its sides composites of the cells and \
             at least one cell a path of paths",
        ),
        CheckRefusal::UndischargedLaw { .. } => String::from(
            "prove the law by a definition at its type, or admit it where the host asserts it",
        ),
        CheckRefusal::UnassertedLaw { .. } => String::from("prove the law"),
        CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::EmptySum,
            ..
        } => String::from("delete the injection, because the empty sum has no summand to name"),
        CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::Summand,
            ..
        } => String::from("name a summand that the sum declares"),
        CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::Positional,
            ..
        } => String::from("split the record by label, as `*{.label = name, …}`"),
        CheckRefusal::ShapeMismatch { .. } => String::from(
            "change the term or the type it is checked against, so that the type has the required \
             shape",
        ),
        CheckRefusal::Linearity {
            defect: LinearityDefect::Closed { .. },
            ..
        } => String::from("move the action before the `close`, or delete it"),
        CheckRefusal::Linearity {
            defect: LinearityDefect::BufferUnreturned { .. },
            ..
        } => String::from(
            "hand the buffer back with a `send`, an operation or a resumption before the body ends",
        ),
        CheckRefusal::Linearity {
            defect: LinearityDefect::Captured { by, .. },
            ..
        } => format!("use the endpoint outside {}", Captor(by)),
        CheckRefusal::Linearity {
            defect: LinearityDefect::BufferReturnedTwice { .. },
            ..
        } => String::from("return the buffer only once"),
        CheckRefusal::Access {
            defect: AccessDefect::HeldCaptured { by },
            ..
        } => format!(
            "use the held value outside {}, or declare its `var` inside it",
            Captor(by)
        ),
        CheckRefusal::Access {
            defect: AccessDefect::Kept,
            ..
        } => String::from("write the value only after the scope that keeps its shared view ends"),
        CheckRefusal::Access {
            defect: AccessDefect::Consumed,
            ..
        } => String::from("use the held value before the consumed method call"),
        CheckRefusal::Access {
            defect: AccessDefect::Unindexed,
            ..
        } => String::from("access a list before indexing it"),
        CheckRefusal::HandlerUnlawful { .. } => {
            String::from("change the handler's clauses so that they satisfy the law")
        },
        CheckRefusal::ModelUnanswered { .. } => String::from(
            "declare a module that is a model of the theory at these types, or supply one by name \
             in brackets",
        ),
        CheckRefusal::RuleNotPresentable { .. } => String::from(
            "write each rule with a declared constructor at its head and its declared field count",
        ),
        CheckRefusal::NotSynthesisable { .. } => {
            String::from("write a type ascription for this form")
        },
        CheckRefusal::ModelAmbiguous { .. } => {
            String::from("supply the intended model by name in brackets before the parentheses")
        },
        CheckRefusal::NonCovariantMotive { .. } => {
            String::from("use the moving endpoint only where a run of it is produced")
        },
        CheckRefusal::Codata {
            fault: CodataFault::KindNotUniverse,
            ..
        } => String::from("give the codata declaration a computation universe as its kind"),
        CheckRefusal::Codata {
            fault: CodataFault::Occurrence,
            ..
        } => String::from(
            "write the codata type only as an observation's result, with its parameters in order",
        ),
        CheckRefusal::Located {
            defect: LocatedDefect::CapabilityMissing { .. },
            ..
        } => String::from("migrate with the target world's capability"),
        CheckRefusal::TacticRefused { .. } => String::from("replace the tactic with a proof term"),
        CheckRefusal::CapabilityEscaped { .. } => {
            String::from("keep the capability inside its scope")
        },
        CheckRefusal::UnenclosedRun { .. } => {
            String::from("write the run in a function's body, where the body can run its effects")
        },
        CheckRefusal::StagesDisagree { .. } => {
            String::from("change the call's arguments so that they stand at one stage")
        },
        CheckRefusal::SessionMismatch {
            defect: ProtocolDefect::Action { .. },
            ..
        } => String::from("change the endpoint action or protocol so that they agree"),
        CheckRefusal::SessionMismatch {
            defect: ProtocolDefect::Arms,
            ..
        } => String::from("handle every label of the endpoint's protocol exactly once"),
        CheckRefusal::Access {
            defect: AccessDefect::Spent,
            ..
        } => String::from("use the view before its `resume` or `abort`"),
        CheckRefusal::Access {
            defect: AccessDefect::ReadOnly,
            ..
        } => String::from("end the shared view with its body, without `resume` or `abort`"),
        CheckRefusal::Access {
            defect: AccessDefect::UnwindEffect,
            ..
        } => String::from("remove the effect from the `unwind`"),
        CheckRefusal::SessionNotEquivalent { .. } => {
            String::from("make the two protocols bisimilar at every step")
        },
        CheckRefusal::RoundTripDistinct { .. } => {
            String::from("make each `equiv` round trip return its input")
        },
        CheckRefusal::SessionNotSubtype { .. } => String::from(
            "make the source protocol select no more and offer no less than the target",
        ),
        CheckRefusal::OpenSessionPayload { .. } => {
            String::from("bind the session payload inside the run's protocol")
        },
        CheckRefusal::Access {
            defect: AccessDefect::Unended,
            ..
        } => String::from("end the access body with `resume` or `abort`"),
        CheckRefusal::AtomTransport { .. } => {
            String::from("add a transport law to the abstract type's identity attribute")
        },
        CheckRefusal::Linearity {
            defect: LinearityDefect::BufferRead { .. },
            ..
        } => String::from("return the buffer with `send`, the operation or `resume`"),
        CheckRefusal::Located {
            defect: LocatedDefect::CapabilityCaptured { .. },
            ..
        } => String::from("move the `migrate` outside the thunk that captures its capability"),
        CheckRefusal::CapabilityForged { .. } => {
            String::from("pass a capability that a hold binds or the host grants")
        },
        CheckRefusal::CapabilityConsumable(_) => {
            String::from("remove the capability's `[1]` grade")
        },
        CheckRefusal::Boundary { .. } => {
            String::from("write the boundary flow in the direction its position's variance permits")
        },
        CheckRefusal::Linearity {
            defect: LinearityDefect::ContinuationAsValue { .. },
            ..
        } => String::from("use the continuation only with `resume` or `abandon`"),
        CheckRefusal::Linearity {
            defect: LinearityDefect::ContinuationCaptured { .. },
            ..
        } => String::from("move the continuation outside the construct that captures it"),
        CheckRefusal::Linearity {
            defect: LinearityDefect::ContinuationUnspent { .. },
            ..
        } => String::from("end the continuation once with `resume` or `abandon`"),
        CheckRefusal::Linearity {
            defect: LinearityDefect::ContinuationUsedTwice { .. },
            ..
        } => String::from("end the continuation only once"),
        CheckRefusal::DataFieldLevel { .. } => {
            String::from("lower each constructor field to its datatype's universe")
        },
        CheckRefusal::DataKindNotUniverse(_) => {
            String::from("give the data declaration a universe kind")
        },
        CheckRefusal::DependentBind { .. } => {
            String::from("bind a computation whose result type ignores its value")
        },
        CheckRefusal::DialogueInverted { .. } => {
            String::from("log each send before its matching receipt")
        },
        CheckRefusal::Linearity {
            defect: LinearityDefect::UsedTwice { .. },
            ..
        } => String::from("use the endpoint only once in this action"),
        CheckRefusal::Located {
            defect: LocatedDefect::EntryNamed { .. },
            ..
        } => String::from("call a non-entry declaration instead"),
        CheckRefusal::Located {
            defect: LocatedDefect::HoldElsewhere { .. },
            ..
        } => String::from("migrate to the handle's world before using `hold`"),
        CheckRefusal::DialogueUnmatched { .. } => {
            String::from("make each dialogue receipt match its sent value")
        },
        CheckRefusal::MissingRecordField { .. } => String::from("add the record's missing field"),
        CheckRefusal::PatchOutsideBase { .. } => {
            String::from("fix only the fields that the base record holds")
        },
        CheckRefusal::LevelMismatch { .. } => {
            String::from("lower the code to the expected universe")
        },
        CheckRefusal::IndexOccurrence(_) => {
            String::from("remove the datatype from the field's index")
        },
        CheckRefusal::Located {
            defect: LocatedDefect::MarkUnfounded { .. },
            ..
        } => String::from("remove `mobile` or use a representation that crosses"),
        CheckRefusal::Undecided { .. } => {
            String::from("write code whose unfolding the checker can decide")
        },
        CheckRefusal::Located {
            defect: LocatedDefect::UndeclaredWorld { .. },
            ..
        } => String::from("declare the named world with `world w ;`"),
        CheckRefusal::Linearity {
            defect: LinearityDefect::Unrestricted,
            ..
        } => String::from("open the endpoint with `fork` or `recv`"),
        CheckRefusal::SessionMismatch {
            defect: ProtocolDefect::Label,
            ..
        } => String::from("select a label the endpoint's protocol offers"),
        CheckRefusal::Located {
            defect: LocatedDefect::Unlocated,
            ..
        } => String::from("give the declaration a world with `@[ entry(w) ]`"),
        CheckRefusal::Access {
            defect: AccessDefect::Moved,
            ..
        } => String::from("end the view with `resume` after reading its value"),
        CheckRefusal::AbsentTupleComponent(_) => {
            String::from("select a component that the tuple has")
        },
        CheckRefusal::AbstractKindNotUniverse(_) => {
            String::from("give the abstract type a universe as its kind")
        },
        CheckRefusal::CapabilityOutsideAuthority { .. } => {
            String::from("use an operation the capability grants")
        },
        CheckRefusal::Codata {
            fault: CodataFault::ObservationLevel,
            ..
        } => String::from("lower each observation type to the codata declaration's universe"),
        CheckRefusal::FamilyArgumentClassifier { .. } => {
            String::from("give each type operator argument its parameter's kind")
        },
        CheckRefusal::CrossBlockReference { .. } => {
            String::from("declare the referenced datatype before this datatype")
        },
        CheckRefusal::Codata {
            fault: CodataFault::Undeclared,
            ..
        } => String::from("declare the codata type before naming it"),
        CheckRefusal::Codata {
            fault: CodataFault::WithoutObservations,
            ..
        } => String::from("declare at least one codata observation"),
        CheckRefusal::FamilyArity { .. } => {
            String::from("give the type operator its declared number of arguments")
        },
        CheckRefusal::FootprintsOverlap { .. } => {
            String::from("give each fork half separate authority")
        },
        CheckRefusal::HandlerCoverage { .. } => {
            String::from("handle each interface operation exactly once")
        },
        CheckRefusal::LiteralAmbiguous { .. } => {
            String::from("apply the intended literal model reader by name")
        },
        CheckRefusal::LoopUndecided { .. } => {
            String::from("simplify the loop obligation until the checker decides it")
        },
        CheckRefusal::NonUniformOccurrence(_) => {
            String::from("apply the datatype only to its own parameters")
        },
        CheckRefusal::NotADataType(_) => String::from("use a declared datatype"),
        CheckRefusal::NotAnAbstractType(_) => {
            String::from("admit the abstract type before using it")
        },
        CheckRefusal::NotOver { .. } => {
            String::from("start `Path.walk` with an identity over the path")
        },
        CheckRefusal::Access {
            defect: AccessDefect::NotAView,
            ..
        } => String::from("open the value with `access` before resuming it"),
        CheckRefusal::Access {
            defect: AccessDefect::NotHeld,
            ..
        } => String::from("open a value with `var` before accessing it"),
        CheckRefusal::UaInequivalent {
            defect: UaDefect::NotInverse { .. },
            ..
        } => String::from("make the `ua` translators inverse"),
        CheckRefusal::RepresentationAboveKind { .. } => {
            String::from("seal a representation within its abstract type's universe")
        },
        CheckRefusal::PathCode(_) => {
            String::from("use a quoted closed first-order code at each end")
        },
        CheckRefusal::SessionCodeExpected { .. } => {
            String::from("give the session identity two session types")
        },
        CheckRefusal::SortMismatch { .. } => String::from("use a code of the expected sort"),
        CheckRefusal::StageNotCarried { .. } => {
            String::from("transport the recursive value only along a set")
        },
        CheckRefusal::UaInequivalent {
            defect: UaDefect::PastTheBound { .. },
            ..
        } => String::from("use a corolla within the `ua` catalogue bound"),
        CheckRefusal::StaticClassifierExpected { .. } => {
            String::from("give each type parameter a universe or kind")
        },
        CheckRefusal::StaticLambdaArgument { .. } => {
            String::from("pass a value instead of a type operator")
        },
        CheckRefusal::UnknownConstant { .. } => String::from("use a declaration with a known type"),
        CheckRefusal::UaInequivalent {
            defect: UaDefect::Stuck { .. },
            ..
        } => String::from("make each `ua` translator return a target element"),
        CheckRefusal::UaInequivalent {
            defect: UaDefect::UnknownGenerator { .. },
            ..
        } => String::from("name only generators of the `ua` description"),
        CheckRefusal::BuiltinRepeated { .. } => {
            String::from("remove the `builtin` mark from one of the two declarations")
        },
        CheckRefusal::BuiltinMisplaced(_) => String::from(
            "mark a datatype with `irSignature` or `irPair`, and a definition with `irArgs` or \
             `irDecode`",
        ),
        CheckRefusal::BuiltinNotCanonical { .. } => {
            String::from("write the holder in the canonical form of its role")
        },
        // Unworded: a later slice words each, most-seen first.
        CheckRefusal::SealSiteRepeated(_)
        | CheckRefusal::DataArgumentArity(_)
        | CheckRefusal::UnknownConstructor { .. }
        | CheckRefusal::ConstructorArity(_)
        | CheckRefusal::NonExhaustiveDataCase(_)
        | CheckRefusal::UnknownOperation { .. }
        | CheckRefusal::ShiftWithoutReset { .. }
        | CheckRefusal::DependentStack { .. }
        | CheckRefusal::FunextUnsupported { .. }
        | CheckRefusal::EquivUnsupported { .. }
        | CheckRefusal::UncertifiedStratum { .. }
        | CheckRefusal::OutsideFold { .. }
        | CheckRefusal::UaUncertified { .. }
        | CheckRefusal::ComposeUncertified { .. }
        | CheckRefusal::FillUncertified { .. }
        | CheckRefusal::GeneratorFamilyUnsupported { .. }
        | CheckRefusal::EffectSignatureConflict { .. }
        | CheckRefusal::OutOfFragment { .. }
        | CheckRefusal::UnboundIndex { .. }
        | CheckRefusal::BudgetExceeded { .. }
        | CheckRefusal::DanglingNode { .. }
        | CheckRefusal::AdmissionOrder { .. }
        | CheckRefusal::MachineInvariant
        | CheckRefusal::Linearity { .. }
        | CheckRefusal::Codata { .. }
        | CheckRefusal::Located { .. }
        | CheckRefusal::CapabilityUngranted { .. }
        | CheckRefusal::RideUnsupported { .. }
        | CheckRefusal::ForwardUnsupported { .. } => return Maybe::Absent(help::Absent::Unworded),
    })
}

/// The refusal names the procedural rewrite has worded, each on one line.
#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::advice;
    use super::help;
    use crate::message::tests::one_of_every_name;

    /// The names the procedural rewrite has worded: the most-seen first,
    /// then the names worded as their goldens regenerated.
    const WORDED: [&str; 235] = [
        "TypeMismatch",
        "MalformedForm",
        "EndpointMismatch",
        "IllFormedDescription",
        "StageNotBelow",
        "UnresolvedName",
        "OutOfFragment.WrongSort",
        "ViewEscaped",
        "UnknownMember",
        "DuplicateDefinition",
        "HeldLent",
        "ImplicitUnsolved",
        "NegativeOccurrence",
        "NotApart",
        "RuleNotRespected",
        "RunNotAdmitted",
        "UndecidedCoverage",
        "KeptEscaped",
        "LinearResidue",
        "RulesUncompleted",
        "Immobile",
        "NotOpen",
        "Immobile.Capture",
        "Immobile.Homed",
        "NotOpen.Capture",
        "NotOpen.Homed",
        "NotATranslation",
        "SignatureMismatch.Sort",
        "BridgeAtSealedType",
        "UnlabelledRequirement",
        "UnfixedParameter",
        "ComposeNotAShape",
        "ComposeDoesNotFill",
        "NoFiller",
        "NoFiller.Omitted",
        "DerivedComponent",
        "UnenclosedRun",
        "UnresolvedTypeHead",
        "UsedAfterClose",
        "ModelUnanswered",
        "NonExhaustiveMatch",
        "ShapeMismatch",
        "BufferUnreturned",
        "HandlerUnlawful",
        "HeldCaptured",
        "HeldKept",
        "IllTypedPayload",
        "ModelAmbiguous",
        "NonCovariantMotive",
        "NotSynthesisable",
        "OutOfFragment.Arity",
        "RuleNotPresentable",
        "RulesNonLinear",
        "RulesOverlapCondition",
        "RulesUnoriented",
        "UninterfacedMember",
        "ViewNotPlace",
        "AbsentRecordField",
        "AcrossHandler",
        "ArmsDisagree",
        "CapabilityAmplified",
        "GenericMisplaced",
        "HeldCopied",
        "InertRead",
        "OutOfFragment.Stage",
        "PhaseDependence",
        "RulesOverlapSecondOrder",
        "TacticRefused",
        "UndescribedMember.LhsNotOperation",
        "UndescribedMember.IllSorted",
        "UnguardedCorecursion",
        "UnprovenLaw.Admitted",
        "BufferReturnedTwice",
        "CapabilityEscaped",
        "CapabilityMissing",
        "CapturedEndpoint",
        "CodataKindNotUniverse",
        "CodataOccurrence",
        "CompoundEndpoint",
        "Elsewhere",
        "EndpointAsValue",
        "HeldConsumed",
        "HeldShared",
        "ImportCycle",
        "LoopNotRespected",
        "ModelImplicitValue",
        "OutOfFragment.Held",
        "OutOfFragment.Unannotated",
        "RulesDiverge",
        "RulesNeverComplete",
        "SessionMismatch",
        "SessionNotEquivalent",
        "StagesDisagree",
        "StrayReceiverMode",
        "UnwindEffect",
        "ViewReadOnly",
        "ViewSpent",
        "AmbiguousMethod",
        "AtomTransport",
        "BareFeedback",
        "Boundary",
        "BoundaryUnrealised.Size",
        "BufferRead",
        "CapabilityCaptured",
        "CapabilityConsumable",
        "CapabilityForged",
        "ViewUnended",
        "CellNotALoop",
        "ContinuationAsValue",
        "ContinuationCaptured",
        "ContinuationUnspent",
        "ContinuationUsedTwice",
        "DataFieldLevel",
        "DataKindNotUniverse",
        "DependentBind",
        "DescentOnSeveralParameters",
        "DialogueInverted",
        "DialogueUnmatched",
        "DirectedCell",
        "EndpointUsedTwice",
        "EntryNamed",
        "FamilyTelescope",
        "ForwardMemberReference",
        "GenericUncovered",
        "HoldElsewhere",
        "ImplicitInParentheses",
        "ImplicitUnsupplied",
        "ImportShadows",
        "ImportUnresolved",
        "IndexOccurrence",
        "InstanceAmbiguous",
        "InstanceUnanswered",
        "LevelMismatch",
        "MarkUnfounded",
        "MismatchedPattern",
        "MissingPayload",
        "MissingRecordField",
        "NestedOccurrence",
        "NonValuePayload",
        "NotAHandle",
        "NotNatural",
        "OfferArms",
        "OpenSessionPayload",
        "OpenedElsewhere",
        "OutOfFragment.ForeignClaim",
        "OutOfFragment.Misplaced",
        "OutOfFragment.NonContractive",
        "OutOfFragment.NotAFunction",
        "OutOfFragment.TopLevel",
        "PlaceUnindexed",
        "PointwiseDistinct",
        "ProjectionFromApplication",
        "RegionAsValue",
        "RoundTripDistinct",
        "SessionNotSubtype",
        "ShadowedBuiltin",
        "TelescopeCycle",
        "Undecided",
        "UndeclaredWorld",
        "UnderivedRule",
        "UnknownAttribute",
        "UnknownTactic",
        "Unlocated",
        "UnofferedLabel",
        "UnrestrictedEndpoint",
        "UnresolvedDocLink",
        "UnstatedComponent.Arity",
        "UnstatedComponent.IllSorted",
        "UnstatedComponent.UnknownHead",
        "UnstatedComponent.Unsorted",
        "UnstatedComponent.Unbound",
        "ViewMoved",
        "ViewOfNoPlace",
        "WithoutK",
        "AbsentTupleComponent",
        "AbstractKindNotUniverse",
        "BoundaryUnrealised.Align",
        "BoundaryUnrealised.Arity",
        "BoundaryUnrealised.Members",
        "BoundaryUnrealised.Niche",
        "CapabilityOutsideAuthority",
        "CodataObservationLevel",
        "CodataUndeclared",
        "CodataWithoutObservations",
        "CorollaCardinality",
        "CorollaTables",
        "CrossBlockReference",
        "DuplicateAttribute",
        "DuplicateImportAlias",
        "DuplicateSignature",
        "EntryType",
        "FamilyArgumentClassifier",
        "FamilyArity",
        "FootprintsOverlap",
        "HandlerCoverage",
        "LiteralAmbiguous",
        "LoopUndecided",
        "MalformedLiteral",
        "NoUniverseAbove",
        "NonUniformOccurrence",
        "NotADataType",
        "NotAFunctor",
        "NotAModel",
        "NotAView",
        "NotAnAbstractType",
        "NotHeld",
        "NotInverse",
        "NotOver",
        "OutOfFragment.EmptyList",
        "OutOfFragment.JoinsBlock",
        "OutOfFragment.NonUniform",
        "OutOfFragment.NotAtResult",
        "OutOfFragment.NotInTail",
        "OutOfFragment.View",
        "OutsideLoop",
        "PartialField",
        "PastTheBound",
        "PathCode",
        "RepresentationAboveKind",
        "SessionCodeExpected",
        "SortMismatch",
        "StageNotCarried",
        "StaticClassifierExpected",
        "StaticLambdaArgument",
        "TranslatorStuck",
        "UndescribedMember.ResultArity",
        "UnexportedName",
        "UnknownConstant",
        "UnknownGenerator",
        "UnlockedDependency",
        "UnmarkedSelfReference",
        "Unreachable",
        "BuiltinRepeated",
        "BuiltinMisplaced",
        "BuiltinNotCanonical",
    ];

    /// Every worded name has a one-line help that opens with a lowercase verb.
    /// Every other name is unworded.
    #[test]
    fn the_most_seen_names_are_worded_on_one_line()
    {
        let mut seen: alloc::vec::Vec<alloc::string::String> = alloc::vec::Vec::new();
        for refusal in one_of_every_name() {
            let name = alloc::format!("{}", refusal.name());
            match advice(refusal) {
                Maybe::Present(help) => {
                    assert!(WORDED.contains(&name.as_str()), "{name} is worded: {help}");
                    assert!(!help.contains('\n'), "{name}'s help is one line: {help}");
                    assert!(
                        help.starts_with(|first: char| first.is_ascii_lowercase()),
                        "{name}'s help opens with its verb: {help}"
                    );
                    seen.push(name);
                },
                Maybe::Absent(reason) => {
                    assert_eq!(reason, help::Absent::Unworded, "{name}");
                    assert!(!WORDED.contains(&name.as_str()), "{name} has no help");
                },
            }
        }
        for name in WORDED {
            assert!(
                seen.iter().any(|held| held == name),
                "{name} is reached by a refusal of the vocabulary"
            );
        }
    }
}
