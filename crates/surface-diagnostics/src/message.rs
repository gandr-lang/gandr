//! The message a report leads with: what went wrong, in the words of the
//! language a user writes.
//!
//! # The message is the user's; the title is the producer's
//!
//! Every producer words its refusals for whoever reads its own code: the
//! lowering names the grammar's sorts (`` `thunk_expression` has an operand
//! where it takes none ``), the checker names its rules and positions. A
//! diagnostic keeps that text as its detail's
//! [`title`](crate::DiagnosticDetail::title) and leads with its
//! [`Message`](crate::Message) instead: one per refusal variant, chosen by an
//! exhaustive match, naming forms in the words the source is written in, and
//! naming no grammar sort, admission position or node. A refusal no source can
//! reach — a run fault or a producer's broken invariant — says so, as an
//! internal error.
//!
//! Each producer words its refusals for whoever reads its code: the lowering
//! names the grammar's sorts (`` `hole` has an operand where it takes none ``),
//! the checker its rules (`the rule here requires a thunk type`). A report
//! keeps that text as `DiagnosticDetail::title` and leads with its `Message`
//! instead: one plain message per refusal variant, chosen by an exhaustive
//! match in `message.rs`, naming the source's own names and its forms in words
//! (`this hole has an operand it does not take`, `expected a thunk type`, ``
//! `missing` is not defined ``), and naming no grammar sort, node or admission
//! position. A refusal only a producer's broken invariant reaches says
//! `internal error:`. Every other report's message is its title, which is
//! already the user's. The terminal and the language server both lead with the
//! message; the title stays for a face that wants the producer's words, the
//! verbosity levels in particular.
//!
//! The alternative was rewording each producer's `Display`, which would leave
//! the implementer text nowhere: the lowering's and the checker's own tests,
//! ledger lines and a detailed verbosity read it. Reversal: when no face reads
//! the producer's text, the two collapse into one. Witness:
//! `message::tests::every_refusal_name_has_a_plain_message`, which builds one
//! refusal of every vocabulary name and holds each message to one line with no
//! grammar sort.

use core::fmt;

use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::access::AccessDefect;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::session::ProtocolDefect;
use gandr_core_checker::ua::StratumDefect;
use gandr_core_checker::ua::UaDefect;
use gandr_surface_corpus::CorpusRefusal;
use gandr_surface_corpus::Refusal;
use gandr_surface_lowering::Ending;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::FormName;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Offer;
use gandr_surface_lowering::Repair;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GroutShape;
use quenchant_shape::shape::Maybe;

use crate::locus::Action;
use crate::locus::Captor;
use crate::locus::Former;
use crate::locus::Shape;
use crate::locus::Site;
use crate::locus::Stood;

/// A refusal's plain message.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Plain<'step>(pub Refusal<'step>);

impl fmt::Display for Plain<'_>
{
    /// Writes the refusal's plain message.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one message per refusal variant, naming the source's
    ///   own names and forms and no grammar sort or node; propagates a write
    ///   failure.
    /// - provides: the message of every refusal report.
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer or
    ///   independent observation of the destination's failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one refusal of every vocabulary name writes a
    ///   nonempty, single-line message with no underscore-joined grammar sort.
    /// - witness: `message::tests::every_refusal_name_has_a_plain_message`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            Refusal::Lowering(refusal) => lowered(refusal, f),
            Refusal::Checking(refusal) => checked(refusal, f),
            Refusal::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { schema, .. }) => {
                write!(
                    f,
                    "`{schema}` is an expectation only a fixture may state; outside the fixture \
                     root a declaration states `checks` or `runs`"
                )
            },
        }
    }
}

/// A form's name in the words a user reads: the grammar's kind with its
/// underscores spaced.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Spoken(FormName);

impl fmt::Display for Spoken
{
    /// Writes the form's kind with each underscore a space.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for word in self.0.as_ref().split('_').enumerate() {
            if word.0 > 0_usize {
                f.write_str(" ")?;
            }
            f.write_str(word.1)?;
        }
        Ok(())
    }
}

/// A form's name with the indefinite article its spoken name takes: `an`
/// before a vowel sound, `a` otherwise.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Indefinite(FormName);

impl fmt::Display for Indefinite
{
    /// Writes `an ` before a name whose first letter is a vowel spoken as
    /// one, `a ` before any other, then the name as [`Spoken`] writes it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the article is `an` exactly when the name opens with a vowel
    ///   letter and not with `uni` or `use`, which open on a `y` sound (`a
    ///   unit`, `an unpack statement`).
    /// - fails: if the formatter rejects a write.
    /// - panics: none.
    /// - executable: none — the formatter exposes no output buffer.
    ///
    /// # Errors
    /// The formatter's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the wrong-sort refusal writes `an identifier`, `an
    ///   instantiation expression`, `a unit` and `a hole`.
    /// - witness: `message::tests::a_form_takes_the_article_its_name_is_spoken_with`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let name = self.0.as_ref();
        let vowel = name.starts_with(['a', 'e', 'i', 'o', 'u'])
            && !name.starts_with("uni")
            && !name.starts_with("use");
        let article = if vowel { "an" } else { "a" };
        write!(f, "{article} {}", Spoken(self.0))
    }
}

/// Writes the plain message of a lowering refusal.
///
/// # Specification
/// - requires: nothing.
/// - ensures: writes one message per variant, the form a malformed or
///   unadmitted form names spoken in words; propagates a write failure.
/// - provides: the lowering half of [`Plain`].
/// - fails: if the formatter rejects a write.
/// - panics: none.
/// - executable: none — the formatter exposes no output buffer.
///
/// # Errors
/// The formatter's.
///
/// # Adequacy
/// - hypothesis: L3 — one refusal of every lowering name writes a nonempty,
///   single-line message with no grammar sort.
/// - witness: `message::tests::every_refusal_name_has_a_plain_message`
fn lowered(
    refusal: LoweringRefusal<'_>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result
{
    match refusal {
        LoweringRefusal::UnresolvedName { name, .. } => write!(f, "`{name}` is not defined"),
        LoweringRefusal::UnresolvedDocLink { name, .. } => {
            write!(
                f,
                "the documentation links to `{name}`, which is not defined"
            )
        },
        LoweringRefusal::UnresolvedTypeHead { name, arity, .. } => {
            write!(f, "no type named `{name}` is written {arity}")
        },
        LoweringRefusal::DuplicateSignature { name, .. } => {
            write!(f, "`{name}` is given a type twice")
        },
        LoweringRefusal::DuplicateDefinition { name, .. } => {
            write!(f, "`{name}` is defined twice")
        },
        LoweringRefusal::DuplicateImportAlias { alias, .. } => {
            write!(f, "two imports are both named `{alias}`")
        },
        LoweringRefusal::ImportUnresolved { .. } => f.write_str(
            "this import names no source the root holds, so this source's declarations are not read",
        ),
        LoweringRefusal::ImportCycle { .. } => f.write_str(
            "this import leads back to this source, so its declarations are not read",
        ),
        LoweringRefusal::ImportShadows { name, .. } => {
            write!(f, "`{name}` is bound by an import and again in this source")
        },
        LoweringRefusal::UnexportedName { name, .. } => {
            write!(
                f,
                "`{name}` is declared in the imported source without a definition, so it is not exported"
            )
        },
        LoweringRefusal::ShadowedBuiltin { name, .. } => {
            write!(
                f,
                "`{name}` is a builtin name, which this source may not rebind"
            )
        },
        LoweringRefusal::OutOfFragment {
            form,
            sort,
            boundary,
            ..
        } => {
            let spoken = Spoken(form);
            let indefinite = Indefinite(form);
            match boundary {
                FragmentBoundary::Reserved => {
                    write!(f, "the {spoken} is reserved, and not available yet")
                },
                FragmentBoundary::Unadmitted => write!(f, "the {spoken} is not supported yet"),
                FragmentBoundary::WrongSort => {
                    write!(f, "{indefinite} cannot stand where {sort} is expected")
                },
                FragmentBoundary::Arity(operands) => {
                    write!(f, "the {spoken} cannot take {operands} operands")
                },
                FragmentBoundary::Indexed => {
                    f.write_str("indexed datatype families are not supported yet")
                },
                FragmentBoundary::Unannotated => write!(f, "the {spoken} needs a type annotation"),
                FragmentBoundary::NotAFunction => f.write_str(
                    "`cong` maps a path by a function, and a constructor is not one; write a \
                     function definition that applies it",
                ),
                FragmentBoundary::NonUniform => f.write_str(
                    "a recursive call must pass the earlier parameters unchanged; only the last \
                     one descends",
                ),
                FragmentBoundary::NotInTail => write!(
                    f,
                    "{indefinite} leaves only the body of a function, a lambda, a thunk or a \
                     copattern clause, and cannot stand here"
                ),
                FragmentBoundary::JoinsBlock => f.write_str(
                    "an arm of this match exits, so its other arms continue the block and answer \
                     what the block answers; remove the written answer",
                ),
                FragmentBoundary::EmptyList => f.write_str(
                    "`()` is an empty list, never the unit; write the unit value as `unit` and \
                     its type as `Unit`",
                ),
                FragmentBoundary::Endpoint => f.write_str(
                    "a session action acts on an endpoint: a name a `fork` binds as one of its \
                     ends",
                ),
                FragmentBoundary::NonContractive => f.write_str(
                    "this recursive session type recurses before any action; put a send, a \
                     receive or a choice under its `mu`",
                ),
                FragmentBoundary::Held => {
                    f.write_str("an `access` lends a held value: a name a `hold` statement holds")
                },
                FragmentBoundary::View => f.write_str(
                    "`resume` and `abort` end a view: the name an `access` binds after `as`",
                ),
            }
        },
        LoweringRefusal::GradedBridge { grade, .. } => write!(
            f,
            "the grade `{grade}` is not supported; only the default grade `ω` is"
        ),
        LoweringRefusal::MalformedLiteral { form, .. } => {
            write!(f, "this is not a well-formed {}", Spoken(form))
        },
        LoweringRefusal::MalformedForm { form, fault, .. } => {
            let form = Spoken(form);
            match fault {
                FormFault::Repaired(Repair::Grout(GroutShape::Convex)) => {
                    write!(f, "a term is missing in this {form}")
                },
                FormFault::Repaired(Repair::Grout(GroutShape::Prefix | GroutShape::Postfix))
                | FormFault::MissingOperand => write!(f, "an operand is missing in this {form}"),
                FormFault::Repaired(Repair::Grout(GroutShape::Infix)) => {
                    write!(f, "an operator is missing in this {form}")
                },
                FormFault::Repaired(Repair::Keyword(stray)) => match stray.offer {
                    Offer::Capitalised(offer) => write!(
                        f,
                        "`{}` is a keyword and cannot stand here in this {form}; did you mean \
                         `{}`?",
                        stray.written.as_ref(),
                        offer.as_ref()
                    ),
                    Offer::Unspelled => write!(
                        f,
                        "`{}` is a keyword and cannot stand here in this {form}",
                        stray.written.as_ref()
                    ),
                },
                FormFault::Repaired(Repair::GhostClose(close)) => {
                    write!(f, "this {form} is missing its closing `{}`", match close {
                        ClosingClass::Paren => ")",
                        ClosingClass::Bracket => "]",
                        ClosingClass::Brace => "}",
                    })
                },
                FormFault::Repaired(Repair::Unended(Ending::Tile(tile))) => {
                    write!(f, "this {form} is missing its closing `{}`", tile.as_ref())
                },
                FormFault::Repaired(Repair::Unended(Ending::Unnamed)) => {
                    write!(f, "this {form} stops before it is finished")
                },
                FormFault::ExtraOperand => {
                    write!(f, "this {form} has an operand it does not take")
                },
                FormFault::MisplacedTile => {
                    write!(f, "a keyword or symbol of this {form} is out of place")
                },
            }
        },
        LoweringRefusal::UnknownAttribute {
            name, suggestion, ..
        } => match suggestion {
            Maybe::Present(nearest) => {
                write!(
                    f,
                    "there is no attribute `{name}`; did you mean `{nearest}`?"
                )
            },
            Maybe::Absent(_) => write!(f, "there is no attribute `{name}`"),
        },
        LoweringRefusal::DuplicateAttribute { name, .. } => {
            write!(f, "the attribute `{name}` is written twice")
        },
        LoweringRefusal::MissingPayload { name, expected, .. } => {
            write!(f, "the attribute `{name}` needs {expected}")
        },
        LoweringRefusal::NonValuePayload { name, .. } => {
            write!(f, "the argument of the attribute `{name}` must be a value")
        },
        LoweringRefusal::IllTypedPayload {
            name,
            expected,
            written,
            ..
        } => write!(f, "the attribute `{name}` takes {expected}, not {written}"),
        LoweringRefusal::ForwardMemberReference { name, .. } => {
            write!(f, "the member `{name}` is used before it is declared")
        },
        LoweringRefusal::UnknownMember { module, member, .. } => {
            write!(f, "the module `{module}` has no member `{member}`")
        },
        LoweringRefusal::NotAFunctor { name, .. } => {
            write!(f, "`{name}` is not a functor declared before this binding")
        },
        LoweringRefusal::ProjectionFromApplication { functor, .. } => write!(
            f,
            "an application of `{functor}` is read before it is bound; bind it with `module A = \
             {functor}(…) ;` and read `A`"
        ),
        LoweringRefusal::UnreadAscription { name, form, .. } => {
            write!(f, "`{name}` {form}, which is not supported yet")
        },
        LoweringRefusal::UnstatedComponent { name, fault, .. } => {
            write!(
                f,
                "the model signature cannot state `{name}`, which {fault}"
            )
        },
        LoweringRefusal::FamilyTelescope { name, fault, .. } => {
            write!(f, "the type family `{name}` {fault}")
        },
        LoweringRefusal::LowercaseModuleName { name, .. } => write!(
            f,
            "the module `{name}` must start with an uppercase letter at the top level"
        ),
        LoweringRefusal::NonExhaustiveMatch { .. } => {
            f.write_str("this match does not cover every value it can be given")
        },
        LoweringRefusal::UnmarkedSelfReference { name, .. } => write!(
            f,
            "`{name}` calls itself without saying how it recurses; write `{name}[<](…)`"
        ),
        LoweringRefusal::Unreachable { .. } => {
            f.write_str("this code never runs: every path before it leaves the body")
        },
        LoweringRefusal::OutsideLoop { exit, .. } => write!(
            f,
            "{exit} leaves a loop, and no loop runs here; a function, a lambda or a thunk \
             inside a loop has a body of its own"
        ),
        LoweringRefusal::AcrossHandler { exit, .. } => write!(
            f,
            "{exit} would leave a handler's subject while its handler is still running; \
             `return` leaves past the handler, or end the subject with its result"
        ),
        LoweringRefusal::ForNeedsListCase { .. } => f.write_str(
            "`for` loops are not supported yet: a list has no case to step through it with; \
             loop over it by recursion instead",
        ),
        LoweringRefusal::WithoutK { .. } => f.write_str(
            "a path cannot be matched against `here`; use it by transport, through `back`, \
             `then` or `cong`",
        ),
        LoweringRefusal::DirectedCell { .. } => f.write_str(
            "a cell between two terms is written `<->`; a directed cell `-->` between terms is \
             not supported yet",
        ),
        LoweringRefusal::CellNotALoop { .. } => f.write_str(
            "a cell `<->` is a loop: write the same term on both sides; a cell between two \
             distinct terms is not supported yet",
        ),
        LoweringRefusal::RulesUnoriented { .. } => f.write_str(
            "this rule may rewrite forever: its right side is not smaller than its left in the \
             order the block's calls induce, so the block's rules are refused",
        ),
        LoweringRefusal::RulesDiverge { .. } => f.write_str(
            "this rule and an earlier one rewrite one term to two different normal forms, so \
             the block's rules are refused",
        ),
        LoweringRefusal::RulesUndecided { .. } => f.write_str(
            "whether this rule and an earlier one agree was not decided within the step \
             budget, so the block's rules are refused",
        ),
        LoweringRefusal::BudgetExceeded { budget } => write!(
            f,
            "the source is too large to read within the allowance of {budget} steps"
        ),
        LoweringRefusal::GrammarMismatch { .. } => f.write_str(
            "internal error: the source was parsed under a different grammar than it was read \
             with",
        ),
        LoweringRefusal::UnknownMold { .. } => {
            f.write_str("internal error: the parser produced a form its grammar does not hold")
        },
        LoweringRefusal::Unminted { name, .. } => write!(
            f,
            "internal error: the reader produced neither a type nor a body for `{name}`, and \
             reported nothing wrong with it"
        ),
    }
}

/// Writes the plain message of a checker refusal.
///
/// # Specification
/// - requires: nothing.
/// - ensures: writes one message per variant, naming no node and no admission
///   position; a refusal only a producer fault reaches is an internal error;
///   propagates a write failure.
/// - provides: the checker half of [`Plain`].
/// - fails: if the formatter rejects a write.
/// - panics: none.
/// - executable: none — the formatter exposes no output buffer.
///
/// # Errors
/// The formatter's.
///
/// # Adequacy
/// - hypothesis: L3 — one refusal of every checker name writes a nonempty,
///   single-line message with no admission position.
/// - witness: `message::tests::every_refusal_name_has_a_plain_message`
fn checked(
    refusal: CheckRefusal,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result
{
    match refusal {
        CheckRefusal::NotADataType(_) => f.write_str("this is not a datatype"),
        CheckRefusal::DataKindNotUniverse(_) => f.write_str("a datatype's kind must be a universe"),
        CheckRefusal::DataFieldLevel { .. } => {
            f.write_str("a constructor field lives in a larger universe than its datatype")
        },
        CheckRefusal::RuleNotPresentable { .. } => {
            f.write_str("these rules do not present the datatype")
        },
        CheckRefusal::RuleNotRespected { .. } => {
            f.write_str("this case might tell apart terms its datatype's rules identify")
        },
        CheckRefusal::NotApart { .. } => {
            f.write_str("this case has no arm, but its path's endpoints are not shown apart")
        },
        CheckRefusal::LoopNotRespected {
            reason: gandr_core_checker::LoopRespect::Apart,
            ..
        } => f.write_str(
            "this case might tell a loop apart from staying put: carried along the loop, its \
             answer at the loop's point is not that answer",
        ),
        CheckRefusal::LoopNotRespected {
            reason: gandr_core_checker::LoopRespect::NotPresentedSet,
            ..
        } => f.write_str(
            "this case answers at its loop's point by a case over another looped point, and \
             the fibre it answers in is not presented as a set: the square between the two \
             loops is owed, and nothing here supplies it",
        ),
        CheckRefusal::LoopUndecided { .. } => f.write_str(
            "deciding whether this case respects its sort's loops ran past the checker's \
             budget: unfolding what the loop's obligation calls did not settle it",
        ),
        CheckRefusal::AbstractKindNotUniverse(_) => {
            f.write_str("an abstract type's kind must be a universe")
        },
        CheckRefusal::RepresentationAboveKind { .. } => {
            f.write_str("the type sealed here lives in a larger universe than its abstract type")
        },
        CheckRefusal::NotAnAbstractType(_) => {
            f.write_str("this names an abstract type that was not admitted")
        },
        CheckRefusal::SealSiteRepeated(_) => {
            f.write_str("internal error: one abstract component was sealed twice")
        },
        CheckRefusal::DataArgumentArity(_) => {
            f.write_str("the datatype is given the wrong number of arguments")
        },
        CheckRefusal::UnknownConstructor { .. } => {
            f.write_str("the datatype has no such constructor")
        },
        CheckRefusal::ConstructorArity(_) => {
            f.write_str("the constructor is given the wrong number of fields")
        },
        CheckRefusal::NonExhaustiveDataCase(_) => {
            f.write_str("the case must handle every constructor exactly once")
        },
        CheckRefusal::AbsentRecordField(_) => f.write_str("the record has no such field"),
        CheckRefusal::AbsentTupleComponent(_) => f.write_str("the tuple has no such component"),
        CheckRefusal::MissingRecordField { .. } => f.write_str("the record is missing a field"),
        CheckRefusal::UnknownOperation { .. } => f.write_str("the interface has no such operation"),
        CheckRefusal::HandlerCoverage { .. } => {
            f.write_str("the handler must handle every operation of its interface exactly once")
        },
        CheckRefusal::ShiftWithoutReset { .. } => f.write_str("`shift` needs an enclosing `reset`"),
        CheckRefusal::DependentStack { .. } => {
            f.write_str("the stack's result type depends on the value it consumes")
        },
        CheckRefusal::EffectSignatureConflict { .. } => {
            f.write_str("two effects give the same operation different types")
        },
        CheckRefusal::PathCode(_) => {
            f.write_str("a universe path needs a quoted, closed, first-order code at each end")
        },
        CheckRefusal::EndpointMismatch { .. } => {
            f.write_str("`here` needs both endpoints of the path to equal its point")
        },
        CheckRefusal::CompoundEndpoint { .. } => {
            f.write_str("a path endpoint must compute a value without effects")
        },
        CheckRefusal::FunextUnsupported { .. } => f.write_str(
            "`funext` needs two closed pure functions between types built from units, \
             integers, strings, pairs and two-way sums; an argument may itself be a \
             function between such types",
        ),
        CheckRefusal::PointwiseDistinct { .. } => f.write_str(
            "`funext` needs both functions to agree at every input: return the same value, \
             or apply their function argument at the same input",
        ),
        CheckRefusal::EquivUnsupported { .. } => f.write_str(
            "`equiv` needs two closed pure translators between types built from units, \
             integers, strings, tuples and sums",
        ),
        CheckRefusal::UncertifiedStratum { .. } => {
            f.write_str("`equiv` cannot certify a recursive type such as a list")
        },
        CheckRefusal::RoundTripDistinct { .. } => {
            f.write_str("`equiv` needs each round trip to return its input")
        },
        CheckRefusal::NotOver { .. } => f.write_str(
            "`transport` needs its identity over the path to start from the start transported \
             along the path",
        ),
        CheckRefusal::UaUncertified { stratum, .. } => match stratum {
            StratumDefect::Degree { .. } => {
                f.write_str("`ua` is certified from degree 1 to the catalogue's largest degree")
            },
            StratumDefect::Condition { .. } => f.write_str(
                "`ua` needs a catalogue whose site meets the corolla and Segal conditions",
            ),
            StratumDefect::Allowance { .. } => {
                f.write_str("`ua` enumerates catalogues of bound 5 at most")
            },
        },
        CheckRefusal::UaInequivalent { defect, .. } => match defect {
            UaDefect::UnknownGenerator { .. } => {
                f.write_str("a `ua` translator record must name the generators of its description")
            },
            UaDefect::PastTheBound { .. } => {
                f.write_str("a generator stands at a corolla past the `ua` catalogue bound")
            },
            UaDefect::Cardinality { .. } => f.write_str(
                "the two descriptions have different numbers of generators at a corolla",
            ),
            UaDefect::Tables { .. } => {
                f.write_str("`ua` needs exactly one translator per corolla on each side")
            },
            UaDefect::NotInverse { .. } => {
                f.write_str("the `ua` translators are not inverse to each other")
            },
            UaDefect::NotNatural { .. } => {
                f.write_str("the `ua` translators do not commute with the symmetries of a corolla")
            },
            UaDefect::Stuck { .. } => {
                f.write_str("a `ua` translator returns no element of its target code")
            },
        },
        CheckRefusal::UnenclosedRun { .. } => f.write_str(
            "a computation read as a value runs before the computation around it, and none \
             stands around this one",
        ),
        CheckRefusal::SessionNotEquivalent { .. } => {
            f.write_str("`bisim` needs the two protocols to behave alike at every step")
        },
        CheckRefusal::SessionNotSubtype { .. } => f.write_str(
            "`sim` needs its first protocol to select no more and offer no less than its second",
        ),
        CheckRefusal::SessionCodeExpected { .. } => {
            f.write_str("a session identity relates two session types")
        },
        CheckRefusal::NonCovariantMotive { .. } => f.write_str(
            "a flow runs one way: `ride` may use the moving endpoint only where a run of it \
             would be produced",
        ),
        CheckRefusal::RideUnsupported { .. } => f.write_str(
            "`ride` moves a run of the moving endpoint, a value whose type does not depend \
             on it, or a value the flow's translator computes",
        ),
        CheckRefusal::RunNotAdmitted { .. } => f.write_str("the protocol does not admit this run"),
        CheckRefusal::ForwardUnsupported { .. } => {
            f.write_str("`forward` cannot image this translator at every input")
        },
        CheckRefusal::Boundary { .. } => {
            f.write_str("this boundary flow runs against the variance of its position")
        },
        CheckRefusal::TypeMismatch(_) => f.write_str("mismatched types"),
        CheckRefusal::ShapeMismatch { wanted, .. } => write!(f, "expected {}", Shape(wanted)),
        CheckRefusal::NotSynthesisable { form } => write!(
            f,
            "the type of {} cannot be inferred where it stands",
            match form {
                CheckingForm::Reify(_) => "a stack literal",
                CheckingForm::Handle(_) => "a handler",
                CheckingForm::Reset(_) => "a reset",
                CheckingForm::Shift(_) => "a shift",
                CheckingForm::With(_) => "a lazy pair",
                CheckingForm::Injection(_) => "an injection",
                CheckingForm::List(_) => "a list",
                CheckingForm::Case(_) => "a case",
                CheckingForm::Split(_) => "a split",
                CheckingForm::Thunk(_) => "a thunk",
                CheckingForm::Lambda(_) => "a function",
                CheckingForm::Return(_) => "a return",
                CheckingForm::Hole(_) => "a hole",
                CheckingForm::StaticLambda(_) => "a type operator",
                CheckingForm::Fixpoint(_) => "a recursive definition",
                CheckingForm::Nested(_) => "a computation written where a value is read",
                CheckingForm::Offer(_) => "an offer",
                CheckingForm::Scope(_) => "a capability scope",
                CheckingForm::Run(_) => "a recorded run",
            }
        ),
        CheckRefusal::UnknownConstant { .. } => {
            f.write_str("this names a declaration whose type is not known")
        },
        CheckRefusal::OutOfFragment { former, .. } => {
            write!(f, "{} is not supported here", Former(former))
        },
        CheckRefusal::UnboundIndex { .. } => {
            f.write_str("internal error: a variable refers past every binder around it")
        },
        CheckRefusal::BudgetExceeded { budget } => write!(
            f,
            "checking this ran out of its allowance of {budget} steps"
        ),
        CheckRefusal::DanglingNode { .. } => {
            f.write_str("internal error: a term refers to something the checker cannot find")
        },
        CheckRefusal::AdmissionOrder { .. } => {
            f.write_str("internal error: the declarations were checked out of order")
        },
        CheckRefusal::MachineInvariant => {
            f.write_str("internal error: the checker's bookkeeping disagreed with itself")
        },
        CheckRefusal::SortMismatch { .. } => {
            f.write_str("a value type's code and a computation type's code are confused here")
        },
        CheckRefusal::LevelMismatch { .. } => {
            f.write_str("this code lives in a larger universe than the one expected")
        },
        CheckRefusal::DependentBind { .. } => {
            f.write_str("the result type of this `run` depends on the value it binds")
        },
        CheckRefusal::Undecided { .. } => {
            f.write_str("the checker could not decide what this code unfolds to")
        },
        CheckRefusal::FamilyArity {
            expected, actual, ..
        } => write!(
            f,
            "the type operator takes {} arguments but is given {}",
            u32::from(expected),
            u32::from(actual)
        ),
        CheckRefusal::FamilyArgumentClassifier { position, .. } => write!(
            f,
            "argument {} of the type operator has the wrong kind",
            u32::from(position)
        ),
        CheckRefusal::StaticLambdaArgument { .. } => {
            f.write_str("a type operator is given where a value is needed")
        },
        CheckRefusal::StaticClassifierExpected { .. } => {
            f.write_str("a type operator's parameter must range over a universe or a kind")
        },
        CheckRefusal::NegativeOccurrence(site) => write!(
            f,
            "the datatype occurs to the left of an arrow in its {} where no stage reaches it; it is admitted there only applied directly to its own parameters, one stage below its constructor",
            Site(site)
        ),
        CheckRefusal::NestedOccurrence(site) => write!(
            f,
            "the datatype occurs nested inside another type in its {}, at a place that type does not hold strictly positively",
            Site(site)
        ),
        CheckRefusal::IndexOccurrence(site) => {
            write!(f, "the datatype occurs inside a term in its {}", Site(site))
        },
        CheckRefusal::NonUniformOccurrence(site) => write!(
            f,
            "the datatype is applied to other arguments than its parameters in its {}",
            Site(site)
        ),
        CheckRefusal::CrossBlockReference { site, .. } => write!(
            f,
            "the datatype's {} refers to a declaration written after it",
            Site(site)
        ),
        CheckRefusal::StageNotBelow { found, .. } => {
            write!(f, "the recursion is not structural: {}", Stood(found))
        },
        CheckRefusal::SessionMismatch { defect, .. } => match defect {
            ProtocolDefect::Action { expected, observed } => write!(
                f,
                "the endpoint's protocol expects {} here, not {}",
                Action(expected),
                Action(observed)
            ),
            ProtocolDefect::Label => {
                f.write_str("the endpoint's protocol offers no such label here")
            },
            ProtocolDefect::Arms => {
                f.write_str("`offer` must handle every label of its protocol exactly once")
            },
        },
        CheckRefusal::Linearity { defect, .. } => match defect {
            LinearityDefect::Residue { .. } => {
                f.write_str("the endpoint is not closed before its half of the fork ends")
            },
            LinearityDefect::Closed { .. } => f.write_str("the endpoint is used after `close`"),
            LinearityDefect::UsedTwice { .. } => f.write_str("one action names the endpoint twice"),
            LinearityDefect::Captured { by, .. } => write!(
                f,
                "the endpoint is used inside {}, which may run it other than once",
                Captor(by)
            ),
            LinearityDefect::Delegated => {
                f.write_str("an endpoint or a protocol cannot be sent as a payload")
            },
            LinearityDefect::AsValue { .. } => {
                f.write_str("an endpoint can be used only by a session action")
            },
            LinearityDefect::ArmsDisagree { .. } => {
                f.write_str("the arms of this `offer` leave the endpoints in different states")
            },
            LinearityDefect::Unrestricted => f.write_str(
                "a declaration cannot have a session type; an endpoint is opened by `fork`",
            ),
            LinearityDefect::Unbound { .. } => {
                f.write_str("internal error: a session action names an endpoint no `fork` opened")
            },
        },
        CheckRefusal::Access { defect, .. } => match defect {
            AccessDefect::NotHeld => {
                f.write_str("`access` needs a value opened by `hold`; this names something else")
            },
            AccessDefect::Lent => f.write_str(
                "the held value is lent to an `access` here, which ends before it can be read",
            ),
            AccessDefect::HeldCaptured { by } => write!(
                f,
                "the held value is used inside {}, which may run it other than once",
                Captor(by)
            ),
            AccessDefect::Escaped { by } => write!(
                f,
                "the view is used inside {}, which may outlive its `access`",
                Captor(by)
            ),
            AccessDefect::Unended => {
                f.write_str("the body of this `access` must end its view with `resume` or `abort`")
            },
            AccessDefect::Spent => f.write_str("the view is used after its `resume` or `abort`"),
            AccessDefect::NotAView => {
                f.write_str("`resume` and `abort` need the view an `access` opened")
            },
            AccessDefect::UnwindEffect => {
                f.write_str("an `unwind` runs under the empty row and cannot perform an effect")
            },
        },
        CheckRefusal::CapabilityForged { .. } => f.write_str(
            "a capability cannot be made from a term; only one held or granted can stand here",
        ),
        CheckRefusal::CapabilityAmplified(_) => {
            f.write_str("this capability grants less than the one expected here")
        },
        CheckRefusal::CapabilityOutsideAuthority { .. } => {
            f.write_str("the capability does not grant this operation")
        },
        CheckRefusal::CapabilityEscaped { .. } => {
            f.write_str("a capability its scope introduced would outlive the scope here")
        },
        CheckRefusal::CapabilityConsumable(_) => {
            f.write_str("a consumable capability is not supported")
        },
        CheckRefusal::CapabilityUngranted { .. } => {
            f.write_str("this capability claims authority the host did not grant")
        },
    }
}

/// Every refusal name's message, read through one constructed refusal each.
#[cfg(test)]
mod tests
{
    use gandr_core_checker::ArgumentPosition;
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckRefusal;
    use gandr_core_checker::CheckingForm;
    use gandr_core_checker::ComponentOrdinal;
    use gandr_core_checker::CoreNode;
    use gandr_core_checker::ExpectedShape;
    use gandr_core_checker::Mismatch;
    use gandr_core_checker::SealSite;
    use gandr_core_checker::SealingSite;
    use gandr_core_checker::StaticArity;
    use gandr_core_checker::TermNode;
    use gandr_core_checker::TypeNode;
    use gandr_core_checker::UnadmittedFormer;
    use gandr_core_checker::access::AccessDefect;
    use gandr_core_checker::session::Capture;
    use gandr_core_checker::session::Endpoint;
    use gandr_core_checker::session::ForkSide;
    use gandr_core_checker::session::LinearityDefect;
    use gandr_core_checker::session::ProtocolDefect;
    use gandr_core_checker::ua::StratumDefect;
    use gandr_core_checker::ua::UaDefect;
    use gandr_core_checker::ua::Way;
    use gandr_core_term::BinderDepth;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Zone;
    use gandr_core_term::session::ActionKind;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::OccurrenceSite;
    use gandr_kernel_term::ParameterPosition;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;
    use gandr_kernel_term::Standing;
    use gandr_surface_corpus::CorpusRefusal;
    use gandr_surface_corpus::ExpectationSchema;
    use gandr_surface_corpus::Refusal;
    use gandr_surface_corpus::RefusalName;
    use gandr_surface_lowering::AscriptionForm;
    use gandr_surface_lowering::AttributeRegistry;
    use gandr_surface_lowering::AttributeSchema;
    use gandr_surface_lowering::CrossedExit;
    use gandr_surface_lowering::FormFault;
    use gandr_surface_lowering::FormName;
    use gandr_surface_lowering::FragmentBoundary;
    use gandr_surface_lowering::FragmentSort;
    use gandr_surface_lowering::HeadArity;
    use gandr_surface_lowering::LoopExit;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::OperandCount;
    use gandr_surface_lowering::PayloadForm;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_lowering::TelescopeFault;
    use gandr_surface_lowering::model::ModelFault;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use gandr_theory_sites::Degree;
    use gandr_theory_sites::ElementIndex;
    use gandr_theory_sites::PortCount;
    use gandr_theory_sites::Profile;
    use gandr_theory_sites::ShapeIndex;
    use gandr_theory_sites::ShapeSize;

    use super::Plain;

    #[test]
    fn every_refusal_name_has_a_plain_message()
    {
        let mut arena = CoreArena::new();
        let value = arena.value_unit();
        let computation = arena.computation_return(value);
        let value_type = arena.value_type_unit();
        let comp_type = arena.comp_type_returner(value_type);
        let span = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(1_usize))
            .expect("an ordered span");
        let name = SurfaceName::from("x");
        let form = FormName::HOLE;
        let registered = AttributeRegistry::names()
            .first()
            .copied()
            .expect("the registry holds a name");
        let site = OccurrenceSite::Parameter(ParameterPosition::from(0_usize));
        let corolla = ShapeIndex::from(0_usize);
        let element = ElementIndex::from(0_usize);
        let endpoint = Endpoint {
            fork: computation,
            side: ForkSide::Child,
        };
        let node = CoreNode::Term(TermNode::Computation(computation));
        let lowering = [
            LoweringRefusal::UnresolvedName { span, name },
            LoweringRefusal::UnresolvedDocLink { span, name },
            LoweringRefusal::UnresolvedTypeHead {
                span,
                name,
                arity: HeadArity::Nullary,
            },
            LoweringRefusal::DuplicateSignature {
                span,
                name,
                first: span,
            },
            LoweringRefusal::DuplicateDefinition {
                span,
                name,
                first: span,
            },
            LoweringRefusal::DuplicateImportAlias {
                span,
                alias: name,
                first: span,
            },
            LoweringRefusal::ImportUnresolved {
                span,
                refused: span,
            },
            LoweringRefusal::ImportCycle {
                span,
                refused: span,
            },
            LoweringRefusal::ImportShadows {
                span,
                name,
                import: span,
                other: span,
            },
            LoweringRefusal::UnexportedName {
                span,
                name,
                declared: span,
            },
            LoweringRefusal::ShadowedBuiltin { span, name },
            LoweringRefusal::OutOfFragment {
                span,
                form,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::WrongSort,
            },
            LoweringRefusal::GradedBridge { span, grade: name },
            LoweringRefusal::MalformedLiteral { span, form },
            LoweringRefusal::MalformedForm {
                span,
                form,
                fault: FormFault::ExtraOperand,
            },
            LoweringRefusal::UnknownAttribute {
                span,
                name,
                suggestion: AttributeRegistry::suggestion(SurfaceName::from("check")),
            },
            LoweringRefusal::DuplicateAttribute {
                span,
                name,
                first: span,
            },
            LoweringRefusal::MissingPayload {
                span,
                name: registered,
                expected: AttributeSchema::Integer,
            },
            LoweringRefusal::NonValuePayload {
                span,
                name: registered,
                form,
            },
            LoweringRefusal::IllTypedPayload {
                span,
                name: registered,
                expected: AttributeSchema::Integer,
                written: PayloadForm::Text,
            },
            LoweringRefusal::ForwardMemberReference {
                span,
                name,
                declared: span,
            },
            LoweringRefusal::UnknownMember {
                span,
                module: name,
                member: name,
            },
            LoweringRefusal::NotAFunctor { span, name },
            LoweringRefusal::ProjectionFromApplication {
                span,
                functor: name,
            },
            LoweringRefusal::UnreadAscription {
                span,
                name,
                form: AscriptionForm::Kinded,
            },
            LoweringRefusal::UnstatedComponent {
                span,
                name,
                fault: ModelFault::Inherited,
            },
            LoweringRefusal::FamilyTelescope {
                span,
                name,
                fault: TelescopeFault::Index(OperandCount::from(1_usize)),
            },
            LoweringRefusal::LowercaseModuleName { span, name },
            LoweringRefusal::NonExhaustiveMatch { span },
            LoweringRefusal::UnmarkedSelfReference { span, name },
            LoweringRefusal::Unreachable { span },
            LoweringRefusal::OutsideLoop {
                span,
                exit: LoopExit::Break,
            },
            LoweringRefusal::AcrossHandler {
                span,
                exit: CrossedExit::Continue,
            },
            LoweringRefusal::ForNeedsListCase { span },
            LoweringRefusal::WithoutK { span },
            LoweringRefusal::DirectedCell { span },
            LoweringRefusal::CellNotALoop { span },
            LoweringRefusal::RulesUnoriented { span },
            LoweringRefusal::RulesDiverge { span, first: span },
            LoweringRefusal::RulesUndecided { span, first: span },
            LoweringRefusal::BudgetExceeded {
                budget: 0_usize.into(),
            },
            LoweringRefusal::GrammarMismatch {
                tree: GrammarFingerprint::from(1_u64),
                grammar: GrammarFingerprint::from(2_u64),
            },
            LoweringRefusal::UnknownMold {
                span,
                mold: MoldId::from(0_u32),
            },
            LoweringRefusal::Unminted {
                span,
                name: SurfaceName::from("windHom"),
            },
        ]
        .map(Refusal::Lowering);
        let checking = [
            CheckRefusal::NotADataType(ConstantIndex::from(0_usize)),
            CheckRefusal::DataKindNotUniverse(value_type),
            CheckRefusal::DataFieldLevel {
                field: value_type,
                kind: value_type,
            },
            CheckRefusal::RuleNotPresentable {
                kind: value_type,
                refusal: gandr_kernel_term::RuleRefusal {
                    rule: gandr_kernel_term::RuleIndex::from(0_usize),
                    fault: gandr_kernel_term::RuleFault::NotDecreasing,
                },
            },
            CheckRefusal::RuleNotRespected {
                at: computation,
                rule: gandr_kernel_term::RuleIndex::from(0_usize),
                left: value,
                right: value,
            },
            CheckRefusal::NotApart {
                at: computation,
                reason: gandr_kernel_term::Apartness::Agree,
            },
            CheckRefusal::LoopNotRespected {
                at: computation,
                cell: gandr_kernel_term::CellIndex::from(0_usize),
                left: computation,
                right: computation,
                reason: gandr_core_checker::LoopRespect::NotPresentedSet,
            },
            CheckRefusal::LoopUndecided {
                at: computation,
                cell: gandr_kernel_term::CellIndex::from(0_usize),
            },
            CheckRefusal::AbstractKindNotUniverse(value_type),
            CheckRefusal::RepresentationAboveKind {
                representation: value_type,
                kind: value_type,
            },
            CheckRefusal::NotAnAbstractType(ConstantIndex::from(0_usize)),
            CheckRefusal::SealSiteRepeated(SealSite::new(
                SealingSite::from(0_usize),
                ComponentOrdinal::from(0_usize),
            )),
            CheckRefusal::DataArgumentArity(value_type),
            CheckRefusal::UnknownConstructor {
                at: value,
                tag: ConstructorTag::from(0_usize),
            },
            CheckRefusal::ConstructorArity(value),
            CheckRefusal::NonExhaustiveDataCase(computation),
            CheckRefusal::AbsentRecordField(computation),
            CheckRefusal::AbsentTupleComponent(computation),
            CheckRefusal::MissingRecordField {
                at: value,
                expected: value_type,
            },
            CheckRefusal::UnknownOperation { at: computation },
            CheckRefusal::HandlerCoverage { at: computation },
            CheckRefusal::ShiftWithoutReset { at: computation },
            CheckRefusal::DependentStack {
                at: value,
                synthesised: comp_type,
            },
            CheckRefusal::PathCode(value),
            CheckRefusal::TypeMismatch(Mismatch::Value {
                at: value,
                synthesised: value_type,
                expected: value_type,
            }),
            CheckRefusal::EffectSignatureConflict {
                at: computation,
                first: comp_type,
                second: comp_type,
            },
            CheckRefusal::ShapeMismatch {
                at: TermNode::Value(value),
                wanted: ExpectedShape::Thunk,
                found: TypeNode::Value(value_type),
            },
            CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(value),
            },
            CheckRefusal::UnknownConstant {
                at: value,
                constant: ConstantIndex::from(0_usize),
            },
            CheckRefusal::OutOfFragment {
                at: CoreNode::Term(TermNode::Computation(computation)),
                former: UnadmittedFormer::Shift,
            },
            CheckRefusal::UnboundIndex {
                at: value,
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
                depth: BinderDepth::from(0_usize),
            },
            CheckRefusal::BudgetExceeded {
                budget: CheckBudget::from(0_usize),
            },
            CheckRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Computation(comp_type)),
            },
            CheckRefusal::AdmissionOrder {
                constant: ConstantIndex::from(0_usize),
                admitted: ConstantIndex::from(1_usize),
            },
            CheckRefusal::MachineInvariant,
            CheckRefusal::SortMismatch {
                at: value,
                synthesised: value_type,
                expected: value_type,
            },
            CheckRefusal::LevelMismatch {
                at: value,
                synthesised: value_type,
                expected: value_type,
            },
            CheckRefusal::DependentBind {
                at: computation,
                synthesised: comp_type,
            },
            CheckRefusal::Undecided { at: value },
            CheckRefusal::FamilyArity {
                at: value,
                expected: StaticArity::from(1_u32),
                actual: StaticArity::from(2_u32),
            },
            CheckRefusal::FamilyArgumentClassifier {
                at: value,
                position: ArgumentPosition::from(0_u32),
                synthesised: value_type,
                expected: value_type,
            },
            CheckRefusal::StaticLambdaArgument { at: value },
            CheckRefusal::StaticClassifierExpected {
                at: value_type,
                found: value_type,
            },
            CheckRefusal::NegativeOccurrence(site),
            CheckRefusal::NestedOccurrence(site),
            CheckRefusal::IndexOccurrence(site),
            CheckRefusal::NonUniformOccurrence(site),
            CheckRefusal::CrossBlockReference {
                site,
                index: ConstantIndex::from(1_usize),
            },
            CheckRefusal::StageNotBelow {
                at: value,
                found: Standing::Top,
                bound: Stage::At(StageId::from(0_usize)),
            },
            CheckRefusal::EndpointMismatch {
                at: value,
                left: value,
                right: value,
            },
            CheckRefusal::CompoundEndpoint {
                at: value,
                synthesised: comp_type,
            },
            CheckRefusal::FunextUnsupported {
                at: value,
                classifier: value_type,
            },
            CheckRefusal::PointwiseDistinct { at: value },
            CheckRefusal::EquivUnsupported {
                at: value,
                classifier: value_type,
            },
            CheckRefusal::UncertifiedStratum {
                at: value,
                code: value_type,
            },
            CheckRefusal::RoundTripDistinct { at: value },
            CheckRefusal::NotOver {
                at: value,
                synthesised: value_type,
                expected: value_type,
            },
            CheckRefusal::UaUncertified {
                at: value,
                stratum: StratumDefect::Degree {
                    degree: Degree::from(2_usize),
                },
            },
            CheckRefusal::UaUncertified {
                at: value,
                stratum: StratumDefect::Condition {
                    degree: Degree::from(1_usize),
                },
            },
            CheckRefusal::UaUncertified {
                at: value,
                stratum: StratumDefect::Allowance {
                    bound: ShapeSize::from(6_usize),
                },
            },
            CheckRefusal::UaInequivalent {
                at: value,
                defect: UaDefect::UnknownGenerator { way: Way::Forward },
            },
            CheckRefusal::UaInequivalent {
                at: value,
                defect: UaDefect::PastTheBound {
                    profile: Profile {
                        inputs: PortCount::from(2_usize),
                        outputs: PortCount::from(1_usize),
                    },
                },
            },
            CheckRefusal::UaInequivalent {
                at: value,
                defect: UaDefect::Cardinality { corolla },
            },
            CheckRefusal::UaInequivalent {
                at: value,
                defect: UaDefect::Tables { corolla },
            },
            CheckRefusal::UaInequivalent {
                at: value,
                defect: UaDefect::NotInverse { corolla, element },
            },
            CheckRefusal::UaInequivalent {
                at: value,
                defect: UaDefect::NotNatural { corolla, element },
            },
            CheckRefusal::UaInequivalent {
                at: value,
                defect: UaDefect::Stuck { corolla, element },
            },
            CheckRefusal::SessionMismatch {
                at: computation,
                endpoint,
                state: value_type,
                defect: ProtocolDefect::Action {
                    expected: ActionKind::Send,
                    observed: ActionKind::Close,
                },
            },
            CheckRefusal::SessionMismatch {
                at: computation,
                endpoint,
                state: value_type,
                defect: ProtocolDefect::Label,
            },
            CheckRefusal::SessionMismatch {
                at: computation,
                endpoint,
                state: value_type,
                defect: ProtocolDefect::Arms,
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::Residue {
                    endpoint,
                    state: value_type,
                },
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::Closed { endpoint },
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::UsedTwice { endpoint },
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::Captured {
                    endpoint,
                    by: Capture::Thunk,
                },
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::Delegated,
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::AsValue { endpoint },
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::ArmsDisagree {
                    endpoint,
                    first: computation,
                    other: computation,
                },
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::Unrestricted,
            },
            CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::Unbound {
                    index: DeBruijnIndex::from(0_u32),
                },
            },
            CheckRefusal::Access {
                at: node,
                defect: AccessDefect::NotHeld,
            },
            CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Lent,
            },
            CheckRefusal::Access {
                at: node,
                defect: AccessDefect::HeldCaptured { by: Capture::Thunk },
            },
            CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Escaped { by: Capture::Thunk },
            },
            CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Unended,
            },
            CheckRefusal::Access {
                at: node,
                defect: AccessDefect::Spent,
            },
            CheckRefusal::Access {
                at: node,
                defect: AccessDefect::NotAView,
            },
            CheckRefusal::Access {
                at: node,
                defect: AccessDefect::UnwindEffect,
            },
            CheckRefusal::CapabilityForged {
                at: value,
                expected: value_type,
            },
            CheckRefusal::CapabilityAmplified(Mismatch::Value {
                at: value,
                synthesised: value_type,
                expected: value_type,
            }),
            CheckRefusal::CapabilityOutsideAuthority {
                at: computation,
                capability: value_type,
            },
            CheckRefusal::CapabilityEscaped {
                at: TermNode::Value(value),
                found: TypeNode::Value(value_type),
            },
            CheckRefusal::CapabilityConsumable(value_type),
            CheckRefusal::CapabilityUngranted {
                constant: ConstantIndex::from(0_usize),
                declared: value_type,
            },
            CheckRefusal::UnenclosedRun { at: value },
            CheckRefusal::SessionNotEquivalent { at: value },
            CheckRefusal::SessionNotSubtype { at: value },
            CheckRefusal::SessionCodeExpected { at: value },
            CheckRefusal::NonCovariantMotive { at: computation },
            CheckRefusal::RideUnsupported { at: computation },
            CheckRefusal::RunNotAdmitted {
                at: value,
                fault: gandr_core_checker::RunFault::WrongLabel(gandr_core_checker::RunStep::from(
                    1_u32,
                )),
            },
            CheckRefusal::ForwardUnsupported { at: value },
            CheckRefusal::Boundary { at: value },
        ]
        .map(Refusal::Checking);
        let corpus = Refusal::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot {
            span,
            schema: ExpectationSchema::Owes,
        });
        let refusals: Vec<Refusal<'_>> = lowering
            .into_iter()
            .chain(checking)
            .chain([corpus])
            .collect();
        let named: Vec<RefusalName> = refusals.iter().map(Refusal::name).collect();
        let missing: Vec<RefusalName> = RefusalName::VOCABULARY
            .into_iter()
            .filter(|vocabulary| !named.contains(vocabulary))
            .collect();
        assert!(missing.is_empty(), "every name is exercised: {missing:?}");
        for refusal in refusals {
            let message = Plain(refusal).to_string();
            assert!(!message.is_empty(), "{:?} has a message", refusal.name());
            assert!(!message.contains('\n'), "one line: {message}");
            assert!(
                !message
                    .split(|character: char| character.is_whitespace() || character == '`')
                    .any(|word| word.contains('_')),
                "no grammar sort: {message}"
            );
            assert!(
                !message.contains("admission position") && !message.contains("node "),
                "no producer bookkeeping: {message}"
            );
        }
    }

    /// A refusal that names a form with an article writes the one its name is
    /// spoken with (#417).
    #[test]
    fn a_form_takes_the_article_its_name_is_spoken_with()
    {
        let span = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(1_usize))
            .expect("an ordered span");
        let refused = |form: FormName, boundary: FragmentBoundary| {
            Plain(Refusal::Lowering(LoweringRefusal::OutOfFragment {
                span,
                form,
                sort: FragmentSort::Value,
                boundary,
            }))
            .to_string()
        };
        for (form, opening) in [
            (FormName::IDENTIFIER, "an identifier "),
            (FormName::INSTANTIATION, "an instantiation expression "),
            (FormName::UNPACK_STATEMENT, "an unpack statement "),
            (FormName::UNIT, "a unit "),
            (FormName::HOLE, "a hole "),
        ] {
            for boundary in [FragmentBoundary::WrongSort, FragmentBoundary::NotInTail] {
                let message = refused(form, boundary);
                assert!(message.starts_with(opening), "{opening:?}: {message}");
            }
        }
    }
}
