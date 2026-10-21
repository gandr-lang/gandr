//! Match coverage over typed patterns with holes among them: whether a match
//! is exhaustive and whether each arm is redundant, each answered in three
//! values.
//!
//! # Usefulness decides both questions
//!
//! A pattern vector is useful against a matrix of rows when some value it
//! matches is matched by no row (Maranget, *Warnings for pattern matching*,
//! JFP 2007, doi:10.1017/S0956796807006223). A match is exhaustive when the
//! wildcard is useful against none of its arms, and an arm is redundant when
//! it is useful against none of the arms above it. Usefulness specialises the
//! matrix by the head constructor of the vector's first column, or, under a
//! wildcard, by every constructor of the column's type when the heads present
//! complete its signature and by the default matrix when they do not.
//!
//! # A worklist of disjunctive problems
//!
//! Every step of the usefulness relation is a disjunction over smaller
//! problems, so the walk is a stack of matrix-and-vector problems that answers
//! useful at the first empty vector facing an empty matrix and useless when
//! the stack runs dry. Each problem costs one step of the context's allowance.
//!
//! # A hole is read both ways, and only agreement is definite
//!
//! A pattern hole may be filled with any pattern of its type, so an answer
//! holds only when every filling gives it (Yuan et al., *Live Pattern Matching
//! with Typed Holes*, OOPSLA 2023, doi:10.1145/3586048). Every pattern matches
//! at least what a pattern matching nothing does and at most what a wildcard
//! does, and usefulness only grows as the vector matches more and as the
//! matrix matches less, so the two bounds decide:
//!
//! - **exhaustive** when the wildcard is useless with every hole in the arms
//!   read as matching nothing;
//! - **inexhaustive** when it is useful with every hole read as a wildcard;
//! - **redundant** when the arm is useless with its own holes read as wildcards
//!   and the holes above read as matching nothing;
//! - **irredundant** when the arm is useful with its own holes read as matching
//!   nothing and the holes above read as wildcards;
//! - **possibly** otherwise.
//!
//! A row holding a hole read as matching nothing matches nothing at all, since
//! a row matches only when every column does, so an arm with a hole of its
//! own is never definitely irredundant. Reversal: a sharper lower bound that
//! reads a hole as some single value of its type would answer irredundant for
//! an arm whose hole every filling leaves useful.
//!
//! # The unknown type is read both ways too
//!
//! A column of the unknown type has a signature the program has not fixed. A
//! head of unit, pair or both injections fixes it as unit, product or sum;
//! otherwise the bound that grows usefulness reads it as having constructors
//! no arm names, and the bound that shrinks it reads it as the least signature
//! the heads allow — the constructors named and every tag below the largest.
//! Both read it as inhabited, so a column no head names has a value no arm
//! names. Reversal: should a hole's type be filled with a nominal type of no
//! constructors in practice, the shrinking bound reads a headless column as
//! empty, at the price of answering possibly for every arm over an unknown
//! field.
//!
//! # Coverage takes a pattern table
//!
//! The core calculus has no match former, so [`cover`] takes a pattern table
//! and a scrutinee type rather than a term; a core match former would bring the
//! same answers into the judgement's own rule. Witnesses:
//! `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`,
//! `coverage::tests::literals_never_complete_and_nested_columns_specialise`,
//! `coverage::tests::a_nominal_type_is_complete_when_every_constructor_stands`,
//! `coverage::tests::a_pattern_hole_is_answered_possibly` and
//! `coverage::tests::an_unknown_scrutinee_reads_the_least_and_the_widest_signature`.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ConstructorTag;
use gandr_core_term::DataSignature;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::formation::FormedValueType;
use crate::former;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;

/// Whether a match covers every value of its scrutinee's type.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Exhaustiveness
{
    /// Every value is matched by some arm, whatever the holes are filled with.
    Exhaustive,
    /// Some value is matched by no arm, whatever the holes are filled with.
    Inexhaustive,
    /// A hole, or a signature the program has not fixed, decides.
    Possibly,
}

/// Whether an arm matches some value no arm above it matches.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Redundancy
{
    /// The arm matches a value no arm above it does, whatever the fill.
    Irredundant,
    /// Every value the arm matches is matched above it, whatever the fill.
    Redundant,
    /// A hole, or a signature the program has not fixed, decides.
    Possibly,
}

/// A match's coverage: the match's exhaustiveness and each arm's redundancy.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Coverage
{
    /// Whether the arms cover the scrutinee's type.
    exhaustiveness: Exhaustiveness,
    /// Each arm's redundancy, in arm order.
    arms: Vec<Redundancy>,
}

impl Coverage
{
    /// Whether the arms cover the scrutinee's type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn exhaustiveness(&self) -> Exhaustiveness
    {
        self.exhaustiveness
    }

    /// Each arm's redundancy, in arm order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arms(&self) -> &[Redundancy]
    {
        &self.arms
    }
}

/// Why a match's coverage has no answer.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CoverageFault
{
    /// A pattern id names no pattern of the table.
    DanglingPattern(PatternId),
    /// A pattern's former cannot stand in a column of this type.
    IllTypedPattern
    {
        /// The pattern.
        pattern: PatternId,
        /// The type of the column it stands in.
        column: ValueTypeId,
    },
    /// Reading a column's type was refused: a dangling type, a nominal type
    /// with no admitted declaration, or the allowance spent.
    Refused(CheckRefusal),
}

/// Answer `arms`' coverage of `scrutinee`: exhaustiveness and each arm's
/// redundancy, three-valued over the holes the patterns hold.
///
/// # Specification
/// - requires: every arm names a pattern of `patterns` written at `scrutinee`.
/// - ensures: exhaustive or inexhaustive only when every filling of the holes
///   and of the unknown type agrees, and likewise redundant or irredundant per
///   arm; possibly otherwise. Without holes or the unknown type the answers are
///   Maranget's usefulness verdicts.
/// - provides: one redundancy per arm, in arm order.
/// - fails: a dangling pattern, a pattern former that cannot stand at its
///   column's type, an unreadable type, or the allowance.
/// - panics: none.
///
/// # Errors
/// - [`CoverageFault`] — the patterns do not fit the scrutinee, or the
///   allowance ran out.
///
/// # Adequacy
/// - hypothesis: L3 — a sum, a product of a literal column and a sum, a nominal
///   type, the unknown type, and holes standing alone, nested and below a
///   covering prefix separate the complete and incomplete signatures, the
///   default matrix, the two readings and the three answers.
/// - witness: `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`
/// - witness: `coverage::tests::literals_never_complete_and_nested_columns_specialise`
/// - witness: `coverage::tests::a_nominal_type_is_complete_when_every_constructor_stands`
/// - witness: `coverage::tests::a_pattern_hole_is_answered_possibly`
/// - witness: `coverage::tests::an_unknown_scrutinee_reads_the_least_and_the_widest_signature`
#[spec(ensures: |ret| match ret.as_ref() {
    | Ok(coverage) => coverage.arms().len() == arms.len(),
    | Err(_) => true,
})]
#[inline]
pub fn cover(
    context: &mut CheckingContext<'_>,
    scrutinee: FormedValueType,
    patterns: &Patterns,
    arms: &[PatternId],
) -> Result<Coverage, CoverageFault>
{
    let unknown = context.arena_mut().value_type_unknown();
    let remaining = usize::from(context.budget());
    let mut walker = Walker {
        context,
        patterns,
        unknown,
        remaining,
    };
    let column = scrutinee.id();
    let widest = walker.useful(arms, Cell::Anything, column, Reading {
        rows: HoleReading::Nothing,
        query: HoleReading::Anything,
        constructors: Constructors::Open,
    })?;
    let least = walker.useful(arms, Cell::Anything, column, Reading {
        rows: HoleReading::Anything,
        query: HoleReading::Anything,
        constructors: Constructors::Closed,
    })?;
    let exhaustiveness = match (widest, least) {
        (Usefulness::Useless, Usefulness::Useless) => Exhaustiveness::Exhaustive,
        (Usefulness::Useful, Usefulness::Useful) => Exhaustiveness::Inexhaustive,
        (Usefulness::Useful, Usefulness::Useless) => Exhaustiveness::Possibly,
        (Usefulness::Useless, Usefulness::Useful) => {
            return Err(CoverageFault::Refused(CheckRefusal::MachineInvariant));
        },
    };
    let mut redundancy = Vec::with_capacity(arms.len());
    for (index, &arm) in arms.iter().enumerate() {
        let above = arms
            .get(.. index)
            .ok_or(CoverageFault::Refused(CheckRefusal::MachineInvariant))?;
        let widest = walker.useful(above, Cell::Written(arm), column, Reading {
            rows: HoleReading::Nothing,
            query: HoleReading::Anything,
            constructors: Constructors::Open,
        })?;
        let least = walker.useful(above, Cell::Written(arm), column, Reading {
            rows: HoleReading::Anything,
            query: HoleReading::Nothing,
            constructors: Constructors::Closed,
        })?;
        redundancy.push(match (widest, least) {
            (Usefulness::Useless, Usefulness::Useless) => Redundancy::Redundant,
            (Usefulness::Useful, Usefulness::Useful) => Redundancy::Irredundant,
            (Usefulness::Useful, Usefulness::Useless) => Redundancy::Possibly,
            (Usefulness::Useless, Usefulness::Useful) => {
                return Err(CoverageFault::Refused(CheckRefusal::MachineInvariant));
            },
        });
    }
    Ok(Coverage {
        exhaustiveness,
        arms: redundancy,
    })
}

/// One cell of a pattern matrix: a written pattern or a wildcard the walk
/// introduced.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cell
{
    /// A pattern of the table.
    Written(PatternId),
    /// A wildcard standing for a constructor's fields.
    Anything,
}

/// A head constructor: what a pattern demands of its value's outermost
/// former.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Head
{
    /// The unit value.
    Unit,
    /// One literal.
    Literal(Literal),
    /// A pair.
    Pair,
    /// An injection into one side.
    Injection(Side),
    /// A nominal constructor.
    Constructor(ConstructorTag),
}

/// How many fields a head's pattern takes apart.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Arity(usize);

/// What a cell demands.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Read
{
    /// Nothing: a wildcard, a binder, or a hole read as a wildcard.
    Anything,
    /// A head constructor, with the parts its fields must match.
    Head
    {
        /// The head.
        head: Head,
        /// The parts, one per field.
        parts: Vec<PatternId>,
        /// The pattern read.
        pattern: PatternId,
    },
}

/// How a pattern hole is read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HoleReading
{
    /// As matching nothing: a row holding it matches nothing.
    Nothing,
    /// As a wildcard.
    Anything,
}

/// How the signature of a column of the unknown type is read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Constructors
{
    /// The type has constructors no head names.
    Open,
    /// The type has exactly the least signature the heads allow.
    Closed,
}

/// One bound: how the matrix's holes, the vector's holes and the unknown
/// type's signature are read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Reading
{
    /// The holes of the matrix's rows.
    rows: HoleReading,
    /// The holes of the vector.
    query: HoleReading,
    /// The unknown type's signature.
    constructors: Constructors,
}

/// Whether a vector matches some value no row of the matrix matches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Usefulness
{
    /// It does.
    Useful,
    /// It does not.
    Useless,
}

/// Whether a pattern holds a hole anywhere beneath it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Holes
{
    /// It does.
    Held,
    /// It does not.
    Absent,
}

/// What a column's type allows to stand in it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// The unit type: the unit pattern.
    Unit,
    /// A product: pair patterns over the two factors.
    Product(ValueTypeId, ValueTypeId),
    /// A sum: injections into the two summands.
    Sum(ValueTypeId, ValueTypeId),
    /// A nominal type: its constructors.
    Data,
    /// A base type: its literals, never all of them.
    Literals,
    /// The unknown type: any head, read by the bound.
    Unknown,
    /// Any other type: wildcards and binders only.
    Opaque,
}

/// Whether the heads present in a column complete its signature.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Completeness
{
    /// They do: every constructor of the signature, with its field types.
    Complete(Vec<(Head, Vec<ValueTypeId>)>),
    /// They do not.
    Incomplete,
}

/// One usefulness problem: a matrix, a vector and the column types.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Problem
{
    /// The matrix's rows.
    rows: Vec<Vec<Cell>>,
    /// The vector.
    query: Vec<Cell>,
    /// The type of each column.
    columns: Vec<ValueTypeId>,
}

/// The state one coverage question walks with.
struct Walker<'table, 'context, 'arena>
{
    /// The context types are read in.
    context: &'context mut CheckingContext<'arena>,
    /// The patterns the arms are written in.
    patterns: &'table Patterns,
    /// The unknown type, minted once, for the fields of unknown columns.
    unknown: ValueTypeId,
    /// The problems left before the walk refuses.
    remaining: usize,
}

impl Walker<'_, '_, '_>
{
    /// Decide whether `query` is useful against `rows` in a column of type
    /// `column`, under one reading of holes and unknown signatures.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: useful exactly when, with holes and the unknown type read as
    ///   `reading` says, some value of `column` matched by `query` is matched
    ///   by no row.
    /// - fails: a dangling or ill-typed pattern, an unreadable type, or the
    ///   allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault`] — as for [`cover`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the coverage tests drive the specialised, default and
    ///   complete branches under both readings.
    /// - witness: `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`
    /// - witness: `coverage::tests::literals_never_complete_and_nested_columns_specialise`
    /// - witness: `coverage::tests::a_pattern_hole_is_answered_possibly`
    #[spec(captures: before = self.remaining, ensures: self.remaining <= before)]
    fn useful(
        &mut self,
        rows: &[PatternId],
        query: Cell,
        column: ValueTypeId,
        reading: Reading,
    ) -> Result<Usefulness, CoverageFault>
    {
        if let Cell::Written(pattern) = query
            && reading.query == HoleReading::Nothing
            && self.holes(pattern)? == Holes::Held
        {
            return Ok(Usefulness::Useless);
        }
        let mut kept = Vec::with_capacity(rows.len());
        for &row in rows {
            if reading.rows == HoleReading::Nothing && self.holes(row)? == Holes::Held {
                continue;
            }
            kept.push(vec![Cell::Written(row)]);
        }
        let mut stack = vec![Problem {
            rows: kept,
            query: vec![query],
            columns: vec![column],
        }];
        while let Some(problem) = stack.pop() {
            self.charge()?;
            let Some(&first) = problem.query.first()
            else {
                if problem.rows.is_empty() {
                    return Ok(Usefulness::Useful);
                }
                continue;
            };
            let &column = problem
                .columns
                .first()
                .ok_or(CoverageFault::Refused(CheckRefusal::MachineInvariant))?;
            let kind = self.kind(column)?;
            match self.read(first)? {
                Read::Head {
                    head,
                    parts,
                    pattern,
                } => {
                    let fields = self.fields(column, kind, &head, Arity(parts.len()), pattern)?;
                    stack.push(self.specialise(&problem, &head, &fields)?);
                },
                Read::Anything => {
                    match self.complete(&problem, column, kind, reading.constructors)? {
                        Completeness::Complete(constructors) => {
                            for (head, fields) in constructors {
                                stack.push(self.specialise(&problem, &head, &fields)?);
                            }
                        },
                        Completeness::Incomplete => stack.push(self.default(&problem)?),
                    }
                },
            }
        }
        Ok(Usefulness::Useless)
    }

    /// Spend one problem of the allowance.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fewer problem remains on success.
    /// - fails: the allowance, when none remains.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault::Refused`] with [`CheckRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a context of one step refuses a match that needs two
    ///   problems.
    /// - witness: `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`
    #[spec(captures: before = self.remaining, ensures: |ret| ret.is_err() || before.checked_sub(1) == Some(self.remaining))]
    fn charge(&mut self) -> Result<(), CoverageFault>
    {
        self.remaining = self.remaining.checked_sub(1).ok_or_else(|| {
            CoverageFault::Refused(CheckRefusal::BudgetExceeded {
                budget: self.context.budget(),
            })
        })?;
        Ok(())
    }

    /// The pattern `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the table's pattern under `id`.
    /// - fails: a dangling id.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault::DanglingPattern`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every walk reads through here; a wrong read changes
    ///   every coverage answer.
    /// - witness: `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`
    #[spec(ensures: |ret| ret.is_ok() == self.patterns.pattern(id).is_some())]
    fn pattern(
        &self,
        id: PatternId,
    ) -> Result<&Pattern, CoverageFault>
    {
        self.patterns
            .pattern(id)
            .ok_or(CoverageFault::DanglingPattern(id))
    }

    /// Whether a hole stands anywhere beneath `pattern`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: held exactly when `pattern` or one of its transitive parts is
    ///   a hole.
    /// - fails: a dangling part.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault::DanglingPattern`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hole alone and a hole beneath an injection separate
    ///   the root from the walk.
    /// - witness: `coverage::tests::a_pattern_hole_is_answered_possibly`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.patterns.pattern(pattern), Some(Pattern::Hole(_))) <= (ret == Ok(Holes::Held)))]
    fn holes(
        &self,
        pattern: PatternId,
    ) -> Result<Holes, CoverageFault>
    {
        let mut pending = vec![pattern];
        while let Some(next) = pending.pop() {
            let read = self.pattern(next)?;
            if let Pattern::Hole(_) = *read {
                return Ok(Holes::Held);
            }
            pending.extend(read.parts());
        }
        Ok(Holes::Absent)
    }

    /// What `cell` demands of its value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: wildcards, binders and holes demand nothing; every other
    ///   former demands its head, with its parts in order.
    /// - fails: a dangling pattern.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault::DanglingPattern`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every head former and the three wildcard readings
    ///   occur in the coverage tests.
    /// - witness: `coverage::tests::literals_never_complete_and_nested_columns_specialise`
    /// - witness: `coverage::tests::a_nominal_type_is_complete_when_every_constructor_stands`
    #[spec(ensures: |ret| ret.is_err() || cell != Cell::Anything || ret == Ok(Read::Anything))]
    fn read(
        &self,
        cell: Cell,
    ) -> Result<Read, CoverageFault>
    {
        let Cell::Written(pattern) = cell
        else {
            return Ok(Read::Anything);
        };
        let (head, parts) = match *self.pattern(pattern)? {
            Pattern::Wildcard | Pattern::Binder | Pattern::Hole(_) => return Ok(Read::Anything),
            Pattern::Unit => (Head::Unit, Vec::new()),
            Pattern::Literal(ref literal) => (Head::Literal(literal.clone()), Vec::new()),
            Pattern::Pair(first, second) => (Head::Pair, vec![first, second]),
            Pattern::Injection(side, body) => (Head::Injection(side), vec![body]),
            Pattern::Constructor { tag, ref fields } => (Head::Constructor(tag), fields.clone()),
        };
        Ok(Read::Head {
            head,
            parts,
            pattern,
        })
    }

    /// What may stand in a column of type `column`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the kind of `column`'s former, a dependent pair read as the
    ///   pair of its factors, since the head former of its second factor does
    ///   not depend on the binder; a type no pattern head inhabits, a product
    ///   of neither zero nor two components and a sum of other than two
    ///   summands are opaque.
    /// - fails: a dangling type.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault::Refused`] with [`CheckRefusal::DanglingNode`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unit, product, sum, nominal, base and unknown columns
    ///   occur in the coverage tests.
    /// - witness: `coverage::tests::literals_never_complete_and_nested_columns_specialise`
    /// - witness: `coverage::tests::an_unknown_scrutinee_reads_the_least_and_the_widest_signature`
    #[spec(ensures: |ret| ret.is_ok() == self.context.arena().value_type(column).is_some())]
    fn kind(
        &self,
        column: ValueTypeId,
    ) -> Result<Kind, CoverageFault>
    {
        match self.context.arena().value_type(column) {
            None => Err(CoverageFault::Refused(CheckRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(column)),
            })),
            Some(&ValueType::Product(ref parts)) => match **parts {
                [] => Ok(Kind::Unit),
                [first, second] => Ok(Kind::Product(first, second)),
                _ => Ok(Kind::Opaque),
            },
            Some(&ValueType::Sigma { first, second }) => Ok(Kind::Product(first, second)),
            Some(&ValueType::Sum(ref parts)) => match **parts {
                [left, right] => Ok(Kind::Sum(left, right)),
                _ => Ok(Kind::Opaque),
            },
            Some(&ValueType::Data { .. }) => Ok(Kind::Data),
            Some(&ValueType::Base(_)) => Ok(Kind::Literals),
            Some(&ValueType::Unknown) => Ok(Kind::Unknown),
            Some(
                &(ValueType::Record(_)
                | ValueType::List(_)
                | ValueType::Stack { .. }
                | ValueType::Capability { .. }
                | ValueType::PathUniverse(..)
                | ValueType::Path { .. }
                | ValueType::Flow { .. }
                | ValueType::Run(_)
                | ValueType::Thunk(_)
                | ValueType::Universe { .. }
                | ValueType::Lift { .. }
                | ValueType::Element { .. }
                | ValueType::Abstract(_)
                | ValueType::Session(_)
                | ValueType::StaticPi { .. }
                | ValueType::Staged { .. }
                | ValueType::Kept { .. }
                | ValueType::World(_)),
            ) => Ok(Kind::Opaque),
        }
    }

    /// The field types of `head` in a column of type `column`.
    ///
    /// # Specification
    /// - requires: `kind` is `column`'s kind.
    /// - ensures: the factors of a product, the injected summand, a
    ///   constructor's fields instantiated at the type's arguments, nothing for
    ///   unit and literals, and `arity` unknown types in an unknown column.
    /// - fails: a head that cannot stand in the column, a constructor of the
    ///   wrong arity, or an unreadable nominal declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault::IllTypedPattern`] naming `pattern`, or a refusal
    ///   reading the declaration.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each kind with a fitting head, and a pair against a
    ///   nominal type, separate the field tables from the refusal.
    /// - witness: `coverage::tests::a_nominal_type_is_complete_when_every_constructor_stands`
    /// - witness: `coverage::tests::literals_never_complete_and_nested_columns_specialise`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|fields| fields.len() == arity.0))]
    fn fields(
        &mut self,
        column: ValueTypeId,
        kind: Kind,
        head: &Head,
        arity: Arity,
        pattern: PatternId,
    ) -> Result<Vec<ValueTypeId>, CoverageFault>
    {
        let ill = CoverageFault::IllTypedPattern { pattern, column };
        let fields = match (kind, head) {
            (Kind::Unit, &Head::Unit) | (Kind::Literals, &Head::Literal(_)) => Vec::new(),
            (Kind::Product(first, second), &Head::Pair) => vec![first, second],
            (Kind::Sum(left, _), &Head::Injection(Side::Left)) => vec![left],
            (Kind::Sum(_, right), &Head::Injection(Side::Right)) => vec![right],
            (Kind::Data, &Head::Constructor(tag)) => {
                let signature = self.signature(column)?;
                let declared = signature.constructors().get(usize::from(tag)).ok_or(ill)?;
                let mut fields = Vec::with_capacity(declared.len());
                for (position, &field) in declared.iter().enumerate() {
                    let outside = former::field_outside(
                        self.context,
                        column,
                        field,
                        gandr_kernel_term::FieldPosition::from(position),
                    )
                    .map_err(CoverageFault::Refused)?;
                    // A field naming one before it is read at the unknown
                    // column: its classifier varies with the pattern there.
                    fields.push(match outside {
                        Maybe::Present(ty) => ty,
                        Maybe::Absent(_) => self.unknown,
                    });
                }
                fields
            },
            (Kind::Unknown, _) => vec![self.unknown; arity.0],
            (
                Kind::Unit,
                &(Head::Literal(_) | Head::Pair | Head::Injection(_) | Head::Constructor(_)),
            )
            | (
                Kind::Product(..),
                &(Head::Unit | Head::Literal(_) | Head::Injection(_) | Head::Constructor(_)),
            )
            | (
                Kind::Sum(..),
                &(Head::Unit | Head::Literal(_) | Head::Pair | Head::Constructor(_)),
            )
            | (Kind::Data, &(Head::Unit | Head::Literal(_) | Head::Pair | Head::Injection(_)))
            | (
                Kind::Literals,
                &(Head::Unit | Head::Pair | Head::Injection(_) | Head::Constructor(_)),
            )
            | (Kind::Opaque, _) => return Err(ill),
        };
        if fields.len() == arity.0 {
            Ok(fields)
        }
        else {
            Err(ill)
        }
    }

    /// The admitted signature of the nominal type `column`.
    ///
    /// # Specification
    /// - requires: `column` is a nominal type.
    /// - ensures: the signature admitted under its declaration.
    /// - fails: no admitted declaration or the wrong parameter count.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault::Refused`] with the formation refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nominal column with an admitted declaration reads
    ///   its constructor table.
    /// - witness: `coverage::tests::a_nominal_type_is_complete_when_every_constructor_stands`
    #[spec(ensures: |ret| ret.is_ok() <= matches!(self.context.arena().value_type(column), Some(ValueType::Data { .. })))]
    fn signature(
        &mut self,
        column: ValueTypeId,
    ) -> Result<Arc<DataSignature>, CoverageFault>
    {
        former::signature(self.context, column).map_err(CoverageFault::Refused)
    }

    /// Whether the heads in `problem`'s first column complete the column's
    /// signature, under `constructors` for an unknown column.
    ///
    /// # Specification
    /// - requires: `kind` is `column`'s kind, the first column's.
    /// - ensures: complete, with every constructor and its field types, when
    ///   the heads present name every constructor of the signature — vacuously
    ///   for a nominal type without constructors; a base type is never
    ///   complete; an unknown column follows the reading of its module
    ///   documentation.
    /// - fails: a head that cannot stand in the column, or two heads of
    ///   different formers in an unknown column.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault`] — an ill-typed head or an unreadable declaration.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete and incomplete sums, nominal types and
    ///   unknown columns under both readings separate the answers.
    /// - witness: `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`
    /// - witness: `coverage::tests::a_nominal_type_is_complete_when_every_constructor_stands`
    /// - witness: `coverage::tests::an_unknown_scrutinee_reads_the_least_and_the_widest_signature`
    #[spec(ensures: |ret| ret.is_err() || kind != Kind::Literals || ret == Ok(Completeness::Incomplete))]
    fn complete(
        &mut self,
        problem: &Problem,
        column: ValueTypeId,
        kind: Kind,
        constructors: Constructors,
    ) -> Result<Completeness, CoverageFault>
    {
        let mut present: Vec<(Head, Arity, PatternId)> = Vec::new();
        for row in &problem.rows {
            let &cell = row
                .first()
                .ok_or(CoverageFault::Refused(CheckRefusal::MachineInvariant))?;
            if let Read::Head {
                head,
                parts,
                pattern,
            } = self.read(cell)?
            {
                let arity = Arity(parts.len());
                let _fields = self.fields(column, kind, &head, arity, pattern)?;
                present.push((head, arity, pattern));
            }
        }
        let named = |wanted: &Head| present.iter().any(|entry| entry.0 == *wanted);
        let completeness = match kind {
            Kind::Unit if named(&Head::Unit) => {
                Completeness::Complete(vec![(Head::Unit, Vec::new())])
            },
            Kind::Product(first, second) if named(&Head::Pair) => {
                Completeness::Complete(vec![(Head::Pair, vec![first, second])])
            },
            Kind::Sum(left, right)
                if named(&Head::Injection(Side::Left)) && named(&Head::Injection(Side::Right)) =>
            {
                Completeness::Complete(vec![
                    (Head::Injection(Side::Left), vec![left]),
                    (Head::Injection(Side::Right), vec![right]),
                ])
            },
            Kind::Data => {
                let count = self.signature(column)?.constructors().len();
                if (0 .. count).all(|tag| named(&Head::Constructor(ConstructorTag::from(tag)))) {
                    let arms = constructor_arms(&present);
                    let mut all = Vec::with_capacity(count);
                    for tag in 0 .. count {
                        let tag = ConstructorTag::from(tag);
                        let &(arity, pattern) = arms
                            .get(&tag)
                            .ok_or(CoverageFault::Refused(CheckRefusal::MachineInvariant))?;
                        let head = Head::Constructor(tag);
                        let fields = self.fields(column, kind, &head, arity, pattern)?;
                        all.push((head, fields));
                    }
                    Completeness::Complete(all)
                }
                else {
                    Completeness::Incomplete
                }
            },
            Kind::Unknown => self.unknown_signature(column, &present, constructors)?,
            Kind::Unit | Kind::Product(..) | Kind::Sum(..) | Kind::Literals | Kind::Opaque => {
                Completeness::Incomplete
            },
        };
        Ok(completeness)
    }

    /// Whether the heads present complete an unknown column's signature.
    ///
    /// # Specification
    /// - requires: `present` lists the heads of the column, each with its arity
    ///   and pattern.
    /// - ensures: a unit or pair head completes the column, both injections do,
    ///   and a closed reading completes constructors naming every tag up to the
    ///   largest; nothing else completes it, a column without heads included.
    /// - fails: heads of two different formers.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault::IllTypedPattern`] naming the first head that
    ///   disagrees with the column's first head.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no head, a unit head, one injection and a lone
    ///   constructor under both readings separate the answers.
    /// - witness: `coverage::tests::an_unknown_scrutinee_reads_the_least_and_the_widest_signature`
    #[spec(ensures: |ret| ret.is_err() || !present.is_empty() || ret == Ok(Completeness::Incomplete))]
    fn unknown_signature(
        &self,
        column: ValueTypeId,
        present: &[(Head, Arity, PatternId)],
        constructors: Constructors,
    ) -> Result<Completeness, CoverageFault>
    {
        let Some(first) = present.first().map(|entry| &entry.0)
        else {
            return Ok(Completeness::Incomplete);
        };
        for &(ref head, _, pattern) in present {
            let agrees = matches!(
                (first, head),
                (&Head::Unit, &Head::Unit)
                    | (&Head::Literal(_), &Head::Literal(_))
                    | (&Head::Pair, &Head::Pair)
                    | (&Head::Injection(_), &Head::Injection(_))
                    | (&Head::Constructor(_), &Head::Constructor(_))
            );
            if !agrees {
                return Err(CoverageFault::IllTypedPattern { pattern, column });
            }
        }
        let named = |wanted: &Head| present.iter().any(|entry| entry.0 == *wanted);
        let unknown = self.unknown;
        Ok(match *first {
            Head::Unit => Completeness::Complete(vec![(Head::Unit, Vec::new())]),
            Head::Pair => Completeness::Complete(vec![(Head::Pair, vec![unknown, unknown])]),
            Head::Injection(_)
                if named(&Head::Injection(Side::Left)) && named(&Head::Injection(Side::Right)) =>
            {
                Completeness::Complete(vec![
                    (Head::Injection(Side::Left), vec![unknown]),
                    (Head::Injection(Side::Right), vec![unknown]),
                ])
            },
            Head::Constructor(_) if constructors == Constructors::Closed => {
                let largest = present
                    .iter()
                    .filter_map(|entry| match entry.0 {
                        Head::Constructor(tag) => Some(usize::from(tag)),
                        Head::Unit | Head::Literal(_) | Head::Pair | Head::Injection(_) => None,
                    })
                    .max()
                    .unwrap_or(0);
                let arms = constructor_arms(present);
                let mut all = Vec::new();
                for tag in 0 ..= largest {
                    let tag = ConstructorTag::from(tag);
                    let Some(&(arity, _)) = arms.get(&tag)
                    else {
                        return Ok(Completeness::Incomplete);
                    };
                    all.push((Head::Constructor(tag), vec![unknown; arity.0]));
                }
                Completeness::Complete(all)
            },
            Head::Injection(_) | Head::Constructor(_) | Head::Literal(_) => {
                Completeness::Incomplete
            },
        })
    }

    /// Specialise `problem` by `head`: keep the rows whose first cell admits
    /// it, their parts or wildcards in its place.
    ///
    /// # Specification
    /// - requires: `problem`'s vector starts with `head` or a wildcard, and
    ///   `fields` are `head`'s field types in the first column.
    /// - ensures: rows headed by another head are dropped; a wildcard row gains
    ///   one wildcard per field; a row headed by `head` gains its parts; the
    ///   columns are `fields` then the rest.
    /// - fails: a part count that disagrees with `fields`, or a malformed
    ///   problem.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault`] — an ill-typed pattern or a machine invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested pairs over injections specialise twice; a
    ///   wrong drop or a wrong part order changes the answers.
    /// - witness: `coverage::tests::literals_never_complete_and_nested_columns_specialise`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|next| next.rows.len() <= problem.rows.len()))]
    fn specialise(
        &self,
        problem: &Problem,
        head: &Head,
        fields: &[ValueTypeId],
    ) -> Result<Problem, CoverageFault>
    {
        let invariant = CoverageFault::Refused(CheckRefusal::MachineInvariant);
        let mut rows = Vec::with_capacity(problem.rows.len());
        for row in &problem.rows {
            let Some((&first, rest)) = row.split_first()
            else {
                return Err(invariant);
            };
            if let Some(specialised) = self.specialise_row(first, rest, head, fields)? {
                rows.push(specialised);
            }
        }
        let Some((&first, rest)) = problem.query.split_first()
        else {
            return Err(invariant);
        };
        let query = self
            .specialise_row(first, rest, head, fields)?
            .ok_or(invariant)?;
        let mut columns = fields.to_vec();
        columns.extend(problem.columns.get(1 ..).ok_or(invariant)?);
        Ok(Problem {
            rows,
            query,
            columns,
        })
    }

    /// Specialise one row, `first` then `rest`, by `head`.
    ///
    /// # Specification
    /// - requires: `fields` are `head`'s field types.
    /// - ensures: dropped when `first` demands another head; otherwise the
    ///   parts of `first`, or one wildcard per field, then `rest`.
    /// - fails: a part count that disagrees with `fields`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault`] — an ill-typed or dangling pattern.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as for [`Walker::specialise`].
    /// - witness: `coverage::tests::literals_never_complete_and_nested_columns_specialise`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|row| row.as_ref().is_none_or(|row| row.len() == fields.len().saturating_add(rest.len()))))]
    fn specialise_row(
        &self,
        first: Cell,
        rest: &[Cell],
        head: &Head,
        fields: &[ValueTypeId],
    ) -> Result<Option<Vec<Cell>>, CoverageFault>
    {
        let mut row = match self.read(first)? {
            Read::Anything => vec![Cell::Anything; fields.len()],
            Read::Head {
                head: named,
                parts,
                pattern,
            } => {
                if named != *head {
                    return Ok(None);
                }
                if parts.len() != fields.len() {
                    return Err(CoverageFault::IllTypedPattern {
                        pattern,
                        column: fields.first().copied().unwrap_or(self.unknown),
                    });
                }
                parts.into_iter().map(Cell::Written).collect()
            },
        };
        row.extend_from_slice(rest);
        Ok(Some(row))
    }

    /// The default matrix of `problem`: the rows whose first cell demands
    /// nothing, without it.
    ///
    /// # Specification
    /// - requires: `problem`'s vector starts with a wildcard.
    /// - ensures: the wildcard rows' tails, the vector's tail and the columns'
    ///   tail.
    /// - fails: a malformed problem or a dangling pattern.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CoverageFault`] — a dangling pattern or a machine invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an incomplete sum and a literal column take the
    ///   default; keeping a headed row would answer exhaustive wrongly.
    /// - witness: `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`
    /// - witness: `coverage::tests::literals_never_complete_and_nested_columns_specialise`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|next| next.rows.len() <= problem.rows.len()))]
    fn default(
        &self,
        problem: &Problem,
    ) -> Result<Problem, CoverageFault>
    {
        let invariant = CoverageFault::Refused(CheckRefusal::MachineInvariant);
        let mut rows = Vec::with_capacity(problem.rows.len());
        for row in &problem.rows {
            let Some((&first, rest)) = row.split_first()
            else {
                return Err(invariant);
            };
            match self.read(first)? {
                Read::Anything => rows.push(rest.to_vec()),
                Read::Head { .. } => {},
            }
        }
        Ok(Problem {
            rows,
            query: problem.query.get(1 ..).ok_or(invariant)?.to_vec(),
            columns: problem.columns.get(1 ..).ok_or(invariant)?.to_vec(),
        })
    }
}

/// The constructor heads of a column, each with the arity and pattern of
/// the first row that names it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a tag maps to the arity and pattern of the first entry of
///   `present` whose head is that constructor; a tag no entry names is absent,
///   as is every head that is not a constructor.
/// - provides: one lookup per tag where a scan of `present` per tag would grow
///   with the column's rows.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a closed data column whose rows name every constructor
///   completes with each constructor's own fields, and an unknown column
///   missing a tag below its largest stays incomplete; a map keeping a later
///   row's arity, or losing a tag, changes the answer.
/// - witness: `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`
/// - witness: `coverage::tests::an_unknown_scrutinee_reads_the_least_and_the_widest_signature`
#[spec(ensures: |arms| arms.len() <= present.len())]
fn constructor_arms(
    present: &[(Head, Arity, PatternId)]
) -> BTreeMap<ConstructorTag, (Arity, PatternId)>
{
    let mut arms = BTreeMap::new();
    for &(ref head, arity, pattern) in present {
        if let Head::Constructor(tag) = *head {
            let _first = arms.entry(tag).or_insert((arity, pattern));
        }
    }
    arms
}

#[cfg(test)]
mod tests;
