//! A function's clauses, `def f : (A, …) => C where { | p, … => c … }`: one
//! column per arrow of the stated type, compiled as one matrix over the
//! function's parameters themselves.
//!
//! **Choice.** The columns are the tree's first binders, the lambdas of the
//! parameters they match, so the tree stands directly under them and a
//! recursive function descends on a parameter its fixpoint stages, never on a
//! component of a tuple built from them. **Alternatives.** A match on the
//! tuple of the parameters, whose components no stage relates to the
//! parameters (`StageNotBelow`). **Reversal.** A column whose type depends on
//! an earlier one joins once the columns read a telescope.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::pattern::Patterns;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Answer;
use super::ArmAt;
use super::CaseForm;
use super::CaseIndex;
use super::Depth;
use super::Former;
use super::Lowerer;
use super::Over;
use super::ParameterAt;
use super::PatternAt;
use super::Reading;
use super::Roots;
use super::Row;
use super::Scrutiny;
use super::Site;
use super::Stretch;
use super::Test;
use super::Written;
use super::answered;
use super::closed;
use super::exhausted;
use super::passed;
use super::recursion;
use super::stuck;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::origin::CaseOrigin;
use crate::origin::PatternReading;
use crate::origin::scrutinised;
use crate::resolve::Frame;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::binder_site;
use crate::resolve::binder_type;
use crate::unbuilt::Unbuilt;

/// The columns a clause tail's stated type gives its clauses.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: one domain per column, left to right, each the type of the
///   parameter at the same place of `parameters`.
/// - provides: what [`Lowerer::clauses`] compiles its rows against.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — the parameter store is not retained; `columns` and
///   `clauses` interpret the coordinates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::columns`].
/// - witness: `lower::native::tests::clauses_match_one_column_per_arrow`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct Columns
{
    /// The stated type, `(A, …) => C`.
    pub stated: NodeIndex,
    /// Each column's type, `A, …`.
    pub domains: Vec<NodeIndex>,
    /// The result, `C`.
    pub result: NodeIndex,
    /// The parameters the columns bind, in the lowerer's parameter store.
    pub parameters: Stretch,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Read a clause tail's stated type, `: (A, …) => C where`, under `frame`,
    /// and bind one parameter per column.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the tail's `:`, after every written
    ///   parameter and the function's own name bound.
    /// - ensures: a value function space `(A1, …, An) => C` gives `n` columns
    ///   at `A1` to `An`, each read as a value type under `frame` and bound as
    ///   an unnamed parameter in a frame extending the one before it, and `C`
    ///   is read as the result under `frame`; any other type gives no column
    ///   and is itself the result. The cursor then stands past `where`.
    /// - provides: the parameters [`Self::clauses`] matches.
    /// - fails: a fault naming the function form for a hole or tile out of
    ///   shape, and the domain list's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The tail's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two columns over `Nat` lower to two lambdas whose
    ///   arrows are the stated type's.
    /// - witness: `lower::native::tests::clauses_match_one_column_per_arrow`
    #[spec(
        captures: before = self.parameters.len(),
        ensures: |ret| ret.as_ref().map_or(true, |columns| columns.parameters.start == before
            && columns.parameters.end == self.parameters.len()
            && columns.domains.len() == self.parameters.len().saturating_sub(before)),
    )]
    pub(in crate::lower) fn columns(
        &mut self,
        function: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Columns, LoweringRefusal<'source>>
    {
        closed(function, cursor, TileName::COLON)?;
        let stated = function.one(cursor.operands())?;
        closed(function, cursor, TileName::WHERE)?;
        let mut domains = Vec::new();
        let mut result = stated.node;
        if let Some((_, Former::ValueFunctionType)) = self.form_at(stated)? {
            let mut pieces = Pieces::new();
            read_pieces(self.pbg, self.tree, stated.node, &mut pieces)?;
            if let Maybe::Present(repaired) = pieces.repair {
                return Err(repaired.refusal(function.name));
            }
            let mut arrow = Cursor::new(&pieces.pieces, stated.span);
            let domain = function.one(arrow.operands())?;
            closed(function, &mut arrow, TileName::FAT_ARROW)?;
            let codomain = function.one(arrow.operands())?;
            let start = self.operands.len();
            let listed = self.domains(domain);
            domains.extend(self.operands.drain(start ..));
            listed?;
            result = codomain.node;
        }
        let start = self.parameters.len();
        let mut chained = frame;
        for &domain in &domains {
            self.read(domain, Reading::ValueType(frame));
            let bound = self.scope.extend_typed(
                chained,
                SurfaceName::from(""),
                domain,
                Maybe::Absent(binder_site::Absent::Unwritten),
            );
            self.parameters.push(super::super::Parameter {
                binder: domain,
                frame: bound,
                declared: Maybe::Present(domain),
                component: None,
            });
            chained = Frame::Inner(bound);
        }
        self.read(result, Reading::Result(frame));

        Ok(Columns {
            stated: stated.node,
            domains,
            result,
            parameters: Stretch {
                start,
                end: self.parameters.len(),
            },
        })
    }

    /// Read a clause tail's clauses, `{ | p1, …, pk => c … }`, matching
    /// `columns` under `frame`, the frame binding the function's own name.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the clauses' `{`; `columns` was just read
    ///   by [`Self::columns`] for the same function, whose recursion is
    ///   `recursion`.
    /// - ensures: the clauses are read as [`Self::clause_tree`] reads them,
    ///   each column against its stated type, every body answering the
    ///   function's result, under the parameters' lambdas the function mints; a
    ///   recursive function's position of its first column is the one the
    ///   staged column is counted from.
    /// - provides: the clause body of a function tail.
    /// - fails: as [`Self::clause_tree`].
    /// - panics: none.
    ///
    /// # Errors
    /// The clauses' refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — clauses over two columns compile to a switch on the
    ///   column their patterns test, and a clause of one pattern too many is
    ///   refused at it.
    /// - witness: `lower::native::tests::clauses_match_one_column_per_arrow`
    /// - witness: `lower::native::tests::a_clause_of_too_many_patterns_is_refused`
    #[spec(
        captures: before = self.cases.len(),
        ensures: |ret| ret.as_ref().map_or(true, |&index| index == CaseIndex(before) && self.cases.len() == before.saturating_add(1)),
    )]
    pub(in crate::lower) fn clauses(
        &mut self,
        function: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
        columns: &Columns,
        recursion: Maybe<ScopeId, recursion::Absent>,
    ) -> Result<CaseIndex, LoweringRefusal<'source>>
    {
        let written = Self::written_clauses(function, cursor)?;
        let recursion = match recursion {
            Maybe::Present(own) => {
                self.recursions
                    .get(&own)
                    .map_or(Maybe::Absent(recursion::Absent::Plain), |held| {
                        let first = columns
                            .parameters
                            .start
                            .saturating_sub(held.parameters.start);
                        Maybe::Present((own, ParameterAt(first)))
                    })
            },
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let shape = Shape {
            domains: columns
                .domains
                .iter()
                .map(|&domain| Maybe::Present(domain))
                .collect(),
            scrutinee: columns.stated,
            answer: Maybe::Present(Answer {
                node: columns.result,
                frame,
                over: Over::Written,
                arm: Maybe::Absent(passed::Absent::Unpassed),
            }),
            roots: Roots::Parameters(Depth(columns.domains.len())),
            recursion,
        };
        self.clause_tree(function, written, frame, &shape)
    }

    /// Classify a matching lambda, `fun { | p1, …, pk => c … }`: one lambda
    /// per column, its clauses matching their binders.
    ///
    /// # Specification
    /// - requires: `site` is a lambda in term position whose `fun` is followed
    ///   by `{`.
    /// - ensures: the columns are as many as the first clause's patterns; each
    ///   column takes the domain of the next arrow its position answers, and
    ///   the bodies answer what is left past the last, as a lambda's binder and
    ///   body take them ([`Self::arrow_of`]); a column no arrow answers is read
    ///   untyped. The clauses compile as [`Self::clause_tree`] reads them,
    ///   under one lambda per column the tree mints itself, and the lambda is
    ///   planned as that tree.
    /// - provides: the matching lambda.
    /// - fails: the wrong-sort refusal where no bridge reaches a computation;
    ///   as [`Self::clause_tree`]; the walk's refusal reading an arrow.
    /// - panics: none.
    ///
    /// # Errors
    /// The lambda's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a matching lambda over two columns lowers to two
    ///   lambdas over its tree.
    /// - witness: `lower::native::tests::a_matching_lambda_binds_one_lambda_per_column`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(site.at.node), Some(&super::Plan::Case(_))))]
    pub(in crate::lower) fn matching_lambda(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, super::Produced::Computation)?;
        let _keyword = cursor.tile(TileName::FUN);
        let written = Self::written_clauses(site, &mut cursor)?;
        let width = written
            .clauses
            .first()
            .map_or(0, |clause| clause.patterns.len());
        let scrutinee = written
            .clauses
            .first()
            .and_then(|clause| clause.patterns.first())
            .map_or(site.at.node, |pattern| pattern.node);
        let mut answer = self
            .answers
            .get(&site.at.node)
            .or_else(|| self.thunked.get(&site.at.node))
            .copied();
        let mut domains = Vec::with_capacity(width);
        for _column in 0 .. width {
            let arrow = match answer {
                Some(held) => self.arrow_of(held)?,
                None => None,
            };
            if let Some((domain, rest)) = arrow {
                domains.push(Maybe::Present(domain));
                answer = Some(rest);
            }
            else {
                domains.push(Maybe::Absent(binder_type::Absent::Untyped));
                answer = None;
            }
        }
        let shape = Shape {
            domains,
            scrutinee,
            answer: answer.map_or(Maybe::Absent(answered::Absent::Unstated), Maybe::Present),
            roots: Roots::Lambdas(Depth(width)),
            recursion: Maybe::Absent(recursion::Absent::Plain),
        };
        let case = self.clause_tree(site, written, frame, &shape)?;
        self.plan(site, super::Plan::Case(case));

        Ok(())
    }

    /// Read the clauses `{ | p1, …, pk if g => c … }` at `cursor`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the clauses' `{`, which the form's last
    ///   piece closes.
    /// - ensures: each clause's patterns in order, its guard when it writes
    ///   one, keyed by its place, and its body; the cursor past the `}` with
    ///   nothing after it.
    /// - provides: the one reading of a clause block's pieces.
    /// - fails: a fault naming `site`'s form for a hole or a tile out of place.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::clause_tree`].
    /// - witness: `lower::native::tests::a_guard_reads_its_clause_s_variables`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |written| written.clauses.iter().all(|clause| !clause.patterns.is_empty())))]
    fn written_clauses(
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<WrittenClauses, LoweringRefusal<'source>>
    {
        closed(site, cursor, TileName::BRACE_OPEN)?;
        let mut written = WrittenClauses::default();
        while let Maybe::Absent(_) = cursor.tile(TileName::BRACE_CLOSE) {
            closed(site, cursor, TileName::ARM_BAR)?;
            let mut patterns = Vec::from([site.one(cursor.operands())?]);
            while let Maybe::Present(_) = cursor.tile(TileName::COMMA) {
                patterns.push(site.one(cursor.operands())?);
            }
            if let Maybe::Present(_) = cursor.tile(TileName::IF) {
                let guard = site.one(cursor.operands())?;
                let _first = written
                    .guards
                    .insert(ArmAt(written.clauses.len()), guard.node);
            }
            closed(site, cursor, TileName::FAT_ARROW)?;
            let body = site.one(cursor.operands())?;
            written.clauses.push(Clause { patterns, body });
        }
        exhausted(site, cursor)?;

        Ok(written)
    }

    /// Compile `written`, clauses of the form at `site`, to one tree over the
    /// columns `shape` states, its bodies read under `frame`.
    ///
    /// # Specification
    /// - requires: `written` was just read at `site` by
    ///   [`Self::written_clauses`]; `frame` is the frame the clauses stand in,
    ///   outside their columns.
    /// - ensures: each clause's patterns are read, one per column against the
    ///   column's type where one is stated, an or-pattern in a column giving
    ///   one row per choice of alternative, and the rows compile to one tree
    ///   under one binder per column, a guarded clause's leaf behind its guard;
    ///   each body and guard is read as a computation under `frame` and the
    ///   clause's variables, the body answering `shape`'s answer and ending the
    ///   body the clauses write; a recursion stages the column its tree first
    ///   switches on, counted from its first column, and every body records
    ///   that position as the one its claims descend on. The tree is stored and
    ///   its index returned.
    /// - provides: the clauses of a function and of a matching lambda.
    /// - fails: a fault naming `site`'s form for a clause of other than one
    ///   pattern per column; an or-pattern binding a variable; a pattern's own
    ///   refusal; a non-exhaustive tree; a tree eliminating native data with no
    ///   answer, as unannotated.
    /// - panics: none.
    ///
    /// # Errors
    /// The clauses' refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::clauses`] and [`Self::matching_lambda`].
    /// - witness: `lower::native::tests::clauses_match_one_column_per_arrow`
    /// - witness: `lower::native::tests::a_guard_reads_its_clause_s_variables`
    #[spec(
        captures: before = self.cases.len(),
        ensures: |ret| ret.as_ref().map_or(true, |&index| index == CaseIndex(before) && self.cases.len() == before.saturating_add(1)),
    )]
    fn clause_tree(
        &mut self,
        site: Site,
        written: WrittenClauses,
        frame: Frame,
        shape: &Shape,
    ) -> Result<CaseIndex, LoweringRefusal<'source>>
    {
        let WrittenClauses { clauses, guards } = written;
        let width = shape.domains.len();
        for clause in &clauses {
            if let Some(extra) = clause.patterns.get(width) {
                return Err(site.fault(extra.span, FormFault::ExtraOperand));
            }
            if clause.patterns.len() < width
                && let Some(last) = clause.patterns.last()
            {
                return Err(site.fault(last.span, FormFault::MissingOperand));
            }
        }
        let mut patterns = Written::default();
        let mut rows = Vec::with_capacity(clauses.len());
        let mut variables: Vec<Vec<Placed>> = Vec::with_capacity(clauses.len());
        let mut roots = Vec::new();
        // Each column's alternatives; a row per choice of one in each.
        let mut choices: Vec<Vec<PatternAt>> = Vec::with_capacity(width);
        for (arm, clause) in clauses.iter().enumerate() {
            let arm = ArmAt(arm);
            let mut named = Vec::new();
            choices.clear();
            for (&pattern, &domain) in clause.patterns.iter().zip(&shape.domains) {
                let alternatives = self.alternatives(pattern)?;
                let several = alternatives.len() > 1;
                let mut read = Vec::with_capacity(alternatives.len());
                for (place, alternative) in alternatives.into_iter().enumerate() {
                    let before = named.len();
                    let root =
                        self.pattern(site, alternative, domain, &mut patterns, &mut named)?;
                    if several && named.len() > before {
                        return Err(LoweringRefusal::OutOfFragment {
                            span: pattern.span,
                            form: FormName::OR_PATTERN,
                            sort: site.reading.sort(),
                            boundary: FragmentBoundary::Unadmitted(Unbuilt::OrPattern),
                        });
                    }
                    if several && place == 0_usize {
                        patterns
                            .spelled
                            .push((root, pattern.span, PatternReading::Matched));
                    }
                    roots.push((arm, root, alternative.node, clause.body.node));
                    read.push(root);
                }
                choices.push(read);
            }
            let mut combined: Vec<Vec<PatternAt>> = Vec::from([Vec::new()]);
            for column in &choices {
                combined = combined
                    .iter()
                    .flat_map(|prefix| {
                        column.iter().map(move |&root| {
                            let mut row = prefix.clone();
                            row.push(root);
                            row
                        })
                    })
                    .collect();
            }
            rows.extend(combined.into_iter().map(|columns| Row {
                columns,
                arm,
                bindings: Vec::new(),
                stuck: Maybe::Absent(stuck::Absent::Decided),
            }));
            variables.push(named);
        }
        let guarded = guards.keys().copied().collect();
        let tests = self.compile(site, &patterns, (rows, Depth(width), guarded))?;
        let eliminates = tests.iter().any(|test| {
            matches!(
                *test,
                Test::Data { .. }
                    | Test::Split {
                        dependent: super::Dependent(true),
                        ..
                    }
            )
        });
        if eliminates && matches!(shape.answer, Maybe::Absent(_)) {
            return Err(site.out(FragmentBoundary::Unannotated));
        }
        let mut kept = CaseOrigin {
            written: site.at.node,
            scrutinee: shape.scrutinee,
            scrutinised: Maybe::Absent(scrutinised::Absent::Unminted),
            patterns: Patterns::new(),
            arms: Vec::new(),
            spans: Vec::new(),
            labelled: Vec::new(),
        };
        Self::keep(&patterns, &roots, &mut kept);
        // The first column the tree switches on is the one a recursive
        // function's fixpoint stages.
        let staged = tests
            .iter()
            .find_map(|test| {
                if let Test::Data { level, .. } = *test
                    && (1 ..= width).contains(&level.0)
                {
                    Some(level.0.saturating_sub(1))
                }
                else {
                    None
                }
            })
            .unwrap_or_default();
        let scrutiny = match shape.recursion {
            Maybe::Present((own, ParameterAt(first))) => match self.recursions.get_mut(&own) {
                Some(held) => {
                    let position = ParameterAt(first.saturating_add(staged));
                    held.staged = position;
                    Some(Scrutiny {
                        recursion: own,
                        position,
                    })
                },
                None => None,
            },
            Maybe::Absent(_) => None,
        };
        let mut bodies = Vec::with_capacity(clauses.len());
        for (arm, (clause, bound)) in clauses.iter().zip(&variables).enumerate() {
            let mut inner = frame;
            for &binder in bound {
                let name = SurfaceName::from(self.text_at(binder));
                self.note_binder(binder, name)?;
                let written = Maybe::Present(binder.span);
                let id = match self.pattern_stated.get(&binder.node) {
                    Some(&stated) => self.scope.extend_typed(inner, name, stated, written),
                    None => self.scope.extend(inner, name, written),
                };
                inner = Frame::Inner(id);
            }
            let body = clause.body.node;
            self.read(body, Reading::Computation(inner));
            // A guard reads the clause's variables as its body does, and is
            // tested as a conditional's condition is.
            if let Some(&guard) = guards.get(&ArmAt(arm)) {
                let _tested = self.tested.insert(guard);
                self.read(guard, Reading::Computation(inner));
            }
            if let Maybe::Present(answer) = shape.answer {
                let _first = self.answers.insert(body, answer);
            }
            if let Some(scrutiny) = scrutiny {
                let _first = self.scrutinised.insert(body, scrutiny);
            }
            let end = super::super::Block {
                statements: Stretch {
                    start: self.statements.len(),
                    end: self.statements.len(),
                },
                last: body,
            };
            self.open_body(site, end, shape.answer)?;
            bodies.push(body);
        }
        let index = CaseIndex(self.cases.len());
        self.cases.push(CaseForm {
            scrutinee: shape.scrutinee,
            roots: shape.roots,
            frame,
            answer: shape.answer,
            ascribed: Maybe::Absent(answered::Absent::Unstated),
            bodies,
            guards,
            tests,
            loops: Vec::new(),
            origin: kept,
            variables,
        });

        Ok(index)
    }
}

/// One clause, `| p1, …, pk if g => c`, as written.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Clause
{
    /// The patterns, one per column.
    patterns: Vec<Placed>,
    /// The body.
    body: Placed,
}

/// A clause block, as written.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct WrittenClauses
{
    /// The clauses, in order.
    clauses: Vec<Clause>,
    /// Each guarded clause's guard, by the clause's place.
    guards: BTreeMap<ArmAt, NodeIndex>,
}

/// What clauses match and answer.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Shape
{
    /// Each column's type, where one is stated.
    domains: Vec<Maybe<NodeIndex, binder_type::Absent>>,
    /// The node the case's record names for its columns.
    scrutinee: NodeIndex,
    /// What every body answers.
    answer: Maybe<Answer, answered::Absent>,
    /// The binders the tree stands under.
    roots: Roots,
    /// The recursion the clauses define, and the place of their first column
    /// among its parameters.
    recursion: Maybe<(ScopeId, ParameterAt), recursion::Absent>,
}
