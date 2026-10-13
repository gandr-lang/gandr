//! Element identity in the lowering: the path type `Path(A, a, b)`, its
//! reflexivity `here(a)`, function extensionality `funext(f, g)`, universe
//! equivalence `equiv(f, g)`, transport `transport(\X. T, p, v)` and its
//! dependent form `transport(M, p, z₀, q, v)`, and `back`, `then` and `cong`,
//! each unfolded to the transport it derives; and the native list's
//! constructors `nil` and `cons(h, t)`, the recursive motive transport first
//! moves along a universe path.
//!
//! # Endpoints are values, and a computation is the value it returns
//!
//! A path type's endpoints, and the point of `here`, are terms the grammar
//! parses as expressions, and the lowering reads them where a value is read.
//! A computation standing there, or anywhere under one where a value is read
//! — `mul(x, y)`, `n + 1`, the inner call of `mul(mul(x, y), z)` — is not
//! refused: it reaches the position as the value it returns, a compound
//! endpoint the checker compares by what it computes and admits only when
//! it is pure. The alternative, refusing every endpoint that is not a value,
//! is the reading that made `Path(Integer, mul(neutral, x), x)` unwritable; a
//! statement the author must name first, `run m <- mul(neutral, x)`, cannot
//! stand in a type. Reversal: an endpoint language with its own let, which
//! would bind the computation once and reuse it in both the type and the
//! body.
//!
//! An endpoint is a term inside a type, so a parameter it names is read at
//! its index in the type's telescope and makes the arrow binding it
//! dependent, as a parameter a later type decodes does. The point of `here`
//! is a term of the body and reads its parameters there.
//!
//! # The identity vocabulary is names nothing else binds
//!
//! `here`, `funext`, `equiv`, `transport`, `back` and `cong` are spelled as
//! ordinary calls and resolved after every binder and every earlier
//! declaration, so a parameter or a definition of the same name shadows them,
//! as it shadows a prelude primitive; `then` is the grammar's own infix tile.
//! Reserving the names outright was the alternative; it would break every
//! program that already binds one. Reversal: a namespace for the identity
//! vocabulary, `Path.here`, once the namespaces carry formers rather than
//! primitives. The native list's `nil` and `cons` resolve the same way, the
//! spellings the printer already writes them with; a list literal `[a, b]`,
//! which the grammar parses, was the alternative, declined because a cell over
//! a tail that is no literal has no literal spelling to print back.
//!
//! `funext(f, g)` and `equiv(f, g)` stand as values, as `here` does, and read
//! both functions as values; the checker synthesises the path type from the
//! first and decides it by computation (`gandr_core_checker`'s funext and
//! equiv rules). Univalence at a stratum, `ua[n, k](a, b, f, g)`, is the same
//! kind of name with its stratum in the head; [`super::ua`] lowers it.
//!
//! # `transport` states its motive
//!
//! `transport(\X. T, p, v)` moves `v : T[a/X]` along `p : Path(A, a, b)` to
//! `T[b/X]`. Its motive is written as a static abstraction whose body is the
//! family over the path's carrier, so `\X. List(X)` over a universe path is
//! `y. List(El y)`; the transport stands as a computation. A motive written
//! any other way is refused as unannotated. The alternative, inferring the
//! motive from the expected type, is higher-order unification, which the
//! checker does not do. Reversal: a checker that elaborates the motive from
//! the operand's and the answer's types.
//!
//! # A derived operation reads its motive off the path type it answers
//!
//! `back(p)`, `p then q` and `cong(f, p)` are transports whose motive names
//! the carrier and the endpoint that stays fixed (`gandr_core_term::identity`).
//! The lowering reads both off the path type the position answers — the
//! function's result or the match's answer, written `-F Path(A, a, b)` or
//! `Path(A, a, b)` — relocated to where the operation stands. An operation
//! standing where no written path type is answered is refused as
//! unannotated. The alternative, synthesising the path's own type in the
//! lowering, duplicates the checker's work. Reversal: a checker that
//! elaborates a derived operation against its expected type makes the
//! written answer optional.
//!
//! # A dependent `transport` reads its motive as a thunked telescope
//!
//! Five operands, `transport(+U ((y : A) -> (z : B) -> -F C), p, z₀, q, v)`,
//! spell the transport whose motive depends on the path's endpoint `y` and on
//! an element `z` of the family over it (`gandr_core_term::identity`):
//! `p : Path(A, a, b)`, `z₀ : B[a]`, `q` an identity over `p` from `z₀`
//! transported along it to some `z₁ : B[b]`, and `v : C[a, z₀]`; it returns
//! `C[b, z₁]`. The motive is read as a value type, the thunk of the
//! computation type `Π (y : A). Π (z : B). -F C` that the telescope alias
//! `(y : A, z : B) => C` abbreviates, and the transport takes the computation
//! type under the thunk. The alias itself cannot stand as an argument, where
//! the grammar reads `(` as a tuple or an annotation, so the motive is written
//! in the spelling the alias stands for. An entry written as a plain arrow,
//! `+U (A -> B -> -F C)`, is made dependent, its codomain moved under the
//! binder it then stands under. Any other motive is minted as written, a value
//! type other than a thunk as the returner over it, and the checker refuses
//! its shape by name. The alternative, a binder form of its own for motives,
//! would duplicate the telescope the dependent arrow already reads; the one
//! binder transport's static abstraction, `\X. T`, binds a type, not a point
//! and an element. Reversal: a type-level lambda in argument position would
//! write the motive as the family it is. `J` is not a primitive: it is this
//! transport in the singleton,
//! `transport(+U ((y : A) -> (q : Path(A, a, y)) -> -F C), p, here(a),
//! here(p), d)`, written as an ordinary definition.
//!
//! # Reflexivity is not a pattern
//!
//! A path is used by transport and by nothing else. `here` written as a
//! pattern would be a second eliminator, and matching a path whose endpoints
//! are fixed against it is axiom K, which univalence refutes; it is refused
//! as [`LoweringRefusal::WithoutK`]. Reversal: none in this vocabulary — `J`
//! is derived as transport in the singleton, which is what a match on `here`
//! with a free endpoint would mean, and is written with `transport`.

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_kernel_strata::Level;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Former;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Sink;
use super::Site;
use super::arguments;
use super::closed;
use super::exhausted;
use super::lowered;
use super::native::Answer;
use super::native::record_since;
use super::native::rooted;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Piece;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::TypeFormer;
use crate::resolve::type_former;

#[cfg(test)]
pub(super) mod tests;

/// Reflexivity's spelling, which no pattern may take.
pub(super) const HERE: &str = "here";

/// The empty native list's spelling, a name resolved after every binder and
/// earlier declaration.
pub(super) const NIL: &str = "nil";

quenchant_shape::reason_enum! {
    /// Why a call's head names no identity operation.
    pub mod spelled {
        /// The head is not one of the identity operations' names, free.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The head is no bare name or `ua[n, k]` instantiation, spells
            /// another name, or names a binder or an earlier declaration that
            /// shadows the operation.
            Unspelled,
        }
    }
}

/// An identity operation a call's head spells.
///
/// # Specification
/// - ensures: reflexivity, function and universe extensionality, transport in a
///   one-binder motive or a telescope, the two derived operations, and the
///   native list cell, spelled as calls.
/// - executable: none — a tag holds no head to check its spelling against.
///
/// # Adequacy
/// - hypothesis: L3 — each spelling lowers to its own former.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
/// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
/// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Operation
{
    /// `here(a)`.
    Here,
    /// `funext(f, g)`.
    Funext,
    /// `equiv(f, g)`.
    Equiv,
    /// `transport(\X. T, p, v)`.
    Transport,
    /// `back(p)`.
    Back,
    /// `cong(f, p)`.
    Cong,
    /// `cons(h, t)`.
    Cons,
}

/// The identity operations a call's head spells, by name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each operation once, under its surface name.
/// - provides: the table [`Lowerer::identity_head`] resolves against.
/// - fails: never.
/// - panics: none.
/// - executable: none — the specification attribute does not support const
///   items; the head's reader checks the spelling it resolved.
///
/// # Adequacy
/// - hypothesis: L3 — every row is spelled by a witness.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
/// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
/// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
const SPELLED: [(&str, Operation); 7] = [
    (HERE, Operation::Here),
    ("funext", Operation::Funext),
    ("equiv", Operation::Equiv),
    ("transport", Operation::Transport),
    ("back", Operation::Back),
    ("cong", Operation::Cong),
    ("cons", Operation::Cons),
];

/// A derived operation's written operands.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each operand is the syntax node it was written as.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — each operation transports along its own path.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Derivation
{
    /// `back(path)`.
    Back
    {
        /// The path reversed.
        path: NodeIndex,
    },
    /// `first then second`.
    Then
    {
        /// The path composed first.
        first: NodeIndex,
        /// The path composed second, the one transported along.
        second: NodeIndex,
    },
    /// `cong(function, path)`.
    Cong
    {
        /// The map applied along the path.
        function: NodeIndex,
        /// The path mapped.
        path: NodeIndex,
    },
}

/// A derived operation as the classification planned it: its operands, the
/// path type its position answers, and the frame it stands under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the answer is a written path type, under a returner or not.
/// - executable: none — the plan holds no tree to check its answer against.
///
/// # Adequacy
/// - hypothesis: L3 — each operation's motive is read off its answer.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Derived
{
    /// The operation and its operands.
    derivation: Derivation,
    /// The path type the position answers.
    answer: Answer,
    /// The frame the operation stands under.
    frame: Frame,
}

/// A dependent transport's written operands and the frame it stands under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each operand is the syntax node it was written as.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — each operand reaches its own slot of the transport.
/// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Transported
{
    /// The motive, written as a telescope.
    motive: NodeIndex,
    /// The path transported along.
    path: NodeIndex,
    /// The family element at the path's source.
    start: NodeIndex,
    /// The identity over the path.
    over: NodeIndex,
    /// The value transported.
    value: NodeIndex,
    /// The frame the transport stands under.
    frame: Frame,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify a path type, `Path(A, a, b)`.
    ///
    /// # Specification
    /// - requires: `site` is a path type in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: the form stands as a value type, reads its carrier as a value
    ///   type and its two endpoints as endpoints standing inside a type, all
    ///   under its own frame, and is planned over the three.
    /// - provides: element identity's type former.
    /// - fails: yields the wrong-sort refusal where no value type is read, and
    ///   a misplaced-tile or extra-operand fault for a form out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed path type and one whose endpoint is a
    ///   computation, each read back out of the arena.
    /// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    /// - witness: `lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Path(carrier, left, right))
                        if self.reading(carrier) == Reading::ValueType(site.reading.frame())
                            && self.reading(left) == Reading::Value(site.reading.frame())
                            && self.reading(right) == Reading::Value(site.reading.frame())
                            && self.in_type.contains(&left)
                            && self.in_type.contains(&right)
                            && self.at_endpoint.contains(&left)
                            && self.at_endpoint.contains(&right)
                )
        },
    )]
    pub(super) fn path_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        closed(site, &mut cursor, TileName::PATH)?;
        closed(site, &mut cursor, TileName::PAREN_OPEN)?;
        let carrier = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::COMMA)?;
        let left = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::COMMA)?;
        let right = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        exhausted(site, &cursor)?;
        self.read(carrier.node, Reading::ValueType(frame));
        self.read(left.node, Reading::Value(frame));
        self.read(right.node, Reading::Value(frame));
        self.in_type.extend([left.node, right.node]);
        self.at_endpoint.extend([left.node, right.node]);
        self.plan(site, Plan::Path(carrier.node, left.node, right.node));

        Ok(())
    }

    /// The identity operation `head`, the head of a call written at `site`,
    /// names.
    ///
    /// # Specification
    /// - requires: `head` is the first operand of the call at `site`.
    /// - ensures: the operation a bare name spells when no binder and no
    ///   earlier declaration carries that name; the unspelled absence for any
    ///   other head.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold; the refusals the name's resolution yields.
    /// - panics: none.
    ///
    /// # Errors
    /// The resolution's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a free spelling and a bound one take their own
    ///   readings.
    /// - witness: `lower::identity::tests::a_bound_name_shadows_an_identity_operation`
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body searches the fixed spelling table for the head's name once; the check searches it once more"
        )
    )]
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(operation)) => SPELLED
                .iter()
                .any(|&(spelling, spelled)| spelled == operation && self.text_at(head).as_ref() == spelling),
            | _ => true,
        },
    )]
    pub(super) fn identity_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Operation, spelled::Absent>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(head.node)
        else {
            return Ok(Maybe::Absent(spelled::Absent::Unspelled));
        };
        let Shape::Form {
            former: Former::Name,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Ok(Maybe::Absent(spelled::Absent::Unspelled));
        };
        let name = self.name_at(head);
        let Some(&(_spelling, operation)) = SPELLED
            .iter()
            .find(|&&(spelling, _operation)| name.as_ref() == spelling)
        else {
            return Ok(Maybe::Absent(spelled::Absent::Unspelled));
        };
        let named = Site { at: head, ..site };
        if let Maybe::Present(_shadowed) = self.resolve_name(named, site.reading.frame(), name)? {
            return Ok(Maybe::Absent(spelled::Absent::Unspelled));
        }

        Ok(Maybe::Present(operation))
    }

    /// Classify the call of `operation` at `site`, its head read, the cursor
    /// at its arguments.
    ///
    /// # Specification
    /// - requires: `operation` is what the call's head spells.
    /// - ensures: `here(a)` stands as a value reading its point as a value at
    ///   an endpoint; `funext(f, g)`, `equiv(f, g)` and `cons(h, t)` stand as
    ///   values reading both operands as values; `transport(\X. T, p, v)`
    ///   stands as a computation reading its motive, path and value as values,
    ///   and `transport(M, p, z₀, q, v)` as a computation reading its motive as
    ///   a value type and the other four as values; `back(p)` and `cong(f, p)`
    ///   stand as computations derived as [`Self::derive`] does. Every operand
    ///   is read under the site's frame.
    /// - fails: the wrong-sort refusal where the operation's sort is not read;
    ///   the arity refusal for other than one argument to `here` or `back`, two
    ///   to `funext`, `equiv`, `cons` or `cong`, and three or five to
    ///   `transport`; the unannotated refusal for a three-operand transport
    ///   whose motive is no static abstraction; [`Self::derive`]'s refusal; the
    ///   argument list's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation at its own arity, and `here` at two,
    ///   each asserted as the planned former or the exact refusal.
    /// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    /// - witness: `lower::identity::tests::funext_lowers_to_its_former`
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    /// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| {
            self.operands.len() == start
                && (ret.is_err()
                    || match (operation, self.plans.get(usize::from(site.at.node))) {
                        | (Operation::Here, Some(&Plan::Here(point))) => self.at_endpoint.contains(&point),
                        | (Operation::Funext, Some(&Plan::Funext(..)))
                        | (Operation::Equiv, Some(&Plan::Equiv(..)))
                        | (Operation::Cons, Some(&Plan::ListCons(..)))
                        | (Operation::Transport, Some(&(Plan::Transport(..) | Plan::TelescopeTransport(_))))
                        | (Operation::Back | Operation::Cong, Some(&Plan::Derived(_))) => true,
                        | _ => false,
                    })
        },
    )]
    pub(super) fn identity_call(
        &mut self,
        site: Site,
        operation: Operation,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let produced = match operation {
            | Operation::Here | Operation::Funext | Operation::Equiv | Operation::Cons => {
                Produced::Value
            },
            | Operation::Back | Operation::Cong | Operation::Transport => Produced::Computation,
        };
        let frame = self.require(site, produced)?;
        let start = self.operands.len();
        let read = arguments(site, &mut cursor, &mut self.operands);
        let count = self.operands.len().saturating_sub(start);
        let first = self.operands.get(start).copied();
        let second = self.operands.get(start.saturating_add(1_usize)).copied();
        let third = self.operands.get(start.saturating_add(2_usize)).copied();
        let written = self
            .operands
            .get(start ..)
            .and_then(|written| <[NodeIndex; 5]>::try_from(written).ok());
        self.operands.truncate(start);
        read?;
        match (operation, count, first, second, third) {
            | (Operation::Here, 1_usize, Some(point), ..) => {
                self.read(point, Reading::Value(frame));
                let _marked = self.at_endpoint.insert(point);
                self.plan(site, Plan::Here(point));
                Ok(())
            },
            | (
                Operation::Funext | Operation::Equiv | Operation::Cons,
                2_usize,
                Some(left),
                Some(right),
                _,
            ) => {
                self.read(left, Reading::Value(frame));
                self.read(right, Reading::Value(frame));
                let plan = match operation {
                    | Operation::Equiv => Plan::Equiv(left, right),
                    | Operation::Cons => Plan::ListCons(left, right),
                    | _ => Plan::Funext(left, right),
                };
                self.plan(site, plan);
                Ok(())
            },
            | (Operation::Transport, 3_usize, Some(motive), Some(path), Some(value)) => {
                self.stated_motive(site, motive)?;
                for operand in [motive, path, value] {
                    self.read(operand, Reading::Value(frame));
                }
                self.plan(site, Plan::Transport(motive, path, value));
                Ok(())
            },
            | (Operation::Transport, 5_usize, ..) => match written {
                | Some([motive, path, departure, over, value]) => {
                    self.read(motive, Reading::ValueType(frame));
                    for operand in [path, departure, over, value] {
                        self.read(operand, Reading::Value(frame));
                    }
                    self.plan(
                        site,
                        Plan::TelescopeTransport(Transported {
                            motive,
                            path,
                            start: departure,
                            over,
                            value,
                            frame,
                        }),
                    );
                    Ok(())
                },
                | None => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
            },
            | (Operation::Back, 1_usize, Some(path), ..) => {
                self.derive(site, frame, Derivation::Back { path })
            },
            | (Operation::Cong, 2_usize, Some(function), Some(path), _) => {
                self.derive(site, frame, Derivation::Cong { function, path })
            },
            | _ => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
        }
    }

    /// Require a transport's motive to be written as a static abstraction.
    ///
    /// # Specification
    /// - requires: `motive` is the first operand of the transport at `site`.
    /// - ensures: `Ok` exactly when the operand is a static abstraction, `\X.
    ///   T`, whose body is the family the transport moves its value in.
    /// - fails: the unannotated refusal at `site` for any other operand; the
    ///   refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The motive's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an abstraction motive lowers and a named one is
    ///   refused.
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    #[spec(ensures: |ret| ret.is_err() || matches!(
        self.tree.node(motive).map(|node| shape_of(self.pbg, node)),
        Some(Ok(Shape::Form { former: Former::StaticAbstraction, .. }))
    ))]
    fn stated_motive(
        &self,
        site: Site,
        motive: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let unannotated = site.out(FragmentBoundary::Unannotated);
        let Some(node) = self.tree.node(motive)
        else {
            return Err(unannotated);
        };
        match shape_of(self.pbg, node)? {
            | Shape::Form {
                former: Former::StaticAbstraction,
                ..
            } => Ok(()),
            | _ => Err(unannotated),
        }
    }

    /// Classify the derived operation `derivation`, standing as a computation
    /// at `site` under `frame`.
    ///
    /// # Specification
    /// - requires: `site` stands as a computation under `frame`.
    /// - ensures: every operand is read as a value under `frame`, and the
    ///   operation is planned against the path type its position answers.
    /// - fails: the unannotated refusal where the position answers no type, or
    ///   one that is not a written path type under at most a returner and
    ///   parentheses; the allowance refusal from that walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The operation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation under a path answer, and one under an
    ///   answer that is no path type.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::a_derived_operation_needs_a_written_path_answer`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Derived(planned)) if planned.derivation == derivation && planned.frame == frame
                )
        },
    )]
    pub(super) fn derive(
        &mut self,
        site: Site,
        frame: Frame,
        derivation: Derivation,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(&answer) = self.answers.get(&site.at.node)
        else {
            return Err(site.out(FragmentBoundary::Unannotated));
        };
        self.answers_path(site, answer.node)?;
        match derivation {
            | Derivation::Back { path } => self.read(path, Reading::Value(frame)),
            | Derivation::Then { first, second }
            | Derivation::Cong {
                function: first,
                path: second,
            } => {
                self.read(first, Reading::Value(frame));
                self.read(second, Reading::Value(frame));
            },
        }
        self.plan(
            site,
            Plan::Derived(Derived {
                derivation,
                answer,
                frame,
            }),
        );

        Ok(())
    }

    /// Require the type written at `answer` to be a path type, under at most a
    /// returner and any parentheses.
    ///
    /// # Specification
    /// - requires: `answer` is a node read where a result is read.
    /// - ensures: `Ok` exactly when the walk from `answer` through
    ///   parenthesised types and one `-F` reaches a path type.
    /// - provides: the classification-time guarantee that a derived operation's
    ///   answer mints as `F (Path(A, a, b))`.
    /// - fails: the unannotated refusal at `site` when the walk reaches another
    ///   form; [`LoweringRefusal::BudgetExceeded`] when it outruns the
    ///   allowance; the refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Termination
    /// Every turn spends one unit of the lowerer's allowance and steps to the
    /// operand of the node it read, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `-F Path(…)`, a parenthesised `-F(Path(…))`, and an
    ///   integer answer.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::a_derived_operation_needs_a_written_path_answer`
    #[spec(captures: before = self.fuel.remaining, ensures: self.fuel.remaining <= before)]
    fn answers_path(
        &mut self,
        site: Site,
        answer: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut position = answer;
        let mut returned = false;
        let unannotated = site.out(FragmentBoundary::Unannotated);
        loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(position)
            else {
                return Err(unannotated);
            };
            let Shape::Form { former, .. } = shape_of(self.pbg, node)?
            else {
                return Err(unannotated);
            };
            let wrapped = match former {
                | Former::PathType => return Ok(()),
                | Former::ReturnerType if !returned => {
                    returned = true;
                    true
                },
                | Former::ParenthesizedType => false,
                | _ => return Err(unannotated),
            };
            let mut scratch = core::mem::take(&mut self.scratch);
            let read = read_pieces(self.pbg, self.tree, position, &mut scratch);
            let mut operands = scratch.pieces.iter().filter_map(|piece| match *piece {
                | Piece::Operand(operand) => Some(operand.node),
                | Piece::Tile { .. } => None,
            });
            let inner = match (operands.next(), operands.next()) {
                | (Some(inner), None) => Some(inner),
                | _ => None,
            };
            let keyword = scratch.pieces.iter().find_map(|piece| match *piece {
                | Piece::Tile { at, .. } => Some(at),
                | Piece::Operand(_) => None,
            });
            self.scratch = scratch;
            read?;
            let returner = !wrapped
                || keyword.is_some_and(|at| {
                    type_former(self.name_at(at)) == Maybe::Present(TypeFormer::Returner)
                });
            match inner {
                | Some(inner) if returner => position = inner,
                | _ => return Err(unannotated),
            }
        }
    }

    /// Mint the derived operation `derived`: the transport it unfolds to.
    ///
    /// # Specification
    /// - requires: the operands and the answer are already minted or absent.
    /// - ensures: the answer, a returner over `Path(A, a, b)` relocated to the
    ///   operation's frame, gives the carrier and the endpoints: `back(p)` is
    ///   `tr(y. Path(A, y, b), p, here(b))`, `p then q` is `tr(y. Path(A, a,
    ///   y), q, p)` and `cong(f, p)` is `tr(y. Path(A, a, ⟨force f y⟩), p,
    ///   here(a))`. The transport carries the written origin and every other
    ///   node minted for it the inserted identity origin. Nothing when an
    ///   operand or the answer did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation read back out of the arena and
    ///   checked.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_derived(
        &self,
        derived: Derived,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = match self.comp_type_at(derived.answer.node) {
            | Maybe::Present(written) => written,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let (first, second) = match derived.derivation {
            | Derivation::Back { path } => match self.value_at(path) {
                | Maybe::Present(path) => (path, path),
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            | Derivation::Then { first, second }
            | Derivation::Cong {
                function: first,
                path: second,
            } => match (self.value_at(first), self.value_at(second)) {
                | (Maybe::Present(first), Maybe::Present(second)) => (first, second),
                | (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                    return Maybe::Absent(reason);
                },
            },
        };
        let mark = sink.arena.watermark();
        let gap = self
            .scope
            .telescope_binders(derived.frame)
            .count()
            .saturating_sub(self.scope.telescope_binders(derived.answer.frame).count());
        let lift = Binders::from(u32::try_from(gap).unwrap_or(u32::MAX));
        let answered = self.relocate(sink.arena, written, derived.answer.frame, lift);
        let path = match sink.arena.comp_type(answered) {
            | Some(&CompType::Returner { result, .. }) => match sink.arena.value_type(result) {
                | Some(&ValueType::Path {
                    carrier,
                    left,
                    right,
                }) => Some((carrier, left, right)),
                | _ => None,
            },
            | _ => None,
        };
        let inserted = origin.inserted(Insertion::Identity);
        let Some((carrier, left, right)) = path
        else {
            record_since(
                sink,
                mark,
                inserted,
                Maybe::Absent(rooted::Absent::Unminted),
            );
            return Maybe::Absent(lowered::Absent::OtherSort);
        };
        let root = match derived.derivation {
            | Derivation::Back { .. } => {
                gandr_core_term::identity::back(sink.arena, carrier, right, first)
            },
            | Derivation::Then { .. } => {
                gandr_core_term::identity::then(sink.arena, carrier, left, first, second)
            },
            | Derivation::Cong { .. } => {
                gandr_core_term::identity::cong(sink.arena, carrier, first, left, second)
            },
        };
        record_since(sink, mark, inserted, Maybe::Present((root, origin)));

        Maybe::Present(Lowered::Computation(root))
    }

    /// Mint `transport(\X. T, p, v)`: the element transport in the family the
    /// abstraction's body denotes under its binder.
    ///
    /// # Specification
    /// - requires: the three operands are already minted or absent.
    /// - ensures: the transport of the value along the path in the decode of
    ///   the motive's body at the fuss-free level — the quoted type itself when
    ///   the body quotes one, so `\X. List(X)` is `y. List(El y)`. The
    ///   transport carries the written origin and the family the inserted
    ///   identity origin. Nothing when an operand did not lower or the motive
    ///   minted as no static abstraction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list motive over a universe path, read back out of
    ///   the arena.
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_transport(
        &self,
        (abstraction, path, value): (NodeIndex, NodeIndex, NodeIndex),
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let (motive, path, value) = match (
            self.value_at(abstraction),
            self.value_at(path),
            self.value_at(value),
        ) {
            | (Maybe::Present(motive), Maybe::Present(path), Maybe::Present(value)) => {
                (motive, path, value)
            },
            | (Maybe::Absent(reason), ..)
            | (_, Maybe::Absent(reason), _)
            | (_, _, Maybe::Absent(reason)) => return Maybe::Absent(reason),
        };
        let Some(&Value::StaticLambda(body)) = sink.arena.value(motive)
        else {
            return Maybe::Absent(lowered::Absent::OtherSort);
        };
        let mark = sink.arena.watermark();
        let family = sink.arena.value_type_element(body, Level::zero());
        let root = sink.arena.computation_path_transport(family, path, value);
        let inserted = origin.inserted(Insertion::Identity);
        record_since(sink, mark, inserted, Maybe::Present((root, origin)));

        Maybe::Present(Lowered::Computation(root))
    }

    /// Mint the dependent transport `transported`.
    ///
    /// # Specification
    /// - requires: the operands are already minted or absent.
    /// - ensures: the transport over the motive's computation type, its two
    ///   entries made dependent by [`telescope`] and relocated to the
    ///   transport's frame, and the four values in order. The transport carries
    ///   the written origin and every other node minted for it the inserted
    ///   identity origin. Nothing when an operand did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a motive whose body ignores its element and one that
    ///   names both entries, each read back out of the arena.
    /// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin)
                && matches!(sink.arena.computation(id), Some(&gandr_core_term::Computation::TelescopeTransport { .. })),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_telescope_transport(
        &self,
        transported: Transported,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let motive = match self.value_type_at(transported.motive) {
            | Maybe::Present(motive) => motive,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let (path, start, over, value) = match (
            self.value_at(transported.path),
            self.value_at(transported.start),
            self.value_at(transported.over),
            self.value_at(transported.value),
        ) {
            | (
                Maybe::Present(path),
                Maybe::Present(start),
                Maybe::Present(over),
                Maybe::Present(value),
            ) => (path, start, over, value),
            | (Maybe::Absent(reason), ..)
            | (_, Maybe::Absent(reason), ..)
            | (_, _, Maybe::Absent(reason), _)
            | (.., Maybe::Absent(reason)) => return Maybe::Absent(reason),
        };
        let mark = sink.arena.watermark();
        let written = match sink.arena.value_type(motive) {
            | Some(&ValueType::Thunk(computation)) => computation,
            | _ => sink.arena.comp_type_returner(motive),
        };
        let dependent = telescope(sink.arena, written);
        let carried = self.relocate(sink.arena, dependent, transported.frame, Binders::NONE);
        let root = sink
            .arena
            .computation_telescope_transport(carried, path, start, over, value);
        record_since(
            sink,
            mark,
            origin.inserted(Insertion::Identity),
            Maybe::Present((root, origin)),
        );

        Maybe::Present(Lowered::Computation(root))
    }
}

/// `written`, a motive's computation type, with both entries of a two-entry
/// telescope dependent.
///
/// # Specification
/// - requires: `written` names a computation type of `arena`.
/// - ensures: for `A ⋆ (B ⋆ C)`, each `⋆` an arrow or a dependent arrow, the
///   two-entry telescope `Π (y : A). Π (z : B). C` with every arrow's codomain
///   shifted under the binder it now stands under; `written` itself when both
///   entries are already dependent or it is no two-entry telescope.
/// - provides: the one reading of the telescope alias as a dependent
///   transport's motive.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a motive whose body ignores its element and one that
///   names both entries.
/// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
#[spec(ensures: |ret| ret == written || matches!(arena.comp_type(ret), Some(&CompType::Pi { .. })))]
fn telescope(
    arena: &mut CoreArena,
    written: CompTypeId,
) -> CompTypeId
{
    let (outer, rest, outer_arrow) = match arena.comp_type(written) {
        | Some(&CompType::Pi { domain, codomain }) => (domain, codomain, false),
        | Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, true),
        | _ => return written,
    };
    let rest = if outer_arrow {
        gandr_core_term::shift_comp_type(arena, rest, Binders::ONE)
    }
    else {
        rest
    };
    let (inner, body, inner_arrow) = match arena.comp_type(rest) {
        | Some(&CompType::Pi { domain, codomain }) => (domain, codomain, false),
        | Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, true),
        | _ => return written,
    };
    if !outer_arrow && !inner_arrow {
        return written;
    }
    let body = if inner_arrow {
        gandr_core_term::shift_comp_type(arena, body, Binders::ONE)
    }
    else {
        body
    };
    let entry = arena.comp_type_pi(inner, body);
    arena.comp_type_pi(outer, entry)
}
