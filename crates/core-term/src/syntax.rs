//! The core language: [`Value`] and [`Computation`] on the term side,
//! [`ValueType`] and [`CompType`] on the type side, and the zone-qualified
//! variable reference the two-zone context is read through.
//!
//! # The alphabet is the kernel's; the grammar is this crate's
//!
//! Levels, base types, literals, sum sides, de Bruijn indices and admission
//! positions are re-used from the trusted base rather than restated, so the two
//! languages cannot disagree about what a literal or a level *is* and the
//! erasure that carries a core term down to a kernel term stays an id remapping
//! rather than a payload translation.
//!
//! The node enums are this crate's own, and that is the half that matters: the
//! elaboration-only formers — [`Value::Hole`], [`Value::Mark`], their
//! computation counterparts and the unknown types — enter here rather than
//! widening the vocabulary the kernel is obliged to represent, whose closedness
//! is one of the trusted base's stated properties. The bridge to the kernel
//! refuses every one of them by name; [`crate::hole`] states what they mean.
//!
//! # A variable names its zone
//!
//! The context carries two zones, and a de Bruijn index counts binders within
//! one zone rather than across both, so an occurrence that did not say which
//! zone it counted in would be ambiguous. [`Value::Variable`] therefore carries
//! a [`Zone`] beside its index.
//!
//! No former in the core vocabulary binds into the linear zone, so the linear
//! spelling is reachable only through a context built directly. The zone stays
//! on every occurrence, so a former that binds linearly changes no occurrence
//! site.
//!
//! # Children are ids, and the derived relations are shallow
//!
//! A node's children are typed arena ids and leaf payloads stay inline, so the
//! derived `Clone`, `Drop`, `PartialEq`, `Eq` and `Hash` do not walk term
//! depth. The derived equality is child-id equality rather than structural
//! equality: two structurally equal subterms need not share an id, so every use
//! site either compares inline leaf payloads or resolves ids explicitly.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::classifier::Sort;
use crate::hole::HoleId;
use crate::hole::MarkIndex;

/// The zone of the unified context a binder or an occurrence belongs to.
///
/// The two zones are `Γ; Σ`: the intuitionistic zone, whose bindings admit
/// weakening and contraction, and the linear zone, whose bindings are consumed
/// exactly once. They are separate flat stacks with separate de Bruijn index
/// spaces, so an index alone does not identify a binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Zone
{
    /// The intuitionistic zone `Γ`: structural, reusable bindings.
    Intuitionistic,
    /// The linear zone `Σ`: one-shot bindings, the type-level form of "a
    /// control capture cannot be naively duplicated".
    Linear,
}

/// A value: the positive fragment of the core term vocabulary.
///
/// Values are the total, thunkable half of the polarity split; the only value
/// embedding a computation is [`Self::Thunk`], and a thunk suspends rather than
/// runs it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Value
{
    /// A table-typed prelude thunk, with its generated curried body.
    Primitive
    {
        /// The row defining the thunk's signature.
        primitive: crate::primitive::Primitive,
        /// The generated lambda chain, ending in the saturated operation.
        body: ComputationId,
    },
    /// Reflexivity at a quoted closed code.
    PathRefl(ValueId),
    /// Componentwise product of two native path values.
    PathProduct(ValueId, ValueId),
    /// A native equivalence with untrusted, arena-independent replay evidence.
    PathEquiv
    {
        /// The native universe-path classifier.
        path_type: ValueTypeId,
        /// The closed forward translator.
        forward: ValueId,
        /// The closed backward translator.
        backward: ValueId,
        /// Both round-trip dialogues, checked again at kernel admission.
        evidence: alloc::sync::Arc<gandr_kernel_term::PathEvidence>,
    },
    /// A bound value variable, in a named zone of the unified context.
    Variable
    {
        /// The zone whose binder stack the index counts in.
        zone: Zone,
        /// The de Bruijn index, counting binders outward from the use site
        /// within `zone` alone.
        index: DeBruijnIndex,
    },
    /// A reference to a prior declaration by its admission position.
    Constant(ConstantIndex),
    /// The unique inhabitant of the unit type.
    Unit,
    /// A base-type literal.
    Literal(Literal),
    /// A pair, introducing the product `A × B`.
    Pair(ValueId, ValueId),
    /// A sum injection, introducing `A + B` on the given side.
    Injection(Side, ValueId),
    /// The empty native list, checked against its element type.
    ListNil,
    /// A native list cell with its head and list tail.
    ListCons(ValueId, ValueId),
    /// A thunk, suspending a computation into the value type `U C`.
    Thunk(ComputationId),
    /// An explicit universe lift: given `body : A` with `A`'s level strictly
    /// below `target`, this value inhabits `Lift A target`. There is no
    /// implicit cumulativity, so the lift is written rather than inferred.
    Lift
    {
        /// The target universe level of the lift.
        target: Level,
        /// The value being lifted.
        body: ValueId,
    },
    /// The quote `⌜A⌝` of a value type: the code of `A`, inhabiting
    /// `Type[+, l]` where `l` is `A`'s level.
    Quote(ValueTypeId),
    /// The quote `⌜C⌝` of a computation type: the code of `C`, inhabiting
    /// `Type[-, l]` where `l` is `C`'s level. A computation type's code is a
    /// value like any other code: quoting suspends nothing.
    QuoteComputation(CompTypeId),
    /// A static lambda `λ. v`, binding one intuitionistic value variable over
    /// a value body: a type operator, introducing a static Pi. It is static
    /// content, erased before runtime, and the kernel never represents it.
    StaticLambda(ValueId),
    /// A static application `f a` of a type operator to a value argument,
    /// eliminating a static Pi. Applied to a static lambda it is a static
    /// redex; applied to anything else it stands as a neutral spine.
    StaticApplication(ValueId, ValueId),
    /// A constructor of a nominal application, with declaration-ordered fields.
    Constructor
    {
        /// The complete nominal classifier, including its arguments.
        datatype: ValueTypeId,
        /// The constructor's ordinal in its declaration.
        tag: ConstructorTag,
        /// Ordinary field values in signature order.
        fields: Vec<ValueId>,
    },
    /// A structural record, in exact UTF-8 label order.
    Record(BTreeMap<FieldLabel, ValueId>),
    /// A typed hole: a value the author has not written yet, named so a fill
    /// can find it. It synthesises [`ValueType::Unknown`] and checks against
    /// any type.
    Hole(HoleId),
    /// A marked value: a subterm the elaborator could not type, kept in place
    /// under the mark-table entry that says why. It types as a hole does and
    /// its body is not judged.
    Mark
    {
        /// The mark-table entry recording the refusal.
        mark: MarkIndex,
        /// The subterm as written.
        body: ValueId,
    },
    /// A first-class stack, ordered from the first observation to its answer.
    Reify(alloc::sync::Arc<[crate::control::StackFrame]>),
}

/// A computation: the negative fragment of the core term vocabulary.
///
/// The eliminators — application, force, bind, case — synthesize; the
/// introductions — lambda, return, fixpoint — check against an expected
/// computation type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Computation
{
    /// A saturated native operation; currying uses ordinary lambdas.
    Primitive
    {
        /// The row defining names, signature and evaluation.
        primitive: crate::primitive::Primitive,
        /// Value arguments in source order.
        arguments: crate::primitive::Arguments,
    },
    /// Transport a value along a native universe path.
    Transport(ValueId, ValueId),
    /// A lambda `λ. M`, binding one intuitionistic value variable; introduces
    /// `A → C`.
    Lambda(ComputationId),
    /// A fixpoint `fix x. M`, binding its own thunk `x : U C` as one
    /// intuitionistic value variable over `M : C`; it checks at any
    /// computation type and carries the termination claim it is offered
    /// with.
    Fixpoint
    {
        /// The body, under the self binder.
        body: ComputationId,
        /// The termination claim.
        evidence: FixpointEvidence,
    },
    /// An application `M v` of a computation to a value argument.
    Application(ComputationId, ValueId),
    /// A returner `return v`, introducing `F A`.
    Return(ValueId),
    /// A sequencing bind `x ← M; N`, binding the value `M` returns into `N`.
    Bind(ComputationId, ComputationId),
    /// A force `force v` of a thunk value `v : U C`, running it as `C`.
    Force(ValueId),
    /// A sum elimination, binding the injected value into each branch.
    Case
    {
        /// The scrutinee value, of a sum type.
        scrutinee: ValueId,
        /// The left branch, checked with the left summand bound.
        on_left: ComputationId,
        /// The right branch, checked with the right summand bound.
        on_right: ComputationId,
    },
    /// A nominal case with a motive under one scrutinee binder.
    DataCase
    {
        /// The nominal value being eliminated.
        scrutinee: ValueId,
        /// Result type under one intuitionistic scrutinee binder.
        motive: CompTypeId,
        /// One ordinary function over the constructor's fields per tag.
        branches: Vec<ComputationId>,
    },
    /// Select a named field, returning it in the computation fragment.
    RecordProjection(ValueId, FieldLabel),
    /// A typed hole in computation position. It synthesises
    /// [`CompType::Unknown`] and checks against any computation type.
    Hole(HoleId),
    /// A marked computation: a subterm the elaborator could not type, kept in
    /// place under the mark-table entry that says why.
    Mark
    {
        /// The mark-table entry recording the refusal.
        mark: MarkIndex,
        /// The subterm as written.
        body: ComputationId,
    },
    /// A pure right fold; the cell branch binds head then folded result.
    ListFold
    {
        /// Element type in the ambient context.
        element: ValueTypeId,
        /// Result type in the ambient context.
        result: ValueTypeId,
        /// Native list to eliminate.
        list: ValueId,
        /// Empty branch in the ambient context.
        on_nil: ComputationId,
        /// Cell branch beneath two intuitionistic binders.
        on_cons: ComputationId,
    },
    /// Perform an operation from an inline-carried interface.
    Perform
    {
        /// Operation names and their payload and reply types.
        signature: crate::effect::EffectSig,
        /// The selected operation.
        operation: crate::effect::OperationName,
        /// Its value payload.
        payload: ValueId,
    },
    /// Handle one interface deeply; clauses run outside the handled scope.
    Handle
    {
        /// The interface whose operations are handled.
        signature: crate::effect::EffectSig,
        /// The computation being handled.
        subject: ComputationId,
        /// Return clause beneath one intuitionistic result binder.
        on_return: ComputationId,
        /// Operation clauses beneath payload then resumption binders.
        clauses: alloc::sync::Arc<[crate::control::EffectClause]>,
    },
    /// Feed a computation to a first-class stack.
    Resume(ValueId, ComputationId),
    /// Delimit a continuation capture.
    Reset(ComputationId),
    /// Capture to the nearest reset, binding one intuitionistic stack value.
    Shift(ComputationId),
    /// A lazy negative pair; only the observed component executes.
    With(ComputationId, ComputationId),
    /// Observe one component of a negative product.
    Project(Side, ComputationId),
}

/// A value type: the positive fragment of the core type vocabulary.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ValueType
{
    /// A generative nominal head applied to its declared parameter telescope.
    Data
    {
        /// Admission position of the defining signature; never a carrier alias.
        declaration: ConstantIndex,
        /// Quoted type or ordinary value arguments, in telescope order.
        arguments: Vec<ValueId>,
    },
    /// A structural record classifier, in exact UTF-8 label order.
    Record(BTreeMap<FieldLabel, ValueTypeId>),
    /// Certified equivalences between two quoted closed first-order codes.
    PathUniverse(ValueId, ValueId),
    /// A rigid base-type atom.
    Base(BaseType),
    /// The unit type, inhabited by [`Value::Unit`] alone.
    Unit,
    /// The non-dependent product `A × B`.
    Product(ValueTypeId, ValueTypeId),
    /// The sum `A + B`, with left and right injections.
    Sum(ValueTypeId, ValueTypeId),
    /// The native finite-list type over its element type.
    List(ValueTypeId),
    /// The thunk type `U C` of a computation type `C`.
    Thunk(CompTypeId),
    /// The universe of one sort at a canonical level `l`: `Type[+, l]`
    /// classifies the value types at `l` and `Type[-, l]` the computation
    /// types. Both are value types, whose own level is `l + 1`.
    Universe
    {
        /// The family the universe classifies.
        sort: Sort,
        /// The level within that family.
        level: Level,
    },
    /// An explicit lift of a value type into a strictly higher universe.
    Lift
    {
        /// The value type being lifted.
        inner: ValueTypeId,
        /// The target universe level, which is the lifted type's level.
        target: Level,
    },
    /// The value type a code denotes: `El l v`, where `v` is a value of type
    /// `Type[+, l]`. It is one of the two formers whose child crosses from the
    /// type language into the term language, which is what lets a dependent
    /// codomain mention its binder at all.
    ///
    /// A decode of a quote is the quoted type: the arena mints the type
    /// itself rather than this node, so `El ⌜A⌝` is never represented.
    Element
    {
        /// The code: a value whose type is `Type[+, target]`.
        code: ValueId,
        /// The universe the code is read out of, which is this type's own
        /// level.
        target: Level,
    },
    /// A sealed abstract type: a nominal atom named by the admission position
    /// of the declaration that introduced it.
    Abstract(ConstantIndex),
    /// The static Pi: the classifier of a type operator, taking an operand
    /// classified by the domain to a result classified by the codomain.
    /// Formation admits only static classifiers — universes and static Pis —
    /// as either child, and a static classifier mentions no term variable, so
    /// the codomain cannot depend on the operand and stands in the ambient
    /// context: the [`CompType::Arrow`] scoping, not the [`CompType::Pi`] one.
    StaticPi
    {
        /// The classifier of the operand, in the ambient context.
        domain: ValueTypeId,
        /// The classifier of the result, in the ambient context.
        codomain: ValueTypeId,
    },
    /// The unknown value type: what a hole or a mark synthesises. It is
    /// consistent with every value type and matches every former with unknown
    /// components.
    Unknown,
    /// A first-class continuation consuming one computation and delivering
    /// another.
    Stack
    {
        /// The computation consumed by the stack.
        input: CompTypeId,
        /// The answer delivered by the stack.
        output: CompTypeId,
    },
}

/// A computation type: the negative fragment of the core type vocabulary.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CompType
{
    /// The returner `F^effects A` of a value type `A`.
    Returner
    {
        /// The returned value type.
        result: ValueTypeId,
        /// The closed set of interfaces this computation may perform.
        effects: crate::effect::EffectRow,
    },
    /// The non-dependent function type `A → C`: its codomain stands in the
    /// ambient context and binds nothing.
    Arrow
    {
        /// The value-type domain.
        domain: ValueTypeId,
        /// The computation-type codomain, in the ambient context.
        codomain: CompTypeId,
    },
    /// The dependent function type `Π (x : A). C`, whose codomain stands in the
    /// ambient context extended by the domain's binder.
    ///
    /// The scoping is the whole difference from [`Self::Arrow`], which is why
    /// the two are distinct nodes rather than one former with a flag: the same
    /// two children mean two different things, and a flag would make a child's
    /// meaning depend on a payload.
    Pi
    {
        /// The value-type domain, in the ambient context.
        domain: ValueTypeId,
        /// The computation-type codomain, under the domain's binder.
        codomain: CompTypeId,
    },
    /// The computation type a code denotes: `El l v`, where `v` is a value of
    /// type `Type[-, l]`.
    ///
    /// Like its value counterpart, a decode of a computation quote is the
    /// quoted computation type and is never represented as this node.
    Element
    {
        /// The code: a value whose type is `Type[-, target]`.
        code: ValueId,
        /// The universe the code is read out of, which is this type's own
        /// level.
        target: Level,
    },
    /// The unknown computation type: what a hole or a mark in computation
    /// position synthesises.
    Unknown,
    /// A lazy negative product; an observation selects one component.
    With(CompTypeId, CompTypeId),
}

/// One pair of native syntax roots awaiting structural comparison.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum StructuralGoal
{
    /// Values.
    Value(ValueId, ValueId),
    /// Computations.
    Computation(ComputationId, ComputationId),
    /// Value types.
    ValueType(ValueTypeId, ValueTypeId),
    /// Computation types.
    CompType(CompTypeId, CompTypeId),
}

/// Result of evidence-erasing certificate syntax comparison.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertificateEquality
{
    /// Every constructor and non-evidence payload agrees.
    Equal,
    /// Syntax differs, or a requested node is unreadable.
    Different,
}

/// Compare native certificate syntax, erasing evidence but performing no
/// reduction.
///
/// # Specification
/// - requires: nothing; unreadable roots or children fail closed.
/// - ensures: compares every constructor, leaf and child, except path evidence;
///   distinct translator programs stay distinct even if extensionally equal.
/// - provides: certificate conversion independent of allocation and proof
///   bytes.
/// - fails: returns `Different` on a dangling node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — fresh allocations and different evidence compare equal;
///   an administrative translator redex changes the certificate.
/// - witness: `syntax::tests::certificate_syntax_erases_only_evidence`
#[spec(ensures: |ret| match (arena.value(left), arena.value(right)) {
    (Some(&Value::Unit), Some(&Value::Unit)) => ret == CertificateEquality::Equal,
    (Some(a), Some(b)) => ret != CertificateEquality::Equal || core::mem::discriminant(a) == core::mem::discriminant(b),
    _ => ret == CertificateEquality::Different,
})]
#[inline]
#[must_use]
pub fn equal_certificate_syntax(
    arena: &crate::CoreArena,
    left: ValueId,
    right: ValueId,
) -> CertificateEquality
{
    equal_syntax(arena, StructuralGoal::Value(left, right))
}

/// Compare signature type syntax without making allocation identity observable.
///
/// # Specification
/// - ensures: equal roots have the same former and structurally equal children.
/// - fails: unreadable roots or children compare different.
///
/// # Adequacy
/// - hypothesis: L3 — separately allocated equal signatures retain row
///   inclusion; changing an operation reply removes inclusion.
/// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
#[spec(ensures: |ret| ret != CertificateEquality::Equal || match (arena.value_type(left), arena.value_type(right)) {
    (Some(left), Some(right)) => core::mem::discriminant(left) == core::mem::discriminant(right),
    _ => false,
})]
pub fn equal_type_syntax(
    arena: &crate::CoreArena,
    left: ValueTypeId,
    right: ValueTypeId,
) -> CertificateEquality
{
    equal_syntax(arena, StructuralGoal::ValueType(left, right))
}

/// Queue operation type pairs after checking interface and operation
/// identities.
///
/// # Specification
/// - ensures: [`CertificateEquality::Equal`] preserves names and queues payload
///   before reply per operation; [`CertificateEquality::Different`] queues
///   nothing further for a mismatched name or arity.
/// - executable: none — this is the structural comparison's work-list rule.
///
/// # Adequacy
/// - hypothesis: L3 — reordered allocations preserve equality, changed replies
///   do not.
/// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
fn signature_children(
    pending: &mut alloc::vec::Vec<StructuralGoal>,
    left: &crate::effect::EffectSig,
    right: &crate::effect::EffectSig,
) -> CertificateEquality
{
    if left.name() != right.name() || left.operations().len() != right.operations().len() {
        return CertificateEquality::Different;
    }
    for (left, right) in left.operations().zip(right.operations()) {
        if left.name != right.name {
            return CertificateEquality::Different;
        }
        pending.extend([
            StructuralGoal::ValueType(left.payload, right.payload),
            StructuralGoal::ValueType(left.reply, right.reply),
        ]);
    }
    CertificateEquality::Equal
}

/// Run the shared, evidence-erasing structural comparison.
///
/// # Specification
/// - ensures: returns equal exactly when every reached pair agrees in syntax
///   after path evidence is erased; no reduction is performed.
/// - executable: none — the contract is the inductive graph comparison, not a
///   second traversal pretending to be an independent postcondition.
///
/// # Adequacy
/// - hypothesis: L3 — both certificate and type roots must reach the same child
///   comparison rules without depending on allocation order.
/// - witness: `syntax::tests::certificate_syntax_erases_only_evidence`
/// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
fn equal_syntax(
    arena: &crate::CoreArena,
    root: StructuralGoal,
) -> CertificateEquality
{
    use StructuralGoal::CompType as CT;
    use StructuralGoal::Computation as C;
    use StructuralGoal::Value as V;
    use StructuralGoal::ValueType as VT;
    let mut pending = alloc::vec![root];
    let mut visited = alloc::collections::BTreeSet::new();
    while let Some(goal) = pending.pop() {
        if !visited.insert(goal) {
            continue;
        }
        match goal {
            | V(a, b) => {
                let (Some(a), Some(b)) = (arena.value(a), arena.value(b))
                else {
                    return CertificateEquality::Different;
                };
                {
                    let (matched_left_value, matched_right_value) = (a, b);
                    if let Value::Constructor {
                        datatype: a,
                        tag: ta,
                        fields: ref fa,
                    } = *matched_left_value
                        && let Value::Constructor {
                            datatype: b,
                            tag: tb,
                            fields: ref fb,
                        } = *matched_right_value
                        && (ta == tb && fa.len() == fb.len())
                    {
                        {
                            pending.push(VT(a, b));
                            pending.extend(fa.iter().zip(fb).map(|(a, b)| V(*a, *b)));
                        }
                    }
                    else if let Value::Record(ref a) = *matched_left_value
                        && let Value::Record(ref b) = *matched_right_value
                        && (a.len() == b.len() && a.keys().eq(b.keys()))
                    {
                        {
                            pending.extend(a.values().zip(b.values()).map(|(a, b)| V(*a, *b)));
                        }
                    }
                    else if let Value::Reify(ref left) = *matched_left_value
                        && let Value::Reify(ref right) = *matched_right_value
                        && left.len() == right.len()
                    {
                        for (left, right) in left.iter().zip(right.iter()) {
                            match (*left, *right) {
                                | (
                                    crate::control::StackFrame::Apply(left),
                                    crate::control::StackFrame::Apply(right),
                                ) => pending.push(V(left, right)),
                                | (
                                    crate::control::StackFrame::Bind(left),
                                    crate::control::StackFrame::Bind(right),
                                ) => pending.push(C(left, right)),
                                | (
                                    crate::control::StackFrame::Project(left),
                                    crate::control::StackFrame::Project(right),
                                ) if left == right => {},
                                | _ => return CertificateEquality::Different,
                            }
                        }
                    }
                    else if matches!(
                        (matched_left_value, matched_right_value),
                        (&Value::ListNil, &Value::ListNil)
                    ) {
                    }
                    else if let (&Value::ListCons(a, b), &Value::ListCons(c, d)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.extend([V(a, c), V(b, d)]);
                    }
                    else if let Value::PathRefl(a) = *matched_left_value
                        && let Value::PathRefl(b) = *matched_right_value
                    {
                        pending.push(V(a, b));
                    }
                    else if let Value::StaticLambda(a) = *matched_left_value
                        && let Value::StaticLambda(b) = *matched_right_value
                    {
                        pending.push(V(a, b));
                    }
                    else if let Value::PathProduct(a, b) = *matched_left_value
                        && let Value::PathProduct(c, d) = *matched_right_value
                    {
                        {
                            pending.extend([V(a, c), V(b, d)]);
                        }
                    }
                    else if let Value::Pair(a, b) = *matched_left_value
                        && let Value::Pair(c, d) = *matched_right_value
                    {
                        {
                            pending.extend([V(a, c), V(b, d)]);
                        }
                    }
                    else if let Value::StaticApplication(a, b) = *matched_left_value
                        && let Value::StaticApplication(c, d) = *matched_right_value
                    {
                        {
                            pending.extend([V(a, c), V(b, d)]);
                        }
                    }
                    else if let Value::PathEquiv {
                        path_type: left_type,
                        forward: left_forward,
                        backward: left_backward,
                        ..
                    } = *matched_left_value
                        && let Value::PathEquiv {
                            path_type: right_type,
                            forward: right_forward,
                            backward: right_backward,
                            ..
                        } = *matched_right_value
                    {
                        pending.extend([
                            VT(left_type, right_type),
                            V(left_forward, right_forward),
                            V(left_backward, right_backward),
                        ]);
                    }
                    else if let Value::Injection(s, a) = *matched_left_value
                        && let Value::Injection(t, b) = *matched_right_value
                        && (s == t)
                    {
                        {
                            pending.push(V(a, b));
                        }
                    }
                    else if let Value::Thunk(a) = *matched_left_value
                        && let Value::Thunk(b) = *matched_right_value
                    {
                        pending.push(C(a, b));
                    }
                    else if let Value::Primitive { primitive: a, .. } = *matched_left_value
                        && let Value::Primitive { primitive: b, .. } = *matched_right_value
                        && (a == b)
                    {
                        {}
                    }
                    else if let Value::Lift { ref target, body } = *matched_left_value
                        && let Value::Lift {
                            target: ref other,
                            body: right,
                        } = *matched_right_value
                        && (target == other)
                    {
                        pending.push(V(body, right));
                    }
                    else if let Value::Quote(a) = *matched_left_value
                        && let Value::Quote(b) = *matched_right_value
                    {
                        pending.push(VT(a, b));
                    }
                    else if let Value::QuoteComputation(a) = *matched_left_value
                        && let Value::QuoteComputation(b) = *matched_right_value
                    {
                        {
                            pending.push(CT(a, b));
                        }
                    }
                    else if let Value::Mark {
                        mark: left_mark,
                        body: left_body,
                    } = *matched_left_value
                        && let Value::Mark {
                            mark: right_mark,
                            body: right_body,
                        } = *matched_right_value
                        && (left_mark == right_mark)
                    {
                        pending.push(V(left_body, right_body));
                    }
                    else if (matches!(
                        *matched_left_value,
                        Value::Variable { .. }
                            | Value::Constant(_)
                            | Value::Unit
                            | Value::Literal(_)
                            | Value::Hole(_)
                    ) && (a == b))
                    {
                        {}
                    }
                    else {
                        return CertificateEquality::Different;
                    }
                }
            },
            | C(a, b) => {
                let (Some(a), Some(b)) = (arena.computation(a), arena.computation(b))
                else {
                    return CertificateEquality::Different;
                };
                match (a, b) {
                    | (
                        &Computation::DataCase {
                            scrutinee: a,
                            motive: am,
                            branches: ref ab,
                        },
                        &Computation::DataCase {
                            scrutinee: b,
                            motive: bm,
                            branches: ref bb,
                        },
                    ) if ab.len() == bb.len() => {
                        pending.extend([V(a, b), CT(am, bm)]);
                        pending.extend(ab.iter().zip(bb).map(|(a, b)| C(*a, *b)));
                    },
                    | (
                        &Computation::RecordProjection(a, ref al),
                        &Computation::RecordProjection(b, ref bl),
                    ) if al == bl => pending.push(V(a, b)),
                    | (
                        &Computation::Perform {
                            signature: ref left,
                            operation: ref left_op,
                            payload: left_payload,
                        },
                        &Computation::Perform {
                            signature: ref right,
                            operation: ref right_op,
                            payload: right_payload,
                        },
                    ) if left_op == right_op => {
                        if signature_children(&mut pending, left, right)
                            == CertificateEquality::Different
                        {
                            return CertificateEquality::Different;
                        }
                        pending.push(V(left_payload, right_payload));
                    },
                    | (
                        &Computation::Handle {
                            signature: ref left,
                            subject: left_subject,
                            on_return: left_return,
                            clauses: ref left_clauses,
                        },
                        &Computation::Handle {
                            signature: ref right,
                            subject: right_subject,
                            on_return: right_return,
                            clauses: ref right_clauses,
                        },
                    ) if left_clauses.len() == right_clauses.len() => {
                        if signature_children(&mut pending, left, right)
                            == CertificateEquality::Different
                        {
                            return CertificateEquality::Different;
                        }
                        pending
                            .extend([C(left_subject, right_subject), C(left_return, right_return)]);
                        for (left, right) in left_clauses.iter().zip(right_clauses.iter()) {
                            if left.operation != right.operation {
                                return CertificateEquality::Different;
                            }
                            pending.push(C(left.body, right.body));
                        }
                    },
                    | (&Computation::Resume(a, b), &Computation::Resume(c, d)) => {
                        pending.extend([V(a, c), C(b, d)]);
                    },
                    | (&Computation::Reset(a), &Computation::Reset(b))
                    | (&Computation::Shift(a), &Computation::Shift(b))
                    | (&Computation::Lambda(a), &Computation::Lambda(b)) => pending.push(C(a, b)),
                    | (&Computation::With(a, b), &Computation::With(c, d))
                    | (&Computation::Bind(a, b), &Computation::Bind(c, d)) => {
                        pending.extend([C(a, c), C(b, d)]);
                    },
                    | (&Computation::Project(a, b), &Computation::Project(c, d)) if a == c => {
                        pending.push(C(b, d));
                    },
                    | (
                        &Computation::ListFold {
                            element: left_element,
                            result: left_result,
                            list: left_list,
                            on_nil: left_nil,
                            on_cons: left_cons,
                        },
                        &Computation::ListFold {
                            element: right_element,
                            result: right_result,
                            list: right_list,
                            on_nil: right_nil,
                            on_cons: right_cons,
                        },
                    ) => pending.extend([
                        VT(left_element, right_element),
                        VT(left_result, right_result),
                        V(left_list, right_list),
                        C(left_nil, right_nil),
                        C(left_cons, right_cons),
                    ]),
                    | (
                        &Computation::Primitive {
                            primitive: a,
                            arguments: ref aa,
                        },
                        &Computation::Primitive {
                            primitive: b,
                            arguments: ref right_arguments,
                        },
                    ) if a == b && aa.len() == right_arguments.len() => pending.extend(
                        aa.iter()
                            .zip(right_arguments.iter())
                            .map(|(a, b)| V(*a, *b)),
                    ),
                    | (
                        &Computation::Fixpoint {
                            body: a,
                            evidence: left_evidence,
                        },
                        &Computation::Fixpoint {
                            body: b,
                            evidence: right_evidence,
                        },
                    ) if left_evidence == right_evidence => pending.push(C(a, b)),
                    | (&Computation::Return(a), &Computation::Return(b))
                    | (&Computation::Force(a), &Computation::Force(b)) => pending.push(V(a, b)),
                    | (&Computation::Application(a, b), &Computation::Application(c, d)) => {
                        pending.extend([C(a, c), V(b, d)]);
                    },
                    | (&Computation::Transport(a, b), &Computation::Transport(c, d)) => {
                        pending.extend([V(a, c), V(b, d)]);
                    },
                    | (
                        &Computation::Case {
                            scrutinee: left_scrutinee,
                            on_left: left_branch,
                            on_right: right_branch,
                        },
                        &Computation::Case {
                            scrutinee: right_scrutinee,
                            on_left: other_left_branch,
                            on_right: other_right_branch,
                        },
                    ) => pending.extend([
                        V(left_scrutinee, right_scrutinee),
                        C(left_branch, other_left_branch),
                        C(right_branch, other_right_branch),
                    ]),
                    | (&Computation::Hole(left), &Computation::Hole(right)) if left == right => {},
                    | (
                        &Computation::Mark {
                            mark: left_mark,
                            body: left_body,
                        },
                        &Computation::Mark {
                            mark: right_mark,
                            body: right_body,
                        },
                    ) if left_mark == right_mark => pending.push(C(left_body, right_body)),
                    | _ => return CertificateEquality::Different,
                }
            },
            | VT(a, b) => {
                let (Some(a), Some(b)) = (arena.value_type(a), arena.value_type(b))
                else {
                    return CertificateEquality::Different;
                };
                {
                    let (matched_left_value, matched_right_value) = (a, b);
                    if let ValueType::Data {
                        declaration: a,
                        arguments: ref aa,
                    } = *matched_left_value
                        && let ValueType::Data {
                            declaration: b,
                            arguments: ref right_arguments,
                        } = *matched_right_value
                        && (a == b && aa.len() == right_arguments.len())
                    {
                        {
                            pending.extend(aa.iter().zip(right_arguments).map(|(a, b)| V(*a, *b)));
                        }
                    }
                    else if let ValueType::Record(ref a) = *matched_left_value
                        && let ValueType::Record(ref b) = *matched_right_value
                        && (a.len() == b.len() && a.keys().eq(b.keys()))
                    {
                        {
                            pending.extend(a.values().zip(b.values()).map(|(a, b)| VT(*a, *b)));
                        }
                    }
                    else if let (
                        &ValueType::Stack {
                            input: a,
                            output: b,
                        },
                        &ValueType::Stack {
                            input: c,
                            output: d,
                        },
                    ) = (matched_left_value, matched_right_value)
                    {
                        pending.extend([CT(a, c), CT(b, d)]);
                    }
                    else if let (&ValueType::List(a), &ValueType::List(b)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.push(VT(a, b));
                    }
                    else if let ValueType::PathUniverse(a, b) = *matched_left_value
                        && let ValueType::PathUniverse(c, d) = *matched_right_value
                    {
                        {
                            pending.extend([V(a, c), V(b, d)]);
                        }
                    }
                    else if let ValueType::Product(a, b) = *matched_left_value
                        && let ValueType::Product(c, d) = *matched_right_value
                    {
                        pending.extend([VT(a, c), VT(b, d)]);
                    }
                    else if let ValueType::Sum(a, b) = *matched_left_value
                        && let ValueType::Sum(c, d) = *matched_right_value
                    {
                        pending.extend([VT(a, c), VT(b, d)]);
                    }
                    else if let ValueType::StaticPi {
                        domain: a,
                        codomain: b,
                    } = *matched_left_value
                        && let ValueType::StaticPi {
                            domain: c,
                            codomain: d,
                        } = *matched_right_value
                    {
                        pending.extend([VT(a, c), VT(b, d)]);
                    }
                    else if let ValueType::Thunk(a) = *matched_left_value
                        && let ValueType::Thunk(b) = *matched_right_value
                    {
                        pending.push(CT(a, b));
                    }
                    else if let ValueType::Lift {
                        inner: a,
                        ref target,
                    } = *matched_left_value
                        && let ValueType::Lift {
                            inner: b,
                            target: ref other,
                        } = *matched_right_value
                        && (target == other)
                    {
                        pending.push(VT(a, b));
                    }
                    else if let ValueType::Element {
                        code: a,
                        ref target,
                    } = *matched_left_value
                        && let ValueType::Element {
                            code: b,
                            target: ref other,
                        } = *matched_right_value
                        && (target == other)
                    {
                        pending.push(V(a, b));
                    }
                    else if (matches!(
                        *matched_left_value,
                        ValueType::Base(_)
                            | ValueType::Unit
                            | ValueType::Universe { .. }
                            | ValueType::Abstract(_)
                            | ValueType::Unknown
                    ) && (a == b))
                    {
                        {}
                    }
                    else {
                        return CertificateEquality::Different;
                    }
                }
            },
            | CT(a, b) => {
                let (Some(a), Some(b)) = (arena.comp_type(a), arena.comp_type(b))
                else {
                    return CertificateEquality::Different;
                };
                match (a, b) {
                    | (&CompType::With(a, b), &CompType::With(c, d)) => {
                        pending.extend([CT(a, c), CT(b, d)]);
                    },
                    | (
                        &CompType::Returner {
                            result: a,
                            effects: ref first,
                        },
                        &CompType::Returner {
                            result: b,
                            effects: ref second,
                        },
                    ) => {
                        if first.signatures().len() != second.signatures().len() {
                            return CertificateEquality::Different;
                        }
                        for (left, right) in first.signatures().zip(second.signatures()) {
                            if signature_children(&mut pending, left, right)
                                == CertificateEquality::Different
                            {
                                return CertificateEquality::Different;
                            }
                        }
                        pending.push(VT(a, b));
                    },
                    | (
                        &CompType::Arrow {
                            domain: a,
                            codomain: b,
                        },
                        &CompType::Arrow {
                            domain: c,
                            codomain: d,
                        },
                    )
                    | (
                        &CompType::Pi {
                            domain: a,
                            codomain: b,
                        },
                        &CompType::Pi {
                            domain: c,
                            codomain: d,
                        },
                    ) => pending.extend([VT(a, c), CT(b, d)]),
                    | (
                        &CompType::Element {
                            code: a,
                            ref target,
                        },
                        &CompType::Element {
                            code: b,
                            target: ref other,
                        },
                    ) if target == other => pending.push(V(a, b)),
                    | (&CompType::Unknown, &CompType::Unknown) => {},
                    | _ => return CertificateEquality::Different,
                }
            },
        }
    }
    CertificateEquality::Equal
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn certificate_syntax_erases_only_evidence()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_type_unit();
        let code = arena.value_quote(unit);
        let classifier = arena.value_type_path_universe(code, code);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(variable);
        let lambda = arena.computation_lambda(returned);
        let identity = arena.value_thunk(lambda);
        let first =
            arena.value_path_equiv(classifier, identity, identity, alloc::sync::Arc::default());
        let mut evidence = gandr_kernel_term::PathEvidence::default();
        evidence.source.push(alloc::vec::Vec::new());
        let evidence = alloc::sync::Arc::new(evidence);
        let same = arena.value_path_equiv(
            classifier,
            identity,
            identity,
            alloc::sync::Arc::clone(&evidence),
        );
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&arena, first, same)
        );
        let extra = arena.computation_bind(returned, returned);
        let extra = arena.computation_lambda(extra);
        let extra = arena.value_thunk(extra);
        let different = arena.value_path_equiv(classifier, extra, identity, evidence);
        assert_eq!(
            CertificateEquality::Different,
            equal_certificate_syntax(&arena, first, different)
        );
        let fresh = arena.value_type_unit();
        let fresh = arena.value_quote(fresh);
        let one = arena.value_path_refl(code);
        let two = arena.value_path_refl(fresh);
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&arena, one, two)
        );
    }
}

/// A nominal declaration's parameter telescope, constructor table and universe.
///
/// Parameter classifiers are scoped under their predecessors. Constructor
/// fields are scoped under all parameters and do not bind one another.
/// Admission, not this container, verifies those scopes and the universe bound.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DataSignature
{
    /// Parameter classifiers in telescope order.
    parameters: Vec<ValueTypeId>,
    /// Constructor fields in tag order.
    constructors: Vec<Vec<ValueTypeId>>,
    /// The positive universe bounding every constructor field.
    kind: ValueTypeId,
}

impl DataSignature
{
    /// Construct a signature whose formation remains the checker's obligation.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn new(
        parameters: Vec<ValueTypeId>,
        constructors: Vec<Vec<ValueTypeId>>,
        kind: ValueTypeId,
    ) -> Self
    {
        Self {
            parameters,
            constructors,
            kind,
        }
    }

    /// Parameter classifiers in telescope order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn parameters(&self) -> &[ValueTypeId]
    {
        &self.parameters
    }

    /// Constructor field classifiers in tag order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn constructors(&self) -> &[Vec<ValueTypeId>]
    {
        &self.constructors
    }

    /// The positive universe bounding constructor fields.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn kind(&self) -> ValueTypeId
    {
        self.kind
    }
}
