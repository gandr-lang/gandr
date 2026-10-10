//! An item's typing: the checker's verdict, projected to a form free of arena
//! ids and admission positions.
//!
//! # A coordinate change, nothing more
//!
//! A [`Verdict`] names arena ids and positions, which differ between two runs
//! over two arenas even when the runs agree. The projection replaces each id
//! with the content it names — a term node with its index in the item's
//! table, a type with its type table — and each position with the reference
//! it resolves to. Two runs agree exactly when their projections are equal,
//! which is what "incremental equals batch" compares. The origin token is not
//! projected: it is the producer's coordinate for the item, echoed from the
//! edited declaration, never reused from a checkpoint.

use gandr_core_checker::ArgumentPosition;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::ConversionCount;
use gandr_core_checker::CoreNode;
use gandr_core_checker::ExpectedShape;
use gandr_core_checker::Mismatch;
use gandr_core_checker::StaticArity;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::Verdict;
use gandr_core_term::BinderDepth;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemOrdinal;
use crate::boundary::NodeIndex;
use crate::content::ArenaNode;
use crate::content::Sites;
use crate::content::TypeContent;
use crate::content::encode_item;
use crate::region::Layout;
use crate::region::Program;
use crate::region::Reference;

/// Where in its item a refusal stood.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Site
{
    /// The node at this index of the item's table.
    Node(NodeIndex),
    /// A node the item's walk did not reach; the judgement names none, and the
    /// projection stays total without inventing an index.
    Unreached,
}

/// A checking-only form met where a type had to be synthesised.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Form
{
    /// A thunk.
    Thunk(Site),
    /// A lambda.
    Lambda(Site),
    /// A return.
    Return(Site),
    /// A static lambda.
    StaticLambda(Site),
    /// The item's own hole.
    Hole,
}

/// A refusal, projected.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Refusal
{
    /// A synthesised type did not convert to the expected one.
    TypeMismatch
    {
        /// The term checked.
        at: Site,
        /// The type it synthesised.
        synthesised: TypeContent,
        /// The type expected.
        expected: TypeContent,
    },
    /// A rule met a type of another former than it requires.
    ShapeMismatch
    {
        /// The term whose type lacks the shape.
        at: Site,
        /// The former required.
        wanted: ExpectedShape,
        /// The type met.
        found: TypeContent,
    },
    /// A checking-only form stood in synthesis position.
    NotSynthesisable
    {
        /// The form.
        form: Form,
    },
    /// A constant named nothing with a type.
    UnknownConstant
    {
        /// The constant.
        at: Site,
        /// What its position names.
        constant: Reference,
    },
    /// A former the judgement has no rule for.
    OutOfFragment
    {
        /// The node carrying the former.
        at: Site,
        /// The former.
        former: UnadmittedFormer,
    },
    /// A variable counted past its zone's binders.
    UnboundIndex
    {
        /// The variable.
        at: Site,
        /// Its zone.
        zone: Zone,
        /// Its index.
        index: DeBruijnIndex,
        /// The binders the zone held.
        depth: BinderDepth,
    },
    /// The allowance ran out.
    BudgetExceeded
    {
        /// The allowance.
        budget: CheckBudget,
    },
    /// An id named no node of the arena.
    DanglingNode
    {
        /// The unresolved node.
        at: Site,
    },
    /// The item was admitted out of order, which a program never allows.
    AdmissionOrder,
    /// The machine's bookkeeping disagreed with itself.
    MachineInvariant,
    /// A code was checked at a universe of the other sort.
    SortMismatch
    {
        /// The code.
        at: Site,
        /// The universe it synthesised.
        synthesised: TypeContent,
        /// The universe expected.
        expected: TypeContent,
    },
    /// A code was checked at a universe of its sort it does not fit.
    LevelMismatch
    {
        /// The code.
        at: Site,
        /// The universe it synthesised.
        synthesised: TypeContent,
        /// The universe expected.
        expected: TypeContent,
    },
    /// A bind's body synthesised a type that mentions the bound name.
    DependentBind
    {
        /// The bind.
        at: Site,
        /// The type its body synthesised, under the binder.
        synthesised: TypeContent,
    },
    /// The normaliser did not certify the unfolding of a code constant.
    Undecided
    {
        /// The code.
        at: Site,
    },
    /// A static application passed more arguments than its head takes.
    FamilyArity
    {
        /// The static application.
        at: Site,
        /// The static Pis the head's type opens.
        expected: StaticArity,
        /// The arguments passed.
        actual: StaticArity,
    },
    /// A static application passed an argument at the wrong classifier.
    FamilyArgumentClassifier
    {
        /// The argument.
        at: Site,
        /// Its position among the arguments.
        position: ArgumentPosition,
        /// The classifier it synthesised.
        synthesised: TypeContent,
        /// The domain it was passed at.
        expected: TypeContent,
    },
    /// A dynamic application passed a type operator that does not normalize
    /// away.
    StaticLambdaArgument
    {
        /// The argument.
        at: Site,
    },
    /// A static Pi stood over a type that classifies no codes.
    StaticClassifierExpected
    {
        /// The static Pi.
        at: Site,
        /// The child that classifies no codes.
        found: TypeContent,
    },
}

/// An item's typing: its verdict, projected.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Typing
{
    /// The body checked against the signature.
    Checked
    {
        /// The conversions the check made.
        conversions: ConversionCount,
    },
    /// The unsigned body synthesised a type.
    Synthesised
    {
        /// The type produced.
        produced: TypeContent,
        /// The conversions the synthesis made.
        conversions: ConversionCount,
    },
    /// The body is a hole under the signature, owed.
    Owed,
    /// The item was refused.
    Refused(Refusal),
}

/// What a projection reads beside the verdict: the arena its ids resolve in,
/// the program its positions resolve through, and the item's sites.
pub struct Projection<'arena, 'layout, 'sites>
{
    /// The arena the verdict's ids resolve in.
    pub arena: &'arena CoreArena,
    /// The program positions resolve through.
    pub layout: &'layout Layout,
    /// The item's table indices of its arena nodes.
    pub sites: &'sites Sites,
}

impl Projection<'_, '_, '_>
{
    /// The projected typing of `verdict`.
    ///
    /// # Specification
    /// - requires: `verdict` judged the item whose sites these are, in this
    ///   arena.
    /// - ensures: each verdict maps to its typing, each id to the content or
    ///   site it names, each position to its reference, and nothing else is
    ///   dropped but the origin and the admission positions of an out-of-order
    ///   refusal.
    /// - provides: the coordinate change both runs of the differential pass
    ///   through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the per-variant maps, separated by
    ///   one item per verdict and per refusal the fragment can reach, each
    ///   asserted as an exact typing against content built by hand.
    /// - witness: `typing::tests::each_verdict_projects_to_its_typing`
    /// - witness: `typing::tests::each_refusal_projects_its_payload`
    pub(crate) fn typing(
        &self,
        verdict: &Verdict,
    ) -> Typing
    {
        match *verdict {
            | Verdict::Checked { evidence, .. } => Typing::Checked {
                conversions: evidence.conversions(),
            },
            | Verdict::Synthesised { synthesised, .. } => Typing::Synthesised {
                produced: self.value_type(synthesised.produced().id()),
                conversions: synthesised.conversions(),
            },
            | Verdict::Owed(_) => Typing::Owed,
            | Verdict::Refused(refusal) => Typing::Refused(self.refusal(refusal)),
        }
    }

    /// The content of a value type.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &self,
        ty: gandr_core_term::ValueTypeId,
    ) -> TypeContent
    {
        TypeContent::of(self.arena, self.layout, ArenaNode::ValueType(ty))
    }

    /// The content of a type node.
    ///
    /// # Specification
    /// trivial.
    fn type_node(
        &self,
        node: TypeNode,
    ) -> TypeContent
    {
        match node {
            | TypeNode::Value(ty) => self.value_type(ty),
            | TypeNode::Computation(ty) => {
                TypeContent::of(self.arena, self.layout, ArenaNode::CompType(ty))
            },
        }
    }

    /// The site of an arena node.
    ///
    /// # Specification
    /// trivial.
    fn site(
        &self,
        node: ArenaNode,
    ) -> Site
    {
        match self.sites.of(node) {
            | Maybe::Present(index) => Site::Node(index),
            | Maybe::Absent(_) => Site::Unreached,
        }
    }

    /// The site of a term node.
    ///
    /// # Specification
    /// trivial.
    fn term_site(
        &self,
        node: TermNode,
    ) -> Site
    {
        match node {
            | TermNode::Value(id) => self.site(ArenaNode::Value(id)),
            | TermNode::Computation(id) => self.site(ArenaNode::Computation(id)),
        }
    }

    /// The site of any core node.
    ///
    /// # Specification
    /// trivial.
    fn core_site(
        &self,
        node: CoreNode,
    ) -> Site
    {
        match node {
            | CoreNode::Term(term) => self.term_site(term),
            | CoreNode::Type(TypeNode::Value(id)) => self.site(ArenaNode::ValueType(id)),
            | CoreNode::Type(TypeNode::Computation(id)) => self.site(ArenaNode::CompType(id)),
        }
    }

    /// The projected refusal.
    ///
    /// # Specification
    /// trivial.
    fn refusal(
        &self,
        refusal: CheckRefusal,
    ) -> Refusal
    {
        match refusal {
            | CheckRefusal::TypeMismatch(Mismatch::Value {
                at,
                synthesised,
                expected,
            }) => Refusal::TypeMismatch {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            | CheckRefusal::TypeMismatch(Mismatch::Computation {
                at,
                synthesised,
                expected,
            }) => Refusal::TypeMismatch {
                at: self.site(ArenaNode::Computation(at)),
                synthesised: self.type_node(TypeNode::Computation(synthesised)),
                expected: self.type_node(TypeNode::Computation(expected)),
            },
            | CheckRefusal::ShapeMismatch { at, wanted, found } => Refusal::ShapeMismatch {
                at: self.term_site(at),
                wanted,
                found: self.type_node(found),
            },
            | CheckRefusal::NotSynthesisable { form } => Refusal::NotSynthesisable {
                form: match form {
                    | CheckingForm::Thunk(id) => Form::Thunk(self.site(ArenaNode::Value(id))),
                    | CheckingForm::Lambda(id) => {
                        Form::Lambda(self.site(ArenaNode::Computation(id)))
                    },
                    | CheckingForm::Return(id) => {
                        Form::Return(self.site(ArenaNode::Computation(id)))
                    },
                    | CheckingForm::Hole(_) => Form::Hole,
                    | CheckingForm::StaticLambda(id) => {
                        Form::StaticLambda(self.site(ArenaNode::Value(id)))
                    },
                },
            },
            | CheckRefusal::UnknownConstant { at, constant } => Refusal::UnknownConstant {
                at: self.site(ArenaNode::Value(at)),
                constant: self.layout.resolve(constant),
            },
            | CheckRefusal::OutOfFragment { at, former } => Refusal::OutOfFragment {
                at: self.core_site(at),
                former,
            },
            | CheckRefusal::UnboundIndex {
                at,
                zone,
                index,
                depth,
            } => Refusal::UnboundIndex {
                at: self.site(ArenaNode::Value(at)),
                zone,
                index,
                depth,
            },
            | CheckRefusal::BudgetExceeded { budget } => Refusal::BudgetExceeded { budget },
            | CheckRefusal::DanglingNode { node } => Refusal::DanglingNode {
                at: self.core_site(node),
            },
            | CheckRefusal::AdmissionOrder { .. } => Refusal::AdmissionOrder,
            | CheckRefusal::MachineInvariant => Refusal::MachineInvariant,
            | CheckRefusal::SortMismatch {
                at,
                synthesised,
                expected,
            } => Refusal::SortMismatch {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            | CheckRefusal::LevelMismatch {
                at,
                synthesised,
                expected,
            } => Refusal::LevelMismatch {
                at: self.site(ArenaNode::Value(at)),
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            | CheckRefusal::DependentBind { at, synthesised } => Refusal::DependentBind {
                at: self.site(ArenaNode::Computation(at)),
                synthesised: self.type_node(TypeNode::Computation(synthesised)),
            },
            | CheckRefusal::Undecided { at } => Refusal::Undecided {
                at: self.site(ArenaNode::Value(at)),
            },
            | CheckRefusal::FamilyArity {
                at,
                expected,
                actual,
            } => Refusal::FamilyArity {
                at: self.site(ArenaNode::Value(at)),
                expected,
                actual,
            },
            | CheckRefusal::FamilyArgumentClassifier {
                at,
                position,
                synthesised,
                expected,
            } => Refusal::FamilyArgumentClassifier {
                at: self.site(ArenaNode::Value(at)),
                position,
                synthesised: self.value_type(synthesised),
                expected: self.value_type(expected),
            },
            | CheckRefusal::StaticLambdaArgument { at } => Refusal::StaticLambdaArgument {
                at: self.site(ArenaNode::Value(at)),
            },
            | CheckRefusal::StaticClassifierExpected { at, found } => {
                Refusal::StaticClassifierExpected {
                    at: self.site(ArenaNode::ValueType(at)),
                    found: self.value_type(found),
                }
            },
        }
    }
}

/// The typing `verdict` projects to, for the item at `ordinal` of `program`,
/// judged in `arena`.
///
/// # Specification
/// - requires: `arena` is `program`'s arena or grew from a copy of it, so every
///   id of the program names the same node in it; `verdict` judged the item at
///   `ordinal` in it.
/// - ensures: the typing an incremental or batch run of this crate records for
///   that verdict.
/// - provides: the coordinate change a caller needs to compare its own batch
///   run — the checker's module entry, say — against this crate's typings.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the differential suite projects the checker's module
///   entry through this function on every generated program and compares the
///   result against the incremental run.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
#[inline]
#[must_use]
pub fn project(
    program: &Program,
    arena: &CoreArena,
    ordinal: ItemOrdinal,
    verdict: &Verdict,
) -> Typing
{
    let encoded = encode_item(arena, program.layout(), ordinal);
    Projection {
        arena,
        layout: program.layout(),
        sites: &encoded.sites,
    }
    .typing(verdict)
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec;

    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::Declaration;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::UnadmittedFormer;
    use gandr_core_checker::Verdict;
    use gandr_core_checker::body;
    use gandr_core_checker::check_declaration_supported;
    use gandr_core_checker::signature;
    use gandr_core_term::BinderDepth;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use quenchant_shape::shape::Maybe;

    use super::Form;
    use super::Projection;
    use super::Refusal;
    use super::Site;
    use super::Typing;
    use crate::boundary::ItemOrdinal;
    use crate::boundary::NodeIndex;
    use crate::content::ContentNode;
    use crate::content::TypeContent;
    use crate::content::encode_item;
    use crate::region::Item;
    use crate::region::ItemKey;
    use crate::region::Program;
    use crate::region::Reference;

    /// A one-item program's verdict and its projection, judged under
    /// `budget` in a fresh context.
    ///
    /// # Specification
    /// trivial.
    fn judged(
        arena: CoreArena,
        signature: Maybe<ValueTypeId, signature::Absent>,
        body: Maybe<ValueId, body::Absent>,
        budget: CheckBudget,
    ) -> (Verdict, Typing)
    {
        let mut program = Program::new(arena, vec![Item::new(
            ItemKey::from("it"),
            Declaration::new(
                ConstantIndex::from(0_usize),
                signature,
                body,
                OriginToken::from(0_usize),
            ),
        )])
        .expect("one item ascends");
        let declarations = program.declarations();
        let encoded = encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(0_usize),
        );
        let (arena, layout) = program.parts_mut();
        let mut context = CheckingContext::new(arena, budget);
        let Some(declaration) = declarations.first()
        else {
            panic!("one declaration");
        };
        let verdict = check_declaration_supported(&mut context, declaration).verdict();
        let projection = Projection {
            arena: context.arena(),
            layout,
            sites: &encoded.sites,
        };
        let typing = projection.typing(&verdict);
        (verdict, typing)
    }

    /// The type table of one base type.
    ///
    /// # Specification
    /// trivial.
    fn base(base: BaseType) -> TypeContent
    {
        TypeContent::from_nodes(
            crate::fixture::closed_table(&[ContentNode::Base(base)]),
            crate::support::Thinning::default(),
        )
    }

    /// The integer literal zero.
    ///
    /// # Specification
    /// trivial.
    fn zero() -> Literal
    {
        Literal::Integer(IntegerLiteral::new(Sign::NonNegative, Magnitude::zero()))
    }

    #[test]
    fn each_verdict_projects_to_its_typing()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let literal = arena.value_literal(zero());
        let (verdict, typing) = judged(
            arena,
            Maybe::Present(integer),
            Maybe::Present(literal),
            CheckBudget::DEFAULT,
        );
        let Verdict::Checked { evidence, .. } = verdict
        else {
            panic!("a literal checks against its base type: {verdict:?}");
        };
        assert_eq!(
            typing,
            Typing::Checked {
                conversions: evidence.conversions(),
            },
            "a checked verdict keeps its conversion count"
        );

        let mut arena = CoreArena::new();
        let literal = arena.value_literal(zero());
        let (verdict, typing) = judged(
            arena,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(literal),
            CheckBudget::DEFAULT,
        );
        let Verdict::Synthesised { synthesised, .. } = verdict
        else {
            panic!("an unsigned literal synthesises: {verdict:?}");
        };
        assert_eq!(
            typing,
            Typing::Synthesised {
                produced: base(BaseType::Integer),
                conversions: synthesised.conversions(),
            },
            "a synthesised verdict carries its type as content"
        );

        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let (_verdict, typing) = judged(
            arena,
            Maybe::Present(integer),
            Maybe::Absent(body::Absent::Hole),
            CheckBudget::DEFAULT,
        );
        assert_eq!(typing, Typing::Owed, "a signed hole is owed");

        let (_verdict, typing) = judged(
            CoreArena::new(),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Absent(body::Absent::Hole),
            CheckBudget::DEFAULT,
        );
        assert_eq!(
            typing,
            Typing::Refused(Refusal::NotSynthesisable { form: Form::Hole }),
            "an unsigned hole is refused"
        );
    }

    #[test]
    fn each_refusal_projects_its_payload()
    {
        let unsigned = || Maybe::Absent(signature::Absent::Unsigned);
        let first = Site::Node(NodeIndex::from(0_usize));

        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_literal(Literal::Text(StringLiteral::new(String::from("a"))));
        let (_verdict, typing) = judged(
            arena,
            Maybe::Present(integer),
            Maybe::Present(text),
            CheckBudget::DEFAULT,
        );
        assert_eq!(
            typing,
            Typing::Refused(Refusal::TypeMismatch {
                at: Site::Node(NodeIndex::from(1_usize)),
                synthesised: base(BaseType::String),
                expected: base(BaseType::Integer),
            }),
            "a mismatch names the body's root and both types"
        );

        let mut arena = CoreArena::new();
        let dangling = arena.value_constant(ConstantIndex::from(5_usize));
        let (_verdict, typing) = judged(
            arena,
            unsigned(),
            Maybe::Present(dangling),
            CheckBudget::DEFAULT,
        );
        assert_eq!(
            typing,
            Typing::Refused(Refusal::UnknownConstant {
                at: first,
                constant: Reference::Unoccupied,
            }),
            "an unknown constant names what its position resolves to"
        );

        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let sum = arena.value_type_sum(unit, unit);
        let (_verdict, typing) = judged(
            arena,
            Maybe::Present(sum),
            Maybe::Absent(body::Absent::Hole),
            CheckBudget::DEFAULT,
        );
        assert_eq!(
            typing,
            Typing::Refused(Refusal::OutOfFragment {
                at: first,
                former: UnadmittedFormer::Sum,
            }),
            "a former without a rule names the node carrying it"
        );

        let mut arena = CoreArena::new();
        let literal = arena.value_literal(zero());
        let returned = arena.computation_return(literal);
        let thunk = arena.value_thunk(returned);
        let (_verdict, typing) = judged(
            arena,
            unsigned(),
            Maybe::Present(thunk),
            CheckBudget::DEFAULT,
        );
        assert_eq!(
            typing,
            Typing::Refused(Refusal::NotSynthesisable {
                form: Form::Thunk(first),
            }),
            "a checking-only form names its site"
        );

        let mut arena = CoreArena::new();
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let (_verdict, typing) = judged(
            arena,
            unsigned(),
            Maybe::Present(variable),
            CheckBudget::DEFAULT,
        );
        assert_eq!(
            typing,
            Typing::Refused(Refusal::UnboundIndex {
                at: first,
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
                depth: BinderDepth::from(0_usize),
            }),
            "an unbound variable names its zone, index and depth"
        );

        let mut arena = CoreArena::new();
        let literal = arena.value_literal(zero());
        let exhausted = CheckBudget::from(0_usize);
        let (_verdict, typing) = judged(arena, unsigned(), Maybe::Present(literal), exhausted);
        assert_eq!(
            typing,
            Typing::Refused(Refusal::BudgetExceeded { budget: exhausted }),
            "an exhausted allowance is named"
        );
    }
}
