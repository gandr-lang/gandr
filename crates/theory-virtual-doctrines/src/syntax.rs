//! First-order reflected types and terms.

use alloc::boxed::Box;
use alloc::vec;

use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use gandr_theory_levitation::tree::ArgumentCount;
use gandr_theory_levitation::tree::Children;
use gandr_theory_levitation::tree::Head;
use gandr_theory_levitation::tree::Tree;
use gandr_theory_levitation::tree::TreeRef;

use crate::vdc::RelationRef;
use crate::vdc::SignatureRef;
use crate::vdc::TermRef;

/// A **proterm hypothesis variable** — a name bound in the seam-composable
/// hypothesis chain `Φ`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProVar(Name);

impl ProVar
{
    /// A proterm variable of the given name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(name: NameRef<'_>) -> Self
    {
        Self(Name::from(name))
    }

    /// The variable's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn name(&self) -> NameRef<'_>
    {
        NameRef::from(self.0.as_ref())
    }
}

/// A reference to an **embedded engine derivation** — an index into the
/// checking environment's derivation registry.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DerivationId(crate::boundary::DerivationIndex);

impl DerivationId
{
    /// A derivation id from an environment index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(index: crate::boundary::DerivationIndex) -> Self
    {
        Self(index)
    }

    /// The environment index this id names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn index(self) -> crate::boundary::DerivationIndex
    {
        self.0
    }
}

impl From<crate::boundary::DerivationIndex> for DerivationId
{
    #[inline]
    /// # Specification
    /// trivial.
    fn from(value: crate::boundary::DerivationIndex) -> Self
    {
        Self::new(value)
    }
}

impl From<DerivationId> for crate::boundary::DerivationIndex
{
    #[inline]
    /// # Specification
    /// trivial.
    fn from(value: DerivationId) -> Self
    {
        value.0
    }
}

/// The head of a reflected protype; children retain declaration order.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ProtypeKind
{
    /// Path form with 0 child nodes.
    Path
    {
        /// The sig component.
        sig: SignatureRef,
        /// The lhs component.
        lhs: TermRef,
        /// The rhs component.
        rhs: TermRef,
    },
    /// Rel form with 0 child nodes.
    Rel
    {
        /// The rel component.
        rel: RelationRef,
        /// The lhs component.
        lhs: TermRef,
        /// The rhs component.
        rhs: TermRef,
    },
    /// Compose form with 2 child nodes.
    Compose
    {
        /// The mid component.
        mid: SignatureRef,
    },
    /// `ExtendR` form with 2 child nodes.
    ExtendR,
    /// `ExtendL` form with 2 child nodes.
    ExtendL,
    /// Tabulate form with 0 child nodes.
    Tabulate
    {
        /// The rel component.
        rel: RelationRef,
    },
    /// Product form with 2 child nodes.
    Product,
    /// Unit form with 0 child nodes.
    Unit,
}
impl Head for ProtypeKind
{
    /// The number of children of this form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arity(&self) -> ArgumentCount
    {
        match *self {
            | Self::Path { .. } | Self::Rel { .. } | Self::Tabulate { .. } | Self::Unit => {
                0_usize.into()
            },
            | Self::Compose { .. } | Self::ExtendR | Self::ExtendL | Self::Product => {
                2_usize.into()
            },
        }
    }
}
/// A reflected protype in a flat, nonrecursive table.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Protype(Tree<ProtypeKind>);
impl Protype
{
    /// Construct the path form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn path(
        sig: SignatureRef,
        lhs: TermRef,
        rhs: TermRef,
    ) -> Self
    {
        Self(Tree::leaf(ProtypeKind::Path { sig, lhs, rhs }))
    }
    /// Construct the rel form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rel(
        rel: RelationRef,
        lhs: TermRef,
        rhs: TermRef,
    ) -> Self
    {
        Self(Tree::leaf(ProtypeKind::Rel { rel, lhs, rhs }))
    }
    /// Construct the compose form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn compose(
        l: Self,
        mid: SignatureRef,
        r: Self,
    ) -> Self
    {
        Self(Tree::node(ProtypeKind::Compose { mid }, vec![l.0, r.0]))
    }
    /// Construct the extend r form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn extend_r(
        dom: Self,
        cod: Self,
    ) -> Self
    {
        Self(Tree::node(ProtypeKind::ExtendR, vec![dom.0, cod.0]))
    }
    /// Construct the extend l form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn extend_l(
        cod: Self,
        dom: Self,
    ) -> Self
    {
        Self(Tree::node(ProtypeKind::ExtendL, vec![dom.0, cod.0]))
    }
    /// Construct the tabulate form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tabulate(rel: RelationRef) -> Self
    {
        Self(Tree::leaf(ProtypeKind::Tabulate { rel }))
    }
    /// Construct the product form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn product(
        l: Self,
        r: Self,
    ) -> Self
    {
        Self(Tree::node(ProtypeKind::Product, vec![l.0, r.0]))
    }
    /// Construct the unit form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unit() -> Self
    {
        Self(Tree::leaf(ProtypeKind::Unit))
    }
    /// Borrow the root node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_node(&self) -> ProtypeNode<'_>
    {
        ProtypeNode(self.0.to_ref())
    }
}
/// A borrowed protype subtree.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProtypeNode<'syntax>(TreeRef<'syntax, ProtypeKind>);
impl<'syntax> ProtypeNode<'syntax>
{
    /// The node's head.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn kind(self) -> &'syntax ProtypeKind
    {
        self.0.head()
    }
    /// Iterate over child nodes in declaration order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn children(self) -> ProtypeChildren<'syntax>
    {
        ProtypeChildren(self.0.children())
    }
    /// Copy this subtree into an owned flat table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_owned(self) -> Protype
    {
        Protype(self.0.to_tree())
    }
}
/// The child nodes of a reflected protype.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct ProtypeChildren<'syntax>(Children<'syntax, ProtypeKind>);
impl<'syntax> Iterator for ProtypeChildren<'syntax>
{
    type Item = ProtypeNode<'syntax>;
    /// Advance to the next child.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.0.next().map(ProtypeNode)
    }
}

/// The head of a reflected proterm; children retain declaration order.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ProtermKind
{
    /// Var form with 0 child nodes.
    Var
    {
        /// The var component.
        var: ProVar,
    },
    /// Refl form with 0 child nodes.
    Refl
    {
        /// The sig component.
        sig: SignatureRef,
        /// The term component.
        term: TermRef,
    },
    /// `PathInd` form with 2 child nodes.
    PathInd
    {
        /// The motive component.
        motive: Box<Protype>,
    },
    /// Pair form with 2 child nodes.
    Pair
    {
        /// The via component.
        via: TermRef,
    },
    /// `SeamInd` form with 2 child nodes.
    SeamInd,
    /// Lam form with 1 child nodes.
    Lam
    {
        /// The hyp component.
        hyp: ProVar,
    },
    /// App form with 2 child nodes.
    App,
    /// `ProdIntro` form with 2 child nodes.
    ProdIntro,
    /// `ProjL` form with 1 child nodes.
    ProjL,
    /// `ProjR` form with 1 child nodes.
    ProjR,
    /// `UnitTerm` form with 0 child nodes.
    UnitTerm,
    /// Cert form with 0 child nodes.
    Cert
    {
        /// The id component.
        id: DerivationId,
    },
}
impl Head for ProtermKind
{
    /// The number of children of this form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arity(&self) -> ArgumentCount
    {
        match *self {
            | Self::Var { .. } | Self::Refl { .. } | Self::UnitTerm | Self::Cert { .. } => {
                0_usize.into()
            },
            | Self::Lam { .. } | Self::ProjL | Self::ProjR => 1_usize.into(),
            | Self::PathInd { .. }
            | Self::Pair { .. }
            | Self::SeamInd
            | Self::App
            | Self::ProdIntro => 2_usize.into(),
        }
    }
}
/// A reflected proterm in a flat, nonrecursive table.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Proterm(Tree<ProtermKind>);
impl Proterm
{
    /// Construct the var form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn var(var: ProVar) -> Self
    {
        Self(Tree::leaf(ProtermKind::Var { var }))
    }
    /// Construct the refl form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn refl(
        sig: SignatureRef,
        term: TermRef,
    ) -> Self
    {
        Self(Tree::leaf(ProtermKind::Refl { sig, term }))
    }
    /// Construct the path ind form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn path_ind(
        motive: Protype,
        base: Self,
        scrut: Self,
    ) -> Self
    {
        Self(Tree::node(
            ProtermKind::PathInd {
                motive: Box::new(motive),
            },
            vec![base.0, scrut.0],
        ))
    }
    /// Construct the pair form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pair(
        l: Self,
        via: TermRef,
        r: Self,
    ) -> Self
    {
        Self(Tree::node(ProtermKind::Pair { via }, vec![l.0, r.0]))
    }
    /// Construct the seam ind form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn seam_ind(
        scrut: Self,
        arm: Self,
    ) -> Self
    {
        Self(Tree::node(ProtermKind::SeamInd, vec![scrut.0, arm.0]))
    }
    /// Construct the lam form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lam(
        hyp: ProVar,
        body: Self,
    ) -> Self
    {
        Self(Tree::node(ProtermKind::Lam { hyp }, vec![body.0]))
    }
    /// Construct the app form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn app(
        f: Self,
        arg: Self,
    ) -> Self
    {
        Self(Tree::node(ProtermKind::App, vec![f.0, arg.0]))
    }
    /// Construct the prod intro form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn prod_intro(
        l: Self,
        r: Self,
    ) -> Self
    {
        Self(Tree::node(ProtermKind::ProdIntro, vec![l.0, r.0]))
    }
    /// Construct the proj l form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn proj_l(term: Self) -> Self
    {
        Self(Tree::node(ProtermKind::ProjL, vec![term.0]))
    }
    /// Construct the proj r form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn proj_r(term: Self) -> Self
    {
        Self(Tree::node(ProtermKind::ProjR, vec![term.0]))
    }
    /// Construct the unit term form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unit_term() -> Self
    {
        Self(Tree::leaf(ProtermKind::UnitTerm))
    }
    /// Construct the cert form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cert(id: DerivationId) -> Self
    {
        Self(Tree::leaf(ProtermKind::Cert { id }))
    }
    /// Borrow the root node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_node(&self) -> ProtermNode<'_>
    {
        ProtermNode(self.0.to_ref())
    }
}
/// A borrowed proterm subtree.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProtermNode<'syntax>(TreeRef<'syntax, ProtermKind>);
impl<'syntax> ProtermNode<'syntax>
{
    /// The node's head.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn kind(self) -> &'syntax ProtermKind
    {
        self.0.head()
    }
    /// Iterate over child nodes in declaration order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn children(self) -> ProtermChildren<'syntax>
    {
        ProtermChildren(self.0.children())
    }
    /// Copy this subtree into an owned flat table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_owned(self) -> Proterm
    {
        Proterm(self.0.to_tree())
    }
}
/// The child nodes of a reflected proterm.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct ProtermChildren<'syntax>(Children<'syntax, ProtermKind>);
impl<'syntax> Iterator for ProtermChildren<'syntax>
{
    type Item = ProtermNode<'syntax>;
    /// Advance to the next child.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.0.next().map(ProtermNode)
    }
}
