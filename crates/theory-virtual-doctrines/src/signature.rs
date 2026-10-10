//! Flat reflected signature products.

use alloc::boxed::Box;

use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::tree::ArgumentCount;
use gandr_theory_levitation::tree::Children;
use gandr_theory_levitation::tree::Head;
use gandr_theory_levitation::tree::Tree;
use gandr_theory_levitation::tree::TreeRef;
use quenchant_shape::shape::Maybe;

/// A signature root without recursive ownership.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum SignatureKind
{
    /// A nominal signature.
    Single(NominalId),
    /// A finite product, including the terminal empty product.
    Product(ArgumentCount),
}
impl Head for SignatureKind
{
    /// The number of immediate product factors.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arity(&self) -> ArgumentCount
    {
        match self {
            | &Self::Single(_) => 0_usize.into(),
            | &Self::Product(count) => count,
        }
    }
}
/// A reflected nominal signature or finite nested product, stored flat.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SignatureRef(Tree<SignatureKind>);
quenchant_shape::reason_enum! {
/// Why a signature has no product factors.
pub mod product_shape {
    /// The reason the requested value is unavailable.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Absent {
    /// The signature is nominal rather than a product.
    Nominal,
}
}
}
impl SignatureRef
{
    /// Refer to one nominal signature.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn single(id: NominalId) -> Self
    {
        Self(Tree::leaf(SignatureKind::Single(id)))
    }
    /// The terminal signature.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unit() -> Self
    {
        Self(Tree::leaf(SignatureKind::Product(0_usize.into())))
    }
    /// Build a finite product in factor order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn product(parts: Box<[Self]>) -> Self
    {
        let width = parts.len().into();
        Self(Tree::node(
            SignatureKind::Product(width),
            parts.into_vec().into_iter().map(|part| part.0).collect(),
        ))
    }
    /// Borrow a product's factors, distinguishing nominal signatures.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn parts(&self) -> Maybe<SignatureParts<'_>, product_shape::Absent>
    {
        match self.0.to_ref().head() {
            | &SignatureKind::Single(_) => Maybe::Absent(product_shape::Absent::Nominal),
            | &SignatureKind::Product(_) => {
                Maybe::Present(SignatureParts(self.0.to_ref().children()))
            },
        }
    }
    /// Borrow the complete signature.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_node(&self) -> SignatureNode<'_>
    {
        SignatureNode(self.0.to_ref())
    }
}
/// A borrowed factor, retaining nested product structure.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SignatureNode<'signature>(TreeRef<'signature, SignatureKind>);
/// Immediate factors of a product signature.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct SignatureParts<'signature>(Children<'signature, SignatureKind>);
impl<'signature> Iterator for SignatureParts<'signature>
{
    type Item = SignatureNode<'signature>;
    /// Advance to the next factor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.0.next().map(SignatureNode)
    }
}
