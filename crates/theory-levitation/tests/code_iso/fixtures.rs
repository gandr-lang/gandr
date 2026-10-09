//! The monomorphic descriptions, named certificates and finite value samples
//! the certificate suite exercises.
//!
//! Every description is parameter-free, and all but `IntBox` are finite (no
//! recursive occurrence), so the whole value space of each is a short list —
//! the sample sets below. The flagship cross-code instance is the declared
//! two-constructor `Boolean` (the crate's retrofit) against the inline `1 + 1`
//! sum form `BoolSum`.

use alloc::sync::Arc;

use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::ConstructorTag;
use gandr_theory_levitation::CtorDesc;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::DescValue;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::Payload;
use gandr_theory_levitation::PayloadView;
use gandr_theory_levitation::PrimTy;
use gandr_theory_levitation::Side;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::ValueTypeRef;
use gandr_theory_levitation::bool_desc;

use super::harness::CodeIso;
use super::harness::Translate;
use crate::support::Grade;

/// The value of constructor `index` with the unit payload.
///
/// # Specification
/// trivial.
fn nullary_value(index: ConstructorTag) -> DescValue
{
    DescValue::new(index, Payload::unit())
}

/// A nullary constructor of the given name (payload code `1`), targeting the
/// result sort `of`.
///
/// # Specification
/// trivial.
fn nullary<N, R>(
    name: N,
    of: R,
) -> CtorDesc<Grade>
where
    N: Into<Name>,
    R: Into<Name>,
{
    CtorDesc::new(name, Code::unit(), of, Attrs::empty())
}

/// A left injection into an inline sum.
///
/// # Specification
/// trivial.
fn inl(payload: Payload) -> Payload
{
    Payload::inj(Side::Left, payload)
}

/// A right injection into an inline sum.
///
/// # Specification
/// trivial.
fn inr(payload: Payload) -> Payload
{
    Payload::inj(Side::Right, payload)
}

/// The declared two-constructor `Boolean` (`False = 1`, `True = 1`): the
/// crate's retrofit, one side of the flagship instance.
///
/// # Specification
/// trivial.
pub fn bool_two_ctor() -> SignDesc<Grade>
{
    bool_desc()
}

/// The inline `1 + 1` Boolean (`BoolSum { MkBool = (1 + 1) }`): one
/// constructor whose payload is the inline sum, the other side of the
/// flagship instance — a structurally distinct code over the same
/// two-element value space.
///
/// # Specification
/// trivial.
pub fn bool_sum() -> SignDesc<Grade>
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(1_u64), "BoolSum"),
        Vec::new(),
        [CtorDesc::new(
            "MkBool",
            Code::sum(Code::unit(), Code::unit()),
            "BoolSum",
            Attrs::empty(),
        )],
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// A three-constructor enum (`RGB { R = 1, G = 1, B = 1 }`): the carrier of a
/// non-involutive auto-isomorphism, so composition and inverse have content
/// beyond the self-inverse Boolean cases.
///
/// # Specification
/// trivial.
pub fn rgb() -> SignDesc<Grade>
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(2_u64), "RGB"),
        Vec::new(),
        [
            nullary("R", "RGB"),
            nullary("G", "RGB"),
            nullary("B", "RGB"),
        ],
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// The two values of [`bool_two_ctor`]: `False` (tag 0) and `True` (tag 1).
///
/// # Specification
/// trivial.
pub fn bool_two_ctor_values() -> Vec<DescValue>
{
    vec![
        nullary_value(ConstructorTag::from(0_usize)),
        nullary_value(ConstructorTag::from(1_usize)),
    ]
}

/// The two values of [`bool_sum`]: `MkBool(Inl ())` and `MkBool(Inr ())`.
///
/// # Specification
/// trivial.
pub fn bool_sum_values() -> Vec<DescValue>
{
    vec![
        DescValue::new(ConstructorTag::from(0_usize), inl(Payload::unit())),
        DescValue::new(ConstructorTag::from(0_usize), inr(Payload::unit())),
    ]
}

/// The three values of [`rgb`]: `R`, `G`, `B`.
///
/// # Specification
/// trivial.
pub fn rgb_values() -> Vec<DescValue>
{
    vec![
        nullary_value(ConstructorTag::from(0_usize)),
        nullary_value(ConstructorTag::from(1_usize)),
        nullary_value(ConstructorTag::from(2_usize)),
    ]
}

/// The identity auto-isomorphism on [`bool_two_ctor`], the groupoid unit at
/// `(Boolean, Boolean)`.
///
/// # Specification
/// trivial.
pub fn identity_bool() -> CodeIso
{
    CodeIso::identity("id[Boolean]", bool_two_ctor())
}

/// The negation auto-isomorphism on [`bool_two_ctor`]: swaps `False` and
/// `True`, its own inverse, and replay-distinct from [`identity_bool`].
///
/// # Specification
/// trivial.
pub fn negation_bool() -> CodeIso
{
    let flip: Translate = Arc::new(|value: &DescValue| match usize::from(value.ctor) {
        | 0 => nullary_value(ConstructorTag::from(1_usize)),
        | _ => nullary_value(ConstructorTag::from(0_usize)),
    });
    CodeIso::new(
        "negation",
        bool_two_ctor(),
        bool_two_ctor(),
        Arc::clone(&flip),
        flip,
    )
}

/// The flagship cross-code bridge `Boolean → BoolSum`: `False ↦ MkBool(Inl
/// ())`, `True ↦ MkBool(Inr ())` — an isomorphism between two structurally
/// distinct codes, which decidable code equality cannot identify.
///
/// # Specification
/// trivial.
pub fn bool_bridge() -> CodeIso
{
    let forward: Translate = Arc::new(|value: &DescValue| match usize::from(value.ctor) {
        | 0 => DescValue::new(ConstructorTag::from(0_usize), inl(Payload::unit())),
        | _ => DescValue::new(ConstructorTag::from(0_usize), inr(Payload::unit())),
    });
    let backward: Translate = Arc::new(|value: &DescValue| {
        if matches!(value.payload.view(), PayloadView::Inj {
            side: Side::Right,
            ..
        }) {
            nullary_value(ConstructorTag::from(1_usize))
        }
        else {
            nullary_value(ConstructorTag::from(0_usize))
        }
    });
    CodeIso::new(
        "Boolean ⨟ BoolSum",
        bool_two_ctor(),
        bool_sum(),
        forward,
        backward,
    )
}

/// The rotation auto-isomorphism on [`rgb`]: `R → G → B → R`. Not an
/// involution, so its cube is the identity up to replay.
///
/// # Specification
/// trivial.
pub fn rgb_rotate() -> CodeIso
{
    let forward: Translate = Arc::new(|value: &DescValue| {
        let next = match usize::from(value.ctor) {
            | 0 => 1_usize,
            | 1 => 2_usize,
            | _ => 0_usize,
        };
        nullary_value(ConstructorTag::from(next))
    });
    let backward: Translate = Arc::new(|value: &DescValue| {
        let previous = match usize::from(value.ctor) {
            | 0 => 2_usize,
            | 1 => 0_usize,
            | _ => 1_usize,
        };
        nullary_value(ConstructorTag::from(previous))
    });
    CodeIso::new("rgb-rotate", rgb(), rgb(), forward, backward)
}

/// The single-constructor `IntBox` description (`Box = Integer`): one field
/// over the unbounded `Integer` leaf. With one constructor the structural
/// (constructor-permuting) auto-isomorphism group is trivial, so a
/// nontrivial auto-isomorphism must move the leaf.
///
/// # Specification
/// trivial.
pub fn int_box() -> SignDesc<Grade>
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(3_u64), "IntBox"),
        Vec::new(),
        [CtorDesc::new(
            "Box",
            Code::field(
                ValueTypeRef::prim(PrimTy::Integer),
                Grade::One,
                Attrs::empty(),
            ),
            "IntBox",
            Attrs::empty(),
        )],
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// A finite integer an `IntBox` sample carries.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct IntBoxLeaf(i64);

impl IntBoxLeaf
{
    /// Zero, the first replay sample.
    pub const ZERO: Self = Self(0);

    /// One, the successor image of zero.
    pub const ONE: Self = Self(1);

    /// Two, the second positive replay sample.
    const TWO: Self = Self(2);

    /// Negative one, the first negative replay sample.
    const NEGATIVE_ONE: Self = Self(-1);

    /// Negative two, the second negative replay sample.
    const NEGATIVE_TWO: Self = Self(-2);

    /// The successor, representable for every sample.
    ///
    /// # Specification
    /// trivial.
    fn successor(self) -> Self
    {
        Self(
            self.0
                .checked_add(1)
                .expect("the sampled IntBox successor is representable"),
        )
    }

    /// The predecessor, representable for every sample.
    ///
    /// # Specification
    /// trivial.
    fn predecessor(self) -> Self
    {
        Self(
            self.0
                .checked_sub(1)
                .expect("the sampled IntBox predecessor is representable"),
        )
    }
}

/// An [`int_box`] value carrying `n`: constructor `Box` (tag 0) over the
/// decimal-ASCII spelling of `n`, unbounded in length as `Integer`'s leaf is.
///
/// # Specification
/// trivial.
pub fn int_leaf(n: IntBoxLeaf) -> DescValue
{
    DescValue::new(
        ConstructorTag::from(0_usize),
        Payload::leaf(n.0.to_string().into_bytes()),
    )
}

/// The integer an [`int_box`] value carries: its decimal-ASCII leaf parsed.
///
/// # Specification
/// - requires: `value` was built by [`int_leaf`].
/// - panics: on any other value, a fixture error.
fn read_int_leaf(value: &DescValue) -> IntBoxLeaf
{
    let PayloadView::Leaf(bytes) = value.payload.view()
    else {
        panic!("an IntBox value carries a leaf payload");
    };
    let parsed = core::str::from_utf8(bytes.as_ref())
        .expect("the IntBox leaf is decimal-ASCII")
        .parse::<i64>()
        .expect("the IntBox leaf parses as an integer");
    IntBoxLeaf(parsed)
}

/// A finite sample of [`int_box`] values, `0` first, so the earliest replay
/// disagreement with the identity is at `0`.
///
/// # Specification
/// trivial.
pub fn int_box_values() -> Vec<DescValue>
{
    [
        IntBoxLeaf::ZERO,
        IntBoxLeaf::ONE,
        IntBoxLeaf::TWO,
        IntBoxLeaf::NEGATIVE_ONE,
        IntBoxLeaf::NEGATIVE_TWO,
    ]
    .into_iter()
    .map(int_leaf)
    .collect()
}

/// The identity auto-isomorphism on [`int_box`], its sole structural member.
///
/// # Specification
/// trivial.
pub fn int_box_identity() -> CodeIso
{
    CodeIso::identity("id[IntBox]", int_box())
}

/// The leaf-shift auto-isomorphism on [`int_box`]: forward is the successor,
/// backward the predecessor. Its round trips hold on every integer, yet it
/// reads and rewrites the leaf content, so no structural certificate replays
/// it.
///
/// # Specification
/// trivial.
pub fn leaf_shift() -> CodeIso
{
    let forward: Translate =
        Arc::new(|value: &DescValue| int_leaf(read_int_leaf(value).successor()));
    let backward: Translate =
        Arc::new(|value: &DescValue| int_leaf(read_int_leaf(value).predecessor()));
    CodeIso::new("leaf-shift", int_box(), int_box(), forward, backward)
}
