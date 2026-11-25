//! The free distributive lattice on at most 64 generators in normal form, and
//! its spectrum, the cube.
//!
//! A polynomial is the join of an antichain of terms, and a term is the meet
//! of a set of generators. The normal form is unique: absorption removes
//! every term that another term of the join lies below, and the rest are
//! sorted by their bits. A polynomial holds at a vertex of the cube when one
//! of its terms holds there, so it reads as a monotone truth table. A
//! homomorphism sends each generator to a polynomial, and it is dual to a
//! monotone map of cubes in the other direction.
//!
//! On the cube of at most six axes a polynomial is also one word, its truth
//! table. Meet, join and substitution there run on that word and read the
//! normal form back from its minimal vertices. Past six generators they run
//! on the antichains.

use alloc::vec::Vec;
use core::ops::Deref;

use anodized::spec;

use crate::error::DualityError;
use crate::index::Comparison;
use crate::index::Generator;
use crate::index::GeneratorCount;
use crate::index::Membership;
use crate::index::WIDEST;
use crate::index::WIDEST_CUBE;

wrapper! {
    /// A term: the meet of a set of generators, as a bit set over the
    /// generators. The empty set is `⊤`.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Term(u64);
}

wrapper! {
    /// A vertex of a cube: the set of axes at which it is `1`, as a bit set.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Vertex(u64);
}

wrapper! {
    /// A truth table on a cube of at most six axes: the set of vertices where
    /// it holds, as a bit set over the vertices.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Table(u64);
}

/// The term of one generator, or the refusal of a generator past one machine
/// word.
///
/// # Specification
/// - ensures: the term holds exactly `generator`.
/// - fails: a generator at or past 64 is refused by name.
/// - panics: none.
///
/// # Errors
/// - [`DualityError::GeneratorOutside`]: `generator` is at or past 64.
///
/// # Adequacy
/// - hypothesis: L3 — generators 63 and 64 separate the word's bound.
/// - witness: `tests::free::generators_and_terms_are_checked_by_index`
#[spec(ensures: |ref ret| match *ret {
    Ok(term) => term.0.is_power_of_two(),
    Err(error) => error == DualityError::GeneratorOutside(generator),
})]
fn generator_bit(generator: Generator) -> Result<Term, DualityError>
{
    let outside = DualityError::GeneratorOutside(generator);
    let shift = u32::try_from(usize::from(generator)).map_err(|_overflow| outside)?;
    1_u64.checked_shl(shift).map(Term).ok_or(outside)
}

/// The table that holds at every vertex of the cube on `axes` axes.
///
/// # Specification
/// - ensures: the table holds at the `2^axes` least vertices and nowhere else.
/// - fails: a cube of more than six axes is refused.
/// - panics: none.
///
/// # Errors
/// - [`DualityError::TooWide`]: `axes` is past six.
///
/// # Adequacy
/// - hypothesis: L3 — six and seven axes separate the bound, and zero axes
///   gives the one vertex.
/// - witness: `tests::free::polynomials_and_monotone_tables_go_one_to_one`
#[spec(ensures: |ref ret| match *ret {
    Ok(table) => table.0 != 0,
    Err(error) => error == DualityError::TooWide(axes),
})]
fn whole_cube(axes: GeneratorCount) -> Result<Table, DualityError>
{
    let too_wide = DualityError::TooWide(axes);
    if usize::from(axes) > WIDEST_CUBE {
        return Err(too_wide);
    }
    let width = u32::try_from(usize::from(axes)).map_err(|_overflow| too_wide)?;
    let vertices = 1_u32.checked_shl(width).ok_or(too_wide)?;
    let unused = 64_u32.checked_sub(vertices).ok_or(too_wide)?;
    u64::MAX.checked_shr(unused).map(Table).ok_or(too_wide)
}

/// The vertices of the cube on six axes that are `1` on each axis, one word
/// per axis. The cube on fewer axes holds the least `2^axes` bits of each.
/// Raising a vertex along axis `i` moves its bit up by `2^i` places, so one
/// shift of a word raises every vertex of a table at once.
const AXIS_VERTICES: [u64; WIDEST_CUBE] = [
    0xAAAA_AAAA_AAAA_AAAA,
    0xCCCC_CCCC_CCCC_CCCC,
    0xF0F0_F0F0_F0F0_F0F0,
    0xFF00_FF00_FF00_FF00,
    0xFFFF_0000_FFFF_0000,
    0xFFFF_FFFF_0000_0000,
];

/// The number of places a vertex's bit moves when the vertex is raised along
/// each axis: `2^axis`.
const AXIS_STEPS: [u32; WIDEST_CUBE] = [1, 2, 4, 8, 16, 32];

/// The vertices of the cube on six axes at or above a term: the meet of the
/// upper halves of its axes. A generator at or past six has no upper half
/// here, so a term that meets one has no vertex.
///
/// # Specification
/// - ensures: `⊤` holds at every vertex.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every polynomial on up to four generators, against its
///   truth table, separates a lost axis.
/// - witness: `tests::free::polynomials_and_monotone_tables_go_one_to_one`
#[spec(ensures: |ret| term != Term::TOP || ret.0 == u64::MAX)]
fn up_set(term: Term) -> Table
{
    Table(term.generators().fold(u64::MAX, |above, generator| {
        above
            & AXIS_VERTICES
                .get(usize::from(generator))
                .copied()
                .unwrap_or(0)
    }))
}

/// The vertices of the cube on six axes that lie one axis above a vertex of
/// `table`: each vertex of the table raised along each axis, one shift of the
/// word per axis.
///
/// # Specification
/// - ensures: the least vertex lies above no vertex.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every pair of polynomials on three generators, their meet
///   and join read back from their tables, separates a kept vertex that lies
///   above another.
/// - witness: `tests::free::meet_join_and_order_follow_the_tables`
#[spec(ensures: |ret| ret.0 & 1 == 0)]
fn covered(table: Table) -> Table
{
    Table(
        AXIS_VERTICES
            .iter()
            .zip(AXIS_STEPS)
            .fold(0_u64, |raised, (upper_half, step)| {
                raised | (table.0 & !upper_half).checked_shl(step).unwrap_or(0)
            }),
    )
}

impl Term
{
    /// `⊤`, the meet of no generator.
    pub const TOP: Self = Self(0);

    /// The term of one generator.
    ///
    /// # Specification
    /// - ensures: the term holds exactly `generator`.
    /// - fails: a generator at or past 64 is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::GeneratorOutside`]: `generator` is at or past 64.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generators 63 and 64 separate the word's bound.
    /// - witness: `tests::free::generators_and_terms_are_checked_by_index`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(term) => term.0.is_power_of_two(),
        Err(error) => error == DualityError::GeneratorOutside(generator),
    })]
    pub fn generator(generator: Generator) -> Result<Self, DualityError>
    {
        generator_bit(generator)
    }

    /// The meet of two terms: the union of their generators.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn meet(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 | other.0)
    }

    /// Whether this term lies below `other` in the lattice: every generator
    /// of `other` is a generator of this term.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn compare(
        self,
        other: Self,
    ) -> Comparison
    {
        if self.0 & other.0 == other.0 {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }

    /// Whether the term holds at a vertex: every generator of the term is
    /// `1` there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn holds_at(
        self,
        vertex: Vertex,
    ) -> Membership
    {
        if self.0 & vertex.0 == self.0 {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// The generators the term meets, in increasing order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn generators(self) -> impl Iterator<Item = Generator>
    {
        ones!(self.0, Generator::from)
    }

    /// One past the highest generator of the term, and zero for `⊤`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn reach(self) -> GeneratorCount
    {
        let unused = usize::try_from(self.0.leading_zeros()).unwrap_or(WIDEST);
        GeneratorCount::from(WIDEST.saturating_sub(unused))
    }
}

impl Vertex
{
    /// Whether the vertex is `1` on an axis.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn on(
        self,
        axis: Generator,
    ) -> Membership
    {
        match generator_bit(axis) {
            Ok(bit) if self.0 & bit.0 != 0 => Membership::Inside,
            Ok(_) | Err(_) => Membership::Outside,
        }
    }

    /// Whether this vertex lies below `other` in the cube, axis by axis.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn compare(
        self,
        other: Self,
    ) -> Comparison
    {
        if self.0 & other.0 == self.0 {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

impl Table
{
    /// Whether the table holds at a vertex. A vertex past the table's word
    /// lies outside it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn holds_at(
        self,
        vertex: Vertex,
    ) -> Membership
    {
        let bit = u32::try_from(vertex.0)
            .ok()
            .and_then(|shift| 1_u64.checked_shl(shift))
            .unwrap_or(0);
        if self.0 & bit == 0 {
            Membership::Outside
        }
        else {
            Membership::Inside
        }
    }

    /// The vertices where the table holds, in increasing order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn vertices(self) -> impl Iterator<Item = Vertex>
    {
        ones!(self.0, |index| Vertex(
            u64::try_from(index).unwrap_or(u64::MAX)
        ))
    }
}

/// The most terms an antichain holds in place, with no allocation: every
/// antichain of the cube on two axes, and most of three and four.
const INLINE: usize = 4;

/// The terms of a polynomial's antichain: at most [`INLINE`] of them in
/// place, and more on the heap. The form is canonical, so the derived
/// equality is the equality of the terms.
///
/// # Specification
/// - ensures: the heap holds more than [`INLINE`] terms, and the entries past
///   `count` in place are `⊤`.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the constructors',
///   each of which keeps it.
///
/// # Adequacy
/// - hypothesis: L2 — every monotone table on up to four axes, whose antichains
///   reach six terms, read back and rebuilt from its own terms, compares equal
///   on both sides of the bound.
/// - witness: `tests::free::polynomials_and_monotone_tables_go_one_to_one`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Antichain
{
    /// The first `count` entries of `terms`.
    Inline
    {
        /// How many entries are in use.
        count: u8,
        /// The entries, each past `count` the term `⊤`.
        terms: [Term; INLINE],
    },
    /// More than [`INLINE`] terms.
    Heap(Vec<Term>),
}

impl Antichain
{
    /// The antichain of no term, which is `⊥`'s.
    const EMPTY: Self = Self::Inline {
        count: 0,
        terms: [Term::TOP; INLINE],
    };

    /// The antichain of one term.
    ///
    /// # Specification
    /// trivial.
    fn one(term: Term) -> Self
    {
        let mut terms = [Term::TOP; INLINE];
        if let Some(first) = terms.first_mut() {
            *first = term;
        }
        Self::Inline { count: 1, terms }
    }

    /// The antichain of the vertices of `minimal`, each read as a term, in
    /// place when they are few.
    ///
    /// # Specification
    /// trivial.
    fn of_vertices(minimal: Table) -> Self
    {
        let count = usize::try_from(minimal.0.count_ones()).unwrap_or(usize::MAX);
        if count > INLINE {
            let mut terms = Vec::with_capacity(count);
            terms.extend(minimal.vertices().map(|vertex| Term(vertex.0)));
            return Self::Heap(terms);
        }
        let mut terms = [Term::TOP; INLINE];
        for (slot, vertex) in terms.iter_mut().zip(minimal.vertices()) {
            *slot = Term(vertex.0);
        }
        Self::Inline {
            count: u8::try_from(count).unwrap_or(0),
            terms,
        }
    }
}

impl From<Vec<Term>> for Antichain
{
    /// The antichain of `terms`, an antichain already, in place when they
    /// are few.
    ///
    /// # Specification
    /// trivial.
    fn from(terms: Vec<Term>) -> Self
    {
        if terms.len() > INLINE {
            return Self::Heap(terms);
        }
        let mut inline = [Term::TOP; INLINE];
        for (slot, term) in inline.iter_mut().zip(&terms) {
            *slot = *term;
        }
        Self::Inline {
            count: u8::try_from(terms.len()).unwrap_or(0),
            terms: inline,
        }
    }
}

impl Default for Antichain
{
    /// The antichain of no term.
    ///
    /// # Specification
    /// trivial.
    fn default() -> Self
    {
        Self::EMPTY
    }
}

impl Deref for Antichain
{
    type Target = [Term];

    /// The terms in use.
    ///
    /// # Specification
    /// trivial.
    fn deref(&self) -> &[Term]
    {
        match *self {
            Self::Inline { count, ref terms } => terms.get(.. usize::from(count)).unwrap_or(&[]),
            Self::Heap(ref terms) => terms,
        }
    }
}

/// The normal form of the join of `terms`: each term that no other term of
/// the join lies below, sorted by their bits, in the buffer of `terms`.
///
/// # Specification
/// - ensures: the result is sorted and distinct, and it is empty exactly when
///   `terms` is.
/// - panics: none.
/// - intension: one sort and one pass that tests each term against the terms
///   kept before it, so the time is quadratic in the number of terms at worst,
///   and the buffer of `terms` is the result's.
///
/// # Adequacy
/// - hypothesis: L2 — every set of terms on up to three generators, against the
///   minimal vertices of its truth table, separates a kept absorbed term, a
///   lost minimal term and an unsorted result.
/// - witness: `tests::free::meet_join_and_order_follow_the_tables`
#[spec(ensures: |ref ret| ret.len() <= 1 || ret.first() < ret.last())]
fn normalised(mut terms: Vec<Term>) -> Vec<Term>
{
    terms.sort_unstable_by_key(|term| (term.0.count_ones(), term.0));
    terms.dedup();
    let mut kept = 0_usize;
    for index in 0 .. terms.len() {
        let Some(&candidate) = terms.get(index)
        else {
            break;
        };
        let absorbed = terms.get(.. kept).is_some_and(|antichain| {
            antichain
                .iter()
                .any(|smaller| candidate.compare(*smaller) == Comparison::Below)
        });
        if absorbed {
            continue;
        }
        if let Some(slot) = terms.get_mut(kept) {
            *slot = candidate;
        }
        kept = kept.saturating_add(1);
    }
    terms.truncate(kept);
    terms.sort_unstable();
    terms
}

/// An element of a free distributive lattice in normal form: the join of an
/// antichain of terms, sorted by their bits. The empty join is `⊥`.
///
/// # Specification
/// - ensures: no term lies below another, and the terms are sorted and
///   distinct, so two equal elements have equal forms.
/// - provides: meet, join, order and evaluation at a vertex.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the constructors',
///   each of which checks it.
///
/// # Adequacy
/// - hypothesis: L2 — every polynomial on up to four generators, against its
///   truth table, separates a lost term, a kept absorbed term and an order that
///   depends on the input.
/// - witness: `tests::free::meet_join_and_order_follow_the_tables`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Polynomial
{
    /// The antichain of terms, sorted by their bits.
    terms: Antichain,
}

impl Polynomial
{
    /// `⊥`, the join of no term.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bottom() -> Self
    {
        Self {
            terms: Antichain::EMPTY,
        }
    }

    /// `⊤`, the empty term alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn top() -> Self
    {
        Self::term(Term::TOP)
    }

    /// The polynomial of one term.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn term(term: Term) -> Self
    {
        Self {
            terms: Antichain::one(term),
        }
    }

    /// The polynomial of one generator.
    ///
    /// # Specification
    /// - ensures: the polynomial is the term of `generator` alone.
    /// - fails: a generator at or past 64 is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::GeneratorOutside`]: `generator` is at or past 64.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generators 63 and 64 separate the word's bound.
    /// - witness: `tests::free::generators_and_terms_are_checked_by_index`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref polynomial) => polynomial.terms.len() == 1,
        Err(error) => error == DualityError::GeneratorOutside(generator),
    })]
    pub fn generator(generator: Generator) -> Result<Self, DualityError>
    {
        let term = generator_bit(generator)?;
        Ok(Self::term(term))
    }

    /// The normal form of the join of `terms`: each term that no other term
    /// of the join lies below, sorted by their bits.
    ///
    /// # Specification
    /// - ensures: the result is the join of `terms` in normal form; it is empty
    ///   exactly when `terms` is.
    /// - panics: none.
    /// - intension: the absorption of [`normalised`], whose buffer is the
    ///   result's, or none when the result fits in place.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every set of terms on up to three generators, against
    ///   the minimal vertices of its truth table, separates a kept absorbed
    ///   term, a lost minimal term and an unsorted result.
    /// - witness: `tests::free::meet_join_and_order_follow_the_tables`
    #[spec(ensures: |ref ret| ret.terms.len() <= 1 || ret.terms.first() < ret.terms.last())]
    #[must_use]
    #[inline]
    pub fn from_terms(terms: Vec<Term>) -> Self
    {
        Self {
            terms: Antichain::from(normalised(terms)),
        }
    }

    /// The terms of the antichain, sorted by their bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn terms(&self) -> &[Term]
    {
        &self.terms
    }

    /// The join of two polynomials: their terms together, in normal form.
    ///
    /// # Specification
    /// - ensures: the result holds at a vertex exactly when one of the two
    ///   does.
    /// - panics: none.
    /// - intension: in the cube on six axes, one word operation on the two
    ///   truth tables and the minimal vertices read back. Past it, one buffer
    ///   of both antichains' terms, normalised once.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of polynomials on up to three generators,
    ///   against the union of their tables, and the same pairs spread to eight
    ///   generators, separate a meet taken for a join and a lost term on each
    ///   path.
    /// - witness: `tests::free::meet_join_and_order_follow_the_tables`
    #[spec(ensures: |ref ret| ret.terms.len() <= self.terms.len().saturating_add(other.terms.len()))]
    #[must_use]
    #[inline]
    pub fn join(
        &self,
        other: &Self,
    ) -> Self
    {
        if let (Some(left), Some(right)) = (self.cube_table(), other.cube_table()) {
            return Self::of_monotone(Table(left.0 | right.0));
        }
        let mut terms = Vec::with_capacity(self.terms.len().saturating_add(other.terms.len()));
        terms.extend_from_slice(&self.terms);
        terms.extend_from_slice(&other.terms);
        Self::from_terms(terms)
    }

    /// The meet of two polynomials: each term of one met with each term of
    /// the other, in normal form.
    ///
    /// # Specification
    /// - ensures: the result holds at a vertex exactly when both do.
    /// - panics: none.
    /// - intension: in the cube on six axes, one word operation on the two
    ///   truth tables and the minimal vertices read back. Past it, one buffer
    ///   of the product of the antichains' sizes, normalised once.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of polynomials on up to three generators,
    ///   against the intersection of their tables, and the same pairs spread to
    ///   eight generators, separate a join taken for a meet and a lost term on
    ///   each path.
    /// - witness: `tests::free::meet_join_and_order_follow_the_tables`
    #[spec(ensures: |ref ret| ret.terms.len() <= self.terms.len().saturating_mul(other.terms.len()))]
    #[must_use]
    #[inline]
    pub fn meet(
        &self,
        other: &Self,
    ) -> Self
    {
        if let (Some(left), Some(right)) = (self.cube_table(), other.cube_table()) {
            return Self::of_monotone(Table(left.0 & right.0));
        }
        let mut terms = Vec::with_capacity(self.terms.len().saturating_mul(other.terms.len()));
        for outer in self.terms.iter() {
            terms.extend(other.terms.iter().map(|inner| outer.meet(*inner)));
        }
        Self::from_terms(terms)
    }

    /// Whether this polynomial lies below `other`: each of its terms lies
    /// below a term of `other`.
    ///
    /// # Specification
    /// - ensures: `Below` exactly when the table of `self` is included in the
    ///   table of `other`; `⊥` lies below every polynomial.
    /// - panics: none.
    /// - intension: in the cube on six axes, one inclusion of the two truth
    ///   tables. Past it, the join with `other` equals `other` exactly when
    ///   `self` lies below, so the order costs one join.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of polynomials on up to three generators,
    ///   against the inclusion of their tables, separates a reversed order and
    ///   an order read from one term.
    /// - witness: `tests::free::meet_join_and_order_follow_the_tables`
    #[spec(ensures: |ret| !self.terms.is_empty() || ret == Comparison::Below)]
    #[must_use]
    #[inline]
    pub fn compare(
        &self,
        other: &Self,
    ) -> Comparison
    {
        let below = match (self.cube_table(), other.cube_table()) {
            (Some(lower), Some(upper)) => lower.0 & !upper.0 == 0,
            _ => self.join(other) == *other,
        };
        if below {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }

    /// Whether the polynomial holds at a vertex: one of its terms holds
    /// there.
    ///
    /// # Specification
    /// - ensures: `⊥` holds nowhere, and `⊤` holds at every vertex.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every polynomial on up to four generators at every
    ///   vertex, against its minimal vertices, separates `any` taken for `all`.
    /// - witness: `tests::free::polynomials_and_monotone_tables_go_one_to_one`
    #[spec(ensures: |ret| !self.terms.is_empty() || ret == Membership::Outside)]
    #[must_use]
    #[inline]
    pub fn holds_at(
        &self,
        vertex: Vertex,
    ) -> Membership
    {
        if self
            .terms
            .iter()
            .any(|term| term.holds_at(vertex) == Membership::Inside)
        {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// One past the highest generator of the polynomial, and zero for a
    /// polynomial of no generator.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn reach(&self) -> GeneratorCount
    {
        self.terms
            .iter()
            .map(|term| term.reach())
            .max()
            .unwrap_or_default()
    }

    /// The truth table of the polynomial on the cube of `axes` axes.
    ///
    /// # Specification
    /// - ensures: the table holds at a vertex exactly when the polynomial does.
    /// - fails: a cube past six axes, and a polynomial with a generator at or
    ///   past `axes`, are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::TooWide`]: `axes` is past six.
    /// - [`DualityError::GeneratorOutside`]: the polynomial's highest generator
    ///   is at or past `axes`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every polynomial on up to four generators, read back
    ///   from its table, separates a lost vertex; L3 — a generator equal to
    ///   `axes` and seven axes separate the two refusals.
    /// - witness: `tests::free::polynomials_and_monotone_tables_go_one_to_one`
    #[spec(ensures: |ref ret| match *ret {
        Ok(table) => !self.terms.is_empty() || table.0 == 0,
        Err(error) => matches!(error, DualityError::TooWide(_) | DualityError::GeneratorOutside(_)),
    })]
    #[inline]
    pub fn table(
        &self,
        axes: GeneratorCount,
    ) -> Result<Table, DualityError>
    {
        let whole = whole_cube(axes)?;
        let reach = self.reach();
        if reach > axes {
            let highest = usize::from(reach).saturating_sub(1);
            return Err(DualityError::GeneratorOutside(Generator::from(highest)));
        }
        Ok(Table(
            self.terms
                .iter()
                .fold(0_u64, |bits, term| bits | up_set(*term).0)
                & whole.0,
        ))
    }

    /// The polynomial of a monotone truth table on the cube of `axes` axes:
    /// its minimal vertices, read as terms.
    ///
    /// # Specification
    /// - ensures: the polynomial's table is `table`.
    /// - fails: a cube past six axes, a table that holds past the cube, and a
    ///   table that is not monotone are refused, the last by the least pair it
    ///   breaks.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::TooWide`]: `axes` is past six.
    /// - [`DualityError::VertexOutside`]: the table holds at a vertex past the
    ///   cube.
    /// - [`DualityError::TableNotMonotone`]: the table holds at a vertex and
    ///   fails at a vertex one axis above it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every table on up to four axes, the monotone ones
    ///   counted to the Dedekind numbers and read back, separates a lost
    ///   minimal vertex and a missed break; L3 — a table holding past the cube
    ///   and seven axes separate the bounds.
    /// - witness: `tests::free::polynomials_and_monotone_tables_go_one_to_one`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref polynomial) => table.0 != 0 || polynomial.terms.is_empty(),
        Err(error) => matches!(error, DualityError::TooWide(_) | DualityError::VertexOutside(_) | DualityError::TableNotMonotone(..)),
    })]
    #[inline]
    pub fn from_table(
        axes: GeneratorCount,
        table: Table,
    ) -> Result<Self, DualityError>
    {
        let whole = whole_cube(axes)?;
        if let Some(outside) = Table(table.0 & !whole.0).vertices().next() {
            return Err(DualityError::VertexOutside(outside));
        }
        let mut broken: Option<(Vertex, Vertex)> = None;
        for (upper_half, step) in AXIS_VERTICES.iter().zip(AXIS_STEPS).take(usize::from(axes)) {
            let missing = (table.0 & !upper_half).checked_shl(step).unwrap_or(0) & !table.0;
            if missing != 0 {
                let upper = u64::from(missing.trailing_zeros());
                let lower = upper ^ u64::from(step);
                if broken.is_none_or(|(least, _)| lower < least.0) {
                    broken = Some((Vertex(lower), Vertex(upper)));
                }
            }
        }
        if let Some((lower, upper)) = broken {
            return Err(DualityError::TableNotMonotone(lower, upper));
        }
        Ok(Self::of_monotone(table))
    }

    /// The polynomial of a monotone table on the cube of six axes: its
    /// minimal vertices, each read as a term.
    ///
    /// # Specification
    /// - ensures: `⊥` is the polynomial of the empty table.
    /// - panics: none.
    /// - intension: the minimal vertices are the table less its covered
    ///   vertices, six shifts of the word, and at most [`INLINE`] terms
    ///   allocate nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every monotone table on up to four axes, read back,
    ///   separates a lost minimal vertex and a kept covered one.
    /// - witness: `tests::free::polynomials_and_monotone_tables_go_one_to_one`
    #[spec(ensures: |ref ret| table.0 != 0 || ret.terms.is_empty())]
    fn of_monotone(table: Table) -> Self
    {
        let minimal = Table(table.0 & !covered(table).0);
        Self {
            terms: Antichain::of_vertices(minimal),
        }
    }

    /// The truth table of the polynomial on the cube of six axes, when every
    /// generator it meets lies below six.
    ///
    /// # Specification
    /// - ensures: `⊥` has the empty table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of polynomials on three generators,
    ///   against their tables, and the same polynomials spread to eight
    ///   generators separate the two paths of meet and join.
    /// - witness: `tests::free::meet_join_and_order_follow_the_tables`
    #[spec(ensures: |ret| !self.terms.is_empty() || ret == Some(Table(0)))]
    fn cube_table(&self) -> Option<Table>
    {
        if usize::from(self.reach()) > WIDEST_CUBE {
            return None;
        }
        Some(Table(
            self.terms
                .iter()
                .fold(0_u64, |bits, term| bits | up_set(*term).0),
        ))
    }
}

/// A homomorphism of free distributive lattices: the polynomial each
/// generator of its source goes to, in generator order.
///
/// # Specification
/// - ensures: every image lies in the target lattice, and the source has at
///   most 64 generators.
/// - provides: substitution of polynomials, composition, and the monotone map
///   of cubes it is dual to.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`Homomorphism::new`]'s, which checks it.
///
/// # Adequacy
/// - hypothesis: L2 — every homomorphism between lattices on up to three
///   generators, read back from its map of cubes, separates a lost or swapped
///   image.
/// - witness: `tests::free::cube_maps_and_homomorphisms_go_one_to_one`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Homomorphism
{
    /// The number of generators of the target lattice.
    target: GeneratorCount,
    /// The image of each generator of the source lattice.
    images: Vec<Polynomial>,
}

impl Homomorphism
{
    /// The homomorphism from the lattice on as many generators as `images`
    /// holds to the lattice on `target` generators that sends each generator
    /// to its image.
    ///
    /// # Specification
    /// - ensures: the homomorphism's images are `images`, in order.
    /// - fails: a target or a source past 64 generators, and an image with a
    ///   generator at or past `target`, are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::TooManyGenerators`]: the target or the source has more
    ///   than 64 generators.
    /// - [`DualityError::GeneratorOutside`]: an image's highest generator is at
    ///   or past `target`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an image naming generator `target`, 65 images and a
    ///   target of 65 separate the three refusals.
    /// - witness: `tests::free::generators_and_terms_are_checked_by_index`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref homomorphism) => homomorphism.target == target,
        Err(error) => matches!(error, DualityError::TooManyGenerators(_) | DualityError::GeneratorOutside(_)),
    })]
    #[inline]
    pub fn new(
        target: GeneratorCount,
        images: Vec<Polynomial>,
    ) -> Result<Self, DualityError>
    {
        if usize::from(target) > WIDEST {
            return Err(DualityError::TooManyGenerators(target));
        }
        if images.len() > WIDEST {
            return Err(DualityError::TooManyGenerators(GeneratorCount::from(
                images.len(),
            )));
        }
        for image in &images {
            let reach = image.reach();
            if reach > target {
                let highest = usize::from(reach).saturating_sub(1);
                return Err(DualityError::GeneratorOutside(Generator::from(highest)));
            }
        }
        Ok(Self { target, images })
    }

    /// The identity of the lattice on `count` generators.
    ///
    /// # Specification
    /// - ensures: each generator goes to itself.
    /// - fails: more than 64 generators are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::TooManyGenerators`]: `count` is past 64.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the identity composed with every homomorphism on up
    ///   to three generators separates a shifted generator.
    /// - witness: `tests::free::substitution_composes_homomorphisms`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref homomorphism) => homomorphism.target == count,
        Err(error) => error == DualityError::TooManyGenerators(count),
    })]
    #[inline]
    pub fn identity(count: GeneratorCount) -> Result<Self, DualityError>
    {
        if usize::from(count) > WIDEST {
            return Err(DualityError::TooManyGenerators(count));
        }
        let mut images = Vec::with_capacity(usize::from(count));
        for index in 0 .. usize::from(count) {
            let image = Polynomial::generator(Generator::from(index))?;
            images.push(image);
        }
        Ok(Self {
            target: count,
            images,
        })
    }

    /// The number of generators of the source lattice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn source(&self) -> GeneratorCount
    {
        GeneratorCount::from(self.images.len())
    }

    /// The number of generators of the target lattice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> GeneratorCount
    {
        self.target
    }

    /// The image of each generator of the source, in generator order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn images(&self) -> &[Polynomial]
    {
        &self.images
    }

    /// The truth table of each image on the cube of six axes, in generator
    /// order, when every image lies there.
    ///
    /// # Specification
    /// - ensures: the tables exist exactly when every image meets only
    ///   generators below six, so a homomorphism with no images has them.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — homomorphisms into lattices on up to two generators
    ///   and into the lattice on eight generators separate the two paths of
    ///   substitution.
    /// - witness: `tests::free::substitution_composes_homomorphisms`
    #[spec(ensures: |ref ret| ret.is_some() || !self.images.is_empty())]
    fn image_tables(&self) -> Option<[Table; WIDEST]>
    {
        let mut tables = [Table(0); WIDEST];
        for (slot, image) in tables.iter_mut().zip(&self.images) {
            *slot = image.cube_table()?;
        }
        Some(tables)
    }

    /// The image of one polynomial when every image lies in the cube on six
    /// axes: for each term, the meet of its generators' tables, the terms'
    /// tables joined, and the minimal vertices read back.
    ///
    /// # Specification
    /// - ensures: `⊥` goes to `⊥`.
    /// - fails: a generator at or past the source is refused by name.
    /// - panics: none.
    /// - intension: one word operation per generator of each term, and the
    ///   result is the one allocation.
    ///
    /// # Errors
    /// - [`DualityError::GeneratorOutside`]: the polynomial meets a generator
    ///   at or past the source.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — substitution against composition of cube maps
    ///   separates a join taken for the meet and a lost term; L3 — a polynomial
    ///   past the source separates the refusal.
    /// - witness: `tests::free::substitution_composes_homomorphisms`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref image) => !polynomial.terms.is_empty() || image.terms.is_empty(),
        Err(error) => matches!(error, DualityError::GeneratorOutside(_)),
    })]
    fn substitute_tables(
        &self,
        polynomial: &Polynomial,
        tables: &[Table; WIDEST],
    ) -> Result<Polynomial, DualityError>
    {
        let held = tables.get(.. self.images.len()).unwrap_or(&[]);
        let mut joined = 0_u64;
        for term in polynomial.terms.iter() {
            let mut met = u64::MAX;
            for generator in term.generators() {
                let table = held
                    .get(usize::from(generator))
                    .ok_or(DualityError::GeneratorOutside(generator))?;
                met &= table.0;
            }
            joined |= met;
        }
        Ok(Polynomial::of_monotone(Table(joined)))
    }

    /// The image of one polynomial when an image meets a generator at or
    /// past six: for each term, the meet of the images of its generators,
    /// built in `current` and `next`, and the terms joined. The caller keeps
    /// the two buffers across calls, so a composite allocates them once.
    ///
    /// # Specification
    /// - ensures: `⊥` goes to `⊥`.
    /// - fails: a generator at or past the source is refused by name.
    /// - panics: none.
    /// - intension: each meet of a term's images is normalised as it grows, in
    ///   the two buffers in turn, so no meet allocates.
    ///
    /// # Errors
    /// - [`DualityError::GeneratorOutside`]: the polynomial meets a generator
    ///   at or past the source.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — substitution into the lattice on eight generators,
    ///   against the expected normal forms, separates a join taken for the meet
    ///   and a kept absorbed term.
    /// - witness: `tests::free::substitution_composes_homomorphisms`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref image) => !polynomial.terms.is_empty() || image.terms.is_empty(),
        Err(error) => matches!(error, DualityError::GeneratorOutside(_)),
    })]
    fn substitute_terms(
        &self,
        polynomial: &Polynomial,
        current: &mut Vec<Term>,
        next: &mut Vec<Term>,
    ) -> Result<Polynomial, DualityError>
    {
        let mut joined = Vec::new();
        for &term in polynomial.terms.iter() {
            current.clear();
            current.push(Term::TOP);
            for generator in term.generators() {
                let image = self
                    .images
                    .get(usize::from(generator))
                    .ok_or(DualityError::GeneratorOutside(generator))?;
                next.clear();
                for left in current.iter() {
                    next.extend(image.terms.iter().map(|right| left.meet(*right)));
                }
                *next = normalised(core::mem::take(next));
                core::mem::swap(current, next);
            }
            joined.extend_from_slice(current);
        }
        Ok(Polynomial::from_terms(joined))
    }

    /// The image of a polynomial: the join over its terms of the meet of the
    /// images of each term's generators.
    ///
    /// # Specification
    /// - ensures: the result is the unique lattice homomorphism's value, so `⊥`
    ///   goes to `⊥` and `⊤` to `⊤`.
    /// - fails: a polynomial with a generator at or past the source is refused
    ///   by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::GeneratorOutside`]: the polynomial meets a generator
    ///   at or past the source.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every pair of composable maps of cubes on up to two
    ///   axes, against substitution, separates a lost term and a swapped image;
    ///   L3 — a polynomial past the source separates the refusal.
    /// - witness: `tests::free::substitution_composes_homomorphisms`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref image) => !polynomial.terms.is_empty() || image.terms.is_empty(),
        Err(error) => matches!(error, DualityError::GeneratorOutside(_)),
    })]
    #[inline]
    pub fn apply(
        &self,
        polynomial: &Polynomial,
    ) -> Result<Polynomial, DualityError>
    {
        self.image_tables().map_or_else(
            || self.substitute_terms(polynomial, &mut Vec::new(), &mut Vec::new()),
            |tables| self.substitute_tables(polynomial, &tables),
        )
    }

    /// The composite that applies this homomorphism, then `next`.
    ///
    /// # Specification
    /// - ensures: each generator goes to `next` applied to its image here.
    /// - fails: `next` whose source is not this target is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ImageCount`]: `next` has another source than this
    ///   homomorphism's target.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every composable pair of maps of cubes on up to two
    ///   axes separates the composite's order; L3 — a mismatched pair separates
    ///   the refusal.
    /// - witness: `tests::free::substitution_composes_homomorphisms`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref composite) => composite.target == next.target && composite.images.len() == self.images.len(),
        Err(error) => error == DualityError::ImageCount,
    })]
    #[inline]
    pub fn followed_by(
        &self,
        next: &Self,
    ) -> Result<Self, DualityError>
    {
        if next.source() != self.target {
            return Err(DualityError::ImageCount);
        }
        let tables = next.image_tables();
        let (mut current, mut scratch) = (Vec::new(), Vec::new());
        let mut images = Vec::with_capacity(self.images.len());
        for image in &self.images {
            let mapped = match tables.as_ref() {
                Some(tables) => next.substitute_tables(image, tables)?,
                None => next.substitute_terms(image, &mut current, &mut scratch)?,
            };
            images.push(mapped);
        }
        Ok(Self {
            target: next.target,
            images,
        })
    }

    /// The homomorphism dual to a map of cubes: each generator of the map's
    /// target goes to the polynomial of the map's coordinate on that axis.
    ///
    /// # Specification
    /// - ensures: the homomorphism goes from the lattice on the map's target
    ///   axes to the lattice on its source axes, and [`Self::cube_map`] reads
    ///   the map back.
    /// - fails: only on a broken invariant of a [`CubeMap`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::TooWide`], [`DualityError::TableNotMonotone`]:
    ///   unreachable for a map [`CubeMap::new`] admits.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every monotone map between cubes on up to three axes,
    ///   read back, separates a coordinate read on the wrong axis.
    /// - witness: `tests::free::cube_maps_and_homomorphisms_go_one_to_one`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |homomorphism| homomorphism.target == map.source && homomorphism.images.len() == usize::from(map.target)))]
    #[inline]
    pub fn of_cube_map(map: &CubeMap) -> Result<Self, DualityError>
    {
        let mut coordinates = [0_u64; WIDEST_CUBE];
        for (vertex, image) in map.images.iter().enumerate() {
            let held = 1_u64
                .checked_shl(u32::try_from(vertex).unwrap_or(u32::MAX))
                .unwrap_or(0);
            for axis in ones!(image.0, |axis| axis) {
                if let Some(coordinate) = coordinates.get_mut(axis) {
                    *coordinate |= held;
                }
            }
        }
        let mut images = Vec::with_capacity(usize::from(map.target));
        for coordinate in coordinates.iter().take(usize::from(map.target)) {
            images.push(Polynomial::from_table(map.source, Table(*coordinate))?);
        }
        Ok(Self {
            target: map.source,
            images,
        })
    }

    /// The map of cubes dual to this homomorphism: each vertex of the target
    /// lattice's cube goes to the vertex that is `1` on each axis whose
    /// generator's image holds at it.
    ///
    /// # Specification
    /// - ensures: the map goes from the cube on the target's axes to the cube
    ///   on the source's axes, and [`Self::of_cube_map`] reads this
    ///   homomorphism back.
    /// - fails: a source or a target past six axes is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::TooWide`]: the source or the target has more than six
    ///   generators.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every homomorphism between lattices on up to three
    ///   generators, read back, separates a lost image; L3 — seven generators
    ///   separate the refusal.
    /// - witness: `tests::free::cube_maps_and_homomorphisms_go_one_to_one`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref map) => map.source == self.target && map.target == self.source(),
        Err(error) => matches!(error, DualityError::TooWide(_)),
    })]
    #[inline]
    pub fn cube_map(&self) -> Result<CubeMap, DualityError>
    {
        let whole = whole_cube(self.target)?;
        let _source = whole_cube(self.source())?;
        let mut coordinates = [0_u64; WIDEST_CUBE];
        for (coordinate, polynomial) in coordinates.iter_mut().zip(&self.images) {
            *coordinate = polynomial.table(self.target)?.0;
        }
        let mut images = Vec::with_capacity(usize::try_from(whole.0.count_ones()).unwrap_or(0));
        for vertex in whole.vertices() {
            let place = u32::try_from(vertex.0).unwrap_or(u32::MAX);
            let mut image = 0_u64;
            for (axis, coordinate) in coordinates.iter().take(self.images.len()).enumerate() {
                let held = coordinate.checked_shr(place).unwrap_or(0) & 1;
                image |= held
                    .checked_shl(u32::try_from(axis).unwrap_or(u32::MAX))
                    .unwrap_or(0);
            }
            images.push(Vertex(image));
        }
        // Each coordinate is a monotone table, so the map keeps the order of
        // the cube and needs no second check.
        Ok(CubeMap {
            source: self.target,
            target: self.source(),
            images,
        })
    }
}

/// A monotone map from the cube on `source` axes to the cube on `target`
/// axes: the image of each vertex of the source, in vertex order.
///
/// # Specification
/// - ensures: both cubes have at most six axes, every vertex of the source has
///   one image in the target, and the map keeps the order of the cube.
/// - provides: the dual homomorphism by [`Homomorphism::of_cube_map`], and
///   composition.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`CubeMap::new`]'s, which checks it.
///
/// # Adequacy
/// - hypothesis: L2 — every table of vertex images on small cubes, the monotone
///   ones admitted and counted, separates a missed break of order.
/// - witness: `tests::free::cube_maps_and_homomorphisms_go_one_to_one`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct CubeMap
{
    /// The number of axes of the source cube.
    source: GeneratorCount,
    /// The number of axes of the target cube.
    target: GeneratorCount,
    /// The image of each vertex of the source, in vertex order.
    images: Vec<Vertex>,
}

impl CubeMap
{
    /// Admits a map of cubes given by the image of each vertex of its source.
    ///
    /// # Specification
    /// - ensures: the map's images are `images`, in vertex order.
    /// - fails: a cube past six axes, another number of images than the
    ///   source's vertices, an image past the target, and a map that does not
    ///   keep the order are refused, the last by the least pair it breaks.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::TooWide`]: a cube has more than six axes.
    /// - [`DualityError::ImageCount`]: `images` does not hold one image per
    ///   vertex of the source.
    /// - [`DualityError::VertexOutside`]: an image lies past the target cube.
    /// - [`DualityError::CubeMapNotMonotone`]: the image of a vertex is not
    ///   below the image of a vertex one axis above it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every table of vertex images on small cubes separates
    ///   a missed break of order; L3 — one image short, one image past the
    ///   target and seven axes separate the other refusals.
    /// - witness: `tests::free::cube_maps_and_homomorphisms_go_one_to_one`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref map) => map.source == source && map.target == target,
        Err(error) => matches!(error, DualityError::TooWide(_) | DualityError::ImageCount | DualityError::VertexOutside(_) | DualityError::CubeMapNotMonotone(..)),
    })]
    #[inline]
    pub fn new(
        source: GeneratorCount,
        target: GeneratorCount,
        images: Vec<Vertex>,
    ) -> Result<Self, DualityError>
    {
        let from = whole_cube(source)?;
        let to = whole_cube(target)?;
        if Some(images.len()) != usize::try_from(from.0.count_ones()).ok() {
            return Err(DualityError::ImageCount);
        }
        if let Some(&outside) = images
            .iter()
            .find(|image| Table(to.0).holds_at(**image) == Membership::Outside)
        {
            return Err(DualityError::VertexOutside(outside));
        }
        for (index, image) in images.iter().enumerate() {
            let vertex = Vertex(u64::try_from(index).unwrap_or(u64::MAX));
            for axis in 0 .. usize::from(source) {
                let bit = generator_bit(Generator::from(axis))?;
                if vertex.0 & bit.0 != 0 {
                    continue;
                }
                let upper = Vertex(vertex.0 | bit.0);
                let above = usize::try_from(upper.0)
                    .ok()
                    .and_then(|position| images.get(position));
                if above.is_none_or(|above| image.compare(*above) == Comparison::NotBelow) {
                    return Err(DualityError::CubeMapNotMonotone(vertex, upper));
                }
            }
        }
        Ok(Self {
            source,
            target,
            images,
        })
    }

    /// The number of axes of the source cube.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> GeneratorCount
    {
        self.source
    }

    /// The number of axes of the target cube.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> GeneratorCount
    {
        self.target
    }

    /// The image of each vertex of the source, in vertex order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn images(&self) -> &[Vertex]
    {
        &self.images
    }

    /// The image of one vertex.
    ///
    /// # Specification
    /// - provides: the image stored for `vertex`.
    /// - fails: a vertex past the source cube is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::VertexOutside`]: `vertex` lies past the source cube.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first vertex past the source separates the bound.
    /// - witness: `tests::free::cube_maps_and_homomorphisms_go_one_to_one`
    #[spec(ensures: |ref ret| match *ret {
        Ok(image) => usize::try_from(vertex.0).ok().and_then(|position| self.images.get(position)) == Some(&image),
        Err(error) => error == DualityError::VertexOutside(vertex),
    })]
    #[inline]
    pub fn image(
        &self,
        vertex: Vertex,
    ) -> Result<Vertex, DualityError>
    {
        usize::try_from(vertex.0)
            .ok()
            .and_then(|position| self.images.get(position))
            .copied()
            .ok_or(DualityError::VertexOutside(vertex))
    }

    /// The composite that applies this map, then `next`.
    ///
    /// # Specification
    /// - ensures: each vertex goes to `next`'s image of its image here.
    /// - fails: `next` whose source is not this target is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ImageCount`]: `next` has another source than this
    ///   map's target.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every composable pair of maps of cubes on up to two
    ///   axes, against substitution of their homomorphisms, separates the
    ///   composite's order; L3 — a mismatched pair separates the refusal.
    /// - witness: `tests::free::substitution_composes_homomorphisms`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref composite) => composite.source == self.source && composite.target == next.target,
        Err(error) => error == DualityError::ImageCount || matches!(error, DualityError::VertexOutside(_)),
    })]
    #[inline]
    pub fn followed_by(
        &self,
        next: &Self,
    ) -> Result<Self, DualityError>
    {
        if next.source != self.target {
            return Err(DualityError::ImageCount);
        }
        let mut images = Vec::with_capacity(self.images.len());
        for &image in &self.images {
            let mapped = next.image(image)?;
            images.push(mapped);
        }
        Ok(Self {
            source: self.source,
            target: next.target,
            images,
        })
    }
}
