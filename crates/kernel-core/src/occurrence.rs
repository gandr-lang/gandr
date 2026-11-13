//! The results of the occurrence check: how a declaration's recursion
//! stands, whether a family's own occurrences stand strictly positive, and
//! the block that a data declaration is admitted in. `check::occurrence`
//! computes them, and the record keeps them.

use alloc::vec::Vec;

use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ParameterPosition;
use gandr_kernel_term::StagedPosition;
use quenchant_shape::shape::Maybe;

/// What a declaration's recursion was read to be.
///
/// For a data declaration, how its own occurrences stand and how each of its
/// parameters does; for a structural definition, the parameter whose stage its
/// result stands at.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `parameters` holds one variance per parameter of the walked
///   declaration.
/// - executable: none — the declaration is not held beside it.
///
/// # Adequacy
/// - hypothesis: L3 — a family with a negative field below its stage is
///   stratified, and a list's element parameter is strictly positive.
/// - witness: `tests::recursive_data::a_negative_occurrence_below_the_stage_declares`
/// - witness: `tests::recursive_data::a_nested_occurrence_through_a_strictly_positive_parameter_declares`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Accessibility
{
    /// How the family's own occurrences stand.
    stratification: Stratification,
    /// How each parameter stands, in telescope order.
    parameters: Vec<Variance>,
    /// The position of the parameter a definition's result stands at the
    /// stage of, when its own recursion was judged to return at it.
    result: Maybe<StagedPosition, Unstaged>,
}

impl Accessibility
{
    /// What a declaration admitted unchecked is taken to be: stratified, every
    /// parameter not strictly positive — the reading that admits least.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn unwalked() -> Self
    {
        Self {
            stratification: Stratification::Stratified,
            parameters: Vec::new(),
            result: Maybe::Absent(Unstaged::Plain),
        }
    }

    /// The accessibility of a walked declaration: its stratification, how each
    /// parameter stands, and the stage its result stands at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn new(
        stratification: Stratification,
        parameters: Vec<Variance>,
        result: Maybe<StagedPosition, Unstaged>,
    ) -> Self
    {
        Self {
            stratification,
            parameters,
            result,
        }
    }

    /// The same reading, with a definition's result standing at the stage of
    /// its parameter at `position`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn following(
        self,
        position: StagedPosition,
    ) -> Self
    {
        Self {
            result: Maybe::Present(position),
            ..self
        }
    }

    /// The position of the parameter a definition's result stands at the stage
    /// of, when it follows one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn result(&self) -> Maybe<StagedPosition, Unstaged>
    {
        self.result
    }

    /// How the family's own occurrences stand.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stratification(&self) -> Stratification
    {
        self.stratification
    }

    /// How each parameter stands, in telescope order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn parameters(&self) -> &[Variance]
    {
        &self.parameters
    }

    /// How the parameter at `parameter` stands; not strictly positive past the
    /// telescope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn variance(
        &self,
        parameter: ParameterPosition,
    ) -> Variance
    {
        self.parameters
            .get(usize::from(parameter))
            .copied()
            .unwrap_or(Variance::NotStrictlyPositive)
    }

    /// Append this reading's verdict bytes to `out`: the stratification, the
    /// counted parameter variances, then the parameter the result follows.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn write(
        &self,
        out: &mut crate::verdict::EncodedVerdict,
    )
    {
        out.put_stratification(self.stratification);
        out.put_variances(&self.parameters);
        out.put_following(match self.result {
            Maybe::Present(position) => Maybe::Present(position),
            Maybe::Absent(Unstaged::Plain) => {
                Maybe::Absent(crate::verdict::following::Absent::Plain)
            },
        });
    }

    /// The reading [`Accessibility::write`] wrote at the start of `image`,
    /// which advances past it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn read(
        image: &mut crate::verdict::VerdictImage<'_>
    ) -> Maybe<Self, crate::verdict::verdict_image::Absent>
    {
        let Maybe::Present(stratification) = image.stratification()
        else {
            return Maybe::Absent(crate::verdict::verdict_image::Absent::Malformed);
        };
        let Maybe::Present(parameters) = image.variances()
        else {
            return Maybe::Absent(crate::verdict::verdict_image::Absent::Malformed);
        };
        let Maybe::Present(following) = image.following()
        else {
            return Maybe::Absent(crate::verdict::verdict_image::Absent::Malformed);
        };
        Maybe::Present(Self {
            stratification,
            parameters,
            result: match following {
                Maybe::Present(position) => Maybe::Present(position),
                Maybe::Absent(crate::verdict::following::Absent::Plain) => {
                    Maybe::Absent(Unstaged::Plain)
                },
            },
        })
    }
}

/// Whether a family's own occurrences all stand strictly positively.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stratification
{
    /// Every occurrence of a family of its block stands strictly positively.
    Positive,
    /// Some occurrence stands under a function's domain, at a stage below its
    /// constructor's: a case on a value at no stage reads its fields at a
    /// fresh one.
    Stratified,
}

/// Whether every use of a family's parameter stands strictly positively.
///
/// A nested occurrence through a strictly positive parameter is placed: the
/// parameter stands as the decode of a field's own type or a strictly positive
/// position under it, or is handed on to a strictly positive parameter of
/// another family there.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Variance
{
    /// Every use of the parameter is strictly positive.
    StrictlyPositive,
    /// Some use is not, or the family was not walked.
    NotStrictlyPositive,
}

/// The block a data declaration is admitted in: its families, a run of data
/// declarations from the first member, the declaration among them, then the
/// block's definitions up to the position past its last member.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a lone declaration's block holds its own family and ends one past
///   it.
/// - executable: none — the positions hold no table to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a lone family and a mutual block of a family and its
///   decoder are each walked by the block they are admitted in.
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Block
{
    /// The block's first member, its first family.
    first: ConstantIndex,
    /// The position past its last family.
    families: ConstantIndex,
    /// The position past its last member.
    end: ConstantIndex,
}

impl Block
{
    /// The block of the data declaration at `position` alone.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn lone(position: ConstantIndex) -> Self
    {
        let end = ConstantIndex::from(usize::from(position).saturating_add(1));
        Self {
            first: position,
            families: end,
            end,
        }
    }

    /// The block whose families run from `first` to before `families`, and
    /// whose definitions run from there to before `end`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn new(
        first: ConstantIndex,
        families: ConstantIndex,
        end: ConstantIndex,
    ) -> Self
    {
        Self {
            first,
            families,
            end,
        }
    }

    /// The block's first member.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn first(self) -> ConstantIndex
    {
        self.first
    }

    /// The position past the block's last family.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn families(self) -> ConstantIndex
    {
        self.families
    }

    /// The position past the block's last member.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn end(self) -> ConstantIndex
    {
        self.end
    }

    /// Extend the block to end before `end`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn extend_to(
        &mut self,
        end: ConstantIndex,
    )
    {
        self.end = end;
    }

    /// What `position` is in the block: one of its families, one of its
    /// definitions, or outside it.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn membership(
        self,
        position: ConstantIndex,
    ) -> Membership
    {
        if position < self.first || position >= self.end {
            Membership::Other
        }
        else if position < self.families {
            Membership::Family
        }
        else {
            Membership::Definition
        }
    }
}

/// Why a type opens no stage.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unstaged
{
    /// The type is refined at no stage.
    Plain,
}

/// What a position is in a block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Membership
{
    /// A family of the block, in scope while the block's families form.
    Family,
    /// A definition of the block, foreseen at its declared type while the
    /// block's families form.
    Definition,
    /// Outside the block.
    Other,
}
