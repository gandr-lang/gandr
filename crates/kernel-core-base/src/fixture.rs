//! The readings of the record that only tests take. The tests of the
//! judgement read them through these functions, and nothing of them compiles
//! outside the tests.

use crate::encoding::ConstantName;
pub use crate::encoding::fixture::place;
pub use crate::encoding::fixture::stream;
use crate::env::Entries;
use crate::support::SupportContext;

/// How the table of `session` names the constant at `index`.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn constant_name(
    session: &SupportContext,
    index: gandr_kernel_term::ConstantIndex,
) -> Option<ConstantName>
{
    session.constant_name(index)
}

/// How many entries the last check over `entries` read.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn reads(entries: &Entries) -> gandr_kernel_term::ArenaLength
{
    entries.reads()
}

/// The words over the circle that the tests of presented spaces build on, in
/// the record's tests and in the judgement's.
pub mod presented
{
    use alloc::vec::Vec;

    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::Presentation;
    use gandr_kernel_term::PresentedRule;
    use gandr_kernel_term::RuleNode;
    use gandr_kernel_term::RuleVariable;
    use gandr_kernel_term::TermArena;

    /// A constructor of the test's circle, `mark` taking a field of another
    /// type.
    ///
    /// # Specification
    /// trivial.
    #[derive(Clone, Copy, Debug)]
    pub enum Letter
    {
        /// `base`.
        Base,
        /// `loop(x)`.
        Loop,
        /// `unloop(x)`.
        Unloop,
        /// `mark(u)`, its field a unit.
        Mark,
    }

    impl Letter
    {
        /// The constructor's tag.
        ///
        /// # Specification
        /// trivial.
        #[inline]
        #[must_use]
        pub fn tag(self) -> ConstructorTag
        {
            ConstructorTag::from(match self {
                Self::Base => 0_usize,
                Self::Loop => 1,
                Self::Unloop => 2,
                Self::Mark => 3,
            })
        }

        /// The constructor as a rule node.
        ///
        /// # Specification
        /// trivial.
        #[inline]
        #[must_use]
        pub fn node(self) -> RuleNode
        {
            RuleNode::Constructor(self.tag())
        }
    }

    /// The first variable as a rule node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn x() -> RuleNode
    {
        RuleNode::Variable(RuleVariable::from(0_u32))
    }

    /// The circle's two rules.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn circle() -> Presentation
    {
        let (looped, unlooped) = (Letter::Loop.node(), Letter::Unloop.node());
        Presentation::new(alloc::vec![
            PresentedRule::new([looped, unlooped, x()].into(), [x()].into()),
            PresentedRule::new([unlooped, looped, x()].into(), [x()].into()),
        ])
    }

    /// The word over `base` spelled by `letters`, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn word(
        arena: &mut TermArena,
        letters: &[Letter],
    ) -> gandr_kernel_term::ValueId
    {
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let mut built = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            Letter::Base.tag(),
            Vec::new(),
        );
        for &letter in letters.iter().rev() {
            built = arena.value_constructor(
                ConstantIndex::from(0_usize),
                own,
                letter.tag(),
                alloc::vec![built],
            );
        }
        built
    }

    /// `base` as a closed rule side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn base() -> alloc::boxed::Box<[RuleNode]>
    {
        [Letter::Base.node()].into()
    }
}
