//! The statement of univalence at a stratum, as the core holds it: the
//! stratum the statement fixes and the two descriptions it relates.
//!
//! [`Value::Ua`] is `ua[n, k](a, b, f, g)`. Its [`Stratum`] is the degree `n`
//! the statement is made at and the bound `k` its quantifier ranges up to,
//! the largest shape the catalogue enumerates. Its [`Sides`] are the two
//! descriptions as a stratum reads them, each a [`Description`]: the
//! `theory` block's name and its generators, each generator by its label and
//! the profile of its corolla. The translator records `f` and `g` are values,
//! the node's children, each keyed by the labels of the description it reads
//! from; `gandr-core-checker`'s `ua` module decides them.
//!
//! # A description is its generators
//!
//! [`Description::read`] reads a `theory` description as a graphical species:
//! exactly one sort, no index, no parameter, no constructor, no rule, and every
//! operation's legs at that sort. An operation is a generator; the profile of
//! its corolla counts its input and output ports; the generators at one
//! profile are numbered in their written order, which is the order a corolla's
//! elements enumerate them in. [`Description::species`] counts them.
//!
//! # Decisions
//!
//! - **The core holds names and profiles, not the elaborated signature.** A
//!   certified stratum reads a description's generators and their profiles and
//!   nothing else, its shapes above the corollas being their colimits, and the
//!   printer needs the names. The alternative was the elaborated `TheoryDesc`
//!   itself, typed legs and attributes included, which nothing at a stratum
//!   reads and whose grade parameter belongs to the elaborator. Reversal: a
//!   stratum whose shapes above the corollas carry data, whose translators move
//!   composite shapes and whose rules constrain them, reads the whole
//!   description.
//! - **The stratum is written, not inferred.** Univalence at a stratum is a
//!   statement whose alphabet and quantifier range are fixed in the statement;
//!   `n` names the degree and `k` the catalogue the conditions are checked
//!   over. The alternative, a bound computed from the largest profile either
//!   description inhabits, would hide what the statement quantifies over and
//!   make the same source mean more as the descriptions grow. Reversal: a
//!   catalogue that is cheap at every bound a program meets lets the bound be
//!   read off the descriptions.
//! - **A rule takes a description out of the stratum.** A rule equates
//!   composite shapes, so a translator at the corollas alone cannot be shown to
//!   respect it; [`Description::read`] refuses a description with rules or
//!   circuits rather than reading it as the free species it is not. Reversal: a
//!   stratum above the corolla checks the rules' shapes too.
//!
//! [`Value::Ua`]: crate::Value::Ua

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::FieldLabel;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_sites::Degree;
use gandr_theory_sites::GeneratorCount;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Species;
use quenchant_shape::shape::Maybe;

/// The stratum a univalence statement is made at: its degree and the
/// largest shape its catalogue enumerates.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Stratum
{
    /// The degree the statement is made at, `n` in `ua[n, k]`.
    pub degree: Degree,
    /// The catalogue's bound, `k` in `ua[n, k]`: shapes of at most this many
    /// vertices and wires.
    pub bound: ShapeSize,
}

/// One generator of a description: an operation, by its label and the profile
/// of its corolla.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Generator
{
    /// The operation's name, the label a translator record keys it by.
    pub label: FieldLabel,
    /// The corolla it labels: its input and output port counts.
    pub profile: Profile,
}

/// A description as a stratum reads it: its name and its generators, in
/// written order.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Description
{
    /// The `theory` block's name.
    pub name: Name,
    /// The generators, in written order.
    pub generators: Box<[Generator]>,
}

/// The two descriptions a univalence statement relates, the source first.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Sides
{
    /// The description the forward translators read from.
    pub source: Description,
    /// The description the forward translators write to.
    pub target: Description,
}

/// Why a description is not a graphical species.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Unread
{
    /// It declares no sort, or more than one.
    Sorts,
    /// Its sort is indexed.
    Indexed,
    /// It takes parameters.
    Parameters,
    /// It declares constructors: a `data` description, not a `theory` one.
    Constructors,
    /// It declares rules or circuits, which equate composite shapes.
    Rules,
    /// An operation has a leg at a sort other than the description's own.
    Leg
    {
        /// The operation.
        generator: Name,
    },
}

quenchant_shape::reason_enum! {
    /// Why a description has no generator under a label.
    pub mod generator {
        /// The reason a label names no generator.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No operation of the description has that name.
            Unlisted,
        }
    }
}

impl Description
{
    /// Read `theory` as a graphical species, one generator per corolla.
    ///
    /// # Specification
    /// - ensures: one generator per operation, in written order, each labelled
    ///   by its name and at the profile counting its input and output ports;
    ///   the description keeps `theory`'s name.
    /// - fails: a description that is not one unindexed, unparameterised sort
    ///   with operations alone over it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unread::Sorts`] for zero or several sorts, [`Unread::Indexed`] for an
    /// indexed sort, [`Unread::Parameters`], [`Unread::Constructors`],
    /// [`Unread::Rules`] for rules or circuits, and [`Unread::Leg`] for the
    /// first operation with a leg at another sort, checked in that order.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a magma's two operations read at their profiles in
    ///   written order, and a two-sorted description and one with a rule are
    ///   refused, distinguishing a dropped or reordered generator, swapped port
    ///   counts and an unchecked boundary.
    /// - witness: `ua::tests::a_theory_reads_as_its_generators_in_written_order`
    /// - witness: `ua::tests::a_description_outside_the_stratum_is_refused`
    #[inline]
    #[spec(ensures: |result| result.as_ref().map_or(true, |description| description.generators.len() == theory.opers.len()))]
    pub fn read<G>(theory: &TheoryDesc<G>) -> Result<Self, Unread>
    {
        let (1_usize, Some(sort)) = (theory.sorts.len(), theory.sorts.first())
        else {
            return Err(Unread::Sorts);
        };
        if !sort.indices.is_empty() {
            return Err(Unread::Indexed);
        }
        if !theory.params.is_empty() {
            return Err(Unread::Parameters);
        }
        if !theory.ctors.is_empty() {
            return Err(Unread::Constructors);
        }
        if !theory.rules.is_empty() || !theory.circuits.is_empty() {
            return Err(Unread::Rules);
        }
        let mut generators = Vec::with_capacity(theory.opers.len());
        for oper in &theory.opers {
            let legs = oper.arity.inputs.iter().chain(&oper.arity.outputs);
            if legs.clone().any(|leg| leg.sort != sort.name) {
                return Err(Unread::Leg {
                    generator: oper.name.clone(),
                });
            }
            generators.push(Generator {
                label: FieldLabel::from(alloc::string::String::from(oper.name.as_ref())),
                profile: Profile {
                    inputs: PortCount::from(oper.arity.inputs.len()),
                    outputs: PortCount::from(oper.arity.outputs.len()),
                },
            });
        }
        Ok(Self {
            name: theory.id.name.clone(),
            generators: generators.into_boxed_slice(),
        })
    }

    /// The species the description presents: its generators counted at each
    /// profile.
    ///
    /// # Specification
    /// - ensures: the count at each profile is the number of generators at it.
    ///   The predicate observes that every generator's profile is counted and
    ///   that the counts sum to the generators; the witness separates a count
    ///   per profile from a count per description.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two generators at one profile and one at another
    ///   distinguish a count per profile from a count per description.
    /// - witness: `ua::tests::a_theory_reads_as_its_generators_in_written_order`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body counts every generator once; the check looks each generator's profile up once"
        )
    )]
    #[spec(ensures: |ref species| self.generators.iter().all(|generator| usize::from(species.count(generator.profile)) != 0)
        && species.profiles().map(|(_, count)| usize::from(count)).sum::<usize>() == self.generators.len())]
    pub fn species(&self) -> Species
    {
        let mut counts: BTreeMap<Profile, usize> = BTreeMap::new();
        for generator in &self.generators {
            let count = counts.entry(generator.profile).or_default();
            *count = count.saturating_add(1);
        }
        Species::new(
            counts
                .into_iter()
                .map(|(profile, count)| (profile, GeneratorCount::from(count)))
                .collect(),
        )
    }

    /// The generator labelled `label`.
    ///
    /// # Specification
    /// - ensures: present exactly when some generator carries the label, and
    ///   then the first that does.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a listed and an unlisted label distinguish the lookup
    ///   from a constant answer.
    /// - witness: `ua::tests::a_theory_reads_as_its_generators_in_written_order`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body scans the generators for the label once; the check scans them once more when none carries it"
        )
    )]
    #[spec(ensures: |ret| match ret { Maybe::Present(generator) => generator.label == *label, Maybe::Absent(_) => self.generators.iter().all(|generator| generator.label != *label) })]
    pub fn generator(
        &self,
        label: &FieldLabel,
    ) -> Maybe<&Generator, generator::Absent>
    {
        self.generators
            .iter()
            .find(|generator| generator.label == *label)
            .map_or(Maybe::Absent(generator::Absent::Unlisted), Maybe::Present)
    }
}

#[cfg(test)]
mod tests;
