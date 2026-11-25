//! Reductions of words: each removes one letter that a word over the other
//! letters defines, as one Tietze move does. Two removals compose in
//! sequence, and removals of two alphabets sit side by side in a sum.

use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_reductions::Answer;
use gandr_theory_reductions::Closure;
use gandr_theory_reductions::MorseError;
use gandr_theory_reductions::PartIndex;
use gandr_theory_reductions::Reduction;
use gandr_theory_reductions::Refusal;
use gandr_theory_reductions::Sum;
use gandr_theory_reductions::Summand;
use gandr_theory_reductions::matched;

/// A step from one word to another.
type Step = (Vec<char>, Vec<char>);

/// Why the words cannot answer: two steps do not meet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Seam;

/// The removal of `letter` from `source`, which `definition` defines.
#[derive(Debug)]
struct Removal
{
    /// The letters of the source.
    source: Vec<char>,
    /// The letters of the target: the source without `letter`.
    target: Vec<char>,
    /// The letter that the removal removes.
    letter: char,
    /// The word that takes the place of the letter.
    definition: Vec<char>,
}

impl Removal
{
    /// The removal of `letter` from `source`, defined by `definition`.
    ///
    /// # Specification
    /// trivial.
    fn new(
        source: &str,
        letter: char,
        definition: &str,
    ) -> Self
    {
        Self {
            source: source.chars().collect(),
            target: source.chars().filter(|&kept| kept != letter).collect(),
            letter,
            definition: definition.chars().collect(),
        }
    }

    /// `word` with each copy of the letter replaced by its definition.
    ///
    /// # Specification
    /// trivial.
    fn substituted(
        &self,
        word: &[char],
    ) -> Vec<char>
    {
        word.iter()
            .flat_map(|&at| {
                if at == self.letter {
                    self.definition.clone()
                }
                else {
                    vec![at]
                }
            })
            .collect()
    }
}

impl Reduction for Removal
{
    type Cell = char;
    type Composite = Vec<char>;
    type Fault = Seam;
    type Witness = Step;

    /// The source letters.
    ///
    /// # Specification
    /// trivial.
    fn source(&self) -> &[char]
    {
        &self.source
    }

    /// The target letters.
    ///
    /// # Specification
    /// trivial.
    fn target(&self) -> &[char]
    {
        &self.target
    }

    /// The word of one letter.
    ///
    /// # Specification
    /// trivial.
    fn generator(
        &mut self,
        cell: &char,
    ) -> Answer<Self, Vec<char>>
    {
        Ok(vec![*cell])
    }

    /// The word with the letter replaced by its definition.
    ///
    /// # Specification
    /// trivial.
    fn collapse(
        &mut self,
        composite: &Vec<char>,
    ) -> Answer<Self, Vec<char>>
    {
        Ok(self.substituted(composite))
    }

    /// The word itself: each target letter is a source letter.
    ///
    /// # Specification
    /// trivial.
    fn include(
        &mut self,
        composite: &Vec<char>,
    ) -> Answer<Self, Vec<char>>
    {
        Ok(composite.clone())
    }

    /// The step from the word to its collapse, where the two differ.
    ///
    /// # Specification
    /// trivial.
    fn section(
        &mut self,
        composite: &Vec<char>,
    ) -> Answer<Self, Option<Step>>
    {
        let collapsed = self.substituted(composite);
        Ok((collapsed != *composite).then(|| (composite.clone(), collapsed)))
    }

    /// Nothing: a word of the target holds no removed letter.
    ///
    /// # Specification
    /// trivial.
    fn retraction(
        &mut self,
        _composite: &Vec<char>,
    ) -> Answer<Self, Option<Step>>
    {
        Ok(None)
    }

    /// The step itself.
    ///
    /// # Specification
    /// trivial.
    fn include_witness(
        &mut self,
        witness: &Step,
    ) -> Answer<Self, Step>
    {
        Ok(witness.clone())
    }

    /// The step between the two collapsed words.
    ///
    /// # Specification
    /// trivial.
    fn collapse_witness(
        &mut self,
        witness: &Step,
    ) -> Answer<Self, Step>
    {
        Ok((self.substituted(&witness.0), self.substituted(&witness.1)))
    }

    /// The step from the start of `first` to the end of `second`, where they
    /// meet.
    ///
    /// # Specification
    /// trivial.
    fn compose(
        &mut self,
        first: &Step,
        second: &Step,
    ) -> Answer<Self, Step>
    {
        if first.1 == second.0 {
            Ok((first.0.clone(), second.1.clone()))
        }
        else {
            Err(Refusal::Morse(MorseError::Complex(Seam)))
        }
    }

    /// Whether the step runs from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    fn closes(
        &mut self,
        witness: &Step,
        source: &Vec<char>,
        target: &Vec<char>,
    ) -> Answer<Self, Closure>
    {
        Ok(if witness.0 == *source && witness.1 == *target {
            Closure::Closes
        }
        else {
            Closure::Open
        })
    }

    /// The target is the source without the letter, and the definition does
    /// not hold the letter.
    ///
    /// # Specification
    /// trivial.
    fn replay(&mut self) -> Answer<Self, ()>
    {
        let kept: Vec<char> = self
            .source
            .iter()
            .copied()
            .filter(|&at| at != self.letter)
            .collect();
        matched(&kept, &self.target)?;
        if self.definition.contains(&self.letter) {
            return Err(Refusal::Circular(self.letter));
        }
        Ok(())
    }
}

#[test]
fn two_removals_compose_in_sequence()
{
    let mut both = Removal::new("abc", 'c', "bb").then(Removal::new("ab", 'b', "a"));
    assert_eq!(both.replay(), Ok(()));
    assert_eq!(both.target(), ['a'], "the composite keeps the one letter");
    assert_eq!(
        both.collapse(&vec!['c', 'b']),
        Ok(vec!['a', 'a', 'a']),
        "the first collapse, then the second"
    );
    assert_eq!(
        both.section(&vec!['c']),
        Ok(Some((vec!['c'], vec!['a', 'a']))),
        "the first step, then the second step carried back, as one step"
    );
}

#[test]
fn a_composite_over_other_cells_is_unmatched()
{
    let mut apart = Removal::new("abc", 'c', "b").then(Removal::new("ad", 'd', "a"));
    assert_eq!(
        apart.replay(),
        Err(Refusal::Unmatched(Some('b'))),
        "the first target holds `b` where the second source holds `d`"
    );
}

#[test]
fn a_sum_reads_each_cell_in_its_own_part()
{
    let mut sum = Sum::new(vec![
        Removal::new("abc", 'c', "b"),
        Removal::new("xy", 'y', "x"),
    ]);
    let (first, second) = (PartIndex::from(0_usize), PartIndex::from(1_usize));
    assert_eq!(sum.replay(), Ok(()));
    assert_eq!(sum.target(), [
        Summand::new(first, 'a'),
        Summand::new(first, 'b'),
        Summand::new(second, 'x'),
    ]);
    assert_eq!(
        sum.collapse(&Summand::new(second, vec!['y'])),
        Ok(Summand::new(second, vec!['x'])),
        "the second part collapses its own word"
    );
    assert_eq!(
        sum.collapse(&Summand::new(first, vec!['y'])),
        Ok(Summand::new(first, vec!['y'])),
        "the first part has no `y` to remove"
    );
}

#[test]
fn a_part_that_does_not_replay_is_refused_with_its_part()
{
    let mut sum = Sum::new(vec![
        Removal::new("ab", 'b', "a"),
        Removal::new("xy", 'y', "xy"),
    ]);
    assert_eq!(
        sum.replay(),
        Err(Refusal::Circular(Summand::new(
            PartIndex::from(1_usize),
            'y'
        ))),
        "the second part defines `y` by itself"
    );
}
