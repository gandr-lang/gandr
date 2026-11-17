use alloc::vec::Vec;

use super::Precedence;
use super::TelescopePosition;
use super::merge_order;

/// The most positions a relation below ranges over.
const MOST: usize = 4;

/// The shift of each base-four digit of an ordering's code, the first
/// position's the most significant, so codes ascend as orderings do
/// lexicographically.
const SHIFTS: [usize; MOST] = [6, 4, 2, 0];

/// One ordering of the positions below a count.
#[derive(Clone, Copy, Debug)]
struct Ordering
{
    /// The positions, in order; those past the count are unused.
    positions: [TelescopePosition; MOST],
    /// Each position's rank in the ordering.
    ranks: [usize; MOST],
}

/// Every ordering of the positions below `end`, in lexicographic order: the
/// codes of four base-four digits whose leading digits are distinct and
/// below `end`, and whose trailing ones are zero.
///
/// # Specification
/// trivial.
fn orderings(end: TelescopePosition) -> Vec<Ordering>
{
    let count = usize::from(end);
    let mut found = Vec::with_capacity(24);
    for code in 0 .. 256_usize {
        let mut seen = 0_usize;
        let mut admitted = true;
        let mut ordering = Ordering {
            positions: [TelescopePosition::default(); MOST],
            ranks: [0; MOST],
        };
        for (index, &shift) in SHIFTS.iter().enumerate() {
            let digit = (code >> shift) & 3;
            if index >= count {
                admitted &= digit == 0;
                continue;
            }
            admitted &= digit < count && seen & (1_usize << digit) == 0;
            seen |= 1_usize << digit;
            if let (Some(position), Some(rank)) = (
                ordering.positions.get_mut(index),
                ordering.ranks.get_mut(digit),
            ) {
                *position = TelescopePosition::from(digit);
                *rank = index;
            }
        }
        if admitted {
            found.push(ordering);
        }
    }
    found
}

#[test]
fn the_merged_telescope_places_each_parameter_after_what_its_type_mentions()
{
    // Every dependence relation over up to four positions, against the
    // validator: the lexicographically least ordering every precedence holds
    // in, which is the stable sort's answer, or a cycle exactly when no
    // ordering holds them all.
    for count in 1 ..= MOST {
        let end = TelescopePosition::from(count);
        let pairs: Vec<Precedence> = (0 .. count)
            .flat_map(|later| {
                (0 .. count)
                    .filter(move |&earlier| earlier != later)
                    .map(move |earlier| Precedence {
                        later: TelescopePosition::from(later),
                        earlier: TelescopePosition::from(earlier),
                    })
            })
            .collect();
        let candidates = orderings(end);
        let mut relation: Vec<Precedence> = Vec::with_capacity(pairs.len());
        for mask in 0 .. 1_usize << pairs.len() {
            relation.clear();
            let mut held = [[false; MOST]; MOST];
            for (bit, &precedence) in pairs.iter().enumerate() {
                if mask & (1_usize << bit) != 0 {
                    relation.push(precedence);
                    if let Some(cell) = held
                        .get_mut(usize::from(precedence.later))
                        .and_then(|row| row.get_mut(usize::from(precedence.earlier)))
                    {
                        *cell = true;
                    }
                }
            }
            let least = candidates.iter().find(|ordering| {
                relation.iter().all(|precedence| {
                    ordering.ranks.get(usize::from(precedence.earlier))
                        < ordering.ranks.get(usize::from(precedence.later))
                })
            });
            match (least, merge_order(end, &mut relation)) {
                (Some(least), Ok(order)) => assert_eq!(
                    Some(order.as_slice()),
                    least.positions.get(.. count),
                    "mask {mask:#b} over {count}: the least ordering every precedence holds in"
                ),
                (None, Err(cycle)) => assert_eq!(
                    held.get(usize::from(cycle.first))
                        .and_then(|row| row.get(usize::from(cycle.second))),
                    Some(&true),
                    "mask {mask:#b} over {count}: the cycle names a precedence of the relation"
                ),
                (least, answer) => panic!(
                    "mask {mask:#b} over {count}: an ordering {least:?} exactly when the merge \
                     answers one, {answer:?}"
                ),
            }
        }
    }
}
