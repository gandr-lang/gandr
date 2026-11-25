//! A graded poset as a complex: the faces of a cell are the cells of its
//! boundary one rank down, each with the incidence one.
//!
//! A graded poset holds no signs, so each incidence is one. The greedy
//! matching asks only that an incidence be one or minus one, so it matches a
//! poset as it is. A check of the boundary of a boundary needs signs, which a
//! face poset does not carry.

use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;

use crate::complex::Complex;
use crate::complex::Incidence;
use crate::complex::Standing;

impl<Data> Complex for &GradedPoset<Data>
{
    type Cell = Element;
    type Fault = DualityError;

    /// Whether `cell` is a cell of the poset: below its count.
    ///
    /// # Specification
    /// - ensures: [`Standing::Inside`] exactly for a cell below the count.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError`]: never; the poset reads its count without a fault.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last cell and the cell at the count separate the
    ///   two standings.
    /// - witness: `tests::poset::a_cell_past_the_count_lies_outside_the_poset`
    #[spec(ensures: |ref ret| *ret == Ok(if usize::from(*cell) < usize::from(self.count()) { Standing::Inside } else { Standing::Outside }))]
    #[inline]
    fn standing(
        &mut self,
        cell: &Element,
    ) -> Result<Standing, DualityError>
    {
        if usize::from(*cell) < usize::from(self.count()) {
            Ok(Standing::Inside)
        }
        else {
            Ok(Standing::Outside)
        }
    }

    /// Push each cell of the boundary of `cell` one rank down onto `faces`,
    /// each with the incidence one, in cell order.
    ///
    /// # Specification
    /// - requires: `cell` lies in the poset.
    /// - ensures: the cells pushed are exactly the cells of the boundary whose
    ///   rank is one less than the rank of `cell`. No cell lies between such a
    ///   cell and `cell`, since the rank rises strictly along the order.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DualityError::ElementOutside`]: `cell` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a square's whole cell has its four sides as faces and
    ///   no corner, and a side that holds no corner has no face. A cell past
    ///   the count is refused.
    /// - witness: `tests::poset::the_faces_of_a_cell_lie_one_rank_down`
    /// - witness: `tests::poset::a_cell_past_the_count_has_no_faces_to_read`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(DualityError::ElementOutside(*cell)))]
    #[inline]
    fn faces(
        &mut self,
        cell: &Element,
        faces: &mut Vec<(Element, Incidence)>,
    ) -> Result<(), DualityError>
    {
        let rank = usize::from(self.rank(*cell)?);
        let boundary = self.boundary(*cell)?;
        for face in boundary.elements() {
            let below = usize::from(self.rank(face)?);
            if below.saturating_add(1) == rank {
                faces.push((face, Incidence::from(1_i64)));
            }
        }
        Ok(())
    }
}
