//! Kessler's traversal on the molecules of her thesis: the orders it prints,
//! the key, a copy numbered in another order, and the refusal of posets that
//! are not molecules. Each fixture is the face data that the thesis prints,
//! position by position.

use gandr_theory_graded_posets::Face;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_graded_posets::Key;
use gandr_theory_graded_posets::TraversalError;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::Membership;

/// A cell as the thesis names it: its dimension and its position.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Named
{
    /// The dimension of the cell.
    dim: usize,
    /// The position of the cell among the cells of its dimension.
    pos: usize,
}

/// The face data of an oriented graded poset as the thesis prints it: for
/// each dimension and each position, the positions of the input faces and of
/// the output faces one dimension down.
#[repr(transparent)]
struct FaceData(Vec<Vec<(Vec<usize>, Vec<usize>)>>);

/// The number of input and of output faces of each cell, dimension by
/// dimension and sorted.
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
struct Counts(Vec<Vec<(usize, usize)>>);

impl FaceData
{
    /// Each cell, dimension by dimension and in position order.
    ///
    /// # Specification
    /// trivial.
    fn cells(&self) -> Vec<Named>
    {
        self.0
            .iter()
            .enumerate()
            .flat_map(|(dim, row)| (0 .. row.len()).map(move |pos| Named { dim, pos }))
            .collect()
    }

    /// Whether `lower` is a face of `upper` on its side `side`, one dimension
    /// down.
    ///
    /// # Specification
    /// trivial.
    fn on(
        &self,
        lower: &Named,
        upper: &Named,
        side: Face,
    ) -> Membership
    {
        let held = lower.dim.saturating_add(1) == upper.dim
            && self
                .0
                .get(upper.dim)
                .and_then(|row| row.get(upper.pos))
                .is_some_and(|&(ref inputs, ref outputs)| {
                    match side {
                        Face::Input => inputs,
                        Face::Output => outputs,
                    }
                    .contains(&lower.pos)
                });
        if held {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Whether `lower` is a face of `upper`, one dimension down.
    ///
    /// # Specification
    /// trivial.
    fn below(
        &self,
        lower: &Named,
        upper: &Named,
    ) -> Comparison
    {
        if self.on(lower, upper, Face::Input) == Membership::Inside
            || self.on(lower, upper, Face::Output) == Membership::Inside
        {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }

    /// The side of `upper` that its face `lower` lies on.
    ///
    /// # Specification
    /// trivial.
    fn side(
        &self,
        lower: &Named,
        upper: &Named,
    ) -> Face
    {
        if self.on(lower, upper, Face::Output) == Membership::Inside {
            Face::Output
        }
        else {
            Face::Input
        }
    }

    /// The graded poset of these faces, its cells numbered in the order of
    /// `cells`.
    ///
    /// # Specification
    /// trivial.
    fn poset(
        &self,
        cells: Vec<Named>,
    ) -> GradedPoset<Named>
    {
        let most = ElementCount::from(cells.len());
        GradedPoset::new(cells, |lower, upper| self.below(lower, upper), most)
            .expect("the face data is acyclic")
    }

    /// The names of the cells in the order the traversal marks them, the
    /// cells numbered in the order of `cells`.
    ///
    /// # Specification
    /// trivial.
    fn order(
        &self,
        cells: Vec<Named>,
    ) -> Vec<Named>
    {
        let poset = self.poset(cells);
        let traversal = poset
            .traverse(|lower, upper| self.side(lower, upper))
            .expect("a molecule traverses");
        traversal
            .order()
            .iter()
            .filter_map(|&cell| poset.cells().get(usize::from(cell)).copied())
            .collect()
    }

    /// The key of the molecule, its cells numbered in the order of `cells`.
    ///
    /// # Specification
    /// trivial.
    fn key(
        &self,
        cells: Vec<Named>,
    ) -> Key
    {
        self.poset(cells)
            .traverse(|lower, upper| self.side(lower, upper))
            .expect("a molecule traverses")
            .key()
    }

    /// The number of input and of output faces of each cell, dimension by
    /// dimension and sorted: the face data that the thesis checks before it
    /// traverses.
    ///
    /// # Specification
    /// trivial.
    fn counts(&self) -> Counts
    {
        Counts(
            self.0
                .iter()
                .map(|row| {
                    let mut counts: Vec<(usize, usize)> = row
                        .iter()
                        .map(|&(ref inputs, ref outputs)| (inputs.len(), outputs.len()))
                        .collect();
                    counts.sort_unstable();
                    counts
                })
                .collect(),
        )
    }
}

/// Example 2.1.4, whose face data Example 2.4.4 prints: a 2-cell from the
/// path through `(0,1)` to the edge `(1,3)`, whiskered by the edge `(1,2)`.
///
/// # Specification
/// trivial.
fn example_2_1_4() -> FaceData
{
    FaceData(vec![
        vec![(vec![], vec![]); 4],
        vec![
            (vec![0], vec![1]),
            (vec![1], vec![2]),
            (vec![2], vec![3]),
            (vec![0], vec![2]),
        ],
        vec![(vec![0, 1], vec![3])],
    ])
}

/// Example 2.4.11: a 2-cell from the edge `(1,0)` to the path through
/// `(0,3)`, whiskered by the edge `(1,1)`. The order the thesis prints fixes
/// the sides.
///
/// # Specification
/// trivial.
fn example_2_4_11() -> FaceData
{
    FaceData(vec![
        vec![(vec![], vec![]); 4],
        vec![
            (vec![0], vec![1]),
            (vec![1], vec![2]),
            (vec![0], vec![3]),
            (vec![3], vec![1]),
        ],
        vec![(vec![0], vec![2, 3])],
    ])
}

/// The first molecule of Example 2.4.9: a path of four edges, and a 2-cell
/// on its second edge.
///
/// # Specification
/// trivial.
fn example_2_4_9_second_edge() -> FaceData
{
    FaceData(vec![
        vec![(vec![], vec![]); 5],
        vec![
            (vec![0], vec![1]),
            (vec![1], vec![2]),
            (vec![2], vec![3]),
            (vec![3], vec![4]),
            (vec![1], vec![2]),
        ],
        vec![(vec![1], vec![4])],
    ])
}

/// The second molecule of Example 2.4.9: the same path, and a 2-cell on its
/// third edge.
///
/// # Specification
/// trivial.
fn example_2_4_9_third_edge() -> FaceData
{
    FaceData(vec![
        vec![(vec![], vec![]); 5],
        vec![
            (vec![0], vec![1]),
            (vec![1], vec![2]),
            (vec![2], vec![3]),
            (vec![3], vec![4]),
            (vec![2], vec![3]),
        ],
        vec![(vec![2], vec![4])],
    ])
}

#[test]
fn the_traversal_marks_the_cells_of_examples_2_4_10_and_2_4_11_in_the_printed_order()
{
    let name = |(dim, pos)| Named { dim, pos };
    let molecule = example_2_1_4();
    assert_eq!(
        molecule.order(molecule.cells()),
        [
            (0, 0),
            (1, 0),
            (0, 1),
            (1, 1),
            (0, 2),
            (1, 2),
            (0, 3),
            (2, 0),
            (1, 3)
        ]
        .map(name),
        "Example 2.4.10: the input path first, then the 2-cell and its output edge"
    );
    let molecule = example_2_4_11();
    assert_eq!(
        molecule.order(molecule.cells()),
        [
            (0, 0),
            (1, 0),
            (0, 1),
            (1, 1),
            (0, 2),
            (2, 0),
            (1, 2),
            (0, 3),
            (1, 3)
        ]
        .map(name),
        "Example 2.4.11: the 2-cell before the edges of its output path"
    );
}

#[test]
fn the_key_of_example_2_1_4_is_the_face_data_the_thesis_prints()
{
    // The thesis names each cell by its place in traversal order, so the face
    // data it prints for Example 2.4.4 is the key.
    let molecule = example_2_1_4();
    let key = molecule.key(molecule.cells());
    let written: Vec<(usize, Vec<usize>, Vec<usize>)> = key
        .cells()
        .map(|(rank, inputs, outputs)| {
            (
                usize::from(rank),
                inputs.iter().copied().map(usize::from).collect(),
                outputs.iter().copied().map(usize::from).collect(),
            )
        })
        .collect();
    let printed: Vec<(usize, Vec<usize>, Vec<usize>)> = molecule
        .0
        .iter()
        .enumerate()
        .flat_map(|(dim, row)| {
            row.iter()
                .map(move |&(ref inputs, ref outputs)| (dim, inputs.clone(), outputs.clone()))
        })
        .collect();
    assert_eq!(written, printed);
}

#[test]
fn the_two_molecules_of_example_2_4_9_have_the_same_face_counts_and_different_keys()
{
    let second = example_2_4_9_second_edge();
    let third = example_2_4_9_third_edge();
    assert_eq!(
        second.counts(),
        third.counts(),
        "the counts of input and output faces do not tell the two apart"
    );
    assert_ne!(
        second.key(second.cells()),
        third.key(third.cells()),
        "the key does: the 2-cell holds the second edge or the third"
    );
}

#[test]
fn a_molecule_numbered_in_another_order_has_the_same_key()
{
    for molecule in [
        example_2_1_4(),
        example_2_4_11(),
        example_2_4_9_second_edge(),
        example_2_4_9_third_edge(),
    ] {
        let cells = molecule.cells();
        let key = molecule.key(cells.clone());
        let order = molecule.order(cells.clone());
        let reversed: Vec<Named> = cells.iter().rev().copied().collect();
        let mut rotated = cells.clone();
        rotated.rotate_left(3);
        let mut interleaved: Vec<Named> = cells.iter().step_by(2).copied().collect();
        interleaved.extend(cells.iter().skip(1).step_by(2).copied());
        for copy in [reversed, rotated, interleaved] {
            assert_eq!(
                molecule.order(copy.clone()),
                order,
                "the order marks the same named cells"
            );
            assert_eq!(
                molecule.key(copy),
                key,
                "a renumbered copy has the same key"
            );
        }
    }
}

/// A cell as the set of points it holds, one bit for each point.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Points(u8);

#[test]
fn a_poset_that_is_not_a_molecule_is_refused_at_the_cell_where_the_traversal_stops()
{
    let source = Element::from(0_usize);
    let parallel = FaceData(vec![vec![(vec![], vec![]); 2], vec![
        (vec![0], vec![1]),
        (vec![0], vec![1]),
    ]]);
    assert_eq!(
        parallel
            .poset(parallel.cells())
            .traverse(|lower, upper| parallel.side(lower, upper))
            .map(|traversal| traversal.key()),
        Err(TraversalError::NotAMolecule(source)),
        "two parallel edges with no 2-cell: their source has two input cofaces"
    );
    let apart = FaceData(vec![vec![(vec![], vec![]); 2]]);
    assert_eq!(
        apart
            .poset(apart.cells())
            .traverse(|lower, upper| apart.side(lower, upper))
            .map(|traversal| traversal.key()),
        Err(TraversalError::NotAMolecule(source)),
        "two points: no marked cell enters the pair"
    );
    // The point `{b}` lies directly below the top cell `{a, b, c}`, two ranks
    // up, and below no face of it.
    let cells = vec![Points(0b001), Points(0b010), Points(0b101), Points(0b111)];
    let most = ElementCount::from(cells.len());
    let skipping = GradedPoset::new(
        cells,
        |lower, upper| {
            if lower.0 & upper.0 == lower.0 {
                Comparison::Below
            }
            else {
                Comparison::NotBelow
            }
        },
        most,
    )
    .expect("inclusion is acyclic");
    assert_eq!(
        skipping
            .traverse(|_, _| Face::Input)
            .map(|traversal| traversal.key()),
        Err(TraversalError::NotAMolecule(Element::from(3_usize))),
        "a cover that skips a rank refuses its upper cell"
    );
}
