//! The equivalence of a complex with its reduct on the complex's own
//! composites: Doré's graph `two` with paths and squares, two collapses of a
//! triangle in sequence, a square whose faces occur under a context, the
//! cover of a match over two columns as a sum of reductions in sequence, the
//! step of a unifier that solves a variable as one matched pair, and the
//! abelianisation of the test complexes against the reduct's Morse boundary.

use alloc::vec::Vec;
use core::fmt::Debug;

use gandr_theory_discrete_morse::Abelian;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Composites;
use gandr_theory_discrete_morse::Definition;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::Images;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Invertibility;
use gandr_theory_discrete_morse::Matching;
use gandr_theory_discrete_morse::Place;
use gandr_theory_discrete_morse::Standing;
use gandr_theory_discrete_morse::collapse;
use gandr_theory_discrete_morse::equivalence;
use gandr_theory_discrete_morse::greedy;
use gandr_theory_discrete_morse::reduct;
use gandr_theory_reductions::Budget;
use gandr_theory_reductions::Closure;
use gandr_theory_reductions::Count;
use gandr_theory_reductions::MorseError;
use gandr_theory_reductions::PartIndex;
use gandr_theory_reductions::Reduction;
use gandr_theory_reductions::Refusal;
use gandr_theory_reductions::Sum;
use gandr_theory_reductions::SumFault;
use gandr_theory_reductions::Summand;

use crate::simplices::FILLED;
use crate::simplices::Facets;
use crate::simplices::HOLLOW;
use crate::simplices::Triangle;

/// The name of a cell of a test graph.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Name(&'static str);

/// The vertex `true` of `two`.
const TRUE: Name = Name("true");
/// The vertex `false` of `two`.
const FALSE: Name = Name("false");
/// The edge `there : true → false` of `two`.
const THERE: Name = Name("there");
/// The edge `back : false → true` of `two`.
const BACK: Name = Name("back");
/// The vertex `a` of the triangle.
const A: Name = Name("a");
/// The vertex `b` of the triangle.
const B: Name = Name("b");
/// The vertex `c` of the triangle.
const C: Name = Name("c");
/// The edge `p : a → b` of the triangle.
const P: Name = Name("p");
/// The edge `q : b → c` of the triangle.
const Q: Name = Name("q");
/// The edge `r : c → a` of the triangle.
const R: Name = Name("r");

/// A budget that every walk of a test graph stays within.
const ROOM: usize = 8;

/// The way a path crosses an edge.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Way
{
    /// From the edge's source to its target.
    Forward,
    /// From the edge's target to its source.
    Backward,
}

/// A path of a test graph: the vertex it starts at, the vertex it ends at,
/// and the edges it crosses, with no edge crossed and then crossed back at
/// once. The ends are explicit, because an edge of a reduct keeps its name
/// and takes the images of its ends.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Path
{
    /// The vertex the path starts at.
    start: Name,
    /// The vertex the path ends at.
    end: Name,
    /// Each edge the path crosses, in order, with its way.
    steps: Vec<(Name, Way)>,
}

/// The path from `start` to `end` across `steps`.
///
/// # Specification
/// trivial.
fn path(
    start: Name,
    end: Name,
    steps: &[(Name, Way)],
) -> Path
{
    Path {
        start,
        end,
        steps: steps.to_vec(),
    }
}

/// The identity path at `at`.
///
/// # Specification
/// trivial.
fn stay(at: Name) -> Path
{
    path(at, at, &[])
}

impl Path
{
    /// The path crossed back from its end to its start.
    ///
    /// # Specification
    /// trivial.
    fn inverse(&self) -> Self
    {
        Self {
            start: self.end,
            end: self.start,
            steps: self
                .steps
                .iter()
                .rev()
                .map(|&(edge, way)| {
                    (edge, match way {
                        Way::Forward => Way::Backward,
                        Way::Backward => Way::Forward,
                    })
                })
                .collect(),
        }
    }

    /// Cross the steps of `then` after this path's, cancelling an edge that
    /// is crossed and then crossed back at once.
    ///
    /// # Specification
    /// trivial.
    fn append(
        &mut self,
        then: &Self,
    )
    {
        for &(edge, way) in &then.steps {
            match self.steps.last() {
                Some(&(last, back)) if last == edge && back != way => {
                    let _cancelled = self.steps.pop();
                },
                Some(_) | None => self.steps.push((edge, way)),
            }
        }
        self.end = then.end;
    }
}

/// A square of a test graph by its sides: a path from the start of its
/// source to the start of its target, and one between their ends. It closes
/// where its source and then its right side cross the same edges as its left
/// side and then its target.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Square
{
    /// The side between the starts.
    left: Path,
    /// The side between the ends.
    right: Path,
}

/// The square at a vertex whose two sides are `side`.
///
/// # Specification
/// trivial.
fn square(side: Path) -> Square
{
    Square {
        left: side.clone(),
        right: side,
    }
}

/// How the test search defines a redundant vertex.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Search
{
    /// By the other end of its partner, with the partner as its witness.
    Honest,
    /// As the honest search, with a witness that stops at its own vertex.
    Forged,
    /// By itself, so the definition runs through its own cell.
    Circular,
}

/// Why a test graph refuses: a cell that it does not hold, or that defines
/// nothing.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Refused(Name);

/// A test graph and the search it runs. A test reads the pairs it states over
/// the graph through `Matching::on`.
#[derive(Debug)]
struct Graph
{
    /// The vertices.
    vertices: Vec<Name>,
    /// Each edge with its source and its target.
    edges: Vec<(Name, Name, Name)>,
    /// How a redundant vertex is defined.
    search: Search,
}

impl Graph
{
    /// Doré's graph `two`: the vertices `true` and `false`, and the edges
    /// `there : true → false` and `back : false → true`, with the honest
    /// search.
    ///
    /// # Specification
    /// trivial.
    fn two() -> Self
    {
        Self {
            vertices: [TRUE, FALSE].to_vec(),
            edges: [(THERE, TRUE, FALSE), (BACK, FALSE, TRUE)].to_vec(),
            search: Search::Honest,
        }
    }

    /// The triangle: the vertices `a`, `b` and `c`, and the edges
    /// `p : a → b`, `q : b → c` and `r : c → a`, with the honest search.
    ///
    /// # Specification
    /// trivial.
    fn triangle() -> Self
    {
        Self {
            vertices: [A, B, C].to_vec(),
            edges: [(P, A, B), (Q, B, C), (R, C, A)].to_vec(),
            search: Search::Honest,
        }
    }

    /// The cells, each after its faces: the vertices, then the edges.
    ///
    /// # Specification
    /// trivial.
    fn cells(&self) -> Vec<Name>
    {
        let mut cells = self.vertices.clone();
        cells.extend(self.edges.iter().map(|&(edge, ..)| edge));
        cells
    }

    /// The source and the target of `edge`, or nothing for a vertex.
    ///
    /// # Specification
    /// trivial.
    fn ends(
        &self,
        edge: Name,
    ) -> Option<(Name, Name)>
    {
        for &(name, source, target) in &self.edges {
            if name == edge {
                return Some((source, target));
            }
        }
        None
    }
}

/// The graph of the target cells of `reduction`, each edge between the
/// images of its ends, with the honest search.
///
/// # Specification
/// trivial.
fn reduced<R>(reduction: &mut R) -> Graph
where
    R: Reduction<Cell = Name, Composite = Path>,
    R::Fault: Debug,
{
    let mut graph = Graph {
        vertices: Vec::new(),
        edges: Vec::new(),
        search: Search::Honest,
    };
    for cell in reduction.target().to_vec() {
        let generator = reduction.generator(&cell).expect("a target cell");
        let image = reduction.collapse(&generator).expect("the collapse");
        if image.steps.is_empty() {
            graph.vertices.push(cell);
        }
        else {
            graph.edges.push((cell, image.start, image.end));
        }
    }
    graph
}

/// `φ` of the generator of `cell`.
///
/// # Specification
/// trivial.
fn collapsed<R>(
    reduction: &mut R,
    cell: Name,
) -> Result<Path, Refusal<Name, R::Fault>>
where
    R: Reduction<Cell = Name, Composite = Path>,
{
    let generator = reduction.generator(&cell)?;
    reduction.collapse(&generator)
}

impl Complex for Graph
{
    type Cell = Name;
    type Fault = Refused;

    /// A vertex or an edge of the graph lies in it.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        cell: &Name,
    ) -> Result<Standing, Refused>
    {
        Ok(
            if self.vertices.contains(cell) || self.ends(*cell).is_some() {
                Standing::Inside
            }
            else {
                Standing::Outside
            },
        )
    }

    /// An edge's target at the incidence one and its source at minus one.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &Name,
        faces: &mut Vec<(Name, Incidence)>,
    ) -> Result<(), Refused>
    {
        if let Some((source, target)) = self.ends(*cell) {
            faces.push((target, Incidence::from(1_i64)));
            faces.push((source, Incidence::from(-1_i64)));
        }
        Ok(())
    }
}

impl Composites for Graph
{
    type Composite = Path;
    type Witness = Square;

    /// The identity path at a vertex, and the one-step path of an edge.
    ///
    /// # Specification
    /// trivial.
    fn generator(
        &mut self,
        cell: &Name,
    ) -> Result<Path, Refused>
    {
        if let Some((source, target)) = self.ends(*cell) {
            return Ok(path(source, target, &[(*cell, Way::Forward)]));
        }
        if self.vertices.contains(cell) {
            return Ok(stay(*cell));
        }
        Err(Refused(*cell))
    }

    /// The identity path at the start of `composite`.
    ///
    /// # Specification
    /// trivial.
    fn identity(
        &mut self,
        composite: &Path,
    ) -> Result<Path, Refused>
    {
        Ok(stay(composite.start))
    }

    /// The start, each edge the path crosses, and the end. An interior vertex
    /// is a face of the edges at it, and occurs in no composite apart from
    /// them.
    ///
    /// # Specification
    /// trivial.
    fn generators(
        &mut self,
        composite: &Path,
        cells: &mut Vec<Name>,
    ) -> Result<(), Refused>
    {
        cells.push(composite.start);
        cells.extend(composite.steps.iter().map(|&(edge, _)| edge));
        cells.push(composite.end);
        Ok(())
    }

    /// The start moved to its image, and each edge replaced by its image,
    /// crossed back where the path crosses it back. An edge with no image
    /// runs between the images of its ends.
    ///
    /// # Specification
    /// trivial.
    fn substitute(
        &mut self,
        composite: &Path,
        images: &Images<'_, Name, Path>,
    ) -> Result<Path, Refused>
    {
        let moved = |vertex: Name| images.of(&vertex).map_or(vertex, |image| image.start);
        let mut out = stay(moved(composite.start));
        for &(edge, way) in &composite.steps {
            let image = if let Some(image) = images.of(&edge) {
                image.clone()
            }
            else {
                let (source, target) = self.ends(edge).ok_or(Refused(edge))?;
                path(moved(source), moved(target), &[(edge, Way::Forward)])
            };
            match way {
                Way::Forward => out.append(&image),
                Way::Backward => out.append(&image.inverse()),
            }
        }
        Ok(out)
    }

    /// Each side with each mapped cell replaced by its image.
    ///
    /// # Specification
    /// trivial.
    fn carry(
        &mut self,
        witness: &Square,
        images: &Images<'_, Name, Path>,
    ) -> Result<Square, Refused>
    {
        Ok(Square {
            left: self.substitute(&witness.left, images)?,
            right: self.substitute(&witness.right, images)?,
        })
    }

    /// The two squares stacked: each side of `first`, then the same side of
    /// `second`.
    ///
    /// # Specification
    /// trivial.
    fn compose(
        &mut self,
        first: &Square,
        second: &Square,
    ) -> Result<Square, Refused>
    {
        let mut left = first.left.clone();
        left.append(&second.left);
        let mut right = first.right.clone();
        right.append(&second.right);
        Ok(Square { left, right })
    }

    /// The square whose sides are the witnesses at the start and at the end,
    /// or nothing where neither end has one.
    ///
    /// # Specification
    /// trivial.
    fn whisker(
        &mut self,
        composite: &Path,
        witnesses: &Images<'_, Name, Square>,
    ) -> Result<Option<Square>, Refused>
    {
        let left = witnesses
            .of(&composite.start)
            .map(|square| square.left.clone());
        let right = witnesses
            .of(&composite.end)
            .map(|square| square.right.clone());
        Ok(match (left, right) {
            (None, None) => None,
            (left, right) => Some(Square {
                left: left.unwrap_or_else(|| stay(composite.start)),
                right: right.unwrap_or_else(|| stay(composite.end)),
            }),
        })
    }

    /// The other end of the partner edge, with the edge crossed from the
    /// redundant vertex as both sides of its witness.
    ///
    /// # Specification
    /// trivial.
    fn definition(
        &mut self,
        redundant: &Name,
        partner: &Name,
    ) -> Result<Definition<Path, Square>, Refused>
    {
        if self.search == Search::Circular {
            return Ok(Definition {
                replacement: stay(*redundant),
                witness: square(stay(*redundant)),
            });
        }
        let (source, target) = self.ends(*partner).ok_or(Refused(*partner))?;
        let (other, way) = if *redundant == source {
            (target, Way::Forward)
        }
        else if *redundant == target {
            (source, Way::Backward)
        }
        else {
            return Err(Refused(*partner));
        };
        let side = match self.search {
            Search::Forged => stay(*redundant),
            Search::Honest | Search::Circular => path(*redundant, other, &[(*partner, way)]),
        };
        Ok(Definition {
            replacement: stay(other),
            witness: square(side),
        })
    }

    /// Whether the sides join the ends of `source` and `target`, and the
    /// square commutes.
    ///
    /// # Specification
    /// trivial.
    fn replays(
        &mut self,
        witness: &Square,
        source: &Path,
        target: &Path,
    ) -> Result<Closure, Refused>
    {
        let mut down = source.clone();
        down.append(&witness.right);
        let mut across = witness.left.clone();
        across.append(target);
        let joined = witness.left.start == source.start
            && witness.left.end == target.start
            && witness.right.start == source.end
            && witness.right.end == target.end;
        Ok(if joined && down == across {
            Closure::Closes
        }
        else {
            Closure::Open
        })
    }

    /// A vertex alone, or an edge between the inverse of its source's path to
    /// its sink and its target's path to its sink.
    ///
    /// # Specification
    /// trivial.
    fn conjugate(
        &mut self,
        cell: &Name,
        witnesses: &Images<'_, Name, Square>,
    ) -> Result<Path, Refused>
    {
        let Some((source, target)) = self.ends(*cell)
        else {
            return self.generator(cell);
        };
        let mut out = witnesses
            .of(&source)
            .map_or_else(|| stay(source), |square| square.left.inverse());
        out.append(&path(source, target, &[(*cell, Way::Forward)]));
        if let Some(square) = witnesses.of(&target) {
            out.append(&square.right);
        }
        Ok(out)
    }
}

#[test]
fn the_graph_two_collapses_onto_one_vertex_and_one_loop()
{
    let room = Budget::from(ROOM);
    let matching = Matching::stated([(FALSE, BACK)]);
    let mut two = Graph::two();
    let cells = two.cells();
    let mut scheme = matching.on(&mut two);
    let built = equivalence(&mut scheme, &cells, room).expect("an acyclic matching");
    assert_eq!(built.critical(), [TRUE, THERE]);
    let mut bound = built
        .on(&mut scheme, &cells, room)
        .expect("the equivalence reads");
    // `φ` sends `false` to its sink, the matched edge to the identity there,
    // and the edge `true → false` to the loop of the reduct.
    assert_eq!(collapsed(&mut bound, FALSE), Ok(stay(TRUE)));
    assert_eq!(collapsed(&mut bound, BACK), Ok(stay(TRUE)));
    let looped = path(TRUE, TRUE, &[(THERE, Way::Forward)]);
    assert_eq!(collapsed(&mut bound, THERE), Ok(looped.clone()));
    // `ι` sends the loop to the composite of the two edges, a loop at
    // `true`, through the witness from `false` to its sink.
    assert_eq!(
        bound.section(&stay(FALSE)),
        Ok(Some(square(path(FALSE, TRUE, &[(BACK, Way::Forward)]))))
    );
    assert_eq!(
        bound.include(&looped),
        Ok(path(TRUE, TRUE, &[
            (THERE, Way::Forward),
            (BACK, Way::Forward)
        ]))
    );
    assert_eq!(bound.replay(), Ok(()));
}

#[test]
fn a_forged_witness_is_refused_by_name()
{
    let room = Budget::from(ROOM);
    let matching = Matching::stated([(FALSE, BACK)]);
    let mut two = Graph::two();
    two.search = Search::Forged;
    let cells = two.cells();
    let mut scheme = matching.on(&mut two);
    let built = equivalence(&mut scheme, &cells, room).expect("the build trusts the search");
    assert_eq!(
        built.replay(&mut scheme, &cells, room),
        Err(Refusal::Forged(FALSE))
    );
}

#[test]
fn a_matching_with_a_cycle_is_refused_by_name()
{
    // Both vertices pair with the edge that leaves them, so the gradient runs
    // from `true` to `false` and back.
    let matching = Matching::stated([(TRUE, THERE), (FALSE, BACK)]);
    let mut two = Graph::two();
    let cells = two.cells();
    assert_eq!(
        equivalence(&mut matching.on(&mut two), &cells, Budget::from(ROOM)),
        Err(Refusal::Cycle(Count::from(1)))
    );
}

#[test]
fn a_definition_through_its_own_cell_is_circular()
{
    let matching = Matching::stated([(FALSE, BACK)]);
    let mut two = Graph::two();
    two.search = Search::Circular;
    let cells = two.cells();
    assert_eq!(
        equivalence(&mut matching.on(&mut two), &cells, Budget::from(ROOM)),
        Err(Refusal::Circular(FALSE))
    );
}

#[test]
fn a_matching_with_no_pair_gives_the_identity()
{
    let room = Budget::from(ROOM);
    let none = Matching::<Name>::stated([]);
    let mut two = Graph::two();
    let cells = two.cells();
    let mut scheme = none.on(&mut two);
    let built = equivalence(&mut scheme, &cells, room).expect("an acyclic matching");
    assert_eq!(built.critical(), cells.as_slice());
    assert_eq!(built.removals(), []);
    let mut bound = built
        .on(&mut scheme, &cells, room)
        .expect("the equivalence reads");
    for &cell in &cells {
        let generator = bound.generator(&cell).expect("a cell of two");
        assert_eq!(bound.collapse(&generator), Ok(generator.clone()));
        assert_eq!(bound.include(&generator), Ok(generator.clone()));
        assert_eq!(bound.section(&generator), Ok(None));
    }
    assert_eq!(bound.replay(), Ok(()));
}

#[test]
fn two_collapses_compose_in_sequence()
{
    let room = Budget::from(ROOM);
    let b_onto_a = Matching::stated([(B, P)]);
    let c_onto_a = Matching::stated([(C, Q)]);
    let mut triangle = Graph::triangle();
    let cells = triangle.cells();
    let mut base = b_onto_a.on(&mut triangle);
    let first = equivalence(&mut base, &cells, room).expect("an acyclic matching");
    let mut lower = first
        .on(&mut base, &cells, room)
        .expect("the equivalence reads");
    // The first collapse sends `b` to `a`, so `q` runs from `a` to `c`.
    let mut middle = reduced(&mut lower);
    assert_eq!(middle.edges, [(Q, A, C), (R, C, A)]);
    let inner = middle.cells();
    let mut next = c_onto_a.on(&mut middle);
    let second = equivalence(&mut next, &inner, room).expect("an acyclic matching");
    let last = reduct(&mut next, &inner, room)
        .expect("the reduct")
        .cells()
        .to_vec();
    let upper = second
        .on(&mut next, &inner, room)
        .expect("the equivalence reads");
    let mut both = lower.then(upper);
    assert_eq!(both.target(), last.as_slice());
    assert_eq!(both.target(), [A, R]);
    assert_eq!(both.replay(), Ok(()));
    // The composite sends `b` and `c` to `a`, and `r` to the loop there.
    assert_eq!(collapsed(&mut both, B), Ok(stay(A)));
    assert_eq!(collapsed(&mut both, C), Ok(stay(A)));
    let looped = path(A, A, &[(R, Way::Forward)]);
    assert_eq!(collapsed(&mut both, R), Ok(looped.clone()));
    // It includes the loop as the whole boundary of the triangle. Its witness
    // at `c` is the second witness, `q` crossed back, carried by the first
    // inclusion.
    assert_eq!(
        both.include(&looped),
        Ok(path(A, A, &[
            (P, Way::Forward),
            (Q, Way::Forward),
            (R, Way::Forward)
        ]))
    );
    assert_eq!(
        both.section(&stay(B)),
        Ok(Some(square(path(B, A, &[(P, Way::Backward)]))))
    );
    assert_eq!(
        both.section(&stay(C)),
        Ok(Some(square(path(C, A, &[
            (Q, Way::Backward),
            (P, Way::Backward)
        ]))))
    );
}

#[test]
fn a_composite_over_other_cells_is_unmatched()
{
    let room = Budget::from(ROOM);
    let b_onto_a = Matching::stated([(B, P)]);
    let none = Matching::<Name>::stated([]);
    let mut triangle = Graph::triangle();
    let cells = triangle.cells();
    let mut base = b_onto_a.on(&mut triangle);
    let first = equivalence(&mut base, &cells, room).expect("an acyclic matching");
    let lower = first
        .on(&mut base, &cells, room)
        .expect("the equivalence reads");
    // The second reduction reads the whole triangle, not the first target.
    let mut whole = Graph::triangle();
    let all = whole.cells();
    let mut bare = none.on(&mut whole);
    let second = equivalence(&mut bare, &all, room).expect("an acyclic matching");
    let upper = second
        .on(&mut bare, &all, room)
        .expect("the equivalence reads");
    assert_eq!(lower.then(upper).replay(), Err(Refusal::Unmatched(Some(C))));
}

#[test]
fn a_sum_reads_each_cell_in_its_own_part()
{
    let room = Budget::from(ROOM);
    let b_onto_a = Matching::stated([(B, P)]);
    let c_onto_b = Matching::stated([(C, Q)]);
    let mut left = Graph::triangle();
    let mut right = Graph::triangle();
    let cells = left.cells();
    let mut left_scheme = b_onto_a.on(&mut left);
    let mut right_scheme = c_onto_b.on(&mut right);
    let first = equivalence(&mut left_scheme, &cells, room).expect("an acyclic matching");
    let second = equivalence(&mut right_scheme, &cells, room).expect("an acyclic matching");
    let lower = first
        .on(&mut left_scheme, &cells, room)
        .expect("the equivalence reads");
    let upper = second
        .on(&mut right_scheme, &cells, room)
        .expect("the equivalence reads");
    let critical = [lower.target().to_vec(), upper.target().to_vec()];
    let mut sum = Sum::new(Vec::from([lower, upper]));
    let (zero, one) = (PartIndex::from(0_usize), PartIndex::from(1_usize));
    let tagged = |part: PartIndex, list: &[Name]| -> Vec<Summand<Name>> {
        list.iter().map(|&cell| Summand::new(part, cell)).collect()
    };
    assert_eq!(
        sum.source(),
        [tagged(zero, &cells), tagged(one, &cells)].concat()
    );
    assert_eq!(
        sum.target(),
        [tagged(zero, &critical[0]), tagged(one, &critical[1])].concat()
    );
    assert_eq!(sum.replay(), Ok(()));
    // `b` collapses onto `a` in the first part, and stays in the second.
    let early = sum
        .generator(&Summand::new(zero, B))
        .expect("a cell of the first part");
    assert_eq!(sum.collapse(&early), Ok(Summand::new(zero, stay(A))));
    let late = sum
        .generator(&Summand::new(one, B))
        .expect("a cell of the second part");
    assert_eq!(sum.collapse(&late), Ok(Summand::new(one, stay(B))));
    // A part past the parts, and two witnesses of two parts, are refused.
    let past = PartIndex::from(2_usize);
    assert_eq!(
        sum.generator(&Summand::new(past, A)),
        Err(Refusal::Morse(MorseError::Complex(SumFault::NoPart(past))))
    );
    let moved = sum
        .section(&Summand::new(zero, stay(B)))
        .expect("the section reads")
        .expect("`b` moves in the first part");
    let carried = sum
        .section(&Summand::new(one, stay(C)))
        .expect("the section reads")
        .expect("`c` moves in the second part");
    assert_eq!(
        sum.compose(&moved, &carried),
        Err(Refusal::Morse(MorseError::Complex(SumFault::Apart {
            first: zero,
            second: one
        })))
    );
    assert_eq!(
        sum.closes(
            &moved,
            &Summand::new(one, stay(B)),
            &Summand::new(one, stay(A))
        ),
        Ok(Closure::Open)
    );
}

#[test]
fn a_part_that_does_not_replay_is_refused_with_its_part()
{
    let room = Budget::from(ROOM);
    let b_onto_a = Matching::stated([(B, P)]);
    let c_onto_a = Matching::stated([(C, Q)]);
    let none = Matching::<Name>::stated([]);
    let mut honest = Graph::triangle();
    let cells = honest.cells();
    let mut base = b_onto_a.on(&mut honest);
    let first = equivalence(&mut base, &cells, room).expect("an acyclic matching");
    let mut lower = first
        .on(&mut base, &cells, room)
        .expect("the equivalence reads");
    let mut middle = reduced(&mut lower);
    let inner = middle.cells();
    let mut next = c_onto_a.on(&mut middle);
    let second = equivalence(&mut next, &inner, room).expect("an acyclic matching");
    let upper = second
        .on(&mut next, &inner, room)
        .expect("the equivalence reads");
    // The second part's second reduction reads the whole triangle, not the
    // first target.
    let mut other = Graph::triangle();
    let mut repeated = b_onto_a.on(&mut other);
    let again = equivalence(&mut repeated, &cells, room).expect("an acyclic matching");
    let below = again
        .on(&mut repeated, &cells, room)
        .expect("the equivalence reads");
    let mut whole = Graph::triangle();
    let all = whole.cells();
    let mut bare = none.on(&mut whole);
    let plain = equivalence(&mut bare, &all, room).expect("an acyclic matching");
    let above = plain
        .on(&mut bare, &all, room)
        .expect("the equivalence reads");
    let mut sum = Sum::new(Vec::from([lower.then(upper), below.then(above)]));
    assert_eq!(
        sum.replay(),
        Err(Refusal::Unmatched(Some(Summand::new(
            PartIndex::from(1_usize),
            C
        ))))
    );
}

/// The case `Zero, Zero` of a match over two columns of naturals.
const ZZ: Name = Name("Zero, Zero");
/// The case `Zero, Succ`.
const ZS: Name = Name("Zero, Succ");
/// The case `Succ, Zero`.
const SZ: Name = Name("Succ, Zero");
/// The case `Succ, Succ`.
const SS: Name = Name("Succ, Succ");
/// The edge `ZS → ZZ`: the second column varies under the arm `Zero, n`.
const VARIES: Name = Name("n varies");

/// The cases of a match over two columns under the first constructor of the
/// first column: `Zero` with the edge along which its second column varies,
/// or `Succ` with two cases and no edge.
///
/// # Specification
/// trivial.
fn cases(first: Name) -> Graph
{
    if first == ZZ {
        Graph {
            vertices: [ZZ, ZS].to_vec(),
            edges: [(VARIES, ZS, ZZ)].to_vec(),
            search: Search::Honest,
        }
    }
    else {
        Graph {
            vertices: [SZ, SS].to_vec(),
            edges: Vec::new(),
            search: Search::Honest,
        }
    }
}

/// The match `f Zero n`, `f (Succ m) Zero` and `f (Succ m) (Succ n)` over two
/// columns, as the derivation of its cover: `split` on the first column is
/// a sum with one part for each constructor, `compose` is a reduction in
/// sequence, `split` on the second column is the identity on its two cases,
/// and `var` on the second column is the collapse of the case `Zero, Succ`
/// onto `Zero, Zero` along the edge on which the column varies. The cells
/// that stay are the three arms.
#[test]
fn the_cover_of_a_match_over_two_columns_is_a_sum_of_reductions_in_sequence()
{
    let room = Budget::from(ROOM);
    let none = Matching::<Name>::stated([]);
    let varies = Matching::stated([(ZS, VARIES)]);
    let (mut zero_split, mut zero_var) = (cases(ZZ), cases(ZZ));
    let (mut succ_split, mut succ_split_again) = (cases(SZ), cases(SZ));
    let zero_cells = zero_split.cells();
    let succ_cells = succ_split.cells();
    let mut zero_first = none.on(&mut zero_split);
    let mut zero_next = varies.on(&mut zero_var);
    let mut succ_first = none.on(&mut succ_split);
    let mut succ_next = none.on(&mut succ_split_again);
    let zero_split_equivalence = equivalence(&mut zero_first, &zero_cells, room).expect("no pair");
    let zero_var_equivalence =
        equivalence(&mut zero_next, &zero_cells, room).expect("an acyclic matching");
    let succ_split_equivalence = equivalence(&mut succ_first, &succ_cells, room).expect("no pair");
    let succ_again_equivalence = equivalence(&mut succ_next, &succ_cells, room).expect("no pair");
    let zero_identity = zero_split_equivalence
        .on(&mut zero_first, &zero_cells, room)
        .expect("the identity reads");
    let zero_collapse = zero_var_equivalence
        .on(&mut zero_next, &zero_cells, room)
        .expect("the collapse reads");
    let succ_identity = succ_split_equivalence
        .on(&mut succ_first, &succ_cells, room)
        .expect("the identity reads");
    let succ_split_on_second = succ_again_equivalence
        .on(&mut succ_next, &succ_cells, room)
        .expect("the identity reads");
    let mut cover = Sum::new(Vec::from([
        zero_identity.then(zero_collapse),
        succ_identity.then(succ_split_on_second),
    ]));
    let (zero, succ) = (PartIndex::from(0_usize), PartIndex::from(1_usize));
    assert_eq!(
        cover.target(),
        [
            Summand::new(zero, ZZ),
            Summand::new(succ, SZ),
            Summand::new(succ, SS)
        ],
        "the cells that stay are the three arms, each in the part of its first constructor"
    );
    assert_eq!(cover.replay(), Ok(()), "the derivation replays");
    let varied = cover
        .generator(&Summand::new(zero, ZS))
        .expect("a case of the first part");
    assert_eq!(
        cover.collapse(&varied),
        Ok(Summand::new(zero, stay(ZZ))),
        "`var` sends the case to the arm that covers it"
    );
    assert_eq!(
        cover.section(&varied),
        Ok(Some(Summand::new(
            zero,
            square(path(ZS, ZZ, &[(VARIES, Way::Forward)]))
        ))),
        "and its witness is the edge on which the column varies"
    );
    let kept = cover
        .generator(&Summand::new(succ, SS))
        .expect("a case of the second part");
    assert_eq!(
        cover.collapse(&kept),
        Ok(Summand::new(succ, stay(SS))),
        "`split` keeps each case of its column"
    );
}

/// A `prune` is a part with no cell, and the sum states no conflict for it.
/// So the trait accepts a part with no case and no witness of why, where a
/// cover needs the clash of the pruned arm. The record of the cover needs a
/// value that carries it.
#[test]
fn a_part_with_no_cell_replays_with_no_witness_of_its_conflict()
{
    let room = Budget::from(ROOM);
    let none = Matching::<Name>::stated([]);
    let mut empty = Graph {
        vertices: Vec::new(),
        edges: Vec::new(),
        search: Search::Honest,
    };
    let mut kept = cases(SZ);
    let kept_cells = kept.cells();
    let mut empty_scheme = none.on(&mut empty);
    let mut kept_scheme = none.on(&mut kept);
    let no_cell: Vec<Name> = Vec::new();
    let pruned_equivalence = equivalence(&mut empty_scheme, &no_cell, room).expect("no pair");
    let split_equivalence = equivalence(&mut kept_scheme, &kept_cells, room).expect("no pair");
    let pruned = pruned_equivalence
        .on(&mut empty_scheme, &no_cell, room)
        .expect("the identity reads");
    let split = split_equivalence
        .on(&mut kept_scheme, &kept_cells, room)
        .expect("the identity reads");
    let mut cover = Sum::new(Vec::from([pruned, split]));
    let succ = PartIndex::from(1_usize);
    assert_eq!(cover.target(), [
        Summand::new(succ, SZ),
        Summand::new(succ, SS)
    ]);
    assert_eq!(cover.replay(), Ok(()));
}

/// The variable `x` of a telescope.
const X: Name = Name("x");
/// The variable `y` of a telescope.
const Y: Name = Name("y");
/// The term `s` that an equation gives `x`.
const S: Name = Name("s");
/// The equation `e : x = s`.
const E: Name = Name("e");
/// The equation `x = x`.
const SAME: Name = Name("x = x");

/// The telescope `x, e : x = s, y` as a graph: each variable and the term `s`
/// a vertex, and the equation an edge from `x` to `s`.
///
/// # Specification
/// trivial.
fn solved() -> Graph
{
    Graph {
        vertices: [X, S, Y].to_vec(),
        edges: [(E, X, S)].to_vec(),
        search: Search::Honest,
    }
}

/// The rule "solution" of a unifier removes a variable with the equation that
/// defines it: the pair of `x` and `e` is one matched pair. The collapse is
/// the telescope with neither of the two. It sends `x` to `s`, its witness is
/// the equation, and the equivalence replays.
#[test]
fn a_solved_variable_and_its_equation_are_one_matched_pair()
{
    let room = Budget::from(ROOM);
    let solution = Matching::stated([(X, E)]);
    let mut telescope = solved();
    let cells = telescope.cells();
    let mut scheme = solution.on(&mut telescope);
    let built = equivalence(&mut scheme, &cells, room).expect("an acyclic matching");
    assert_eq!(
        built.critical(),
        [S, Y],
        "the telescope without `x` and `e`"
    );
    let mut bound = built
        .on(&mut scheme, &cells, room)
        .expect("the equivalence reads");
    assert_eq!(collapsed(&mut bound, X), Ok(stay(S)));
    assert_eq!(collapsed(&mut bound, E), Ok(stay(S)));
    assert_eq!(collapsed(&mut bound, Y), Ok(stay(Y)));
    assert_eq!(
        bound.section(&stay(X)),
        Ok(Some(square(path(X, S, &[(E, Way::Forward)])))),
        "the witness from `x` to `s` is the equation"
    );
    assert_eq!(bound.replay(), Ok(()));
}

/// The rule "deletion" removes an equation `x = x`. That equation is a loop at
/// `x`, so it cannot be the partner of `x`: the definition of `x` through the
/// loop holds `x` itself, and the equivalence refuses the pair as circular.
/// With no pair the loop stays critical.
#[test]
fn an_equation_of_a_variable_with_itself_has_no_partner()
{
    let room = Budget::from(ROOM);
    let looped = || Graph {
        vertices: [X, Y].to_vec(),
        edges: [(SAME, X, X)].to_vec(),
        search: Search::Honest,
    };
    let mut deleted = looped();
    let cells = deleted.cells();
    let deletion = Matching::stated([(X, SAME)]);
    let mut scheme = deletion.on(&mut deleted);
    assert_eq!(
        equivalence(&mut scheme, &cells, room).map(|built| built.critical().to_vec()),
        Err(Refusal::Circular(X))
    );
    let none = Matching::<Name>::stated([]);
    let mut kept = looped();
    let mut bare = none.on(&mut kept);
    let built = equivalence(&mut bare, &cells, room).expect("no pair");
    assert_eq!(built.critical(), [X, Y, SAME], "the loop stays critical");
}

/// A cell of a square `D` from the edge `γ : x → z` to the composite of
/// `β : x → y` and `α : y → z`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Corner
{
    /// The vertex `x`.
    X,
    /// The vertex `y`.
    Y,
    /// The vertex `z`.
    Z,
    /// The edge `γ`, the whole source of `D`.
    Gamma,
    /// The edge `β`, whiskered by `α` in the target of `D`.
    Beta,
    /// The edge `α`, whiskered by `β` in the target of `D`.
    Alpha,
    /// The square `D : γ ⇒ β α`.
    Square,
}

/// The cells of the square, each after its faces.
const CORNERS: [Corner; 7] = [
    Corner::X,
    Corner::Y,
    Corner::Z,
    Corner::Gamma,
    Corner::Beta,
    Corner::Alpha,
    Corner::Square,
];

/// The square `D : γ ⇒ β α`. It pairs an edge with `D` only where the edge is
/// a whole side of `D`, with no context.
#[derive(Debug)]
struct Whiskered;

impl Complex for Whiskered
{
    type Cell = Corner;
    type Fault = Corner;

    /// Every cell lies in the square.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        _cell: &Corner,
    ) -> Result<Standing, Corner>
    {
        Ok(Standing::Inside)
    }

    /// An edge's target at one and its source at minus one; the square's
    /// target edges at one and its source edge at minus one.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &Corner,
        faces: &mut Vec<(Corner, Incidence)>,
    ) -> Result<(), Corner>
    {
        let (one, minus) = (Incidence::from(1_i64), Incidence::from(-1_i64));
        match *cell {
            Corner::Gamma => faces.extend([(Corner::Z, one), (Corner::X, minus)]),
            Corner::Beta => faces.extend([(Corner::Y, one), (Corner::X, minus)]),
            Corner::Alpha => faces.extend([(Corner::Z, one), (Corner::Y, minus)]),
            Corner::Square => faces.extend([
                (Corner::Beta, one),
                (Corner::Alpha, one),
                (Corner::Gamma, minus),
            ]),
            Corner::X | Corner::Y | Corner::Z => {},
        }
        Ok(())
    }

    /// The square admits `γ`, its whole source, and refuses `β` and `α`,
    /// which occur under a whisker.
    ///
    /// # Specification
    /// trivial.
    fn pairing(
        &mut self,
        face: &Corner,
        cell: &Corner,
        incidence: Incidence,
    ) -> Result<Invertibility, Corner>
    {
        Ok(match (*cell, *face) {
            (Corner::Square, Corner::Beta | Corner::Alpha) => Invertibility::NotInvertible,
            _ => incidence.invertibility(),
        })
    }
}

#[test]
fn a_pair_under_a_context_is_refused_at_the_incidence_one()
{
    let mut faces = Vec::new();
    Whiskered
        .faces(&Corner::Square, &mut faces)
        .expect("the square reads");
    assert!(faces.contains(&(Corner::Alpha, Incidence::from(1_i64))));
    assert!(faces.contains(&(Corner::Gamma, Incidence::from(-1_i64))));
    // `α` occurs once at the incidence one, but under the whisker `β`. The
    // stated pair reads the square's own condition, which refuses it.
    let under = Matching::stated([(Corner::Alpha, Corner::Square)]);
    let done = collapse(
        &mut under.on(&mut Whiskered),
        &CORNERS,
        Budget::from(CORNERS.len()),
    )
    .expect("the square reads");
    let refused = Faults {
        uninvertible: Count::from(1),
        ..Faults::default()
    };
    assert_eq!(done.faults(), refused);
    // `γ` is the whole source of the square, so it pairs.
    let whole = Matching::stated([(Corner::Gamma, Corner::Square)]);
    let done = collapse(
        &mut whole.on(&mut Whiskered),
        &CORNERS,
        Budget::from(CORNERS.len()),
    )
    .expect("the square reads");
    assert_eq!(done.faults(), Faults::default());
}

/// Check that the abelianised equivalence of the complex of `cells` along its
/// greedy matching replays, and that it collapses each critical boundary to
/// the reduct's Morse boundary.
///
/// # Specification
/// trivial.
fn abelianises<C>(
    complex: &mut C,
    cells: &[C::Cell],
) where
    C: Complex,
    C::Cell: Debug,
    C::Fault: Debug,
{
    let budget = Budget::from(cells.len());
    let matching = greedy(complex, cells).expect("the complex reads");
    let reduced = reduct(&mut matching.on(complex), cells, budget).expect("the reduct");
    let mut matched = matching.on(complex);
    let mut abelian = Abelian::new(&mut matched);
    let built = equivalence(&mut abelian, cells, budget).expect("an acyclic matching");
    let mut boundaries = Vec::with_capacity(reduced.cells().len());
    for cell in reduced.cells() {
        boundaries.push(abelian.boundary(cell).expect("the complex reads"));
    }
    let mut bound = built
        .on(&mut abelian, cells, budget)
        .expect("the equivalence reads");
    bound.replay().expect("the equivalence replays");
    let mut morse: Vec<(C::Cell, Incidence)> = Vec::new();
    for (at, (cell, boundary)) in reduced.cells().iter().zip(&boundaries).enumerate() {
        let collapsed = bound.collapse(boundary).expect("the collapse");
        morse.clear();
        morse.extend(
            reduced
                .boundary(Place::from(at))
                .iter()
                .filter_map(|&(face, incidence)| {
                    reduced
                        .cells()
                        .get(usize::from(face))
                        .map(|face| (face.clone(), incidence))
                }),
        );
        morse.sort();
        assert_eq!(collapsed.terms(), morse, "{cell:?}");
    }
}

#[test]
fn the_abelianisation_gives_the_morse_boundary_of_the_reduct()
{
    for weight in [1_i64, 2_i64] {
        let mut hollow = Triangle { weight };
        abelianises(&mut hollow, &HOLLOW);
        let mut filled = Triangle { weight };
        abelianises(&mut filled, &FILLED);
    }
    for mut surface in [
        Facets::sphere(),
        Facets::projective_plane(),
        Facets::torus(),
    ] {
        let cells = surface.cells();
        abelianises(&mut surface, &cells);
    }
}
