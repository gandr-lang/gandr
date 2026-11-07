//! The homotopy basis of B₃⁺ reduced by its critical triples, as Example
//! 7.5.8 of Ara and others states it, and the refusals of the reduction.

use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::Basis;
use gandr_theory_coherent_resolutions::BasisCell;
use gandr_theory_coherent_resolutions::BasisFault;
use gandr_theory_coherent_resolutions::BasisRefusal;
use gandr_theory_coherent_resolutions::CertificateIndex;
use gandr_theory_coherent_resolutions::Composite;
use gandr_theory_coherent_resolutions::Joinability;
use gandr_theory_coherent_resolutions::MovePlace;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::TripleIndex;
use gandr_theory_coherent_resolutions::Witness;
use gandr_theory_coherent_resolutions::join_critical_pairs;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Closure;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Composites;
use gandr_theory_discrete_morse::Count;
use gandr_theory_discrete_morse::Definition;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::Images;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Invertibility;
use gandr_theory_discrete_morse::Matching;
use gandr_theory_discrete_morse::Reduction as _;
use gandr_theory_discrete_morse::Refusal;
use gandr_theory_discrete_morse::Scheme;
use gandr_theory_discrete_morse::Standing;
use gandr_theory_discrete_morse::collapse;
use gandr_theory_discrete_morse::equivalence;

/// A letter of the braid monoid.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Letter
{
    /// The generator `s`.
    S,
    /// The generator `t`.
    T,
    /// The letter `a`, which stands for `st`.
    A,
}

/// The unary operation of `letter` applied to `inner`: the toy sum of its
/// tag and `inner`. No left-hand side unifies with a tag.
///
/// # Specification
/// trivial.
fn letter(
    letter: Letter,
    inner: Toy,
) -> Toy
{
    let tag = match letter {
        Letter::S => Toy::zero(),
        Letter::T => Toy::succ(Toy::zero()),
        Letter::A => Toy::succ(Toy::succ(Toy::zero())),
    };
    Toy::add(tag, inner)
}

/// The word of `letters` on the metavariable `x`, the first letter
/// outermost.
///
/// # Specification
/// trivial.
fn word(letters: &[Letter]) -> Toy
{
    letters
        .iter()
        .rev()
        .fold(Toy::var("x"), |inner, each| letter(*each, inner))
}

/// The four rules of Example 10, in its order: `ta → as`, `st → a`,
/// `sas → aa` and `saa → aat`.
///
/// # Specification
/// trivial.
fn braid() -> CellStore<ToyAlphabet>
{
    use Letter::A;
    use Letter::S;
    use Letter::T;
    let rules: [(&[Letter], &[Letter]); 4] = [
        (&[T, A], &[A, S]),
        (&[S, T], &[A]),
        (&[S, A, S], &[A, A]),
        (&[S, A, A], &[A, A, T]),
    ];
    let mut store = CellStore::new();
    for (lhs, rhs) in rules {
        let _id = store.insert(toy_cell(word(lhs), word(rhs)));
    }
    store
}

/// The certificates of each critical pair of `store`, in the order of the
/// joining: for B₃⁺, A on `sta`, B on `sast`, C on `sasas` and D on `sasaa`.
///
/// # Specification
/// trivial.
fn certificates(store: &CellStore<ToyAlphabet>) -> Vec<Tracelet<ToyAlphabet>>
{
    let Joinability::Joined(certificates) =
        join_critical_pairs(store, NormalizationBudget::from(64_usize))
    else {
        panic!("the presentation is convergent");
    };
    certificates
}

/// The confluence at `place`.
///
/// # Specification
/// trivial.
fn confluence(place: CertificateIndex) -> BasisCell
{
    BasisCell::Confluence(place)
}

/// The triple at `place`.
///
/// # Specification
/// trivial.
fn triple(place: TripleIndex) -> BasisCell
{
    BasisCell::Triple(place)
}

/// The confluences A, B, C and D, and the triples on `sasta`, `sasast`,
/// `sasasas` and `sasasaa`, as the basis of B₃⁺ indexes them.
///
/// # Specification
/// trivial.
fn names() -> ([BasisCell; 4], [BasisCell; 4])
{
    let confluences = [0_usize, 1, 2, 3].map(|place| confluence(CertificateIndex::from(place)));
    let triples = [0_usize, 1, 2, 3].map(|place| triple(TripleIndex::from(place)));
    (confluences, triples)
}

/// The budget of the boundaries.
///
/// # Specification
/// trivial.
fn budget() -> NormalizationBudget
{
    NormalizationBudget::from(16_usize)
}

/// The budget of the collapse walk.
///
/// # Specification
/// trivial.
fn walk() -> Budget
{
    Budget::from(64_usize)
}

#[test]
fn the_braid_monoid_keeps_two_confluences()
{
    let store = braid();
    let certificates = certificates(&store);
    let mut basis = Basis::new(&store, &certificates, budget()).expect("the basis builds");
    let ([a, b, c, d], [sasta, sasast, sasasas, sasasaa]) = names();
    let cells = basis.cells();
    assert_eq!(cells, [a, b, c, d, sasta, sasast, sasasas, sasasaa]);
    let equivalence = equivalence(&mut basis, &cells, walk()).expect("the reduction is acyclic");
    assert_eq!(
        equivalence.critical(),
        [a, b, sasasas, sasasaa],
        "A and B stay, as do the triples that pair nothing"
    );
    let removals: Vec<_> = equivalence
        .removals()
        .iter()
        .map(|removal| (*removal.redundant(), *removal.partner()))
        .collect();
    assert_eq!(
        removals,
        [(c, sasta), (d, sasast)],
        "the triple on sasta removes C, and the triple on sasast removes D"
    );
    let mut held = Vec::new();
    for removal in equivalence.removals() {
        held.clear();
        basis
            .generators(&removal.definition().replacement, &mut held)
            .expect("the replacement reads");
        assert!(
            held.iter()
                .all(|cell| cell != removal.redundant() && [a, b, c].contains(cell)),
            "a replacement holds earlier confluences alone: {held:?}"
        );
    }
    equivalence
        .replay(&mut basis, &cells, walk())
        .expect("the equivalence replays");
    let mut bound = equivalence
        .on(&mut basis, &cells, walk())
        .expect("the equivalence reads on its basis");
    for removed in [c, d] {
        let own = bound.generator(&removed).expect("the confluence is a cell");
        let collapsed = bound.collapse(&own).expect("the collapse reads it");
        held.clear();
        basis_generators(&collapsed, &mut held);
        assert!(
            held.iter().all(|cell| [a, b].contains(cell)),
            "the collapse of {removed:?} holds A and B alone: {held:?}"
        );
    }
}

#[test]
fn each_removal_of_the_braid_reduction_is_one_tietze_move_6059()
{
    // A removal is a Tietze removal: its triple's 4-cell shows the confluence
    // superfluous, a collapsible 3-sphere in § 7.4.6 of Ara and others. Stated
    // alone, the pair is an equivalence that replays, and the reduction
    // collapses each cell as its moves do, the last removal first. Each move
    // reads its own copy of the basis, because the moves are read at once.
    let store = braid();
    let certificates = certificates(&store);
    let basis = Basis::new(&store, &certificates, budget()).expect("the basis builds");
    let cells = basis.cells();
    let mut whole = basis.clone();
    let reduction = equivalence(&mut whole, &cells, walk()).expect("the reduction is acyclic");
    let stated: Vec<Matching<BasisCell>> = reduction
        .removals()
        .iter()
        .map(|removal| Matching::stated([(*removal.redundant(), *removal.partner())]))
        .collect();
    let mut copies: Vec<_> = stated.iter().map(|_| basis.clone()).collect();
    let mut moves = Vec::new();
    for ((removal, matching), copy) in reduction.removals().iter().zip(&stated).zip(&mut copies) {
        let pair = (*removal.redundant(), *removal.partner());
        let mut alone = matching.on(copy);
        let one = equivalence(&mut alone, &cells, walk()).expect("one pair is acyclic");
        let [ref only] = *one.removals()
        else {
            panic!("one removal, not {}", one.removals().len());
        };
        assert_eq!((*only.redundant(), *only.partner()), pair);
        assert_eq!(
            only.definition().replacement,
            removal.definition().replacement,
            "the move defines {pair:?} as the reduction does"
        );
        one.replay(&mut alone, &cells, walk())
            .expect("the move replays");
        moves.push((alone, one));
    }
    assert_eq!(moves.len(), 2, "C and D, one move each");
    let mut bounds: Vec<_> = moves
        .iter_mut()
        .map(|&mut (ref mut alone, ref one)| {
            one.on(alone, &cells, walk())
                .expect("the move reads on its basis")
        })
        .collect();
    for each in &mut bounds {
        assert_eq!(each.replay(), Ok(()), "the move replays as a reduction");
    }
    let mut bound = reduction
        .on(&mut whole, &cells, walk())
        .expect("the reduction reads on its basis");
    for cell in &cells {
        let own = bound.generator(cell).expect("the cell is a generator");
        let reduced = bound.collapse(&own).expect("the reduction collapses it");
        let mut moved = own;
        for each in bounds.iter_mut().rev() {
            moved = each.collapse(&moved).expect("the move collapses it");
        }
        assert_eq!(
            moved, reduced,
            "the moves collapse {cell:?} as the reduction does"
        );
    }
}

/// Push each confluence that a move of `composite` takes onto `held`.
///
/// # Specification
/// trivial.
fn basis_generators(
    composite: &Composite<ToyAlphabet>,
    held: &mut Vec<BasisCell>,
)
{
    use gandr_theory_coherent_resolutions::Move;
    held.extend(
        composite
            .homotopy()
            .moves
            .iter()
            .filter_map(|each| match *each {
                Move::Confluence { certificate, .. } => Some(confluence(certificate)),
                Move::Exchange { .. } | Move::Expand { .. } | Move::Contract { .. } => None,
            }),
    );
}

#[test]
fn the_reduction_passes_the_collapse_and_a_cycle_is_refused()
{
    let store = braid();
    let certificates = certificates(&store);
    let mut basis = Basis::new(&store, &certificates, budget()).expect("the basis builds");
    let cells = basis.cells();
    let checked = collapse(&mut basis, &cells, walk()).expect("the walk stays in budget");
    assert_eq!(
        checked.faults(),
        Faults::default(),
        "the reduction is an acyclic matching"
    );
    let ([_, _, c, d], [_, _, sasasas, sasasaa]) = names();
    let stated = Matching::stated([(c, sasasaa), (d, sasasas)]);
    let mut cyclic = stated.on(&mut basis);
    let checked = collapse(&mut cyclic, &cells, walk()).expect("the walk stays in budget");
    assert_ne!(checked.faults().cycles, Count::default());
    assert!(
        matches!(
            equivalence(&mut cyclic, &cells, walk()),
            Err(Refusal::Cycle(_))
        ),
        "C reaches D through the triple on sasasaa, and D reaches C through the one on sasasas"
    );
}

#[test]
fn a_confluence_under_a_context_is_refused_at_the_incidence_one()
{
    let store = braid();
    let certificates = certificates(&store);
    let mut basis = Basis::new(&store, &certificates, budget()).expect("the basis builds");
    let cells = basis.cells();
    let ([_, b, _, _], [sasta, ..]) = names();
    let mut faces = Vec::new();
    basis
        .faces(&sasta, &mut faces)
        .expect("the triple is a cell");
    assert!(
        faces.contains(&(b, Incidence::from(1_i64))),
        "B occurs once in the triple on sasta, under the substitution of a: {faces:?}"
    );
    assert_eq!(
        basis
            .pairing(&b, &sasta, Incidence::from(1_i64))
            .expect("the pairing reads"),
        Invertibility::NotInvertible
    );
    let stated = Matching::stated([(b, sasta)]);
    let mut whiskered = stated.on(&mut basis);
    assert!(matches!(
        equivalence(&mut whiskered, &cells, walk()),
        Err(Refusal::Unpairable(count)) if count == Count::from(1_usize)
    ));
}

/// The basis with a definition search that gives each witness a cut that
/// names no confluence.
#[derive(Debug)]
#[repr(transparent)]
struct Forging<'basis>
{
    /// The honest basis.
    basis: Basis<'basis, ToyAlphabet>,
}

impl Complex for Forging<'_>
{
    type Cell = BasisCell;
    type Fault = BasisFault;

    /// The basis's standing.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        cell: &BasisCell,
    ) -> Result<Standing, BasisFault>
    {
        self.basis.standing(cell)
    }

    /// The basis's faces.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &BasisCell,
        faces: &mut Vec<(BasisCell, Incidence)>,
    ) -> Result<(), BasisFault>
    {
        self.basis.faces(cell, faces)
    }

    /// The basis's pairing condition.
    ///
    /// # Specification
    /// trivial.
    fn pairing(
        &mut self,
        face: &BasisCell,
        cell: &BasisCell,
        incidence: Incidence,
    ) -> Result<Invertibility, BasisFault>
    {
        self.basis.pairing(face, cell, incidence)
    }
}

impl Scheme for Forging<'_>
{
    /// The basis's class.
    ///
    /// # Specification
    /// trivial.
    fn class(
        &mut self,
        cell: &BasisCell,
    ) -> Result<Class<BasisCell>, BasisFault>
    {
        self.basis.class(cell)
    }
}

impl Composites for Forging<'_>
{
    type Composite = Composite<ToyAlphabet>;
    type Witness = Witness<ToyAlphabet>;

    /// The basis's generator.
    ///
    /// # Specification
    /// trivial.
    fn generator(
        &mut self,
        cell: &BasisCell,
    ) -> Result<Self::Composite, BasisFault>
    {
        self.basis.generator(cell)
    }

    /// The basis's identity.
    ///
    /// # Specification
    /// trivial.
    fn identity(
        &mut self,
        composite: &Self::Composite,
    ) -> Result<Self::Composite, BasisFault>
    {
        self.basis.identity(composite)
    }

    /// The basis's generators.
    ///
    /// # Specification
    /// trivial.
    fn generators(
        &mut self,
        composite: &Self::Composite,
        cells: &mut Vec<BasisCell>,
    ) -> Result<(), BasisFault>
    {
        self.basis.generators(composite, cells)
    }

    /// The basis's substitution.
    ///
    /// # Specification
    /// trivial.
    fn substitute(
        &mut self,
        composite: &Self::Composite,
        images: &Images<'_, BasisCell, Self::Composite>,
    ) -> Result<Self::Composite, BasisFault>
    {
        self.basis.substitute(composite, images)
    }

    /// The basis's carry.
    ///
    /// # Specification
    /// trivial.
    fn carry(
        &mut self,
        witness: &Self::Witness,
        images: &Images<'_, BasisCell, Self::Composite>,
    ) -> Result<Self::Witness, BasisFault>
    {
        self.basis.carry(witness, images)
    }

    /// The basis's composite.
    ///
    /// # Specification
    /// trivial.
    fn compose(
        &mut self,
        first: &Self::Witness,
        second: &Self::Witness,
    ) -> Result<Self::Witness, BasisFault>
    {
        self.basis.compose(first, second)
    }

    /// The basis's whiskering.
    ///
    /// # Specification
    /// trivial.
    fn whisker(
        &mut self,
        composite: &Self::Composite,
        witnesses: &Images<'_, BasisCell, Self::Witness>,
    ) -> Result<Option<Self::Witness>, BasisFault>
    {
        self.basis.whisker(composite, witnesses)
    }

    /// The basis's definition, each fill moved to the first move of its
    /// triple's boundary.
    ///
    /// # Specification
    /// trivial.
    fn definition(
        &mut self,
        redundant: &BasisCell,
        partner: &BasisCell,
    ) -> Result<Definition<Self::Composite, Self::Witness>, BasisFault>
    {
        let mut definition = self.basis.definition(redundant, partner)?;
        for fill in &mut definition.witness.fills {
            fill.cut = MovePlace::default();
        }
        Ok(definition)
    }

    /// The basis's replay of a witness.
    ///
    /// # Specification
    /// trivial.
    fn replays(
        &mut self,
        witness: &Self::Witness,
        source: &Self::Composite,
        target: &Self::Composite,
    ) -> Result<Closure, BasisFault>
    {
        self.basis.replays(witness, source, target)
    }

    /// The basis's conjugate.
    ///
    /// # Specification
    /// trivial.
    fn conjugate(
        &mut self,
        cell: &BasisCell,
        witnesses: &Images<'_, BasisCell, Self::Witness>,
    ) -> Result<Self::Composite, BasisFault>
    {
        self.basis.conjugate(cell, witnesses)
    }
}

#[test]
fn a_forged_witness_is_refused_by_name()
{
    let store = braid();
    let certificates = certificates(&store);
    let basis = Basis::new(&store, &certificates, budget()).expect("the basis builds");
    let cells = basis.cells();
    let mut forging = Forging { basis };
    let forged = equivalence(&mut forging, &cells, walk()).expect("the build trusts its search");
    let ([_, _, c, _], [sasta, ..]) = names();
    let removal = forged.removals().first().expect("C is removed first");
    let own = forging.basis.generator(&c).expect("C is a cell");
    assert_eq!(
        forging
            .basis
            .replays(
                &removal.definition().witness,
                &own,
                &removal.definition().replacement,
            )
            .expect("the replay reads"),
        Closure::Open,
        "the first move of the boundary on sasta is B under a substitution, no cut"
    );
    assert_eq!(*removal.partner(), sasta);
    assert_eq!(
        forged.replay(&mut forging.basis, &cells, walk()),
        Err(Refusal::Forged(c))
    );
}

#[test]
fn cells_with_no_triple_keep_each_confluence()
{
    let mut store = CellStore::new();
    let _left = store.insert(toy_cell(
        Toy::add(Toy::zero(), Toy::var("y")),
        Toy::var("y"),
    ));
    let _right = store.insert(toy_cell(
        Toy::add(Toy::var("x"), Toy::zero()),
        Toy::var("x"),
    ));
    let certificates = certificates(&store);
    let mut basis = Basis::new(&store, &certificates, budget()).expect("the basis builds");
    assert!(basis.triples().is_empty());
    let cells = basis.cells();
    assert_eq!(cells, [confluence(CertificateIndex::from(0_usize))]);
    let equivalence = equivalence(&mut basis, &cells, walk()).expect("nothing pairs");
    assert_eq!(equivalence.critical(), cells.as_slice());
    assert!(equivalence.removals().is_empty());
    equivalence
        .replay(&mut basis, &cells, walk())
        .expect("the identity replays");
    let mut bound = equivalence
        .on(&mut basis, &cells, walk())
        .expect("the equivalence reads on its basis");
    let own = bound
        .generator(&cells[0])
        .expect("the confluence is a cell");
    assert_eq!(bound.collapse(&own), Ok(own.clone()));
    assert_eq!(bound.include(&own), Ok(own));
}

#[test]
fn a_triple_past_the_budget_pairs_nothing()
{
    let store = braid();
    let certificates = certificates(&store);
    let mut basis = Basis::new(&store, &certificates, NormalizationBudget::from(3_usize))
        .expect("the basis builds");
    let ([a, b, c, d], [sasta, sasast, sasasas, sasasaa]) = names();
    assert_eq!(
        basis.unbuilt(),
        [TripleIndex::from(2_usize), TripleIndex::from(3_usize)],
        "the triples on sasasas and sasasaa need four steps"
    );
    assert_eq!(basis.standing(&sasasas), Ok(Standing::Outside));
    assert_eq!(basis.standing(&sasasaa), Ok(Standing::Outside));
    let cells = basis.cells();
    assert_eq!(cells, [a, b, c, d, sasta, sasast]);
    let equivalence = equivalence(&mut basis, &cells, walk()).expect("the reduction is acyclic");
    assert_eq!(equivalence.critical(), [a, b]);
    equivalence
        .replay(&mut basis, &cells, walk())
        .expect("the equivalence replays");
}

#[test]
fn a_cell_that_copies_a_variable_is_refused()
{
    let mut store = CellStore::new();
    let _copy = store.insert(toy_cell(
        Toy::succ(Toy::var("x")),
        Toy::add(Toy::var("x"), Toy::var("x")),
    ));
    assert!(matches!(
        Basis::new(&store, &[], budget()),
        Err(BasisRefusal::Nonlinear(id)) if id == CellId::from(0_usize)
    ));
}
