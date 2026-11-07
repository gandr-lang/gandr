//! Probe 16 of the presented-spaces frame: exact inference over a junction
//! tree is a gluing.
//!
//! The network is the sprinkler network of four binary variables. It is
//! cloudy with the weight one half. The sprinkler acts with one tenth when it
//! is cloudy and with one half otherwise. Rain falls with four fifths when it
//! is cloudy and with one fifth otherwise. The grass is wet with 99/100 when
//! the sprinkler and the rain both act, and with 9/10 when one of them acts.
//! When neither acts, the grass stays dry.
//!
//! Its junction tree has two cliques, {cloudy, sprinkler, rain} and
//! {sprinkler, rain, wet grass}, and one separator, {sprinkler, rain}.
//! Sum-product sums the potential of each clique onto the separator and
//! sends that message to the other clique. The marginal of a clique is its
//! potential times the message it receives. The reference sums the joint
//! distribution over all sixteen worlds.
//!
//! The two cliques and the separator are a graded poset. The separator lies
//! above both cliques, as the opens of a cover lie in reverse inclusion. The
//! stalk of a cell is its table of weights, and the restriction to the
//! separator is marginalisation. Marginalisation sums two weights into one,
//! but an entry map of the crate reads one weight. So the probe holds a sheaf
//! of its own, whose restrictions are linear maps over `Rational`.

use gandr_theory_cellular_sheaves::CoverIndex;
use gandr_theory_cellular_sheaves::Entry;
use gandr_theory_cellular_sheaves::Obstruction;
use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_cellular_sheaves::SheafError;
use gandr_theory_cellular_sheaves::Width;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;

/// A variable of the network.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Variable
{
    /// Whether it is cloudy.
    Cloudy,
    /// Whether the sprinkler acts.
    Sprinkler,
    /// Whether rain falls.
    Rain,
    /// Whether the grass is wet.
    WetGrass,
}

/// The value of a variable in a world.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Truth
{
    /// The variable is false.
    False,
    /// The variable is true.
    True,
}

/// The values of the four variables, one bit each: a set bit is true.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct World(u8);

/// The world where every variable is false.
const NOWHERE: World = World(0);

/// The world where `variable` alone is true.
///
/// # Specification
/// trivial.
const fn only(variable: Variable) -> World
{
    World(match variable {
        Variable::Cloudy => 1,
        Variable::Sprinkler => 2,
        Variable::Rain => 4,
        Variable::WetGrass => 8,
    })
}

impl World
{
    /// The value of `variable` in the world.
    ///
    /// # Specification
    /// trivial.
    const fn holds(
        self,
        variable: Variable,
    ) -> Truth
    {
        if self.0 & only(variable).0 == 0 {
            Truth::False
        }
        else {
            Truth::True
        }
    }

    /// The world with `variable` set to `truth`, and each other variable as
    /// it is.
    ///
    /// # Specification
    /// trivial.
    const fn with(
        self,
        variable: Variable,
        truth: Truth,
    ) -> Self
    {
        match truth {
            Truth::False => Self(self.0 & !only(variable).0),
            Truth::True => Self(self.0 | only(variable).0),
        }
    }
}

/// The variables of a clique or a separator, in the order of the bits of an
/// entry: the first variable is the lowest bit.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Scope(&'static [Variable]);

/// The four variables: the scope of the joint distribution.
const EVERY: Scope = Scope(&[
    Variable::Cloudy,
    Variable::Sprinkler,
    Variable::Rain,
    Variable::WetGrass,
]);

/// The first clique: cloudy, sprinkler and rain.
const WEATHER: Scope = Scope(&[Variable::Cloudy, Variable::Sprinkler, Variable::Rain]);

/// The second clique: sprinkler, rain and wet grass.
const LAWN: Scope = Scope(&[Variable::Sprinkler, Variable::Rain, Variable::WetGrass]);

/// The separator of the two cliques: sprinkler and rain.
const SEPARATOR: Scope = Scope(&[Variable::Sprinkler, Variable::Rain]);

impl Scope
{
    /// The number of weights in a table over the scope: one for each value
    /// of its variables.
    ///
    /// # Specification
    /// trivial.
    fn width(self) -> Width
    {
        let count = u32::try_from(self.0.len()).expect("a scope of four variables at most");
        Width::from(
            1_usize
                .checked_shl(count)
                .expect("a scope of four variables at most"),
        )
    }

    /// The entry of `world` in a table over the scope.
    ///
    /// # Specification
    /// trivial.
    fn entry(
        self,
        world: World,
    ) -> Entry
    {
        Entry::from(self.0.iter().rev().fold(0_usize, |entry, &variable| {
            let bit = match world.holds(variable) {
                Truth::False => 0_usize,
                Truth::True => 1_usize,
            };
            entry.saturating_mul(2_usize).saturating_add(bit)
        }))
    }

    /// The world whose variables in the scope take the values that `entry`
    /// names, and whose other variables are false.
    ///
    /// # Specification
    /// trivial.
    fn world(
        self,
        entry: Entry,
    ) -> World
    {
        self.0
            .iter()
            .enumerate()
            .fold(NOWHERE, |world, (place, &variable)| {
                let shift = u32::try_from(place).expect("a scope of four variables at most");
                let bit = usize::from(entry).checked_shr(shift).unwrap_or(0_usize) & 1_usize;
                let truth = if bit == 0 { Truth::False } else { Truth::True };
                world.with(variable, truth)
            })
    }

    /// The world where the variables of the scope are true, and every other
    /// variable is false.
    ///
    /// # Specification
    /// trivial.
    fn members(self) -> World
    {
        self.0.iter().fold(NOWHERE, |world, &variable| {
            world.with(variable, Truth::True)
        })
    }

    /// Whether the scope lies below `upper` in the junction tree: whether it
    /// holds every variable of `upper` and at least one more.
    ///
    /// # Specification
    /// trivial.
    fn below(
        self,
        upper: Self,
    ) -> Comparison
    {
        let (own, theirs) = (self.members(), upper.members());
        if own != theirs && own.0 & theirs.0 == theirs.0 {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

/// A table of weights over a scope, one weight for each entry.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Table
{
    /// The variables of the table.
    scope: Scope,
    /// The weights, in entry order.
    weights: Vec<Rational>,
}

impl Table
{
    /// The table over `scope` whose weight at each entry is `weight` of the
    /// world of that entry.
    ///
    /// # Specification
    /// trivial.
    fn of<Weight>(
        scope: Scope,
        mut weight: Weight,
    ) -> Result<Self, SheafError>
    where
        Weight: FnMut(World) -> Result<Rational, SheafError>,
    {
        let weights = (0 .. usize::from(scope.width()))
            .map(|entry| weight(scope.world(Entry::from(entry))))
            .collect::<Result<Vec<Rational>, SheafError>>()?;
        Ok(Self { scope, weights })
    }

    /// The weight at `entry`.
    ///
    /// # Specification
    /// trivial.
    fn at(
        &self,
        entry: Entry,
    ) -> Rational
    {
        self.weights
            .get(usize::from(entry))
            .copied()
            .expect("an entry of the table")
    }

    /// The table summed onto `onto`, whose variables the table holds: the
    /// weight at each entry of `onto` is the sum of the weights that agree
    /// with it on the variables of `onto`.
    ///
    /// # Specification
    /// trivial.
    fn marginal(
        &self,
        onto: Scope,
    ) -> Result<Self, SheafError>
    {
        let mut weights = vec![Rational::ZERO; usize::from(onto.width())];
        for (entry, &weight) in self.weights.iter().enumerate() {
            let at = onto.entry(self.scope.world(Entry::from(entry)));
            let sum = weights
                .get_mut(usize::from(at))
                .expect("an entry of the smaller scope");
            *sum = sum.plus(weight)?;
        }
        Ok(Self {
            scope: onto,
            weights,
        })
    }

    /// The table times `message`, whose variables the table holds: each
    /// weight times the weight of `message` at the same world.
    ///
    /// # Specification
    /// trivial.
    fn times(
        &self,
        message: &Self,
    ) -> Result<Self, SheafError>
    {
        Self::of(self.scope, |world| {
            self.at(self.scope.entry(world))
                .times(message.at(message.scope.entry(world)))
        })
    }
}

/// The weight of a variable whose value is `truth`, when the variable is
/// true with the weight `chance`.
///
/// # Specification
/// trivial.
fn given(
    truth: Truth,
    chance: Rational,
) -> Result<Rational, SheafError>
{
    match truth {
        Truth::True => Ok(chance),
        Truth::False => Rational::ONE.plus(chance.times(rational!(-1, 1))?),
    }
}

/// The potential of the weather clique at `world`: the weights of cloudy,
/// of the sprinkler given cloudy, and of the rain given cloudy.
///
/// # Specification
/// trivial.
fn weather(world: World) -> Result<Rational, SheafError>
{
    let (sprinkler, rain) = match world.holds(Variable::Cloudy) {
        Truth::True => (rational!(1, 10), rational!(4, 5)),
        Truth::False => (rational!(1, 2), rational!(1, 5)),
    };
    given(world.holds(Variable::Cloudy), rational!(1, 2))?
        .times(given(world.holds(Variable::Sprinkler), sprinkler)?)?
        .times(given(world.holds(Variable::Rain), rain)?)
}

/// The potential of the lawn clique at `world`: the weight of wet grass
/// given the sprinkler and the rain.
///
/// # Specification
/// trivial.
fn lawn(world: World) -> Result<Rational, SheafError>
{
    let wet = match (
        world.holds(Variable::Sprinkler),
        world.holds(Variable::Rain),
    ) {
        (Truth::True, Truth::True) => rational!(99, 100),
        (Truth::True, Truth::False) | (Truth::False, Truth::True) => rational!(9, 10),
        (Truth::False, Truth::False) => Rational::ZERO,
    };
    given(world.holds(Variable::WetGrass), wet)
}

/// The weight of `world` in the joint distribution: the product of the two
/// potentials.
///
/// # Specification
/// trivial.
fn joint(world: World) -> Result<Rational, SheafError>
{
    weather(world)?.times(lawn(world)?)
}

/// The marginal of each clique by sum-product: its potential times the
/// potential of the other clique summed onto the separator.
///
/// # Specification
/// trivial.
fn sum_product() -> Result<(Table, Table), SheafError>
{
    let weather = Table::of(WEATHER, weather)?;
    let lawn = Table::of(LAWN, lawn)?;
    let to_lawn = weather.marginal(SEPARATOR)?;
    let to_weather = lawn.marginal(SEPARATOR)?;
    Ok((weather.times(&to_weather)?, lawn.times(&to_lawn)?))
}

/// The marginal of the joint distribution on `scope`, summed over all
/// sixteen worlds.
///
/// # Specification
/// trivial.
fn reference(scope: Scope) -> Result<Table, SheafError>
{
    Table::of(EVERY, joint)?.marginal(scope)
}

/// Each entry where `got` differs from `want`, with the weight of each.
///
/// # Specification
/// trivial.
fn differences(
    got: &Table,
    want: &Table,
) -> Vec<(Entry, Rational, Rational)>
{
    got.weights
        .iter()
        .zip(&want.weights)
        .enumerate()
        .filter(|&(_, (left, right))| left != right)
        .map(|(entry, (&left, &right))| (Entry::from(entry), left, right))
        .collect()
}

/// A linear map from the stalk of a cell to the stalk of a cell above it:
/// one row for each entry of the upper stalk, one coefficient for each entry
/// of the lower stalk.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Linear
{
    /// The width of the lower stalk.
    columns: Width,
    /// The coefficients, row by row.
    coefficients: Vec<Rational>,
}

impl Linear
{
    /// Marginalisation from the table over `lower` onto the table over
    /// `upper`: the coefficient is one where an entry of `lower` agrees with
    /// an entry of `upper` on the variables of `upper`, and zero elsewhere.
    ///
    /// # Specification
    /// trivial.
    fn marginalisation(
        lower: Scope,
        upper: Scope,
    ) -> Self
    {
        let columns = lower.width();
        let coefficients = (0 .. usize::from(upper.width()))
            .flat_map(|row| {
                (0 .. usize::from(columns)).map(move |column| {
                    if upper.entry(lower.world(Entry::from(column))) == Entry::from(row) {
                        Rational::ONE
                    }
                    else {
                        Rational::ZERO
                    }
                })
            })
            .collect();
        Self {
            columns,
            coefficients,
        }
    }

    /// The image of `section` under the map.
    ///
    /// # Specification
    /// trivial.
    fn apply(
        &self,
        section: &[Rational],
    ) -> Result<Vec<Rational>, SheafError>
    {
        self.coefficients
            .chunks(usize::from(self.columns))
            .map(|row| {
                row.iter()
                    .zip(section)
                    .try_fold(Rational::ZERO, |sum, (&coefficient, &value)| {
                        sum.plus(coefficient.times(value)?)
                    })
            })
            .collect()
    }
}

/// The verdict of the probe's sheaf on the sections of a cover.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Verdict
{
    /// The sections agree at each overlap. The glued section holds, at each
    /// cell above a member, the restriction of the first member below it.
    Glued(Vec<(Element, Vec<Rational>)>),
    /// These pairs of members differ, in cover order; never empty.
    Obstructed(Vec<Obstruction>),
}

/// A cellular sheaf whose restrictions are linear maps over `Rational`: the
/// poset, and a map for each pair of a cell and a cell above it.
struct LinearSheaf
{
    /// The cells and their order.
    poset: GradedPoset<Scope>,
    /// Each pair of a cell and a cell above it, with the map between their
    /// stalks.
    maps: Vec<(Element, Element, Linear)>,
}

impl LinearSheaf
{
    /// The sheaf of tables on `poset`: the stalk of each cell is the table
    /// over its scope, and each restriction is marginalisation. The poset has
    /// two ranks, so no chain of three cells asks the maps to compose.
    ///
    /// # Specification
    /// trivial.
    fn of_tables(poset: GradedPoset<Scope>) -> Result<Self, SheafError>
    {
        let count = poset.cells().len();
        let pairs = (0 .. count).flat_map(|upper| {
            (0 .. count)
                .filter(move |&lower| lower != upper)
                .map(move |lower| (Element::from(lower), Element::from(upper)))
        });
        let mut maps = Vec::new();
        for (lower, upper) in pairs {
            if poset.compare(lower, upper).map_err(SheafError::Poset)? == Comparison::Below {
                let lower_scope = *poset
                    .cells()
                    .get(usize::from(lower))
                    .ok_or(SheafError::CellOutside(lower))?;
                let upper_scope = *poset
                    .cells()
                    .get(usize::from(upper))
                    .ok_or(SheafError::CellOutside(upper))?;
                maps.push((
                    lower,
                    upper,
                    Linear::marginalisation(lower_scope, upper_scope),
                ));
            }
        }
        Ok(Self { poset, maps })
    }

    /// The stalk width of `cell`.
    ///
    /// # Specification
    /// trivial.
    fn width(
        &self,
        cell: Element,
    ) -> Result<Width, SheafError>
    {
        self.poset
            .cells()
            .get(usize::from(cell))
            .map(|scope| scope.width())
            .ok_or(SheafError::CellOutside(cell))
    }

    /// The restriction of `section`, a section at `lower`, to `upper`: the
    /// section itself when the two cells are one.
    ///
    /// # Specification
    /// trivial.
    fn restrict(
        &self,
        lower: Element,
        upper: Element,
        section: &[Rational],
    ) -> Result<Vec<Rational>, SheafError>
    {
        if lower == upper {
            return Ok(section.to_vec());
        }
        self.maps
            .iter()
            .find(|&&(from, to, _)| from == lower && to == upper)
            .ok_or(SheafError::OutsideSupport(upper))?
            .2
            .apply(section)
    }

    /// The first cell above both `left` and `right`, in cell order, where
    /// their restrictions differ, with the first entry of its stalk where
    /// they differ.
    ///
    /// # Specification
    /// trivial.
    fn difference(
        &self,
        left: (Element, &[Rational]),
        right: (Element, &[Rational]),
    ) -> Result<Option<(Element, Entry)>, SheafError>
    {
        for cell in (0 .. self.poset.cells().len()).map(Element::from) {
            let over_left = self
                .poset
                .compare(left.0, cell)
                .map_err(SheafError::Poset)?;
            let over_right = self
                .poset
                .compare(right.0, cell)
                .map_err(SheafError::Poset)?;
            if over_left == Comparison::NotBelow || over_right == Comparison::NotBelow {
                continue;
            }
            let from_left = self.restrict(left.0, cell, left.1)?;
            let from_right = self.restrict(right.0, cell, right.1)?;
            if let Some(entry) = from_left
                .iter()
                .zip(&from_right)
                .position(|(one, other)| one != other)
            {
                return Ok(Some((cell, Entry::from(entry))));
            }
        }
        Ok(None)
    }

    /// The gluing of the sections of `cover`, as the crate's
    /// `Sheaf::glue` states it.
    ///
    /// # Specification
    /// trivial.
    fn glue(
        &self,
        cover: &[(Element, &[Rational])],
    ) -> Result<Verdict, SheafError>
    {
        for &(cell, section) in cover {
            if Width::from(section.len()) != self.width(cell)? {
                return Err(SheafError::SectionWidth {
                    cell,
                    width: Width::from(section.len()),
                });
            }
        }
        let mut obstructions = Vec::new();
        for (first, &left) in cover.iter().enumerate() {
            for (second, &right) in cover.iter().enumerate().skip(first.saturating_add(1)) {
                if let Some((overlap, entry)) = self.difference(left, right)? {
                    obstructions.push(Obstruction {
                        members: (CoverIndex::from(first), CoverIndex::from(second)),
                        overlap,
                        entry,
                    });
                }
            }
        }
        if !obstructions.is_empty() {
            return Ok(Verdict::Obstructed(obstructions));
        }
        let mut glued = Vec::new();
        for cell in (0 .. self.poset.cells().len()).map(Element::from) {
            let mut below = None;
            for &(member, section) in cover {
                if self
                    .poset
                    .compare(member, cell)
                    .map_err(SheafError::Poset)?
                    == Comparison::Below
                {
                    below = Some((member, section));
                    break;
                }
            }
            if let Some((member, section)) = below {
                glued.push((cell, self.restrict(member, cell, section)?));
            }
        }
        Ok(Verdict::Glued(glued))
    }
}

/// The obstructions of `verdict`: none for a glued cover.
///
/// # Specification
/// trivial.
fn obstructions(verdict: &Verdict) -> &[Obstruction]
{
    match *verdict {
        Verdict::Glued(_) => &[],
        Verdict::Obstructed(ref obstructions) => obstructions.as_slice(),
    }
}

/// The junction tree as a graded poset: the weather clique, the lawn clique,
/// and the separator above both.
///
/// # Specification
/// trivial.
fn junction() -> GradedPoset<Scope>
{
    GradedPoset::new(
        vec![WEATHER, LAWN, SEPARATOR],
        |lower, upper| lower.below(*upper),
        ElementCount::from(3_usize),
    )
    .expect("a poset of three cells")
}

/// The cell of the weather clique.
const WEATHER_CELL: usize = 0;

/// The cell of the lawn clique.
const LAWN_CELL: usize = 1;

/// The cell of the separator.
const SEPARATOR_CELL: usize = 2;

/// An entry map gives each entry of the separator the weight of one entry of
/// the clique. Three of the four separator weights are no weight of the
/// weather clique, and three are no weight of the lawn clique. So no entry
/// map restricts either clique to the separator.
#[test]
fn marginalisation_fits_no_entry_map()
{
    let separator = reference(SEPARATOR).expect("the separator's marginal");
    let weather = reference(WEATHER).expect("the weather clique's marginal");
    let lawn = reference(LAWN).expect("the lawn clique's marginal");
    let read_from = |clique: &Table| -> [bool; 4] {
        core::array::from_fn(|entry| clique.weights.contains(&separator.at(Entry::from(entry))))
    };
    assert_eq!(read_from(&weather), [false, false, false, true]);
    assert_eq!(read_from(&lawn), [true, false, false, false]);
}

/// Sum-product gives each clique the marginal of the joint distribution on
/// its variables, entry by entry. A failure names each entry that differs.
#[test]
fn sum_product_gives_each_clique_the_marginal_of_the_joint()
{
    let (weather, lawn) = sum_product().expect("the clique marginals");
    let total = reference(Scope(&[]))
        .expect("the empty marginal")
        .at(Entry::from(0_usize));
    assert_eq!(total, Rational::ONE);
    let weather_reference = reference(WEATHER).expect("the weather clique's reference");
    assert_eq!(differences(&weather, &weather_reference), []);
    let lawn_reference = reference(LAWN).expect("the lawn clique's reference");
    assert_eq!(differences(&lawn, &lawn_reference), []);
}

/// The separator by hand: from the weather clique, the sum over cloudy; from
/// the lawn clique, the sum over wet grass. Both give these weights, and the
/// two clique marginals glue to the section that holds them and both cliques.
#[test]
fn the_clique_marginals_glue_on_the_separator()
{
    let by_hand = [
        rational!(29, 100),
        rational!(21, 100),
        rational!(41, 100),
        rational!(9, 100),
    ];
    let (weather, lawn) = sum_product().expect("the clique marginals");
    for clique in [&weather, &lawn] {
        let separator = clique.marginal(SEPARATOR).expect("the separator's weights");
        assert_eq!(separator.weights, by_hand, "{:?}", clique.scope);
    }
    let sheaf = LinearSheaf::of_tables(junction()).expect("the sheaf of tables");
    let verdict = sheaf
        .glue(&[
            (Element::from(WEATHER_CELL), weather.weights.as_slice()),
            (Element::from(LAWN_CELL), lawn.weights.as_slice()),
        ])
        .expect("a cover of the two cliques");
    assert_eq!(
        verdict,
        Verdict::Glued(vec![
            (Element::from(WEATHER_CELL), weather.weights),
            (Element::from(LAWN_CELL), lawn.weights),
            (Element::from(SEPARATOR_CELL), by_hand.to_vec()),
        ])
    );
}

/// One weight of one clique, raised by 1/100, breaks the agreement at the
/// separator. The obstruction names the separator entry of that weight's
/// sprinkler and rain.
#[test]
fn one_changed_weight_in_either_clique_is_obstructed_at_its_separator_entry()
{
    let (weather, lawn) = sum_product().expect("the clique marginals");
    let sheaf = LinearSheaf::of_tables(junction()).expect("the sheaf of tables");
    let step = rational!(1, 100);
    let mut sections = [weather.weights, lawn.weights];
    for (member, scope) in [(WEATHER_CELL, WEATHER), (LAWN_CELL, LAWN)] {
        for entry in (0 .. usize::from(scope.width())).map(Entry::from) {
            let weight = sections
                .get_mut(member)
                .and_then(|section| section.get_mut(usize::from(entry)))
                .expect("an entry of the clique");
            let kept = *weight;
            *weight = kept.plus(step).expect("a raised weight");
            let [ref weather_section, ref lawn_section] = sections;
            let verdict = sheaf
                .glue(&[
                    (Element::from(WEATHER_CELL), weather_section.as_slice()),
                    (Element::from(LAWN_CELL), lawn_section.as_slice()),
                ])
                .expect("a cover of the two cliques");
            assert_eq!(
                obstructions(&verdict),
                [Obstruction {
                    members: (CoverIndex::from(0_usize), CoverIndex::from(1_usize)),
                    overlap: Element::from(SEPARATOR_CELL),
                    entry: SEPARATOR.entry(scope.world(entry)),
                }],
                "{scope:?} at {entry:?}"
            );
            let restored = sections
                .get_mut(member)
                .and_then(|section| section.get_mut(usize::from(entry)))
                .expect("an entry of the clique");
            *restored = kept;
        }
    }
}
