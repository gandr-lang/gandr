//! Guarded templates over generated families of certificates: the clauses a
//! template is emitted under, and the verdict table the spike decides on.
//!
//! A family is one base certificate — every certificate `derive_fused` and
//! `complete` produce over the sequent and toy stores — whose peak's and
//! join's holes each member fills with small numerals, in one of three
//! regimes: two arms per entry, one entry varying, every arm distinct. Beside
//! them sit the adversarial classes: a member whose path diverges in one step,
//! a member whose peak carries a body a recorded cell discriminates on, and
//! members sharing no arm. The sequent alphabet's only command position is the
//! root; the toy alphabet's every node is one.

use gandr_theory_cell_complexes::Cat;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_cell_complexes::frame_defining_cell;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToySubst;
use gandr_theory_coherent_resolutions::CompletionBudget;
use gandr_theory_coherent_resolutions::CompletionCellBudget;
use gandr_theory_coherent_resolutions::CompletionStepBudget;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::StuckStep;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::complete;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_deep_inference::EntryIndex;
use gandr_theory_deep_inference::GuardedTemplate;
use gandr_theory_deep_inference::InheritanceCache;
use gandr_theory_deep_inference::InheritanceVerdict;
use gandr_theory_deep_inference::LegStepIndex;
use gandr_theory_deep_inference::MemberIndex;
use gandr_theory_deep_inference::NodeCount;
use gandr_theory_deep_inference::TemplateLeg;
use gandr_theory_deep_inference::TemplateObstruction;
use gandr_theory_deep_inference::TemplateRefusal;
use gandr_theory_deep_inference::anti_unify_tracelets;
use gandr_theory_deep_inference::flows_equal;
use gandr_theory_deep_inference::tracelet_flow;
use proptest::prelude::*;

use crate::fixture::add_s;
use crate::fixture::add_z;
use crate::fixture::cong2_store;

/// How a family's members fill the base's holes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Regime
{
    /// Member `i` fills hole `e` with the numeral of bit `e` of `i`: two arms
    /// per entry once the family has four members.
    TwoArms,
    /// Member `i` fills the first hole with the numeral of `i` and every other
    /// with zero: one entry, as many arms as members.
    OneVarying,
    /// Member `i` fills every hole with the numeral of `i`: no arm shared by
    /// two members.
    AllDistinct,
}

/// Whether a family carries a member that is not an honest instance of its
/// base.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Adversary
{
    /// Every member is an honest instance of the base.
    Honest,
    /// The last member's first path loses its final step.
    Diverged,
    /// The last member's peak carries, where the base's first cell reads, a
    /// body that cell does not fire on.
    Discriminated,
}

/// A family size.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Members(usize);

/// The position of a member in its family, or of a hole in its base's peak.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Ordinal(usize);

/// The numeral a member fills a hole with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Value(usize);

/// The name of a certificate source or of an alphabet, as a table row reads it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Name(&'static str);

/// One source of base certificates: the store they replay over and the
/// certificates.
struct Source<A: CellAlphabet>
{
    /// Where the certificates came from.
    name: Name,
    /// The store every certificate replays over.
    store: CellStore<A>,
    /// The certificates.
    bases: Vec<Tracelet<A>>,
}

/// What a row of the verdict table is about.
struct Label
{
    /// The alphabet the family is generated over.
    alphabet: Name,
    /// The family's class.
    class: String,
}

/// The family sizes the corpus generates.
const SIZES: [Members; 3] = [Members(2), Members(8), Members(64)];

/// The regimes the corpus generates.
const REGIMES: [Regime; 3] = [Regime::TwoArms, Regime::OneVarying, Regime::AllDistinct];

/// A term language the corpus instantiates certificates in.
trait Corpus: CellAlphabet
{
    /// The substitution sending every listed hole to the numeral of its
    /// value.
    ///
    /// # Specification
    /// trivial.
    fn numerals(holes: &[(Self::Var, Value)]) -> Self::Subst;

    /// `peak` with the body the base's first recorded cell reads replaced by
    /// one it does not fire on.
    ///
    /// # Specification
    /// trivial.
    fn discriminated(peak: &Self::Cmd) -> Self::Cmd;
}

/// `n` successors of `Zero`, as a producer.
///
/// # Specification
/// trivial.
fn numeral(n: Value) -> ProdPat
{
    (0_usize .. n.0).fold(ProdPat::ctor("Zero", []), |inner, _| {
        ProdPat::ctor("Succ", [inner])
    })
}

/// `n` return-side `Succ⁻` frames over `★`, as a consumer.
///
/// # Specification
/// trivial.
fn frames(n: Value) -> ConsPat
{
    (0_usize .. n.0).fold(ConsPat::top(), |inner, _| ConsPat::frame("Succ", inner))
}

/// `n` successors of `Zero`, as a toy term.
///
/// # Specification
/// trivial.
fn toy_numeral(n: Value) -> Toy
{
    (0_usize .. n.0).fold(Toy::zero(), |inner, _| Toy::succ(inner))
}

impl Corpus for SequentAlphabet
{
    /// Producer holes bound to numerals, consumer holes to `Succ⁻` frames.
    ///
    /// # Specification
    /// trivial.
    fn numerals(holes: &[(Self::Var, Value)]) -> Self::Subst
    {
        let mut subst = Subst::new();
        for &(ref var, value) in holes {
            match var.cat() {
                | Cat::Producer => subst
                    .bind_prod(var.clone(), numeral(value))
                    .expect("each hole binds once"),
                | Cat::Consumer => subst
                    .bind_cons(var.clone(), frames(value))
                    .expect("each hole binds once"),
            }
        }
        subst
    }

    /// The producer replaced by `Bad`, a constructor no cell reads.
    ///
    /// # Specification
    /// trivial.
    fn discriminated(peak: &Self::Cmd) -> Self::Cmd
    {
        CmdPat::cut(
            peak.polarity(),
            ProdPat::ctor("Bad", []),
            peak.consumer().clone(),
        )
    }
}

impl Corpus for ToyAlphabet
{
    /// Every hole bound to a numeral, through the toy matcher.
    ///
    /// # Specification
    /// trivial.
    fn numerals(holes: &[(Self::Var, Value)]) -> Self::Subst
    {
        let mut subst = ToySubst::default();
        for &(ref var, value) in holes {
            assert!(
                bool::from(Self::match_cmd(
                    &Toy::var(var.clone()),
                    &toy_numeral(value),
                    &mut subst
                )),
                "a hole matches any numeral"
            );
        }
        subst
    }

    /// The root's first child replaced by `Zero`, which neither (add-S) nor a
    /// `Succ` rule fires on; a peak with no child is kept.
    ///
    /// # Specification
    /// trivial.
    fn discriminated(peak: &Self::Cmd) -> Self::Cmd
    {
        Self::splice_cmd_at(
            peak,
            &Self::position_at_path(&[PositionStep::from(0_usize)]),
            Toy::zero(),
        )
        .unwrap_or_else(|_| peak.clone())
    }
}

/// A positive surface rule `lhs ~> rhs`.
///
/// # Specification
/// trivial.
fn rule(
    lhs: CmdPat,
    rhs: CmdPat,
) -> Cell
{
    Cell::new(
        lhs,
        rhs,
        Orientation::PolarityDerived,
        CellProvenance::SurfaceRule,
    )
}

/// The cut `⟨prod | add(n; α)⟩`.
///
/// # Specification
/// trivial.
fn added(prod: ProdPat) -> CmdPat
{
    CmdPat::cut(
        Polarity::Positive,
        prod,
        ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
    )
}

/// The Peano store: the `Succ⁻` frame cell, (add-Z)
/// `⟨Zero | add(n; α)⟩ ~> ⟨n | α⟩` and (add-S)
/// `⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩`.
///
/// # Specification
/// trivial.
fn peano_store() -> CellStore
{
    let mut store = CellStore::new();
    store.insert(frame_defining_cell(&Sym::new("Succ")));
    store.insert(rule(
        added(ProdPat::ctor("Zero", [])),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("n"),
            ConsPat::meta("alpha"),
        ),
    ));
    store.insert(rule(
        added(ProdPat::ctor("Succ", [ProdPat::meta("m")])),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::op(
                "add",
                [ProdPat::meta("n")],
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
        ),
    ));
    store
}

/// Two rules over `⟨Zero | f(α)⟩` with divergent right-hand sides, r1
/// `⟨Zero | f(α)⟩ ~> ⟨Zero | α⟩` and r2 `⟨x | f(α)⟩ ~> ⟨x | g(α)⟩`, whose
/// completion certifies one critical pair.
///
/// # Specification
/// trivial.
fn overlapping_rules() -> CellStore
{
    let mut store = CellStore::new();
    store.insert(rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::op("f", [], ConsPat::meta("alpha")),
        ),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::meta("alpha"),
        ),
    ));
    store.insert(rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("x"),
            ConsPat::op("f", [], ConsPat::meta("alpha")),
        ),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("x"),
            ConsPat::op("g", [], ConsPat::meta("alpha")),
        ),
    ));
    store
}

/// Every fused certificate the compositions of `store` derive, with the store
/// holding every fused cell.
///
/// # Specification
/// trivial.
fn fused<A>(
    name: Name,
    mut store: CellStore<A>,
) -> Source<A>
where
    A: CellAlphabet,
{
    let compositions: Vec<_> = enumerate_overlaps(&store)
        .into_iter()
        .filter(|overlap| overlap.kind == OverlapKind::Composition)
        .collect();
    let bases = compositions
        .iter()
        .filter_map(|overlap| {
            derive_fused(overlap, &mut store)
                .ok()
                .map(|(_fused, base)| base)
        })
        .collect();
    Source { name, store, bases }
}

/// Every certificate completing `store` emits, with the completed store.
///
/// # Specification
/// trivial.
fn completed<A>(
    name: Name,
    store: CellStore<A>,
) -> Source<A>
where
    A: CellAlphabet,
{
    let outcome = complete(
        store,
        CompletionBudget::new(
            CompletionStepBudget::from(64_usize),
            CompletionCellBudget::from(16_usize),
            NormalizationBudget::from(64_usize),
        ),
    );
    Source {
        name,
        store: outcome.store().clone(),
        bases: outcome.certificates().to_vec(),
    }
}

/// The sequent corpus: the Peano store's fused certificates and completion
/// certificates, and the overlapping rules' completion certificates; sources
/// without a certificate are dropped.
///
/// # Specification
/// trivial.
fn sequent_sources() -> Vec<Source<SequentAlphabet>>
{
    [
        fused(Name("fused Peano"), peano_store()),
        completed(Name("completed Peano"), peano_store()),
        completed(Name("completed overlapping rules"), overlapping_rules()),
    ]
    .into_iter()
    .filter(|source| !source.bases.is_empty())
    .collect()
}

/// The toy corpus: the toy addition store's fused certificates and completion
/// certificates, and the two `Succ` rules' completion certificates; sources
/// without a certificate are dropped.
///
/// # Specification
/// trivial.
fn toy_sources() -> Vec<Source<ToyAlphabet>>
{
    let mut addition = CellStore::new();
    addition.insert(add_z());
    addition.insert(add_s());
    let (succ_rules, _f, _g) = cong2_store();
    [
        fused(Name("fused addition"), addition.clone()),
        completed(Name("completed addition"), addition),
        completed(Name("completed Succ rules"), succ_rules),
    ]
    .into_iter()
    .filter(|source| !source.bases.is_empty())
    .collect()
}

/// The Peano store with every fused cell, and the lead base: (add-S) fused
/// into (add-Z), whose first step reads the peak's producer.
///
/// # Specification
/// - panics: when the store derives no lead base, which is a fixture defect.
fn lead_base() -> (CellStore, Tracelet)
{
    let Source { store, bases, .. } = fused(Name("fused Peano"), peano_store());
    let lead = bases
        .into_iter()
        .find(|base| *base.overlap.peak.producer() == numeral(Value(1_usize)))
        .expect("(add-S) composes into (add-Z) at the peak `⟨Succ(Zero) | add(n; α)⟩`");
    (store, lead)
}

/// The distinct metavariables of `cmd`, in order of first occurrence.
///
/// # Specification
/// trivial.
fn holes<A>(cmd: &A::Cmd) -> Vec<A::Var>
where
    A: CellAlphabet,
{
    let mut distinct: Vec<A::Var> = Vec::new();
    for var in A::metavariables(cmd) {
        if !distinct.contains(&var) {
            distinct.push(var);
        }
    }
    distinct
}

/// The value member `member` fills hole `hole` with under `regime`.
///
/// # Specification
/// trivial.
fn value(
    regime: Regime,
    member: Ordinal,
    hole: Ordinal,
) -> Value
{
    Value(match regime {
        | Regime::TwoArms => member
            .0
            .checked_shr(u32::try_from(hole.0).expect("few holes"))
            .unwrap_or_default()
            .checked_rem(2_usize)
            .unwrap_or_default(),
        | Regime::OneVarying if hole.0 == 0 => member.0,
        | Regime::OneVarying => 0_usize,
        | Regime::AllDistinct => member.0,
    })
}

/// The family of `members` instances of `base` under `regime`, its last
/// member made adversarial as `adversary` says.
///
/// # Specification
/// trivial.
fn family<A>(
    base: &Tracelet<A>,
    members: Members,
    regime: Regime,
    adversary: Adversary,
) -> Vec<Tracelet<A>>
where
    A: Corpus,
{
    let base_holes = holes::<A>(&base.overlap.peak);
    let last = members.0.saturating_sub(1);
    (0_usize .. members.0)
        .map(|index| {
            let values: Vec<(A::Var, Value)> = base_holes
                .iter()
                .enumerate()
                .map(|(hole, var)| (var.clone(), value(regime, Ordinal(index), Ordinal(hole))))
                .collect();
            let sigma = A::numerals(&values);
            let mut member = base.clone();
            member.overlap.peak = A::apply_subst(&sigma, &base.overlap.peak);
            member.joins_at = A::apply_subst(&sigma, &base.joins_at);
            if index == last {
                match adversary {
                    | Adversary::Honest => {},
                    | Adversary::Diverged => {
                        member.path_a.pop();
                    },
                    | Adversary::Discriminated => {
                        member.overlap.peak = A::discriminated(&member.overlap.peak);
                    },
                }
            }
            member
        })
        .collect()
}

/// The plain size of `family`, summed member by member: each peak's and
/// join's node counts and one node per recorded step.
///
/// # Specification
/// trivial.
fn plain_size<A>(family: &[Tracelet<A>]) -> NodeCount
where
    A: CellAlphabet,
{
    NodeCount::from(family.iter().fold(0_usize, |total, member| {
        total
            .saturating_add(usize::from(A::cmd_size(&member.overlap.peak)))
            .saturating_add(usize::from(A::cmd_size(&member.joins_at)))
            .saturating_add(member.path_a.len())
            .saturating_add(member.path_b.len())
    }))
}

/// The size of `template`, summed from its parts: the carrier's peak, join
/// and steps, and every arm's node count plus one guard per arm.
///
/// # Specification
/// trivial.
fn template_size<A>(template: &GuardedTemplate<A>) -> NodeCount
where
    A: CellAlphabet,
{
    let carrier = usize::from(plain_size(core::slice::from_ref(template.carrier())));
    NodeCount::from(
        template
            .entries()
            .iter()
            .flat_map(|entry| entry.arms.values())
            .fold(carrier, |total, arm| {
                total
                    .saturating_add(usize::from(arm.size))
                    .saturating_add(1)
            }),
    )
}

/// The recorded steps replaying every member of `family` on its own fires.
///
/// # Specification
/// trivial.
fn plain_steps<A>(family: &[Tracelet<A>]) -> NodeCount
where
    A: CellAlphabet,
{
    NodeCount::from(family.iter().fold(0_usize, |total, member| {
        total
            .saturating_add(member.path_a.len())
            .saturating_add(member.path_b.len())
    }))
}

/// The template of `family`, produced through a cache that records every
/// refused triple as inherited and retries until the producer stops refusing
/// on inheritance: the producer under the most lying cache the family admits.
///
/// # Specification
/// trivial.
fn produced_under_lies<A>(
    family: &[Tracelet<A>],
    store: &CellStore<A>,
) -> Result<GuardedTemplate<A>, TemplateRefusal>
where
    A: CellAlphabet,
{
    let mut cache = InheritanceCache::new();
    loop {
        match anti_unify_tracelets(family, store, &mut cache) {
            | Err(TemplateRefusal::NotInherited { key, .. }) => {
                cache.record(key, InheritanceVerdict::Inherited);
            },
            | produced => return produced,
        }
    }
}

/// The emission clause over one family: a template is emitted only when its
/// size, summed from its parts, stands below the family's plain size, summed
/// member by member, divided by it.
///
/// # Specification
/// - panics: when the clause fails.
fn emitted_below_its_expansion_factor<A>(
    family: &[Tracelet<A>],
    store: &CellStore<A>,
) where
    A: CellAlphabet,
{
    let mut cache = InheritanceCache::new();
    if let Ok(template) = anti_unify_tracelets(family, store, &mut cache) {
        let (s, f) = (template_size(&template), plain_size(family));
        assert_eq!(
            (s, f),
            (template.size(), template.plain_size()),
            "the template reports the sizes its parts and its family sum to"
        );
        let (s, f) = (usize::from(s), usize::from(f));
        assert!(
            f.checked_div(s).is_some_and(|factor| s < factor),
            "a template is emitted only below its expansion factor: s = {s}, F = {f}"
        );
    }
}

/// The admission clause over one family: under the most lying cache, every
/// member rebuilt from the template is its own boundary and admits exactly as
/// its plain replay decides.
///
/// # Specification
/// - panics: when the clause fails.
fn members_admit_as_their_plain_replay<A>(
    family: &[Tracelet<A>],
    store: &CellStore<A>,
) where
    A: CellAlphabet,
{
    let Ok(template) = produced_under_lies(family, store)
    else {
        return;
    };
    for member in family {
        let rebuilt = template
            .peak_substitution(&member.overlap.peak)
            .and_then(|substitution| template.instantiate(&substitution))
            .expect("a member rebuilds from the template");
        assert_eq!(
            (&member.overlap.peak, &member.joins_at),
            (&rebuilt.overlap.peak, &rebuilt.joins_at),
            "a rebuilt member is its own boundary"
        );
        assert_eq!(
            Ok(member.replay(store)),
            template.admit(&member.overlap.peak, store),
            "a member admits exactly as its plain replay decides"
        );
    }
}

/// A generated family's shape: which source, which base, how many members,
/// which regime, which adversary.
///
/// # Specification
/// trivial.
fn shape() -> impl Strategy<
    Value = (
        prop::sample::Index,
        prop::sample::Index,
        Members,
        Regime,
        Adversary,
    ),
>
{
    (
        any::<prop::sample::Index>(),
        any::<prop::sample::Index>(),
        prop::sample::select(SIZES.to_vec()),
        prop::sample::select(REGIMES.to_vec()),
        prop::sample::select(vec![
            Adversary::Honest,
            Adversary::Diverged,
            Adversary::Discriminated,
        ]),
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn a_template_is_emitted_only_below_its_expansion_factor(
        (source, base, members, regime, adversary) in shape(),
    ) {
        let sources = sequent_sources();
        let chosen = source.get(&sources);
        let generated = family(base.get(&chosen.bases), members, regime, adversary);
        emitted_below_its_expansion_factor(&generated, &chosen.store);
        let sources = toy_sources();
        let chosen = source.get(&sources);
        let generated = family(base.get(&chosen.bases), members, regime, adversary);
        emitted_below_its_expansion_factor(&generated, &chosen.store);
    }

    #[test]
    fn every_member_admits_as_its_plain_replay(
        (source, base, members, regime, adversary) in shape(),
    ) {
        let sources = sequent_sources();
        let chosen = source.get(&sources);
        let generated = family(base.get(&chosen.bases), members, regime, adversary);
        members_admit_as_their_plain_replay(&generated, &chosen.store);
        let sources = toy_sources();
        let chosen = source.get(&sources);
        let generated = family(base.get(&chosen.bases), members, regime, adversary);
        members_admit_as_their_plain_replay(&generated, &chosen.store);
    }
}

#[test]
fn a_skeleton_divergent_family_yields_no_template()
{
    let (store, lead) = lead_base();
    let honest = family(&lead, Members(64), Regime::TwoArms, Adversary::Honest);
    assert!(
        anti_unify_tracelets(&honest, &store, &mut InheritanceCache::new()).is_ok(),
        "the near miss, every path shared, yields a template"
    );
    let divergent = family(&lead, Members(64), Regime::TwoArms, Adversary::Diverged);
    assert_eq!(
        Some(TemplateRefusal::SkeletonDivergence {
            member: MemberIndex::from(63_usize)
        }),
        anti_unify_tracelets(&divergent, &store, &mut InheritanceCache::new()).err(),
        "the member whose path diverges in one step is named"
    );
}

#[test]
fn an_entry_a_cell_discriminates_on_yields_no_template()
{
    let (store, lead) = lead_base();
    let honest = family(&lead, Members(64), Regime::TwoArms, Adversary::Honest);
    assert!(
        anti_unify_tracelets(&honest, &store, &mut InheritanceCache::new()).is_ok(),
        "the near miss, every member honest, yields a template"
    );
    let adversarial = family(
        &lead,
        Members(64),
        Regime::TwoArms,
        Adversary::Discriminated,
    );
    assert!(
        !bool::from(adversarial[63].replay(&store)),
        "the discriminated member does not replay on its own"
    );
    let refusal = anti_unify_tracelets(&adversarial, &store, &mut InheritanceCache::new()).err();
    assert!(
        matches!(
            refusal,
            Some(TemplateRefusal::NotInherited {
                key,
                verdict: InheritanceVerdict::Stuck {
                    leg: TemplateLeg::PathA,
                    step,
                    reason: StuckStep::DoesNotFire(_),
                },
            }) if key.entry == EntryIndex::from(0_usize) && step == LegStepIndex::from(0_usize)
        ),
        "the arm the first cell does not fire on is refused at the producer entry: {refusal:?}"
    );
}

#[test]
fn a_family_with_no_shared_content_yields_no_template()
{
    let (store, lead) = lead_base();
    let shared = family(&lead, Members(64), Regime::TwoArms, Adversary::Honest);
    assert!(
        anti_unify_tracelets(&shared, &store, &mut InheritanceCache::new()).is_ok(),
        "the near miss, two arms per entry, yields a template"
    );
    let distinct = family(&lead, Members(64), Regime::AllDistinct, Adversary::Honest);
    let mut cache = InheritanceCache::new();
    let refusal = anti_unify_tracelets(&distinct, &store, &mut cache).err();
    assert!(
        matches!(refusal, Some(TemplateRefusal::DoesNotPay { .. })),
        "a family whose every arm is its own does not pay: {refusal:?}"
    );
    assert_eq!(
        0_usize,
        usize::from(cache.checked()),
        "and a family that does not pay costs no inheritance check"
    );
}

#[test]
fn the_inheritance_check_runs_once_per_distinct_triple()
{
    let (store, lead) = lead_base();
    for members in [Members(64), Members(256)] {
        let family = family(&lead, members, Regime::TwoArms, Adversary::Honest);
        let mut cache = InheritanceCache::new();
        let template =
            anti_unify_tracelets(&family, &store, &mut cache).expect("two arms per entry pay");
        let entries = template.entries().len();
        assert!(
            entries >= 2_usize,
            "the base has a producer and a consumer hole"
        );
        assert!(
            template
                .entries()
                .iter()
                .all(|entry| entry.arms.len() == 2_usize),
            "every entry holds two arms"
        );
        let distinct = entries.saturating_mul(2_usize);
        let lookups = entries.saturating_mul(members.0);
        assert_eq!(
            (distinct, distinct, lookups.saturating_sub(distinct)),
            (
                usize::from(cache.distinct_triples()),
                usize::from(cache.checked()),
                usize::from(cache.hits())
            ),
            "{members:?} check each distinct triple once and read the rest from the cache"
        );
        let report = template.cost_report(&family, &store);
        assert_eq!(
            (members.0, distinct, lookups.saturating_sub(distinct)),
            (
                usize::from(report.admissions),
                usize::from(report.triples_checked),
                usize::from(report.cache_hits)
            ),
            "the report admits every member and carries the cache's two counts"
        );
        assert!(
            usize::from(report.replayed_steps) < usize::from(report.plain_replayed_steps),
            "the checks replay fewer steps than replaying every member"
        );
    }
}

#[test]
fn a_poisoned_inheritance_entry_is_caught_at_admission()
{
    let (store, lead) = lead_base();
    let adversarial = family(
        &lead,
        Members(64),
        Regime::TwoArms,
        Adversary::Discriminated,
    );
    let Some(TemplateRefusal::NotInherited { key, .. }) =
        anti_unify_tracelets(&adversarial, &store, &mut InheritanceCache::new()).err()
    else {
        panic!("an honest cache refuses the discriminated arm");
    };
    // The discriminated arm stands at a position the first cell reads, so with
    // that entry generic no other entry's check fires either: the lie that
    // lets the template through covers every triple the honest check refuses,
    // the discriminated arm's first.
    let mut poisoned = InheritanceCache::new();
    let mut lies = Vec::new();
    let template = loop {
        match anti_unify_tracelets(&adversarial, &store, &mut poisoned) {
            | Err(TemplateRefusal::NotInherited { key: lie, .. }) => {
                poisoned.record(lie, InheritanceVerdict::Inherited);
                lies.push(lie);
            },
            | produced => break produced.expect("the lies let the template through"),
        }
    };
    assert_eq!(
        Some(&key),
        lies.first(),
        "the first lie covers the discriminated arm"
    );
    assert!(
        usize::from(template.production().cache_hits) >= lies.len(),
        "every lie was read from the cache rather than checked"
    );
    let (bad, honest) = adversarial.split_last().expect("a family");
    assert_eq!(
        (Ok(bad.replay(&store)), false),
        (
            template.admit(&bad.overlap.peak, &store),
            bool::from(bad.replay(&store))
        ),
        "the member the lie covers admits as its plain replay, which refuses it"
    );
    assert!(
        honest.iter().all(|member| template
            .admit(&member.overlap.peak, &store)
            .is_ok_and(bool::from)),
        "while every honest member admits"
    );
}

#[test]
fn a_template_has_one_flow_for_its_family()
{
    let (store, lead) = lead_base();
    let family = family(&lead, Members(64), Regime::TwoArms, Adversary::Honest);
    let template = anti_unify_tracelets(&family, &store, &mut InheritanceCache::new())
        .expect("two arms per entry pay");
    let identity = template.flow(&store).expect("the carrier projects");
    for member in &family {
        let own = tracelet_flow(member, &store).expect("a member projects");
        assert!(
            bool::from(flows_equal(&identity.path_a, &own.path_a))
                && bool::from(flows_equal(&identity.path_b, &own.path_b)),
            "every member has the template's flow on both legs"
        );
    }
}

#[test]
fn a_certificate_outside_the_template_is_refused_by_name()
{
    let (store, lead) = lead_base();
    let template = anti_unify_tracelets(
        &family(&lead, Members(64), Regime::TwoArms, Adversary::Honest),
        &store,
        &mut InheritanceCache::new(),
    )
    .expect("two arms per entry pay");
    let Source { bases, .. } = fused(Name("fused Peano"), peano_store());
    let other = bases
        .iter()
        .find(|base| template.peak_substitution(&base.overlap.peak).is_err())
        .expect("a base of another shape");
    assert_eq!(
        Err(TemplateObstruction::PeakNotAnInstance),
        template.admit(&other.overlap.peak, &store),
        "a peak of another shape"
    );
    let outside = family(&lead, Members(3), Regime::OneVarying, Adversary::Honest)
        .pop()
        .expect("a member whose first hole holds two");
    assert_eq!(
        Err(TemplateObstruction::ArmOutsideTemplate {
            entry: EntryIndex::from(0_usize)
        }),
        template.admit(&outside.overlap.peak, &store),
        "a body no member held"
    );
    assert_eq!(
        Err(TemplateObstruction::UnboundEntry {
            entry: EntryIndex::from(0_usize)
        }),
        template.instantiate(&Subst::new()),
        "an entry left unbound"
    );
}

/// One row of the verdict table: the family's class and what the producer
/// made of it.
///
/// # Specification
/// trivial.
fn row<A>(
    label: &Label,
    family: &[Tracelet<A>],
    store: &CellStore<A>,
) -> String
where
    A: CellAlphabet,
{
    let Label {
        alphabet: Name(alphabet),
        ref class,
    } = *label;
    let mut cache = InheritanceCache::new();
    let (members, plain, steps) = (
        family.len(),
        usize::from(plain_size(family)),
        usize::from(plain_steps(family)),
    );
    match anti_unify_tracelets(family, store, &mut cache) {
        | Ok(template) => {
            let report = template.cost_report(family, store);
            let flows = template.flow(store).map_or(0_usize, |identity| {
                family
                    .iter()
                    .filter(|member| {
                        tracelet_flow(member, store).is_ok_and(|own| {
                            bool::from(flows_equal(&identity.path_a, &own.path_a))
                                && bool::from(flows_equal(&identity.path_b, &own.path_b))
                        })
                    })
                    .count()
            });
            format!(
                "| {alphabet} | {class} | {members} | template | {} | {} | {} | {} | {} | {} | {} | {} / {} | {flows} |",
                template.entries().len(),
                usize::from(report.plain_size),
                usize::from(report.template_size),
                usize::from(report.expansion_factor),
                usize::from(report.triples_checked),
                usize::from(report.cache_hits),
                usize::from(report.admissions),
                usize::from(report.replayed_steps),
                usize::from(report.plain_replayed_steps),
            )
        },
        | Err(TemplateRefusal::DoesNotPay { template_size, .. }) => {
            let s = usize::from(template_size);
            format!(
                "| {alphabet} | {class} | {members} | does not pay | — | {plain} | {s} | {} | 0 | 0 | 0 | 0 / {steps} | — |",
                plain.checked_div(s).unwrap_or_default(),
            )
        },
        | Err(TemplateRefusal::NotInherited { key, verdict }) => format!(
            "| {alphabet} | {class} | {members} | not inherited at entry {}: {verdict:?} | — | {plain} | — | — | {} | {} | 0 | — | — |",
            usize::from(key.entry),
            usize::from(cache.checked()),
            usize::from(cache.hits()),
        ),
        | Err(refusal) => format!(
            "| {alphabet} | {class} | {members} | {refusal:?} | — | {plain} | — | — | {} | {} | 0 | — | — |",
            usize::from(cache.checked()),
            usize::from(cache.hits()),
        ),
    }
}

/// The verdict table's rows for every base of every source of one alphabet,
/// in every regime and at every size.
///
/// # Specification
/// trivial.
fn generated_rows<A>(
    alphabet: Name,
    sources: &[Source<A>],
) where
    A: Corpus,
{
    for source in sources {
        for (index, base) in source.bases.iter().enumerate() {
            for regime in REGIMES {
                for members in SIZES {
                    let label = Label {
                        alphabet,
                        class: format!("{} {index} {regime:?}", source.name.0),
                    };
                    println!(
                        "{}",
                        row(
                            &label,
                            &family(base, members, regime, Adversary::Honest),
                            &source.store
                        )
                    );
                }
            }
        }
    }
}

/// The verdict table: one row per generated class — source, base, regime and
/// size — and per adversarial class, over both alphabets, then the bases.
#[test]
#[ignore = "prints the spike's verdict table; run with --ignored --nocapture"]
fn verdict_table()
{
    println!(
        "| alphabet | class | members | outcome | entries | F | s | f | triples checked | cache hits | admissions | replayed / plain-replay steps | members with the template's flow |"
    );
    println!("|---|---|---|---|---|---|---|---|---|---|---|---|---|");
    let (sequent, toy) = (sequent_sources(), toy_sources());
    generated_rows(Name("sequent"), &sequent);
    generated_rows(Name("toy"), &toy);
    let (store, lead) = lead_base();
    for (class, regime, adversary) in [
        (
            "adversarial: a path diverges in one step",
            Regime::TwoArms,
            Adversary::Diverged,
        ),
        (
            "adversarial: an entry a cell discriminates on",
            Regime::TwoArms,
            Adversary::Discriminated,
        ),
        (
            "adversarial: every member distinct at every entry",
            Regime::AllDistinct,
            Adversary::Honest,
        ),
    ] {
        let label = Label {
            alphabet: Name("sequent"),
            class: class.to_owned(),
        };
        println!(
            "{}",
            row(
                &label,
                &family(&lead, Members(64), regime, adversary),
                &store
            )
        );
    }
    for source in &sequent {
        for (index, base) in source.bases.iter().enumerate() {
            println!(
                "sequent {} {index}: peak {:?}",
                source.name.0, base.overlap.peak
            );
        }
    }
    for source in &toy {
        for (index, base) in source.bases.iter().enumerate() {
            println!(
                "toy {} {index}: peak {:?}",
                source.name.0, base.overlap.peak
            );
        }
    }
}
