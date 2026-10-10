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

use anodized::spec;
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
use quenchant_shape::shape::Maybe;

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
///
/// # Specification
/// - ensures: implementations accept consistent numeral assignments and
///   introduce no fresh metavariables when discriminating a peak.
/// - executable: none — trait instrumentation emits lowercase qualifier
///   constants rejected by `non_upper_case_globals`; concrete implementations
///   enforce the method obligations without the trait-level macro.
///
/// # Adequacy
/// - hypothesis: L3 — both local alphabet implementations participate in
///   generated family admission. Concrete predicates inspect typed images and
///   replacement fields; replay witnesses distinguish a conflicting assignment
///   or ineffective adversary.
/// - witness: `tests::template::corpus_boundaries_preserve_typed_assignments`
trait Corpus: CellAlphabet
{
    /// The substitution sending every listed hole to the numeral of its
    /// value.
    ///
    /// # Specification
    /// - requires: repeated variables have the same assigned value.
    /// - ensures: every listed variable denotes the corresponding numeral or
    ///   return-side frame stack in the resulting substitution.
    /// - panics: conflicting repeated assignments are fixture defects.
    /// - executable: none — instrumenting this abstract declaration requires
    ///   the trait macro rejected by the qualifier-constant lint on `Corpus`.
    ///   Both concrete implementations enforce consistent typed assignments.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — finite, consistent assignments, including empty and
    ///   repeated bindings. The shared precondition rules out conflicting
    ///   images; implementation predicates inspect typed bindings, and
    ///   generated admission observes the substitutions in replay.
    /// - witness: `tests::template::corpus_boundaries_preserve_typed_assignments`
    fn numerals(holes: &[(Self::Var, Value)]) -> Self::Subst;

    /// `peak` with the body the base's first recorded cell reads replaced by
    /// one it does not fire on.
    ///
    /// # Specification
    /// - ensures: the alphabet-specific discriminating replacement introduces
    ///   no fresh metavariables. Whether it prevents firing depends on the base
    ///   cell and is checked by the adversarial replay witness.
    /// - panics: none.
    /// - executable: none — instrumenting this abstract declaration requires
    ///   the trait macro rejected by the qualifier-constant lint on `Corpus`.
    ///   Both concrete implementations check their exact replacement fields.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — arbitrary peaks of either local alphabet. The
    ///   metavariable subset excludes an invented hole; concrete replacement
    ///   fields and the failing-versus-honest replay pair distinguish an
    ///   ineffective adversary.
    /// - witness: `tests::template::an_entry_a_cell_discriminates_on_yields_no_template`
    fn discriminated(peak: &Self::Cmd) -> Self::Cmd;
}

/// `n` successors of `Zero`, as a producer.
///
/// # Specification
/// - ensures: exactly `n` unary Succ constructors followed by one Zero leaf.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — representable numeral sizes. The borrowed preorder checks
///   every constructor, arity and node count, detecting a wrong leaf, branching
///   or an off-by-one successor. Zero and two are concrete boundary witnesses.
/// - witness: `tests::template::corpus_boundaries_preserve_typed_assignments`
#[spec(ensures: |output| usize::from(output.size()) == n.0.saturating_add(1)
    && output.to_ref().preorder().enumerate().all(|(index, entry)| match *entry.head() {
        gandr_theory_cell_complexes::ProdHead::Ctor(ref ctor, arity) =>
            ctor.as_ref() == if index < n.0 { "Succ" } else { "Zero" }
                && usize::from(arity) == usize::from(index < n.0),
        gandr_theory_cell_complexes::ProdHead::Meta(_) => false,
    }))]
fn numeral(n: Value) -> ProdPat
{
    (0_usize .. n.0).fold(ProdPat::ctor("Zero", []), |inner, _| {
        ProdPat::ctor("Succ", [inner])
    })
}

/// `n` return-side `Succ⁻` frames over `★`, as a consumer.
///
/// # Specification
/// - ensures: exactly `n` Succ return frames ending in the top consumer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — representable frame stacks. Borrowed frames and their end
///   distinguish a wrong frame symbol, a metavariable tail and an off-by-one
///   depth. Typed consumer substitution checks the same stacks in a family.
/// - witness: `tests::template::corpus_boundaries_preserve_typed_assignments`
#[spec(ensures: |output| output.to_ref().frames().len() == n.0
    && output.to_ref().frames().iter().all(|frame|
        matches!(*frame, gandr_theory_cell_complexes::SpineFrame::Frame(ref ctor) if ctor.as_ref() == "Succ"))
    && matches!(*output.to_ref().end(), gandr_theory_cell_complexes::SpineEnd::Top))]
fn frames(n: Value) -> ConsPat
{
    (0_usize .. n.0).fold(ConsPat::top(), |inner, _| ConsPat::frame("Succ", inner))
}

/// `n` successors of `Zero`, as a toy term.
///
/// # Specification
/// - ensures: a ground successor numeral with `n + 1` command nodes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — representable toy numerals. Node count and absence of
///   metavariables detect wrong depth or an open image; the concrete zero and
///   two numerals distinguish constructors, and generic family admission
///   observes the images under rewriting.
/// - witness: `tests::template::corpus_boundaries_preserve_typed_assignments`
#[spec(ensures: |output| usize::from(ToyAlphabet::cmd_size(&output)) == n.0.saturating_add(1) && ToyAlphabet::metavariables(&output).is_empty())]
fn toy_numeral(n: Value) -> Toy
{
    (0_usize .. n.0).fold(Toy::zero(), |inner, _| Toy::succ(inner))
}

impl Corpus for SequentAlphabet
{
    /// Producer holes bound to numerals, consumer holes to `Succ⁻` frames.
    ///
    /// # Specification
    /// - requires: repeated variables have the same assigned value.
    /// - ensures: every producer binding is its numeral and every consumer
    ///   binding is its frame stack, with no additional bindings.
    /// - panics: a conflicting repeated assignment is a fixture defect.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — consistent typed assignments, including empty and
    ///   repeated variables. Direct binding lookup, category-specific images
    ///   and the distinct-variable count exclude missing, extra or
    ///   swapped-category entries.
    /// - witness: `tests::template::corpus_boundaries_preserve_typed_assignments`
    #[spec(requires: holes.iter().enumerate().all(|(index, binding)| holes[..index].iter().all(|held| held.0 != binding.0 || held.1 == binding.1)), ensures: |output|
        usize::from(output.len()) == holes.iter().enumerate().filter(|entry|
            !holes[..entry.0].iter().any(|held| held.0 == entry.1.0)).count()
        && holes.iter().all(|binding| match binding.0.cat() {
            Cat::Producer => output.get_prod(&binding.0) == Maybe::Present(&numeral(binding.1)),
            Cat::Consumer => output.get_cons(&binding.0) == Maybe::Present(&frames(binding.1)),
        }))]
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
    /// - ensures: the producer is Bad, with polarity and consumer unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — sequent peaks. Exact replacement fields distinguish
    ///   changing the consumer or polarity instead of the producer; honest and
    ///   discriminated family replays establish that this fixed base reads the
    ///   replaced field.
    /// - witness: `tests::template::an_entry_a_cell_discriminates_on_yields_no_template`
    #[spec(ensures: |output| output.polarity() == peak.polarity() && output.consumer() == peak.consumer() && *output.producer() == ProdPat::ctor("Bad", []))]
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
    /// - requires: repeated variables have the same assigned value.
    /// - ensures: applying the substitution to any listed hole produces its
    ///   ground numeral.
    /// - panics: a conflicting repeated assignment is a fixture defect.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — consistent toy assignments. Applying each bound
    ///   variable checks its image rather than the matcher return flag; empty
    ///   and repeated inputs distinguish accidental rejection or lost bindings.
    ///   Generated family admission observes larger images.
    /// - witness: `tests::template::corpus_boundaries_preserve_typed_assignments`
    #[spec(requires: holes.iter().enumerate().all(|(index, binding)| holes[..index].iter().all(|held| held.0 != binding.0 || held.1 == binding.1)), ensures: |output| holes.iter().all(|binding|
        Self::apply_subst(&output, &Toy::var(binding.0.clone())) == toy_numeral(binding.1)))]
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
    /// - ensures: the first child is replaced by Zero if it exists; otherwise
    ///   the peak is preserved. No new metavariable is introduced.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a leaf and a two-child peak. Exact splicing or
    ///   unchanged fallback detects changing a sibling or refusing a valid
    ///   child; generated adversarial admission observes the resulting firing
    ///   refusal where the base reads that child.
    /// - witness: `tests::template::corpus_boundaries_preserve_typed_assignments`
    #[spec(ensures: |output| output == Self::splice_cmd_at(peak, &Self::position_at_path(&[PositionStep::from(0_usize)]), Toy::zero()).unwrap_or_else(|_| peak.clone()))]
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
/// - ensures: every returned base is a composition certificate that replays
///   over the returned store, with the supplied source name preserved.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the fixed sequent and toy stores. Both certificate legs
///   are replayed independently of the overlap enumeration, excluding a missing
///   fused cell or invalid join. Generated admission observes instantiated
///   bases.
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
#[spec(ensures: |output| output.name == name && output.bases.iter().all(|base| base.overlap.kind == OverlapKind::Composition && bool::from(base.replay(&output.store))))]
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
/// - ensures: the bounded completion result retains its source name and every
///   emitted certificate replays over its returned store; exhaustion does not
///   imply completeness.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the two corpus alphabets and their fixed stores.
///   Independent replay checks both legs of every emitted certificate,
///   rejecting a stale store or invalid endpoint without claiming completion
///   succeeded within the budget.
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
#[spec(ensures: |output| output.name == name && output.bases.iter().all(|base| bool::from(base.replay(&output.store))))]
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
/// - ensures: a nonempty sequent corpus containing only sources with
///   certificates, in the fixed candidate order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the fixed three candidate stores. The nonempty-source
///   invariant protects indexed generation and rejects an omitted filter;
///   generated replay and the rendered table exercise the retained
///   certificates.
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
#[spec(ensures: |output| !output.is_empty() && output.iter().all(|source| !source.bases.is_empty()))]
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
/// - ensures: a nonempty toy corpus containing only sources with certificates,
///   in the fixed candidate order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the fixed toy candidate stores. Every retained source
///   must support indexed certificate selection; generated replay and the
///   rendered table exercise the filtered corpus rather than a vacuous sample.
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
#[spec(ensures: |output| !output.is_empty() && output.iter().all(|source| !source.bases.is_empty()))]
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
/// - ensures: a replaying composition certificate whose producer peak is
///   exactly Succ(Zero), in a store holding all its steps.
/// - panics: when the store derives no lead base, which is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L2 — the fixed Peano store. Exact peak shape and both-leg
///   replay exclude a different composition or a stale fused store; all focused
///   adversarial template tests start from this base.
/// - witness: `tests::template::an_entry_a_cell_discriminates_on_yields_no_template`
#[spec(ensures: |output| output.1.overlap.kind == OverlapKind::Composition && *output.1.overlap.peak.producer() == numeral(Value(1)) && bool::from(output.1.replay(&output.0)))]
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
/// - ensures: exactly the distinct metavariables, retaining their
///   first-occurrence order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — commands of either corpus alphabet. An independent
///   first-occurrence filter checks values and order, distinguishing duplicate
///   holes, omissions and reordered assignment slots. A repeated-hole command
///   is observed directly.
/// - witness: `tests::template::family_boundaries_preserve_assignments_and_adversary_positions`
#[spec(ensures: |output| {
    let variables = A::metavariables(cmd);
    output.iter().eq(variables.iter().enumerate().filter_map(|(index, var)|
        (!variables[..index].contains(var)).then_some(var)))
})]
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
/// - requires: in the two-arm regime, the hole index is representable as u32.
/// - ensures: the selected bit, with out-of-word bits zero; alternatively the
///   member index at only the first hole, or at every hole, for the other
///   regimes.
/// - panics: an unrepresentable two-arm hole index is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L1 — all three regimes, including the first hole and a bit
///   beyond the machine word. A bit-mask observer distinguishes the selected
///   bit from parity of the whole member; explicit regime boundaries reject
///   varying the wrong hole.
/// - witness: `tests::template::family_boundaries_preserve_assignments_and_adversary_positions`
#[spec(requires: regime != Regime::TwoArms || u32::try_from(hole.0).is_ok(), ensures: |output| output.0 == match regime {
    Regime::TwoArms => u32::try_from(hole.0).ok().and_then(|shift| 1_usize.checked_shl(shift))
        .map_or(0, |mask| usize::from(member.0 & mask != 0)),
    Regime::OneVarying => if hole.0 == 0 { member.0 } else { 0 },
    Regime::AllDistinct => member.0,
})]
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
/// - ensures: exactly the requested number of instances. Both path skeletons
///   are preserved except that the last first leg loses its final step in the
///   divergent regime; the discriminating regime changes only the last peak.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — empty, singleton and larger families of either alphabet.
///   Path conservation and the exact last-member truncation distinguish an
///   off-by-one adversary, wrong leg or dropped member. The named member-63
///   refusals observe discrimination and divergence separately.
/// - witness: `tests::template::family_boundaries_preserve_assignments_and_adversary_positions`
#[spec(ensures: |output| output.len() == members.0 && output.iter().enumerate().all(|(index, member)| {
    let diverged = adversary == Adversary::Diverged && index.saturating_add(1) == members.0;
    member.path_b == base.path_b && member.path_a.as_slice() == &base.path_a[..base.path_a.len().saturating_sub(usize::from(diverged))]
        && member.overlap.left == base.overlap.left && member.overlap.right == base.overlap.right
        && member.overlap.kind == base.overlap.kind && member.overlap.seam == base.overlap.seam
}))]
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
/// - ensures: the saturating sum of all peak nodes, join nodes and recorded
///   steps in both legs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — empty and populated families. Regrouping boundary-node
///   totals separately from path totals detects a missing leg or boundary
///   contribution; the independent template price audit consumes this count.
/// - witness: `tests::template::family_boundaries_preserve_assignments_and_adversary_positions`
#[spec(ensures: |output| usize::from(output) == family.iter().fold(0_usize, |sum, member|
    sum.saturating_add(usize::from(A::cmd_size(&member.overlap.peak)))
        .saturating_add(usize::from(A::cmd_size(&member.joins_at))))
    .saturating_add(usize::from(plain_steps(family))))]
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
/// - ensures: the carrier node-and-step cost plus the node cost of every
///   distinct arm and one guard per arm, with saturating arithmetic.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — emitted templates of both alphabets. Summing arm costs
///   separately from the carrier detects a lost guard or carrier contribution;
///   the expansion-factor audit compares this structural observer with the
///   production report.
/// - witness: `tests::template::a_template_is_emitted_only_below_its_expansion_factor`
#[spec(ensures: |output| usize::from(output) == usize::from(plain_size(core::slice::from_ref(template.carrier())))
    .saturating_add(template.entries().iter().flat_map(|entry| entry.arms.values())
        .fold(0_usize, |sum, arm| sum.saturating_add(usize::from(arm.size)).saturating_add(1))))]
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
/// - ensures: the total number of recorded applications across both legs of
///   every member, regardless of whether those applications replay.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — empty, singleton and adversarial families. Flattened
///   application counting distinguishes a dropped leg or counting only
///   successful replay steps. The divergent singleton retains two recorded
///   applications even though its replay fails.
/// - witness: `tests::template::family_boundaries_preserve_assignments_and_adversary_positions`
#[spec(ensures: |output| usize::from(output) == family.iter().flat_map(|member| member.path_a.iter().chain(&member.path_b)).count())]
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
/// - ensures: a produced template or a non-inheritance refusal; no
///   `NotInherited` refusal escapes after its key has been poisoned and
///   retried.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — generated honest and adversarial families. The refusal
///   tag distinguishes an early return from the poisoning loop; the
///   poisoned-cache admission witness requires real replay to reject a lying
///   inheritance entry.
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
#[spec(ensures: |output| !matches!(output, Err(TemplateRefusal::NotInherited { .. })))]
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
/// - ensures: every successful emission has its independently summed size and
///   plain cost, and its size is strictly below the integer expansion factor.
/// - panics: when the clause fails.
///
/// # Adequacy
/// - hypothesis: L2 — generated families, including non-paying and adversarial
///   classes. Structural cost observers are independent of cached production
///   counters; the integer quotient separates strict payment from equality at
///   the threshold.
/// - witness: `tests::template::a_template_is_emitted_only_below_its_expansion_factor`
#[spec(ensures: anti_unify_tracelets(family, store, &mut InheritanceCache::new()).map_or_else(|_| true, |template| {
    let size = template_size(&template);
    let plain = plain_size(family);
    size == template.size() && plain == template.plain_size()
        && usize::from(plain).checked_div(usize::from(size)).is_some_and(|factor| usize::from(size) < factor)
}))]
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
/// - ensures: if poisoning produces a template, each member reconstructs its
///   own boundary and admission agrees with independent plain replay.
/// - panics: when the clause fails.
///
/// # Adequacy
/// - hypothesis: L2 — honest, divergent and discriminated generated families
///   over both alphabets. Direct certificate replay and boundary comparison
///   distinguish trusted cache claims from actual admission and catch a
///   reconstructed but wrong join.
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
#[spec(ensures: produced_under_lies(family, store).map_or_else(|_| true, |template| family.iter().all(|member|
    template.peak_substitution(&member.overlap.peak).and_then(|substitution| template.instantiate(&substitution))
        .is_ok_and(|rebuilt| rebuilt.overlap.peak == member.overlap.peak && rebuilt.joins_at == member.joins_at)
        && template.admit(&member.overlap.peak, store) == Ok(member.replay(store)))))]
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
/// - ensures: generated family sizes and regimes come from their fixed corpora,
///   with each of the three adversary modes available.
/// - panics: none.
/// - executable: none — the opaque strategy return causes E0562 in the
///   attribute's evaluation closure under enforcement; a named return type
///   would be required before the attribute can be attached.
///
/// # Adequacy
/// - hypothesis: L3 — 64 sampled cases per property over both alphabets,
///   complemented by deterministic last-member refusals. Concrete near misses
///   prevent an all-refusal generator from hiding admission or payment defects;
///   sampling does not prove the full product space.
/// - witness: `tests::template::a_template_is_emitted_only_below_its_expansion_factor`
/// - witness: `tests::template::every_member_admits_as_its_plain_replay`
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
/// - requires: labels contain no table delimiter or line break.
/// - ensures: one thirteen-column row retaining the alphabet, class, member
///   count and independently summed plain cost, with an outcome and work
///   report.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — table-safe labels and generated certificate families.
///   Parsed label, count and cost columns plus row shape reject a shifted
///   column or a report for another family. The ignored verdict-table witness
///   is run explicitly to observe successful and refused production.
/// - witness: `tests::template::verdict_table`
#[spec(requires: !label.alphabet.0.contains(['|', '\n', '\r']) && !label.class.contains(['|', '\n', '\r']), ensures: |output| {
    let mut columns = output.split('|').map(str::trim);
    columns.next() == Some("") && columns.next() == Some(label.alphabet.0.trim())
        && columns.next() == Some(label.class.trim())
        && columns.next().and_then(|column| column.parse::<usize>().ok()) == Some(family.len())
        && columns.next().is_some_and(|outcome| !outcome.is_empty())
        && columns.next().is_some()
        && columns.next().and_then(|column| column.parse::<usize>().ok()) == Some(usize::from(plain_size(family)))
        && columns.count() == 8 && output.ends_with('|')
})]
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
/// - requires: alphabet and source names contain no table delimiter or line
///   break.
/// - ensures: prints the row for each source/base/regime/size tuple.
/// - panics: output failure follows the standard output writer's behavior.
///
/// # Adequacy
/// - hypothesis: L1 — finite corpus sources with table-safe names. The input
///   predicate prevents labels from changing table structure; the row predicate
///   checks each rendered tuple. The explicit verdict-table run observes the
///   standard-output surface, not an in-memory surrogate.
/// - witness: `tests::template::verdict_table`
#[spec(requires: !alphabet.0.contains(['|', '\n', '\r'])
    && sources.iter().all(|source| !source.name.0.contains(['|', '\n', '\r'])))]
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

#[test]
fn inheritance_refusals_preserve_leg_and_step_boundaries()
{
    let (store, lead) = lead_base();
    let members = family(&lead, Members(64), Regime::TwoArms, Adversary::Honest);
    let mut cache = InheritanceCache::new();
    assert!(matches!(
        anti_unify_tracelets(&members, &CellStore::new(), &mut cache),
        Err(TemplateRefusal::NotInherited {
            verdict: InheritanceVerdict::Stuck {
                leg: TemplateLeg::PathA, step, reason: StuckStep::UnissuedCell,
            }, ..
        }) if usize::from(step) == 0
    ));
    assert_eq!(usize::from(cache.checked()), 1);

    let mut stopped_right = members.clone();
    for member in &mut stopped_right {
        member.path_b = vec![
            lead.path_a
                .last()
                .expect("the composite ends with add-Z")
                .clone(),
        ];
    }
    assert!(matches!(
        anti_unify_tracelets(&stopped_right, &store, &mut InheritanceCache::new()),
        Err(TemplateRefusal::NotInherited {
            verdict: InheritanceVerdict::Stuck {
                leg: TemplateLeg::PathB, step, reason: StuckStep::DoesNotFire(_),
            }, ..
        }) if usize::from(step) == 0
    ));

    let mut wrong_join = members.clone();
    for member in &mut wrong_join {
        member.joins_at = member.overlap.peak.clone();
    }
    assert!(matches!(
        anti_unify_tracelets(&wrong_join, &store, &mut InheritanceCache::new()),
        Err(TemplateRefusal::NotInherited {
            verdict: InheritanceVerdict::MissesTheJoin {
                leg: TemplateLeg::PathA
            },
            ..
        })
    ));

    let mut empty_right = members;
    for member in &mut empty_right {
        member.path_b.clear();
    }
    assert!(matches!(
        anti_unify_tracelets(&empty_right, &store, &mut InheritanceCache::new()),
        Err(TemplateRefusal::NotInherited {
            verdict: InheritanceVerdict::MissesTheJoin {
                leg: TemplateLeg::PathB
            },
            ..
        })
    ));
}

#[test]
fn empty_input_and_report_inputs_do_not_rewrite_production_counts()
{
    let (store, lead) = lead_base();
    let members = family(&lead, Members(64), Regime::TwoArms, Adversary::Honest);
    let mut cache = InheritanceCache::new();
    let template =
        anti_unify_tracelets(&members, &store, &mut cache).expect("the shared family pays");
    let before = cache.clone();
    assert_eq!(
        anti_unify_tracelets::<SequentAlphabet>(&[], &store, &mut cache),
        Err(TemplateRefusal::EmptyFamily)
    );
    assert_eq!(cache, before);

    let outside = family(&lead, Members(3), Regime::OneVarying, Adversary::Honest)
        .pop()
        .expect("an arm outside the two-arm template");
    let empty = template.cost_report(&[], &store);
    let singleton = template.cost_report(core::slice::from_ref(&members[0]), &store);
    let external = template.cost_report(core::slice::from_ref(&outside), &store);
    assert_eq!(usize::from(empty.admissions), 0);
    assert_eq!(usize::from(empty.plain_replayed_steps), 0);
    assert_eq!(usize::from(singleton.admissions), 1);
    assert_eq!(
        usize::from(singleton.plain_replayed_steps),
        members[0].path_a.len() + members[0].path_b.len()
    );
    assert_eq!(usize::from(external.admissions), 0);
    assert_eq!(
        usize::from(external.plain_replayed_steps),
        outside.path_a.len() + outside.path_b.len()
    );
    let production = template.production();
    for report in [empty, singleton, external] {
        assert_eq!(usize::from(report.members), members.len());
        assert_eq!(
            (
                report.triples_checked,
                report.cache_hits,
                report.replayed_steps
            ),
            (
                production.triples_checked,
                production.cache_hits,
                production.replayed_steps
            )
        );
    }
}

#[test]
fn corpus_boundaries_preserve_typed_assignments()
{
    use gandr_theory_cell_complexes::MetaVar;
    assert_eq!(ProdPat::ctor("Zero", []), numeral(Value(0)));
    assert_eq!(ConsPat::top(), frames(Value(0)));
    assert_eq!(Toy::succ(Toy::succ(Toy::zero())), toy_numeral(Value(2)));
    let producer = MetaVar::producer("p");
    let consumer = MetaVar::consumer("k");
    let substitution = SequentAlphabet::numerals(&[
        (producer.clone(), Value(2)),
        (consumer.clone(), Value(1)),
        (producer.clone(), Value(2)),
    ]);
    assert_eq!(
        Maybe::Present(&ProdPat::ctor("Succ", [ProdPat::ctor("Succ", [
            ProdPat::ctor("Zero", [])
        ])])),
        substitution.get_prod(&producer)
    );
    assert_eq!(
        Maybe::Present(&ConsPat::frame("Succ", ConsPat::top())),
        substitution.get_cons(&consumer)
    );
    assert!(bool::from(SequentAlphabet::numerals(&[]).is_empty()));
    let variable = gandr_theory_cell_complexes_tools::ToyVar::from("p");
    let toy_substitution =
        ToyAlphabet::numerals(&[(variable.clone(), Value(2)), (variable.clone(), Value(2))]);
    assert_eq!(
        Toy::succ(Toy::succ(Toy::zero())),
        ToyAlphabet::apply_subst(&toy_substitution, &Toy::var(variable))
    );
    assert_eq!(Toy::zero(), ToyAlphabet::discriminated(&Toy::zero()));
    assert_eq!(
        Toy::add(Toy::zero(), Toy::var("right")),
        ToyAlphabet::discriminated(&Toy::add(Toy::succ(Toy::zero()), Toy::var("right")))
    );
}

#[test]
fn family_boundaries_preserve_assignments_and_adversary_positions()
{
    let command = Toy::add(Toy::var("b"), Toy::add(Toy::var("a"), Toy::var("b")));
    assert_eq!(
        vec![
            gandr_theory_cell_complexes_tools::ToyVar::from("b"),
            gandr_theory_cell_complexes_tools::ToyVar::from("a")
        ],
        holes::<ToyAlphabet>(&command)
    );
    assert_eq!(Value(1), value(Regime::TwoArms, Ordinal(6), Ordinal(1)));
    assert_eq!(
        Value(0),
        value(
            Regime::TwoArms,
            Ordinal(usize::MAX),
            Ordinal(usize::try_from(usize::BITS).expect("word width fits usize"))
        )
    );
    assert_eq!(Value(6), value(Regime::OneVarying, Ordinal(6), Ordinal(0)));
    assert_eq!(Value(0), value(Regime::OneVarying, Ordinal(6), Ordinal(1)));
    assert_eq!(Value(6), value(Regime::AllDistinct, Ordinal(6), Ordinal(1)));
    let (store, base) = lead_base();
    let empty = family(&base, Members(0), Regime::TwoArms, Adversary::Diverged);
    assert!(empty.is_empty());
    assert_eq!(NodeCount::from(0_usize), plain_size(&empty));
    assert_eq!(NodeCount::from(0_usize), plain_steps(&empty));
    let single = family(&base, Members(1), Regime::TwoArms, Adversary::Diverged);
    assert_eq!(
        &base.path_a[.. base.path_a.len().saturating_sub(1)],
        single[0].path_a.as_slice()
    );
    assert_eq!(base.path_b, single[0].path_b);
    assert!(!bool::from(single[0].replay(&store)));
    assert_eq!(NodeCount::from(2_usize), plain_steps(&single));
    assert_eq!(NodeCount::from(12_usize), plain_size(&single));
}
