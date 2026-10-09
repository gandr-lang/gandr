//! The sequent command-pattern alphabet: the first [`CellAlphabet`]
//! inhabitant.
//!
//! This module wires the command-pattern language ([`crate::pattern`]) and its
//! substitutions ([`crate::subst`]) into the generic interface. Everything
//! sequent-specific the generic layer does not know lives here: the
//! orientation and provenance tags ([`Orientation`], [`CellProvenance`],
//! [`EtaKind`]), the per-metavariable metadata derived from a cell's faces
//! ([`CellMeta`], [`CellVarMeta`], [`CellVariance`]), the η-polarity firing
//! discipline, the name-priming apartness renaming, the `$k$` skolem
//! constants of replay, and the return-side frame's defining cell
//! ([`frame_defining_cell`]).
//!
//! Matches over the pattern views stay exhaustive, so a grammar extension is
//! a compile-visible change at every match site here and in
//! [`crate::pattern`].

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::alphabet::CellAlphabet;
use crate::alphabet::CommandSpliceRefusal;
use crate::alphabet::ConvexityDischarge;
use crate::alphabet::Generalization;
use crate::alphabet::PositionOrder;
use crate::alphabet::SeamRole;
use crate::alphabet::anti_unification;
use crate::alphabet::command_subterm;
use crate::alphabet::path_order;
use crate::boundary::CellInvertibility;
use crate::boundary::CellLinearity;
use crate::boundary::FiringPermission;
use crate::boundary::PatternSize;
use crate::boundary::PositionStep;
use crate::boundary::SubstitutionDecision;
use crate::cell::Cell;
use crate::cell::CellStore;
use crate::order::reduction_cmp;
use crate::pattern::Cat;
use crate::pattern::CmdPat;
use crate::pattern::ConsPat;
use crate::pattern::HoleName;
use crate::pattern::MetaVar;
use crate::pattern::Node;
use crate::pattern::NodeRef;
use crate::pattern::Pos;
use crate::pattern::ProdPat;
use crate::pattern::SpliceRefusal;
use crate::pattern::Sym;
use crate::pattern::position_read;
use crate::pattern::splice_cmd;
use crate::pattern::subterm_at;
use crate::polarity::Polarity;
use crate::subst::Subst;
use crate::subst::substitution_from;

/// The sequent command-pattern alphabet: a stateless marker over the
/// [`crate::pattern`] and [`crate::subst`] machinery.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SequentAlphabet;

/// Which η law a cell encodes, tied to the cut polarity it is valid at.
///
/// Data η is valid only at a positive cut (call-by-value), codata η only at a
/// negative cut (call-by-name).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EtaKind
{
    /// Data η: a positive-introduction extensionality law.
    Data,
    /// Codata η: a negative-introduction extensionality law.
    Codata,
}

impl EtaKind
{
    /// The cut polarity this η law requires.
    ///
    /// # Specification
    /// - ensures: [`Polarity::Positive`] for [`EtaKind::Data`],
    ///   [`Polarity::Negative`] for [`EtaKind::Codata`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both kinds are enumerated against both polarities.
    /// - witness: `sequent::tests::each_eta_kind_requires_its_own_polarity`
    #[inline]
    #[must_use]
    pub const fn required_polarity(self) -> Polarity
    {
        match self {
            | Self::Data => Polarity::Positive,
            | Self::Codata => Polarity::Negative,
        }
    }
}

/// How a cell's orientation was fixed.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Orientation
{
    /// Fixed by the cut polarity: the μ/μ̃ pair oriented by `ε`.
    PolarityDerived,
    /// Chosen by the completion reduction order
    /// ([`crate::order::reduction_cmp`]).
    CompletionDerived,
}

/// Where a cell came from.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CellProvenance
{
    /// Elaborated from a surface rule `lhs ~> rhs`.
    SurfaceRule,
    /// The μ/μ̃ critical pair: the fundamental strategy cell.
    MuMuTilde,
    /// A return-side constructor frame's defining cell
    /// `⟨v | K⁻(β)⟩ ~> ⟨K(v) | β⟩` ([`frame_defining_cell`]).
    FrameDefining,
    /// An η law, tied to the polarity its [`EtaKind`] requires.
    Eta(EtaKind),
    /// Synthesized by completion: a derived or fused cell.
    DerivedByCompletion,
}

/// The variance a cell metavariable's hole takes across both faces.
///
/// A hole seen only in producer positions is [`CellVariance::Producer`], only
/// in consumer positions [`CellVariance::Consumer`], and one spanning both is
/// [`CellVariance::Mixed`]: the dinaturality-shaped hole μ, μ̃ and cocase
/// create. Holes are keyed by name, as the apartness renaming keys freshness,
/// so a name worn by a producer and a consumer metavariable is one hole at two
/// polarities.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CellVariance
{
    /// Producer positions only.
    Producer,
    /// Consumer positions only.
    Consumer,
    /// Both: the dinaturality case the composition gate reads.
    Mixed,
}

impl CellVariance
{
    /// The variance one occurrence of category `cat` implies.
    ///
    /// # Specification
    /// - ensures: [`CellVariance::Producer`] for [`Cat::Producer`],
    ///   [`CellVariance::Consumer`] for [`Cat::Consumer`]; never
    ///   [`CellVariance::Mixed`], which is the join of two occurrences.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn from_cat(cat: Cat) -> Self
    {
        match cat {
            | Cat::Producer => Self::Producer,
            | Cat::Consumer => Self::Consumer,
        }
    }
}

/// How a hole is used on a cell's contractum side: the step-growth half of
/// the linearity discipline, beside [`CellVarMeta::linear`]'s redex-side
/// count.
///
/// `Once` preserves a hole, `Erased` weakens it away, `Repeated` contracts it.
/// The derivation reports these and refuses none: the admission boundary
/// ([`crate::linearity::admit_linear_cell`]) governs the redex side alone.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CellContractumUse
{
    /// The `(name, category)` pair does not occur on the right-hand side: the
    /// step drops the hole.
    Erased,
    /// The pair occurs exactly once on the right-hand side: the step
    /// preserves the hole.
    Once,
    /// The pair occurs more than once on the right-hand side: the step
    /// duplicates the hole.
    Repeated,
}

/// The whole-step classification [`CellMeta::step_growth`] reports: the join
/// of the per-hole [`CellContractumUse`] verdicts.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StepGrowth
{
    /// Every hole is used exactly once on each side: the step preserves
    /// information, so a per-step amplification bound is trivial.
    StrictlyLinear,
    /// No hole is duplicated and at least one is dropped: the step weakens.
    Erasing,
    /// At least one hole is duplicated: the step can grow a term.
    Duplicating,
}

/// The derived metadata of one cell metavariable.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CellVarMeta
{
    /// The hole's first occurrence: the representative of a
    /// [`CellVariance::Mixed`] hole, whose category is not single-valued.
    var: MetaVar,
    /// The variance, joined across both faces.
    variance: CellVariance,
    /// Whether `var`'s `(name, category)` pair occurs exactly once on the
    /// left-hand side.
    linear: CellLinearity,
    /// How `var`'s `(name, category)` pair is used on the right-hand side.
    contractum: CellContractumUse,
}

impl CellVarMeta
{
    /// The hole's first occurrence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn var(&self) -> &MetaVar
    {
        &self.var
    }

    /// The variance, joined across both faces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn variance(&self) -> CellVariance
    {
        self.variance
    }

    /// Whether the representative's `(name, category)` pair occurs exactly
    /// once on the left-hand side.
    ///
    /// Counting per pair rather than per name keeps a hole worn at two
    /// polarities linear: one occurrence at each polarity is the seam, not a
    /// copy.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn linear(&self) -> CellLinearity
    {
        self.linear
    }

    /// How the representative's `(name, category)` pair is used on the
    /// right-hand side.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn contractum(&self) -> CellContractumUse
    {
        self.contractum
    }
}

/// The derived metadata of a cell: per-metavariable variance, linearity and
/// contractum use, and whether the cell is an invertible joinability
/// certificate rather than an oriented optimization cell.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CellMeta
{
    /// One entry per distinct hole name, in first-occurrence order.
    vars: Box<[CellVarMeta]>,
    /// Whether the cell is an invertible joinability certificate.
    invertible: CellInvertibility,
}

impl CellMeta
{
    /// The metadata of a cell, derived from its two faces.
    ///
    /// Linearity is counted per `(name, category)` pair and variance per
    /// name. Variance asks which polarities a hole is worn at, so it joins
    /// across them; linearity asks whether a hole is copied, and a hole worn
    /// once as a producer and once as a consumer is the seam, not a copy. This
    /// derivation records; the refusal is the separate admission boundary
    /// [`crate::linearity::admit_linear_cell`].
    ///
    /// # Specification
    /// - ensures: one [`CellVarMeta`] per distinct hole name, in
    ///   first-occurrence order over `lhs` then `rhs`; its variance is
    ///   producer, consumer or mixed by the categories the name is worn at
    ///   across both faces; it is linear exactly when its representative's
    ///   `(name, category)` pair occurs once in `lhs`; its contractum use is
    ///   erased, once or repeated as that pair occurs zero, one or more times
    ///   in `rhs`. `invertible` is carried through.
    /// - panics: none.
    /// - intension: quadratic in the occurrence count, which a cell face keeps
    ///   small.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the variance join and the per-pair linearity count
    ///   are separated by an all-linear cell with a producer-only and a
    ///   consumer-only hole, a same-polarity repeat, and a two-polarity seam
    ///   that comes out mixed and linear; the contractum classification by one
    ///   cell carrying all three uses.
    /// - witness: `sequent::tests::metadata_tracks_variance_and_linearity`
    /// - witness: `sequent::tests::a_repeated_metavariable_is_nonlinear`
    /// - witness: `sequent::tests::a_hole_at_both_polarities_is_a_linear_seam`
    /// - witness: `sequent::tests::the_contractum_use_reports_erased_once_and_repeated`
    #[inline]
    #[must_use]
    pub fn derive(
        lhs: &CmdPat,
        rhs: &CmdPat,
        invertible: CellInvertibility,
    ) -> Self
    {
        let left: Vec<&MetaVar> = lhs.metavars().collect();
        let right: Vec<&MetaVar> = rhs.metavars().collect();
        let mut vars: Vec<CellVarMeta> = Vec::new();
        for &var in left.iter().chain(&right) {
            if vars.iter().any(|seen| seen.var.hole() == var.hole()) {
                continue;
            }
            let worn_at = |cat: Cat| {
                left.iter()
                    .chain(&right)
                    .any(|other| other.hole() == var.hole() && other.cat() == cat)
            };
            let variance = match (worn_at(Cat::Producer), worn_at(Cat::Consumer)) {
                | (true, true) => CellVariance::Mixed,
                | (false, true) => CellVariance::Consumer,
                | (true | false, false) => CellVariance::Producer,
            };
            // Per `(name, category)`, never per name: one hole worn at two
            // polarities is the seam, not a copy.
            let left_count = left.iter().filter(|&&other| other == var).count();
            let right_count = right.iter().filter(|&&other| other == var).count();
            let contractum = match right_count {
                | 0 => CellContractumUse::Erased,
                | 1 => CellContractumUse::Once,
                | _ => CellContractumUse::Repeated,
            };
            vars.push(CellVarMeta {
                var: var.clone(),
                variance,
                linear: CellLinearity::from(left_count == 1),
                contractum,
            });
        }
        Self {
            vars: vars.into_boxed_slice(),
            invertible,
        }
    }

    /// The per-metavariable metadata, in first-occurrence order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn vars(&self) -> &[CellVarMeta]
    {
        &self.vars
    }

    /// Whether the cell is an invertible joinability certificate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn invertible(&self) -> CellInvertibility
    {
        self.invertible
    }

    /// The whole-step growth classification.
    ///
    /// Duplication dominates erasure in the join because it dominates in
    /// cost: a dropped hole shrinks a term, a repeated one can amplify it.
    ///
    /// # Specification
    /// - ensures: [`StepGrowth::Duplicating`] when any hole's contractum use is
    ///   repeated, else [`StepGrowth::Erasing`] when any is erased, else
    ///   [`StepGrowth::StrictlyLinear`] — a cell without metavariables
    ///   included.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three outcomes are separated by the successor
    ///   cell, a cell dropping one of two holes, and a cell dropping one hole
    ///   while duplicating another.
    /// - witness: `sequent::tests::the_step_growth_join_names_duplication_erasure_and_strict_linearity`
    #[inline]
    #[must_use]
    pub fn step_growth(&self) -> StepGrowth
    {
        let mut growth = StepGrowth::StrictlyLinear;
        for var in &self.vars {
            match var.contractum {
                | CellContractumUse::Repeated => return StepGrowth::Duplicating,
                | CellContractumUse::Erased => growth = StepGrowth::Erasing,
                | CellContractumUse::Once => {},
            }
        }
        growth
    }
}

quenchant_shape::reason_enum! {
    /// Why a cell carries no η polarity requirement.
    pub mod eta_requirement {
        /// The reason the cell is unconstrained.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The cell is not an η cell.
            NotEta,
        }
    }
}

impl Cell<SequentAlphabet>
{
    /// The polarity of the cut the cell applies at: its left-hand side's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn polarity(&self) -> Polarity
    {
        self.lhs().polarity()
    }

    /// The cut polarity this cell's η law requires.
    ///
    /// # Specification
    /// - ensures: [`EtaKind::required_polarity`] of the cell's η kind.
    /// - provides: [`eta_requirement::Absent::NotEta`] for every other
    ///   provenance.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both η kinds and a non-η provenance are enumerated.
    /// - witness: `sequent::tests::each_eta_kind_requires_its_own_polarity`
    #[inline]
    pub const fn eta_requirement(&self) -> Maybe<Polarity, eta_requirement::Absent>
    {
        match self.provenance() {
            | CellProvenance::Eta(kind) => Maybe::Present(kind.required_polarity()),
            | CellProvenance::SurfaceRule
            | CellProvenance::MuMuTilde
            | CellProvenance::FrameDefining
            | CellProvenance::DerivedByCompletion => Maybe::Absent(eta_requirement::Absent::NotEta),
        }
    }
}

/// The defining cell of a return-side constructor frame `K⁻`.
///
/// The cell is `⟨v | K⁻(β)⟩ ~> ⟨K(v) | β⟩`, the μ̃ reduction that makes
/// `K⁻(β) := μ̃x.⟨K(x) | β⟩` definable rather than primitive.
///
/// # Specification
/// - ensures: a positive, polarity-derived cell over the metavariables `v`
///   (producer) and `beta` (consumer), both linear, with provenance
///   [`CellProvenance::FrameDefining`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the cell is inserted into a store and deduplicated by its
///   structure, and the order's documented limit is pinned on its two faces.
/// - witness: `sequent::tests::the_store_dedups_on_structural_identity`
/// - witness: `order::tests::the_frame_defining_shape_is_not_oriented_forwards_and_that_is_stated`
#[inline]
#[must_use]
pub fn frame_defining_cell(ctor: &Sym) -> Cell<SequentAlphabet>
{
    let lhs = CmdPat::cut(
        Polarity::Positive,
        ProdPat::meta("v"),
        ConsPat::frame(ctor.clone(), ConsPat::meta("beta")),
    );
    let rhs = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor(ctor.clone(), [ProdPat::meta("v")]),
        ConsPat::meta("beta"),
    );
    Cell::new(
        lhs,
        rhs,
        Orientation::PolarityDerived,
        CellProvenance::FrameDefining,
    )
}

/// The reserved skolem constant for a metavariable.
///
/// # Specification
/// - ensures: the symbol `$k$<name>`, whose `$k$` prefix no datatype symbol
///   carries.
/// - panics: none.
fn skolem_sym(var: &MetaVar) -> Sym
{
    let name: &str = var.hole().as_ref();
    let mut spelled = String::with_capacity(name.len().saturating_add(3));
    spelled.push_str("$k$");
    spelled.push_str(name);
    Sym::from(spelled)
}

/// A name with one prime appended.
///
/// # Specification
/// - ensures: a strictly longer name, so priming terminates against any finite
///   set of taken names.
/// - panics: none.
fn primed(name: &HoleName) -> HoleName
{
    let name: &str = name.as_ref();
    let mut spelled = String::with_capacity(name.len().saturating_add(1));
    spelled.push_str(name);
    spelled.push('\'');
    HoleName::from(spelled)
}

/// The renaming that takes `renamed`'s holes apart from the names in `taken`.
///
/// # Specification
/// - ensures: one fresh name per distinct hole name of `renamed`, in
///   first-occurrence order, each primed until it is absent from `taken` and
///   from the fresh names before it; both categories of one name share its
///   fresh name, so a hole worn at two polarities stays one hole. A name
///   already absent from `taken` maps to itself.
/// - panics: none.
fn apartness_renaming<'var, I>(
    renamed: I,
    mut taken: BTreeSet<HoleName>,
) -> Subst
where
    I: IntoIterator<Item = &'var MetaVar>,
{
    let mut fresh_names: BTreeMap<&HoleName, HoleName> = BTreeMap::new();
    let mut prods: BTreeMap<MetaVar, ProdPat> = BTreeMap::new();
    let mut conss: BTreeMap<MetaVar, ConsPat> = BTreeMap::new();
    for var in renamed {
        let fresh = fresh_names.entry(var.hole()).or_insert_with(|| {
            let mut fresh = var.hole().clone();
            while taken.contains(&fresh) {
                fresh = primed(&fresh);
            }
            taken.insert(fresh.clone());
            fresh
        });
        match var.cat() {
            | Cat::Producer => {
                prods
                    .entry(var.clone())
                    .or_insert_with(|| ProdPat::meta(fresh.clone()));
            },
            | Cat::Consumer => {
                conss
                    .entry(var.clone())
                    .or_insert_with(|| ConsPat::meta(fresh.clone()));
            },
        }
    }
    substitution_from(prods, conss)
}

impl CellAlphabet for SequentAlphabet
{
    type Cmd = CmdPat;
    type Hole = HoleName;
    type Meta = CellMeta;
    type Orientation = Orientation;
    type Pos = Pos;
    type Provenance = CellProvenance;
    type Subst = Subst;
    type Var = MetaVar;

    /// One-sided matching of command patterns.
    ///
    /// # Specification
    /// - ensures: as [`crate::subst::match_cmd`], which leaves `subst`
    ///   unchanged on a negative decision.
    /// - panics: none.
    #[inline]
    fn match_cmd(
        pattern: &Self::Cmd,
        target: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        crate::subst::match_cmd(pattern, target, subst)
    }

    /// Most-general unification of command patterns.
    ///
    /// # Specification
    /// - ensures: as [`crate::subst::unify_cmd`], which leaves `subst`
    ///   unchanged on a negative decision.
    /// - panics: none.
    #[inline]
    fn unify_cmd(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        subst: &mut Self::Subst,
    ) -> SubstitutionDecision
    {
        crate::subst::unify_cmd(lhs, rhs, subst)
    }

    /// The least general generalization of a family of command-pattern
    /// tuples.
    ///
    /// # Specification
    /// - ensures: as [`crate::generalize::anti_unify_cmd`].
    /// - provides: as [`crate::generalize::anti_unify_cmd`].
    /// - panics: none.
    #[inline]
    fn anti_unify_cmd(
        family: &[&[Self::Cmd]]
    ) -> Maybe<Generalization<Self>, anti_unification::Absent>
    {
        crate::generalize::anti_unify_cmd(family)
    }

    /// A command pattern with a substitution applied.
    ///
    /// # Specification
    /// - ensures: as [`Subst::apply_cmd`].
    /// - panics: none.
    #[inline]
    fn apply_subst(
        subst: &Self::Subst,
        cmd: &Self::Cmd,
    ) -> Self::Cmd
    {
        subst.apply_cmd(cmd)
    }

    /// The substitution restricted to `vars`.
    ///
    /// # Specification
    /// - ensures: as [`Subst::restricted`].
    /// - panics: none.
    #[inline]
    fn restrict_subst(
        subst: &Self::Subst,
        vars: &[Self::Var],
    ) -> Self::Subst
    {
        subst.restricted(vars)
    }

    /// The command pattern's metavariables, left to right with repeats.
    ///
    /// # Specification
    /// - ensures: as [`CmdPat::metavars`], owned.
    /// - panics: none.
    #[inline]
    fn metavariables(cmd: &Self::Cmd) -> Vec<Self::Var>
    {
        cmd.metavars().cloned().collect()
    }

    /// The command pattern's node count.
    ///
    /// # Specification
    /// - ensures: as [`CmdPat::size`].
    /// - panics: none.
    #[inline]
    fn cmd_size(cmd: &Self::Cmd) -> PatternSize
    {
        cmd.size()
    }

    /// The command positions of a command pattern: the root alone.
    ///
    /// # Specification
    /// - ensures: exactly the root position; the grammar admits a cut only at
    ///   the root, so no other position addresses a command.
    /// - panics: none.
    #[inline]
    fn command_positions(_cmd: &Self::Cmd) -> Vec<Self::Pos>
    {
        alloc::vec![Pos::root()]
    }

    /// The root position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn root_position() -> Self::Pos
    {
        Pos::root()
    }

    /// The position addressing `path`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn position_at_path(path: &[PositionStep]) -> Self::Pos
    {
        Pos::from_steps(path.iter().copied())
    }

    /// How two positions relate: [`path_order`] over their steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn position_order(
        left: &Self::Pos,
        right: &Self::Pos,
    ) -> PositionOrder
    {
        path_order(left.steps().iter().copied(), right.steps().iter().copied())
    }

    /// The convexity discharge of a store of command-pattern cells.
    ///
    /// # Specification
    /// - ensures: [`ConvexityDischarge::StronglyConnectedOverAcyclicTarget`]
    ///   for every store. The store is not consulted, and that is the finding
    ///   rather than a shortcut: every left-hand side this alphabet can express
    ///   is one cut whose consumer half is a linear spine with a single end, so
    ///   strong connectedness is forced by the grammar, and targets are
    ///   command-pattern trees, hence acyclic. An alphabet with multi-output or
    ///   disconnected left-hand sides breaks the argument and answers
    ///   [`ConvexityDischarge::ReCheckRequired`].
    /// - panics: none.
    #[inline]
    fn convexity_discharge(_store: &CellStore<Self>) -> ConvexityDischarge
    {
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget
    }

    /// The command subterm at `pos`.
    ///
    /// # Specification
    /// - ensures: the whole pattern at the root position.
    /// - provides: [`command_subterm::Absent::OffTerm`] when `pos` leaves the
    ///   pattern; [`command_subterm::Absent::NotACommand`] when it addresses a
    ///   producer or consumer subterm.
    /// - panics: none.
    #[inline]
    fn subterm_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
    ) -> Maybe<Self::Cmd, command_subterm::Absent>
    {
        match subterm_at(NodeRef::Cmd(cmd), pos) {
            | Maybe::Present(NodeRef::Cmd(found)) => Maybe::Present(found.clone()),
            | Maybe::Present(NodeRef::Prod(_) | NodeRef::Cons(_)) => {
                Maybe::Absent(command_subterm::Absent::NotACommand)
            },
            | Maybe::Absent(position_read::Absent::OffPattern) => {
                Maybe::Absent(command_subterm::Absent::OffTerm)
            },
        }
    }

    /// `cmd` with `replacement` spliced in at `pos`.
    ///
    /// # Specification
    /// - ensures: as [`splice_cmd`] with a command replacement.
    /// - fails: [`CommandSpliceRefusal::OffTerm`] when `pos` leaves the
    ///   pattern; [`CommandSpliceRefusal::NotACommand`] when it addresses a
    ///   producer or consumer subterm.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    #[inline]
    fn splice_cmd_at(
        cmd: &Self::Cmd,
        pos: &Self::Pos,
        replacement: Self::Cmd,
    ) -> Result<Self::Cmd, CommandSpliceRefusal>
    {
        splice_cmd(cmd, pos, Node::Cmd(replacement)).map_err(|refusal| match refusal {
            | SpliceRefusal::OffPattern => CommandSpliceRefusal::OffTerm,
            | SpliceRefusal::CategoryMismatch => CommandSpliceRefusal::NotACommand,
        })
    }

    /// The reduction order on command patterns.
    ///
    /// # Specification
    /// - ensures: as [`crate::order::reduction_cmp`].
    /// - panics: none.
    #[inline]
    fn reduction_cmp(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
    ) -> core::cmp::Ordering
    {
        reduction_cmp(lhs, rhs)
    }

    /// `renamed`'s faces with their holes primed apart from `anchor`'s.
    ///
    /// Freshness is keyed by hole name, as the variance derivation keys holes,
    /// so a hole worn at two polarities is renamed as one.
    ///
    /// # Specification
    /// - ensures: every hole name of `renamed` replaced by itself primed until
    ///   it is absent from `anchor`'s names and from the other fresh names,
    ///   both categories of a name together; shapes and categories kept; a cell
    ///   whose names are already absent from `anchor` is unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a seam cell renamed apart from an anchor wearing its
    ///   name stays one hole at two polarities, and a disjoint cell is returned
    ///   unchanged.
    /// - witness: `sequent::tests::renaming_apart_keeps_a_seam_one_hole`
    #[inline]
    fn rename_apart(
        anchor: (&Self::Cmd, &Self::Cmd),
        renamed: (&Self::Cmd, &Self::Cmd),
    ) -> (Self::Cmd, Self::Cmd)
    {
        let taken: BTreeSet<HoleName> = anchor
            .0
            .metavars()
            .chain(anchor.1.metavars())
            .map(|var| var.hole().clone())
            .collect();
        let renaming = apartness_renaming(renamed.0.metavars().chain(renamed.1.metavars()), taken);
        (renaming.apply_cmd(renamed.0), renaming.apply_cmd(renamed.1))
    }

    /// The pattern with every metavariable replaced by its skolem constant.
    ///
    /// # Specification
    /// - ensures: every producer metavariable `x` becomes the nullary
    ///   constructor `$k$x` and every consumer metavariable `α` the opaque
    ///   nullary operation frame `$k$α(; ★)`; the reserved `$k$` prefix never
    ///   collides with a datatype symbol, so the constants are irreducible, and
    ///   the mapping is a function of the name alone.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one peak skolemizes to the same ground pattern twice,
    ///   and that pattern is ground.
    /// - witness: `sequent::tests::skolemization_is_name_stable`
    #[inline]
    fn skolemize(cmd: &Self::Cmd) -> Self::Cmd
    {
        let mut prods: BTreeMap<MetaVar, ProdPat> = BTreeMap::new();
        let mut conss: BTreeMap<MetaVar, ConsPat> = BTreeMap::new();
        for var in cmd.metavars() {
            match var.cat() {
                | Cat::Producer => {
                    prods
                        .entry(var.clone())
                        .or_insert_with(|| ProdPat::ctor(skolem_sym(var), []));
                },
                | Cat::Consumer => {
                    conss
                        .entry(var.clone())
                        .or_insert_with(|| ConsPat::op(skolem_sym(var), [], ConsPat::top()));
                },
            }
        }
        substitution_from(prods, conss).apply_cmd(cmd)
    }

    /// The hole a metavariable belongs to: its name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hole_of(var: &Self::Var) -> Self::Hole
    {
        var.hole().clone()
    }

    /// Whether `provenance` marks a completion-derived certificate.
    ///
    /// # Specification
    /// - ensures: positive exactly for [`CellProvenance::DerivedByCompletion`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a completion-derived cell is built and read back as
    ///   invertible.
    /// - witness: `sequent::tests::completion_cells_are_invertible_certificates`
    #[inline]
    fn completion_certificate(provenance: &Self::Provenance) -> CellInvertibility
    {
        CellInvertibility::from(matches!(*provenance, CellProvenance::DerivedByCompletion))
    }

    /// The metadata of a cell, from its two faces.
    ///
    /// # Specification
    /// - ensures: as [`CellMeta::derive`].
    /// - panics: none.
    #[inline]
    fn derive_meta(
        lhs: &Self::Cmd,
        rhs: &Self::Cmd,
        invertible: CellInvertibility,
    ) -> Self::Meta
    {
        CellMeta::derive(lhs, rhs, invertible)
    }

    /// The flow endpoints `meta` carries for `hole`.
    ///
    /// # Specification
    /// - ensures: one endpoint per metadata entry named `hole`, its role
    ///   [`SeamRole::Forward`] for a producer hole, [`SeamRole::Backward`] for
    ///   a consumer hole, [`SeamRole::Both`] for a mixed one.
    /// - panics: none.
    #[inline]
    fn hole_flow(
        meta: &Self::Meta,
        hole: &Self::Hole,
    ) -> Vec<(Self::Var, SeamRole)>
    {
        meta.vars()
            .iter()
            .filter(|var_meta| var_meta.var().hole() == hole)
            .map(|var_meta| {
                let role = match var_meta.variance() {
                    | CellVariance::Producer => SeamRole::Forward,
                    | CellVariance::Consumer => SeamRole::Backward,
                    | CellVariance::Mixed => SeamRole::Both,
                };
                (var_meta.var().clone(), role)
            })
            .collect()
    }

    /// Whether a cell of `provenance` may fire at `target`.
    ///
    /// # Specification
    /// - ensures: an η cell fires only at a cut of its required polarity; every
    ///   other cell fires at any cut.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both η kinds are enumerated against both target
    ///   polarities, beside a non-η provenance.
    /// - witness: `sequent::tests::each_eta_kind_requires_its_own_polarity`
    #[inline]
    fn may_fire(
        provenance: &Self::Provenance,
        target: &Self::Cmd,
    ) -> FiringPermission
    {
        FiringPermission::from(match *provenance {
            | CellProvenance::Eta(kind) => target.polarity() == kind.required_polarity(),
            | CellProvenance::SurfaceRule
            | CellProvenance::MuMuTilde
            | CellProvenance::FrameDefining
            | CellProvenance::DerivedByCompletion => true,
        })
    }

    /// The orientation completion stamps: completion-derived.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_orientation() -> Self::Orientation
    {
        Orientation::CompletionDerived
    }

    /// The provenance completion stamps: derived by completion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn derived_provenance() -> Self::Provenance
    {
        CellProvenance::DerivedByCompletion
    }
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::boundary::CellCount;
    use crate::cell::cell_lookup;

    /// The metadata entry of the hole named `name`.
    ///
    /// # Specification
    /// - panics: when no entry carries the name, which is a fixture defect.
    fn entry<N>(
        meta: &CellMeta,
        name: N,
    ) -> &CellVarMeta
    where
        N: Into<HoleName>,
    {
        let name = name.into();
        meta.vars()
            .iter()
            .find(|var_meta| *var_meta.var().hole() == name)
            .expect("the hole is present")
    }

    #[test]
    fn metadata_tracks_variance_and_linearity()
    {
        // ⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩ — all three linear.
        let lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        );
        let rhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::op(
                "add",
                [ProdPat::meta("n")],
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
        );
        let meta = CellMeta::derive(&lhs, &rhs, CellInvertibility::from(false));
        assert_eq!(3, meta.vars().len(), "m, n, alpha");
        assert!(
            meta.vars().iter().all(|var| bool::from(var.linear())),
            "each occurs once in the LHS"
        );
        assert_eq!(
            CellVariance::Producer,
            meta.vars()[0].variance(),
            "m is a producer var (producer positions only)"
        );
        assert_eq!(
            CellVariance::Consumer,
            meta.vars()[2].variance(),
            "alpha is a consumer var (consumer positions only)"
        );
    }

    #[test]
    fn a_repeated_metavariable_is_nonlinear()
    {
        // ⟨Pair(x, x) | α⟩ — the producer hole `x` occurs twice at the same
        // polarity: a copy, which the derivation records as non-linear and the
        // admission boundary refuses.
        let lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("x")]),
            ConsPat::meta("alpha"),
        );
        let meta = CellMeta::derive(&lhs, &lhs, CellInvertibility::from(false));
        assert_eq!(2, meta.vars().len(), "x (deduped) and alpha");
        assert!(
            !bool::from(entry(&meta, "x").linear()),
            "the producer x occurs twice, so it is non-linear"
        );
        assert!(
            bool::from(entry(&meta, "alpha").linear()),
            "alpha occurs once, so the copy does not spread to its neighbours"
        );
    }

    #[test]
    fn a_hole_at_both_polarities_is_a_linear_seam()
    {
        // ⟨r | seam(; r)⟩ — the name `r` is worn by a producer and a consumer
        // metavariable: one hole at two polarities, so the derivation promotes
        // it to `Mixed`. It is a seam, not a copy: `r` occurs once at each
        // polarity, so the pattern stays linear.
        let lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("r"),
            ConsPat::op("seam", [], ConsPat::meta("r")),
        );
        let meta = CellMeta::derive(&lhs, &lhs, CellInvertibility::from(false));
        let r = entry(&meta, "r");
        assert_eq!(
            CellVariance::Mixed,
            r.variance(),
            "r spans a producer and a consumer position"
        );
        assert!(
            bool::from(r.linear()),
            "one occurrence at each polarity is a seam, not a copy"
        );
    }

    #[test]
    fn the_contractum_use_reports_erased_once_and_repeated()
    {
        // One cell carrying all three uses: `x` preserved once, `y`
        // duplicated, `z` dropped, and `alpha` kept.
        let lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("T", [
                ProdPat::meta("x"),
                ProdPat::meta("y"),
                ProdPat::meta("z"),
            ]),
            ConsPat::meta("alpha"),
        );
        let rhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("U", [
                ProdPat::meta("x"),
                ProdPat::meta("y"),
                ProdPat::meta("y"),
            ]),
            ConsPat::meta("alpha"),
        );
        let meta = CellMeta::derive(&lhs, &rhs, CellInvertibility::from(false));
        assert_eq!(
            CellContractumUse::Once,
            entry(&meta, "x").contractum(),
            "preserved once"
        );
        assert_eq!(
            CellContractumUse::Repeated,
            entry(&meta, "y").contractum(),
            "duplicated"
        );
        assert_eq!(
            CellContractumUse::Erased,
            entry(&meta, "z").contractum(),
            "dropped"
        );
        assert_eq!(
            CellContractumUse::Once,
            entry(&meta, "alpha").contractum(),
            "the continuation is kept, per pair as ever"
        );
    }

    #[test]
    fn the_step_growth_join_names_duplication_erasure_and_strict_linearity()
    {
        // The successor cell: every hole used exactly once on each side.
        let add_s_lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        );
        let add_s_rhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::op(
                "add",
                [ProdPat::meta("n")],
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
        );
        let linear = CellMeta::derive(&add_s_lhs, &add_s_rhs, CellInvertibility::from(false));
        assert_eq!(
            StepGrowth::StrictlyLinear,
            linear.step_growth(),
            "every hole preserved exactly once"
        );
        // Dropping one of two holes, duplicating none: erasing.
        let drop_lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("y")]),
            ConsPat::meta("alpha"),
        );
        let drop_rhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("x"),
            ConsPat::meta("alpha"),
        );
        let erasing = CellMeta::derive(&drop_lhs, &drop_rhs, CellInvertibility::from(false));
        assert_eq!(
            StepGrowth::Erasing,
            erasing.step_growth(),
            "a dropped hole with no duplication weakens"
        );
        // Duplicating one hole while dropping another: duplication dominates.
        let dup_rhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Pair", [ProdPat::meta("x"), ProdPat::meta("x")]),
            ConsPat::meta("alpha"),
        );
        let duplicating = CellMeta::derive(&drop_lhs, &dup_rhs, CellInvertibility::from(false));
        assert_eq!(
            StepGrowth::Duplicating,
            duplicating.step_growth(),
            "a repeated hole makes the step grow, whatever else it drops"
        );
    }

    #[test]
    fn completion_cells_are_invertible_certificates()
    {
        let lhs = CmdPat::cut(Polarity::Positive, ProdPat::meta("x"), ConsPat::top());
        let cell: Cell = Cell::new(
            lhs.clone(),
            lhs,
            Orientation::CompletionDerived,
            CellProvenance::DerivedByCompletion,
        );
        assert!(
            bool::from(cell.meta().invertible()),
            "a completion-emitted cell is an invertible certificate"
        );
    }

    #[test]
    fn skolemization_is_name_stable()
    {
        let peak = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("v"),
            ConsPat::frame("Succ", ConsPat::meta("v_cons")),
        );
        let once = SequentAlphabet::skolemize(&peak);
        assert_eq!(
            once,
            SequentAlphabet::skolemize(&peak),
            "skolemization is deterministic"
        );
        let expected = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("$k$v", []),
            ConsPat::frame("Succ", ConsPat::op("$k$v_cons", [], ConsPat::top())),
        );
        assert_eq!(expected, once, "and each hole becomes its own constant");
    }

    #[test]
    fn the_store_dedups_on_structural_identity()
    {
        let cell = frame_defining_cell(&Sym::new("Succ"));
        let mut store = CellStore::new();
        let a = store.insert(cell.clone());
        let b = store.insert(cell);
        assert_eq!(a, b, "the same cell inserts once");
        assert_eq!(
            CellCount::from(1_usize),
            store.len(),
            "the store did not grow"
        );
        assert!(
            matches!(store.get(a), Maybe::Present(_)),
            "the issued identifier reads its cell back"
        );
        assert!(
            matches!(
                store.get(crate::cell::CellId::from(1_usize)),
                Maybe::Absent(cell_lookup::Absent::Unissued)
            ),
            "and the next identifier was never issued"
        );
    }

    #[test]
    fn each_eta_kind_requires_its_own_polarity()
    {
        let cut_at = |polarity| CmdPat::cut(polarity, ProdPat::meta("x"), ConsPat::meta("alpha"));
        for (kind, required, refused) in [
            (EtaKind::Data, Polarity::Positive, Polarity::Negative),
            (EtaKind::Codata, Polarity::Negative, Polarity::Positive),
        ] {
            assert_eq!(
                required,
                kind.required_polarity(),
                "each η kind names its own polarity"
            );
            let provenance = CellProvenance::Eta(kind);
            assert!(
                bool::from(SequentAlphabet::may_fire(&provenance, &cut_at(required))),
                "an η cell fires at its own polarity"
            );
            assert!(
                !bool::from(SequentAlphabet::may_fire(&provenance, &cut_at(refused))),
                "and never at the other"
            );
            let cell: Cell = Cell::new(
                cut_at(required),
                cut_at(required),
                Orientation::PolarityDerived,
                provenance,
            );
            assert_eq!(
                Maybe::Present(required),
                cell.eta_requirement(),
                "the cell reports the polarity its law requires"
            );
        }
        let rule: Cell = Cell::new(
            cut_at(Polarity::Negative),
            cut_at(Polarity::Negative),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        );
        assert_eq!(
            Maybe::Absent(eta_requirement::Absent::NotEta),
            rule.eta_requirement(),
            "a non-η cell carries no requirement"
        );
        assert!(
            bool::from(SequentAlphabet::may_fire(
                &CellProvenance::SurfaceRule,
                &cut_at(Polarity::Negative)
            )),
            "and fires at either polarity"
        );
    }

    #[test]
    fn renaming_apart_keeps_a_seam_one_hole()
    {
        // ⟨r | seam(; r)⟩ renamed apart from an anchor wearing `r`: both
        // polarities of `r` move to one fresh name, so the seam survives.
        let seam = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("r"),
            ConsPat::op("seam", [], ConsPat::meta("r")),
        );
        let anchor = CmdPat::cut(Polarity::Positive, ProdPat::meta("r"), ConsPat::top());
        let (renamed, _) = SequentAlphabet::rename_apart((&anchor, &anchor), (&seam, &seam));
        let expected = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("r'"),
            ConsPat::op("seam", [], ConsPat::meta("r'")),
        );
        assert_eq!(expected, renamed, "one hole, one fresh name");
        let elsewhere = CmdPat::cut(Polarity::Positive, ProdPat::meta("q"), ConsPat::top());
        let (unchanged, _) =
            SequentAlphabet::rename_apart((&elsewhere, &elsewhere), (&seam, &seam));
        assert_eq!(
            seam, unchanged,
            "a cell already apart is returned unchanged"
        );
    }
}
