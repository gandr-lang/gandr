//! The sequent-alphabet cells and stores the suites share.

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::HoleName;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_cell_complexes::frame_defining_cell;

/// A positive rule cell `lhs ~> rhs` from the surface.
///
/// # Specification
/// trivial.
pub fn rule(
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

/// (add-S): `⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩`.
///
/// # Specification
/// trivial.
pub fn add_s() -> Cell
{
    rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        ),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::op(
                "add",
                [ProdPat::meta("n")],
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
        ),
    )
}

/// (add-Z): `⟨Zero | add(n; α)⟩ ~> ⟨n | α⟩`.
///
/// # Specification
/// trivial.
pub fn add_z() -> Cell
{
    rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        ),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("n"),
            ConsPat::meta("alpha"),
        ),
    )
}

/// The Peano addition store: the `Succ⁻` frame cell (id 0), (add-Z) (id 1)
/// and (add-S) (id 2).
///
/// # Specification
/// trivial.
pub fn peano_store() -> CellStore
{
    let mut store = CellStore::new();
    store.insert(frame_defining_cell(&Sym::new("Succ")));
    store.insert(add_z());
    store.insert(add_s());
    store
}

/// A rule `⟨K | op(α)⟩ ~> ⟨K | rhs⟩` over the nullary constructor `ctor`.
///
/// # Specification
/// trivial.
pub fn ground_rule(
    ctor: &Sym,
    op: &Sym,
    rhs: ConsPat,
) -> Cell
{
    rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor(ctor.clone(), []),
            ConsPat::op(op.clone(), [], ConsPat::meta("alpha")),
        ),
        CmdPat::cut(Polarity::Positive, ProdPat::ctor(ctor.clone(), []), rhs),
    )
}

/// A rule `⟨binder | op(α)⟩ ~> ⟨binder | rhs⟩` over a producer metavariable.
///
/// # Specification
/// trivial.
pub fn schematic_rule(
    binder: &HoleName,
    op: &Sym,
    rhs: ConsPat,
) -> Cell
{
    rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta(binder.clone()),
            ConsPat::op(op.clone(), [], ConsPat::meta("alpha")),
        ),
        CmdPat::cut(Polarity::Positive, ProdPat::meta(binder.clone()), rhs),
    )
}

/// Two rules over `⟨Zero | f(α)⟩` with divergent right-hand sides: r1
/// `⟨Zero | f(α)⟩ ~> ⟨Zero | α⟩` and r2 `⟨x | f(α)⟩ ~> ⟨x | g(α)⟩`.
///
/// # Specification
/// trivial.
pub fn overlapping_rules() -> CellStore
{
    let f = Sym::new("f");
    let mut store = CellStore::new();
    store.insert(ground_rule(&Sym::new("Zero"), &f, ConsPat::meta("alpha")));
    store.insert(schematic_rule(
        &HoleName::new("x"),
        &f,
        ConsPat::op("g", [], ConsPat::meta("alpha")),
    ));
    store
}

/// Two rules erasing `f` whose reducts coincide: r1 `⟨Zero | f(α)⟩ ~> ⟨Zero |
/// α⟩` and r2 `⟨x | f(α)⟩ ~> ⟨x | α⟩`.
///
/// # Specification
/// trivial.
pub fn joinable_store() -> CellStore
{
    let f = Sym::new("f");
    let mut store = CellStore::new();
    store.insert(ground_rule(&Sym::new("Zero"), &f, ConsPat::meta("alpha")));
    store.insert(schematic_rule(
        &HoleName::new("x"),
        &f,
        ConsPat::meta("alpha"),
    ));
    store
}

/// Three two-rule clusters over the disjoint operations `f`, `g` and `h`.
///
/// Each cluster's ground and schematic rule overlap on their own operation
/// and on nothing else, since no right-hand side head (`p`, `q`) is a
/// left-hand side head, so the six critical pairs schedule into two batches of
/// three. The leading cluster's pair joins outright, both rules reducing to
/// `p`; the other two diverge by size and orient into a derived cell each.
///
/// # Specification
/// trivial.
pub fn independent_rule_clusters() -> CellStore
{
    let reduced = || ConsPat::op("p", [], ConsPat::meta("alpha"));
    let wrapped = || ConsPat::op("q", [], reduced());
    let (f, g, h) = (Sym::new("f"), Sym::new("g"), Sym::new("h"));
    let mut store = CellStore::new();
    store.insert(ground_rule(&Sym::new("Zero"), &f, reduced()));
    store.insert(schematic_rule(&HoleName::new("x"), &f, reduced()));
    store.insert(ground_rule(&Sym::new("Nil"), &g, reduced()));
    store.insert(schematic_rule(&HoleName::new("y"), &g, wrapped()));
    store.insert(ground_rule(&Sym::new("Unit"), &h, reduced()));
    store.insert(schematic_rule(&HoleName::new("z"), &h, wrapped()));
    store
}
