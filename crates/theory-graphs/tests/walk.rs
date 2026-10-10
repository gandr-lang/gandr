//! The walk machine: construction guards, the closures, the canonical order
//! and its filters, the query projections, seen-key keying, the molds
//! projection and the fingerprint, against the paper's figure-33 traces and
//! section-4.1 examples and against fixtures that isolate one key each.

use core::error::Error;

use anodized::spec;
use gandr_theory_graphs::Dir;
use gandr_theory_graphs::End;
use gandr_theory_graphs::SeenKeyVerdict;
use gandr_theory_graphs::StanceTileSorted;
use gandr_theory_graphs::Swing;
use gandr_theory_graphs::SwingAdvance;
use gandr_theory_graphs::SwingArc;
use gandr_theory_graphs::Walk;
use gandr_theory_graphs::WalkBuildError;
use gandr_theory_graphs::WalkChainLength;
use gandr_theory_graphs::WalkIndex;
use gandr_theory_graphs::WalkSpec;
use gandr_theory_graphs::WalkStep;
use gandr_theory_graphs::WalkSym;
use gandr_theory_graphs::WalkSymbolKey;
use proptest::prelude::*;

/// The name of one canonical-order case, printed when it fails.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct OrderCase<'case>(&'case str);

impl<'case> From<&'case str> for OrderCase<'case>
{
    /// Borrows the name.
    ///
    /// # Specification
    /// trivial.
    fn from(value: &'case str) -> Self
    {
        Self(value)
    }
}

impl core::fmt::Display for OrderCase<'_>
{
    /// Writes the name.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(self.0)
    }
}

/// A fixture sort.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct TestSort(u8);

impl From<u8> for TestSort
{
    /// Wraps the raw sort.
    ///
    /// # Specification
    /// trivial.
    fn from(value: u8) -> Self
    {
        Self(value)
    }
}

/// A fixture bounds key.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct TestBounds(u8);

impl From<u8> for TestBounds
{
    /// Wraps the raw bounds.
    ///
    /// # Specification
    /// trivial.
    fn from(value: u8) -> Self
    {
        Self(value)
    }
}

/// A fixture symbol's fingerprint key, which the shapes compare by.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct TestKey(u64);

impl From<u64> for TestKey
{
    /// Wraps the raw key.
    ///
    /// # Specification
    /// trivial.
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}

/// A fixture tile label.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct TestLabel(u8);

impl From<u8> for TestLabel
{
    /// Wraps the raw label.
    ///
    /// # Specification
    /// trivial.
    fn from(value: u8) -> Self
    {
        Self(value)
    }
}

/// A fixture mold.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct TestMold(u8);

impl From<u8> for TestMold
{
    /// Wraps the raw mold.
    ///
    /// # Specification
    /// trivial.
    fn from(value: u8) -> Self
    {
        Self(value)
    }
}

/// A walk read back as its symbols' keys: swings, then stances.
#[derive(Clone, Debug, Eq, PartialEq)]
struct WalkShape
{
    /// Each swing's nonterminal keys.
    swings: Vec<Vec<u64>>,
    /// The stance keys.
    stances: Vec<u64>,
}

impl PartialEq<(Vec<Vec<u64>>, Vec<u64>)> for WalkShape
{
    /// Compares the shape with expected swing and stance keys.
    ///
    /// # Specification
    /// trivial.
    fn eq(
        &self,
        other: &(Vec<Vec<u64>>, Vec<u64>),
    ) -> bool
    {
        self.swings == other.0 && self.stances == other.1
    }
}

impl PartialEq<WalkShape> for (Vec<Vec<u64>>, Vec<u64>)
{
    /// Compares expected swing and stance keys with the shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &WalkShape,
    ) -> bool
    {
        other == self
    }
}

/// The fixture symbol vocabulary.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Sym;

/// A fixture nonterminal: its sort, its bounds and its key.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Nt
{
    /// The sort.
    sort: TestSort,
    /// The bounds.
    bounds: TestBounds,
    /// The key.
    key: TestKey,
}

/// A fixture stance: its sort and key, whether it is tile-sorted, and the
/// label and mold of a molded tile.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct St
{
    /// The sort.
    sort: TestSort,
    /// The key.
    key: TestKey,
    /// Whether the stance is tile-sorted.
    tile: bool,
    /// The label of a molded tile.
    label: Option<TestLabel>,
    /// The mold of a molded tile.
    mold: Option<TestMold>,
}

impl WalkSym for Sym
{
    type Bounds = TestBounds;
    type Label = TestLabel;
    type Mold = TestMold;
    type Nonterminal = Nt;
    type Sort = TestSort;
    type Stance = St;

    /// Reads the nonterminal's sort.
    ///
    /// # Specification
    /// trivial.
    fn nonterminal_sort(nonterminal: &Self::Nonterminal) -> Self::Sort
    {
        nonterminal.sort
    }

    /// Reads the nonterminal's bounds.
    ///
    /// # Specification
    /// trivial.
    fn nonterminal_bounds(nonterminal: &Self::Nonterminal) -> Self::Bounds
    {
        nonterminal.bounds
    }

    /// Reads the stance's sort.
    ///
    /// # Specification
    /// trivial.
    fn stance_sort(stance: &Self::Stance) -> Self::Sort
    {
        stance.sort
    }

    /// Reads whether the stance is tile-sorted.
    ///
    /// # Specification
    /// trivial.
    fn stance_tile_sorted(stance: &Self::Stance) -> StanceTileSorted
    {
        StanceTileSorted::from(stance.tile)
    }

    /// Reads a molded tile's label and mold.
    ///
    /// # Specification
    /// trivial.
    fn label_mold(stance: &Self::Stance) -> Option<(Self::Label, Self::Mold)>
    {
        stance.label.zip(stance.mold)
    }

    /// Reads the nonterminal's key.
    ///
    /// # Specification
    /// trivial.
    fn nonterminal_key(nonterminal: &Self::Nonterminal) -> WalkSymbolKey
    {
        WalkSymbolKey::from(nonterminal.key.0)
    }

    /// Reads the stance's key.
    ///
    /// # Specification
    /// trivial.
    fn stance_key(stance: &Self::Stance) -> WalkSymbolKey
    {
        WalkSymbolKey::from(stance.key.0)
    }
}

#[test]
fn construction_guards_refuse_malformed_shapes() -> Result<(), Box<dyn Error>>
{
    let a = fixture_support::nt(1_u8, 0_u8, 1_u64);
    let b = fixture_support::nt(2_u8, 0_u8, 2_u64);
    let stance = st(9_u8, 9_u64);

    assert_eq!(Err(WalkBuildError::EmptySwing), Swing::<Nt>::new(vec![]));
    assert_eq!(
        Err(WalkBuildError::InvalidWalkShape),
        Walk::<Nt, St>::new(vec![], vec![])
    );
    assert_eq!(
        Err(WalkBuildError::InvalidWalkShape),
        Walk::new(vec![swing(&[a])], vec![stance])
    );
    assert_eq!(
        Err(WalkBuildError::InvalidWalkShape),
        Walk::<Nt, St>::new(vec![swing(&[a]), swing(&[b])], vec![])
    );

    let from_parts = Walk::new(vec![swing(&[a]), swing(&[a, b])], vec![stance])?;
    let from_steps = Walk::from_steps(vec![
        WalkStep::Swing(swing(&[a])),
        WalkStep::Stance(stance),
        WalkStep::Swing(swing(&[a, b])),
    ])?;
    assert_eq!(from_parts, from_steps);
    assert_eq!(shape(&from_parts), (vec![vec![1], vec![1, 2]], vec![9]));
    assert_eq!(WalkChainLength::from(3), from_parts.chain_len()?);
    assert_eq!(
        Err(WalkBuildError::InvalidWalkShape),
        Walk::<Nt, St>::from_steps(vec![])
    );
    assert_eq!(
        Err(WalkBuildError::InvalidWalkShape),
        Walk::from_steps(vec![WalkStep::Swing(swing(&[a])), WalkStep::Stance(stance)])
    );
    assert_eq!(
        Err(WalkBuildError::InvalidWalkShape),
        Walk::<Nt, St>::from_steps(vec![
            WalkStep::Swing(swing(&[a])),
            WalkStep::Swing(swing(&[b])),
        ])
    );

    assert!(matches!(
        SwingArc::<Sym>::new(a, SwingAdvance::Stay, None, None),
        Err(WalkBuildError::UselessArc)
    ));
    SwingArc::<Sym>::new(a, SwingAdvance::Stay, Some(End::Root), None)?;
    SwingArc::<Sym>::new(a, SwingAdvance::Stay, None, Some(b))?;
    assert_eq!(
        Err(WalkBuildError::ZeroMaxChainLen),
        WalkSpec::<Sym>::new(WalkChainLength::from(0)).map(|spec| spec.max_chain_len())
    );
    Ok(())
}

#[test]
fn max_chain_len_reports_exact_accepted_cap() -> Result<(), Box<dyn Error>>
{
    let spec = WalkSpec::<Sym>::new(WalkChainLength::from(2))?;

    assert_eq!(
        WalkChainLength::from(2),
        spec.max_chain_len(),
        "the public accessor must return the exact accepted cap, not a sentinel"
    );
    Ok(())
}

#[test]
fn canonical_unique_key_gate_retains_first_public_row() -> Result<(), Box<dyn Error>>
{
    const UNIQUE_KEY_SRC: u8 = 240;
    const UNIQUE_KEY_DST: u8 = 241;

    let src = End::Node(st(UNIQUE_KEY_SRC, u64::from(UNIQUE_KEY_SRC)));
    let dst = End::Node(st(UNIQUE_KEY_DST, u64::from(UNIQUE_KEY_DST)));
    let only_row = fixture_support::walk(
        &[&[
            fixture_support::nt(1_u8, 0_u8, 1_u64),
            fixture_support::nt(2_u8, 0_u8, 2_u64),
        ]],
        &[],
    );
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(3))?;
    spec.insert_direct(Dir::Left, src.clone(), dst.clone(), only_row.clone());

    let index = WalkIndex::build(&spec)?;
    assert_eq!(
        core::slice::from_ref(&only_row),
        index.walks(Dir::Left, &src, &dst),
        "the first canonical key must be retained before duplicate-key suppression can compare later rows"
    );
    Ok(())
}
#[test]
fn canonical_valid_minimal_gate_excludes_tiled_midpoint() -> Result<(), Box<dyn Error>>
{
    const MINIMAL_GATE_SRC: u8 = 242;
    const MINIMAL_GATE_DST: u8 = 243;

    let src = End::Node(st(MINIMAL_GATE_SRC, u64::from(MINIMAL_GATE_SRC)));
    let dst = End::Node(st(MINIMAL_GATE_DST, u64::from(MINIMAL_GATE_DST)));
    let valid = fixture_support::walk(
        &[
            &[
                fixture_support::nt(1_u8, 0_u8, 1_u64),
                fixture_support::nt(2_u8, 0_u8, 2_u64),
            ],
            &[
                fixture_support::nt(3_u8, 0_u8, 3_u64),
                fixture_support::nt(4_u8, 0_u8, 4_u64),
            ],
        ],
        &[st(8_u8, 8_u64)],
    );
    let tiled_midpoint = fixture_support::walk(
        &[
            &[
                fixture_support::nt(5_u8, 0_u8, 5_u64),
                fixture_support::nt(6_u8, 0_u8, 6_u64),
            ],
            &[fixture_support::nt(7_u8, 0_u8, 7_u64)],
            &[
                fixture_support::nt(8_u8, 0_u8, 8_u64),
                fixture_support::nt(9_u8, 0_u8, 9_u64),
            ],
        ],
        &[tile(9_u8, 9_u64), st(10_u8, 10_u64)],
    );
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(5))?;
    spec.insert_direct(Dir::Left, src.clone(), dst.clone(), tiled_midpoint);
    spec.insert_direct(Dir::Left, src.clone(), dst.clone(), valid.clone());

    let index = WalkIndex::build(&spec)?;
    assert_eq!(
        core::slice::from_ref(&valid),
        index.walks(Dir::Left, &src, &dst),
        "canonical rows require both a valid equality/non-equality shape and minimal tiled-midpoint discipline"
    );
    Ok(())
}
#[test]
fn canonical_height_counts_nonzero_swings_only() -> Result<(), Box<dyn Error>>
{
    const HEIGHT_SRC: u8 = 250;
    const HEIGHT_DST: u8 = 251;
    const ZERO_HEIGHT_LEFT: u8 = 90;
    const ZERO_HEIGHT_RIGHT: u8 = 91;
    const ZERO_HEIGHT_STANCE: u8 = 12;

    let src = End::Node(st(HEIGHT_SRC, u64::from(HEIGHT_SRC)));
    let dst = End::Node(st(HEIGHT_DST, u64::from(HEIGHT_DST)));
    let zero_height_first = fixture_support::walk(
        &[
            &[fixture_support::nt(
                ZERO_HEIGHT_LEFT,
                0_u8,
                u64::from(ZERO_HEIGHT_LEFT),
            )],
            &[fixture_support::nt(
                ZERO_HEIGHT_RIGHT,
                0_u8,
                u64::from(ZERO_HEIGHT_RIGHT),
            )],
        ],
        &[st(ZERO_HEIGHT_STANCE, u64::from(ZERO_HEIGHT_STANCE))],
    );
    let nonzero_second = fixture_support::walk(
        &[&[
            fixture_support::nt(1_u8, 0_u8, 1_u64),
            fixture_support::nt(2_u8, 0_u8, 2_u64),
        ]],
        &[],
    );
    let expected = vec![shape(&zero_height_first), shape(&nonzero_second)];
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(3))?;
    spec.insert_direct(Dir::Left, src.clone(), dst.clone(), nonzero_second);
    spec.insert_direct(Dir::Left, src.clone(), dst.clone(), zero_height_first);

    let index = WalkIndex::build(&spec)?;
    let rows: Vec<_> = index
        .walks(Dir::Left, &src, &dst)
        .iter()
        .map(shape)
        .collect();
    assert_eq!(
        rows, expected,
        "canonical height must count non-zero swings; counting zero-height swings reverses this pair"
    );
    Ok(())
}
#[test]
fn canonical_top_key_requires_zero_height_prefix() -> Result<(), Box<dyn Error>>
{
    const NO_TOP_LEFT: u8 = 80;
    const NO_TOP_RIGHT: u8 = 81;
    const NO_TOP_TAIL_LEFT: u8 = 82;
    const NO_TOP_TAIL_RIGHT: u8 = 83;
    const TOP_SHARED_STANCE: u8 = 7;
    const TOP_BOTTOM_STANCE: u8 = 30;

    let no_top_first = fixture_support::walk(
        &[
            &[
                fixture_support::nt(NO_TOP_LEFT, 0_u8, u64::from(NO_TOP_LEFT)),
                fixture_support::nt(NO_TOP_RIGHT, 0_u8, u64::from(NO_TOP_RIGHT)),
            ],
            &[
                fixture_support::nt(NO_TOP_TAIL_LEFT, 0_u8, u64::from(NO_TOP_TAIL_LEFT)),
                fixture_support::nt(NO_TOP_TAIL_RIGHT, 0_u8, u64::from(NO_TOP_TAIL_RIGHT)),
            ],
        ],
        &[st(TOP_SHARED_STANCE, u64::from(TOP_SHARED_STANCE))],
    );
    let top_second = fixture_support::walk(
        &[
            &[fixture_support::nt(1_u8, 0_u8, 1_u64)],
            &[
                fixture_support::nt(2_u8, 0_u8, 2_u64),
                fixture_support::nt(3_u8, 0_u8, 3_u64),
            ],
            &[
                fixture_support::nt(4_u8, 0_u8, 4_u64),
                fixture_support::nt(5_u8, 0_u8, 5_u64),
            ],
        ],
        &[
            st(TOP_SHARED_STANCE, u64::from(TOP_SHARED_STANCE)),
            st(TOP_BOTTOM_STANCE, u64::from(TOP_BOTTOM_STANCE)),
        ],
    );

    assertion_support::assert_ordered_walks(
        "top key is populated only before the first nonzero swing",
        no_top_first,
        top_second,
    )
}
#[test]
fn canonical_mid_key_requires_strict_interior_count() -> Result<(), Box<dyn Error>>
{
    const MID_PREFIX_LEFT: u8 = 80;
    const MID_PREFIX_RIGHT: u8 = 81;
    const MID_SINGLE: u8 = 82;
    const MID_TAIL_LOW: u8 = 83;
    const MID_TAIL_HIGH: u8 = 84;
    const MID_TOP_LOW: u8 = 7;
    const MID_TOP_HIGH: u8 = 8;
    const MID_BOTTOM: u8 = 30;

    let mid_low_first = fixture_support::walk(
        &[
            &[
                fixture_support::nt(MID_PREFIX_LEFT, 0_u8, u64::from(MID_PREFIX_LEFT)),
                fixture_support::nt(MID_PREFIX_RIGHT, 0_u8, u64::from(MID_PREFIX_RIGHT)),
            ],
            &[fixture_support::nt(MID_SINGLE, 0_u8, u64::from(MID_SINGLE))],
            &[
                fixture_support::nt(MID_TAIL_LOW, 0_u8, u64::from(MID_TAIL_LOW)),
                fixture_support::nt(MID_TAIL_HIGH, 0_u8, u64::from(MID_TAIL_HIGH)),
            ],
        ],
        &[
            st(MID_TOP_LOW, u64::from(MID_TOP_LOW)),
            st(MID_BOTTOM, u64::from(MID_BOTTOM)),
        ],
    );
    let mid_high_second = fixture_support::walk(
        &[
            &[
                fixture_support::nt(1_u8, 0_u8, 1_u64),
                fixture_support::nt(2_u8, 0_u8, 2_u64),
            ],
            &[fixture_support::nt(3_u8, 0_u8, 3_u64)],
            &[
                fixture_support::nt(4_u8, 0_u8, 4_u64),
                fixture_support::nt(5_u8, 0_u8, 5_u64),
            ],
        ],
        &[
            st(MID_TOP_HIGH, u64::from(MID_TOP_HIGH)),
            st(MID_BOTTOM, u64::from(MID_BOTTOM)),
        ],
    );

    assertion_support::assert_ordered_walks(
        "mid key records only positive counts below total height",
        mid_low_first,
        mid_high_second,
    )
}
#[test]
fn transitive_queue_prunes_only_node_endpoints_not_already_seen() -> Result<(), Box<dyn Error>>
{
    let a = End::Node(st(1_u8, 1_u64));
    let b = End::Node(st(2_u8, 2_u64));
    let c = End::Node(st(3_u8, 3_u64));
    let ab = fixture_support::walk(&[&[fixture_support::nt(1_u8, 0_u8, 1_u64)]], &[]);
    let return_walk = fixture_support::walk(&[&[fixture_support::nt(2_u8, 0_u8, 2_u64)]], &[]);
    let mut cyclic = WalkSpec::<Sym>::new(WalkChainLength::from(3))?;
    cyclic.insert_direct(Dir::Left, a.clone(), b.clone(), ab);
    cyclic.insert_direct(Dir::Left, b, a.clone(), return_walk);

    let index = WalkIndex::build(&cyclic)?;
    let loop_rows: Vec<_> = index.walks(Dir::Left, &a, &a).iter().map(shape).collect();
    assert_eq!(
        loop_rows,
        vec![(vec![vec![1], vec![2]], vec![2])],
        "a repeated node endpoint should materialize once but must not be queued again"
    );

    let mut root_terminal = WalkSpec::<Sym>::new(WalkChainLength::from(3))?;
    root_terminal.insert_direct(
        Dir::Left,
        a.clone(),
        End::Root,
        fixture_support::walk(&[&[fixture_support::nt(3_u8, 0_u8, 3_u64)]], &[]),
    );
    root_terminal.insert_direct(
        Dir::Left,
        End::Root,
        c.clone(),
        fixture_support::walk(&[&[fixture_support::nt(4_u8, 0_u8, 4_u64)]], &[]),
    );

    let root_index = WalkIndex::build(&root_terminal)?;
    assert!(root_index.walks(Dir::Left, &a, &c).is_empty());
    assert_eq!(
        &[fixture_support::walk(
            &[&[fixture_support::nt(3_u8, 0_u8, 3_u64)]],
            &[]
        )],
        root_index.walks(Dir::Left, &a, &End::Root),
        "Root destinations are terminal for transitive queueing even when they are newly seen"
    );
    Ok(())
}
#[test]
fn figure_33_fragments_are_literate_external_oracle() -> Result<(), Box<dyn Error>>
{
    const DELTA_E_KEY: u64 = 30;
    const DELTA_P_KEY: u64 = 40;
    const SIGMA_KEY: u64 = 50;
    const S_LET_KEY: u64 = 60;
    const STAR_STANCE: u8 = 10;
    const LET_KEYWORD: u8 = 11;
    const SIGMA_E_STANCE: u8 = 12;
    const IN_KEYWORD: u8 = 13;

    let two = fixture_support::nt(2_u8, 0_u8, 2_u64);
    let delta_e = fixture_support::nt(3_u8, 0_u8, DELTA_E_KEY);
    let delta_p = fixture_support::nt(4_u8, 0_u8, DELTA_P_KEY);
    let sigma = fixture_support::nt(5_u8, 0_u8, SIGMA_KEY);
    let s_let_nt = fixture_support::nt(6_u8, 0_u8, S_LET_KEY);
    let star = st(STAR_STANCE, u64::from(STAR_STANCE));
    let let_kw = st(LET_KEYWORD, u64::from(LET_KEYWORD));
    let sigma_e = st(SIGMA_E_STANCE, u64::from(SIGMA_E_STANCE));
    let in_kw = st(IN_KEYWORD, u64::from(IN_KEYWORD));
    let s_star = End::Node(star);
    let s_let = End::Node(let_kw);
    let s_hat = End::Node(sigma_e);

    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(9))?;
    spec.insert_direct(
        Dir::Left,
        End::Root,
        s_star.clone(),
        fixture_support::walk(&[&[two], &[delta_e]], &[star]),
    );
    spec.insert_direct(
        Dir::Left,
        End::Root,
        s_let.clone(),
        fixture_support::walk(&[&[delta_p], &[sigma], &[delta_e], &[delta_e]], &[
            let_kw, sigma_e, in_kw,
        ]),
    );
    spec.insert_direct(
        Dir::Left,
        End::Root,
        s_hat.clone(),
        fixture_support::walk(&[&[two], &[s_let_nt]], &[sigma_e]),
    );

    let index = WalkIndex::build(&spec)?;
    assert_eq!(1, index.walks(Dir::Left, &End::Root, &s_star).len());
    assert_eq!(
        shape(&index.walks(Dir::Left, &End::Root, &s_star)[0]),
        (vec![vec![2], vec![30]], vec![10]),
        "Fig 33(a): input 2,* completes to the documented S_star trace"
    );
    assert_eq!(
        shape(&index.walks(Dir::Left, &End::Root, &s_let)[0]),
        (vec![vec![40], vec![50], vec![30], vec![30]], vec![
            11, 12, 13
        ]),
        "Fig 33(b): S_let matches the documented let completion"
    );
    assert_eq!(
        shape(&index.walks(Dir::Left, &End::Root, &s_hat)[0]),
        (vec![vec![2], vec![60]], vec![12]),
        "Fig 33(b): S_hat matches the documented completion"
    );
    Ok(())
}
#[test]
fn section_4_1_filters_and_canonical_order_are_observable() -> Result<(), Box<dyn Error>>
{
    const TOP_B_KEY: u64 = 20;
    const GROUT_MID_KEY: u64 = 30;
    const FILTERED_TILE_KEY: u64 = 31;
    const BOTTOM_A_KEY: u64 = 40;

    let a = End::Node(st(1_u8, 1_u64));
    let f = End::Node(st(6_u8, 6_u64));
    let n1 = fixture_support::nt(1_u8, 0_u8, 1_u64);
    let n2 = fixture_support::nt(1_u8, 1_u8, 2_u64);
    let n3 = fixture_support::nt(1_u8, 2_u8, 3_u64);
    let n4 = fixture_support::nt(1_u8, 3_u8, 4_u64);
    let n5 = fixture_support::nt(1_u8, 4_u8, 5_u64);
    let n6 = fixture_support::nt(1_u8, 5_u8, 6_u64);
    let top_a = st(1_u8, 10_u64);
    let top_b = st(2_u8, TOP_B_KEY);
    let grout_mid = st(3_u8, GROUT_MID_KEY);
    let tile_mid = tile(3_u8, FILTERED_TILE_KEY);
    let bottom_a = st(4_u8, BOTTOM_A_KEY);

    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(7))?;
    spec.insert_direct(
        Dir::Left,
        a.clone(),
        f.clone(),
        fixture_support::walk(&[&[n1, n2]], &[]),
    );
    spec.insert_direct(
        Dir::Left,
        a.clone(),
        f.clone(),
        fixture_support::walk(&[&[n1], &[n2, n3]], &[top_b]),
    );
    spec.insert_direct(
        Dir::Left,
        a.clone(),
        f.clone(),
        fixture_support::walk(&[&[n1], &[n2, n3]], &[top_a]),
    );
    spec.insert_direct(
        Dir::Left,
        a.clone(),
        f.clone(),
        fixture_support::walk(&[&[n1], &[n4], &[n2, n3]], &[top_a, bottom_a]),
    );
    spec.insert_direct(
        Dir::Left,
        a.clone(),
        f.clone(),
        fixture_support::walk(&[&[n1], &[n2, n5]], &[top_a]),
    );
    spec.insert_direct(
        Dir::Left,
        a.clone(),
        f.clone(),
        fixture_support::walk(&[&[n1, n2], &[n3], &[n4, n5]], &[grout_mid, bottom_a]),
    );
    spec.insert_direct(
        Dir::Left,
        a.clone(),
        f.clone(),
        fixture_support::walk(&[&[n1, n2], &[n3], &[n4, n6]], &[tile_mid, bottom_a]),
    );

    let index = WalkIndex::build(&spec)?;
    let rows: Vec<_> = index.walks(Dir::Left, &a, &f).iter().map(shape).collect();
    assert_eq!(rows, vec![
        (vec![vec![1, 2]], vec![]),
        (vec![vec![1], vec![2, 3]], vec![10]),
        (vec![vec![1], vec![2, 5]], vec![10]),
        (vec![vec![1], vec![4], vec![2, 3]], vec![10, 40]),
        (vec![vec![1], vec![2, 3]], vec![20]),
        (vec![vec![1, 2], vec![3], vec![4, 5]], vec![30, 40]),
    ]);
    assert!(
        rows.iter()
            .all(|row| !row.stances.contains(&FILTERED_TILE_KEY))
    );
    Ok(())
}
#[test]
fn canonical_order_keys_are_isolated_pairwise_witnesses() -> Result<(), Box<dyn Error>>
{
    const TOP_HIGH: u8 = 20;
    const MID_LOW: u8 = 30;
    const MID_HIGH: u8 = 40;

    let swing_a = fixture_support::nt(1_u8, 0_u8, 1_u64);
    let swing_b = fixture_support::nt(1_u8, 1_u8, 2_u64);
    let swing_c = fixture_support::nt(1_u8, 2_u8, 3_u64);
    let swing_d = fixture_support::nt(1_u8, 3_u8, 4_u64);
    let swing_e = fixture_support::nt(1_u8, 4_u8, 5_u64);
    let swing_f = fixture_support::nt(1_u8, 5_u8, 6_u64);
    let top_low = st(10_u8, 10_u64);
    let top_high = st(TOP_HIGH, u64::from(TOP_HIGH));
    let mid_low = st(MID_LOW, u64::from(MID_LOW));
    let mid_high = st(MID_HIGH, u64::from(MID_HIGH));

    assertion_support::assert_ordered_walks(
        "nonzero swing count outranks summed internal height",
        fixture_support::walk(&[&[swing_a, swing_b, swing_c, swing_d]], &[]),
        fixture_support::walk(&[&[swing_a, swing_b], &[swing_c, swing_d]], &[mid_low]),
    )?;
    assertion_support::assert_ordered_walks(
        "top stance sort precedes later tie-breakers",
        fixture_support::walk(&[&[swing_a], &[swing_b, swing_c]], &[top_low]),
        fixture_support::walk(&[&[swing_a], &[swing_b, swing_c]], &[top_high]),
    )?;
    assertion_support::assert_ordered_walks(
        "intermediate stance sort precedes swing-count fallback",
        fixture_support::walk(&[&[swing_a, swing_b], &[swing_c, swing_d]], &[mid_low]),
        fixture_support::walk(&[&[swing_a, swing_b], &[swing_c, swing_d]], &[mid_high]),
    )?;
    assertion_support::assert_ordered_walks(
        "swing count precedes destination-to-source fallback",
        fixture_support::walk(&[&[swing_f], &[swing_d, swing_e]], &[top_low]),
        fixture_support::walk(&[&[swing_a], &[swing_b], &[swing_a, swing_b]], &[
            top_low, top_high,
        ]),
    )?;
    assertion_support::assert_ordered_walks(
        "fallback is destination-to-source rather than source-to-destination",
        fixture_support::walk(&[&[swing_f], &[swing_a, swing_b]], &[top_low]),
        fixture_support::walk(&[&[swing_a], &[swing_c, swing_d]], &[top_low]),
    )?;

    // Bottom stance is unobservable for a retained non-equality row: the
    // destination-adjacent swing must be nonzero, so no following stance can
    // witness the bottom summary in a public valid walk.
    Ok(())
}
#[test]
fn query_orientation_filters_direct_rows() -> Result<(), Box<dyn Error>>
{
    let l = End::Node(st(1_u8, 1_u64));
    let r = End::Node(st(2_u8, 2_u64));
    let eq_walk = fixture_support::walk(&[&[fixture_support::nt(1_u8, 0_u8, 1_u64)]], &[]);
    let neq_walk = fixture_support::walk(
        &[&[
            fixture_support::nt(1_u8, 0_u8, 1_u64),
            fixture_support::nt(2_u8, 0_u8, 2_u64),
        ]],
        &[],
    );
    let right_walk = fixture_support::walk(
        &[&[
            fixture_support::nt(3_u8, 0_u8, 3_u64),
            fixture_support::nt(4_u8, 0_u8, 4_u64),
        ]],
        &[],
    );
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(5))?;
    spec.insert_direct(Dir::Left, l.clone(), r.clone(), eq_walk.clone());
    spec.insert_direct(Dir::Left, l.clone(), r.clone(), neq_walk.clone());
    spec.insert_direct(Dir::Right, r.clone(), l.clone(), right_walk.clone());
    let index = WalkIndex::build(&spec)?;
    assert_eq!(core::slice::from_ref(&eq_walk), index.eq(&l, &r));
    assert!(index.eq(&r, &l).is_empty());
    assert_eq!(core::slice::from_ref(&neq_walk), index.lt(&l, &r));
    assert!(index.lt(&r, &l).is_empty());
    assert_eq!(core::slice::from_ref(&right_walk), index.gt(&l, &r));
    assert!(index.gt(&r, &l).is_empty());
    Ok(())
}
#[test]
fn direct_rows_reject_nonzero_prefix_with_zero_height_final_swing() -> Result<(), Box<dyn Error>>
{
    let src = End::Node(st(1_u8, 1_u64));
    let dst = End::Node(st(2_u8, 2_u64));
    let valid = fixture_support::walk(
        &[&[fixture_support::nt(1_u8, 0_u8, 1_u64)], &[
            fixture_support::nt(2_u8, 0_u8, 2_u64),
            fixture_support::nt(3_u8, 0_u8, 3_u64),
        ]],
        &[st(9_u8, 9_u64)],
    );
    let invalid = fixture_support::walk(
        &[
            &[
                fixture_support::nt(4_u8, 0_u8, 4_u64),
                fixture_support::nt(5_u8, 0_u8, 5_u64),
            ],
            &[fixture_support::nt(6_u8, 0_u8, 6_u64)],
        ],
        &[st(8_u8, 8_u64)],
    );
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(3))?;
    spec.insert_direct(Dir::Left, src.clone(), dst.clone(), invalid);
    spec.insert_direct(Dir::Left, src.clone(), dst.clone(), valid.clone());

    let index = WalkIndex::build(&spec)?;
    assert_eq!(
        core::slice::from_ref(&valid),
        index.walks(Dir::Left, &src, &dst),
        "walks should omit non-equality candidates whose final swing has zero height"
    );
    assert_eq!(
        &[valid],
        index.lt(&src, &dst),
        "lt should expose only retained non-equality rows with a nonzero final swing"
    );
    Ok(())
}
/// Fixture constructors for nonterminals, molded stances and walks.
mod fixture_support
{
    use super::*;

    /// Builds a nonterminal.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn nt<S, B, K>(
        sort: S,
        bounds: B,
        key: K,
    ) -> Nt
    where
        S: Into<TestSort>,
        B: Into<TestBounds>,
        K: Into<TestKey>,
    {
        Nt {
            sort: sort.into(),
            bounds: bounds.into(),
            key: key.into(),
        }
    }

    /// Builds a molded tile stance.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn mold_st<S, K, L, M>(
        sort: S,
        key: K,
        label: L,
        mold: M,
    ) -> St
    where
        S: Into<TestSort>,
        K: Into<TestKey>,
        L: Into<TestLabel>,
        M: Into<TestMold>,
    {
        St {
            sort: sort.into(),
            key: key.into(),
            tile: true,
            label: Some(label.into()),
            mold: Some(mold.into()),
        }
    }

    /// Builds a walk from its swings and stances.
    ///
    /// # Specification
    /// - requires: every swing is nonempty, and their count is one more than
    ///   the stance count.
    /// - ensures: returns the walk.
    /// - panics: when the shape does not alternate, which is a fixture defect.
    ///
    /// # Adequacy
    /// - hypothesis: For nonempty alternating fixture parts, L3 exact key
    ///   sequences distinguish dropped swings, reversed symbols and misplaced
    ///   stances. The predicate checks the entire borrowed sequence; malformed
    ///   fixture inputs are precondition violations, not grammar inputs.
    /// - witness: `tests::walk::construction_guards_refuse_malformed_shapes`
    /// - witness: `tests::walk::figure_33_fragments_are_literate_external_oracle`
    #[spec(requires: !swings.is_empty() && swings.iter().all(|swing| !swing.is_empty()) && stances.len().checked_add(1) == Some(swings.len()), ensures: |ref result| result.swings().iter().map(Swing::nonterminals).eq(swings.iter().copied()) && result.stances() == stances)]
    pub(super) fn walk(
        swings: &[&[Nt]],
        stances: &[St],
    ) -> Walk<Nt, St>
    {
        Walk::new(
            swings.iter().map(|items| swing(items)).collect(),
            stances.to_vec(),
        )
        .expect("test walks are alternating")
    }
}
#[test]
fn cyclic_outer_closure_terminates_and_cap_errors_are_typed() -> Result<(), Box<dyn Error>>
{
    let a = End::Node(st(1_u8, 1_u64));
    let b = End::Node(st(2_u8, 2_u64));
    let c = End::Node(st(3_u8, 3_u64));
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(9))?;
    spec.insert_direct(
        Dir::Left,
        a.clone(),
        b.clone(),
        fixture_support::walk(&[&[fixture_support::nt(1_u8, 0_u8, 1_u64)]], &[]),
    );
    spec.insert_direct(
        Dir::Left,
        b.clone(),
        a.clone(),
        fixture_support::walk(&[&[fixture_support::nt(2_u8, 0_u8, 2_u64)]], &[]),
    );
    spec.insert_direct(
        Dir::Right,
        b.clone(),
        c.clone(),
        fixture_support::walk(&[&[fixture_support::nt(3_u8, 0_u8, 3_u64)]], &[]),
    );
    spec.insert_direct(
        Dir::Right,
        c.clone(),
        b.clone(),
        fixture_support::walk(&[&[fixture_support::nt(4_u8, 0_u8, 4_u64)]], &[]),
    );
    let index = WalkIndex::build(&spec)?;
    for dir in [Dir::Left, Dir::Right] {
        let mut direction_row_count = 0_usize;
        for src in [&a, &b, &c] {
            for dst in [&a, &b, &c] {
                direction_row_count = direction_row_count
                    .checked_add(index.walks(dir, src, dst).len())
                    .ok_or(WalkBuildError::ArithmeticOverflow)?;
            }
        }
        assert!(
            direction_row_count >= 2,
            "each cyclic direction should retain at least its direct rows"
        );
    }

    let mut generated_cap = WalkSpec::<Sym>::new(WalkChainLength::from(1))?;
    generated_cap.insert_direct(
        Dir::Left,
        a.clone(),
        b.clone(),
        fixture_support::walk(&[&[fixture_support::nt(5_u8, 0_u8, 5_u64)]], &[]),
    );
    generated_cap.insert_direct(
        Dir::Left,
        b.clone(),
        c,
        fixture_support::walk(&[&[fixture_support::nt(6_u8, 0_u8, 6_u64)]], &[]),
    );
    assert!(
        matches!(
            WalkIndex::build(&generated_cap),
            Err(WalkBuildError::ChainLengthExceeded { max, actual }) if max == WalkChainLength::from(1) && actual == WalkChainLength::from(3)
        ),
        "generated a -> b -> c paths must enforce the cap after composing two direct chain-length-1 rows"
    );

    let mut capped = WalkSpec::<Sym>::new(WalkChainLength::from(1))?;
    capped.insert_direct(
        Dir::Left,
        a,
        b,
        fixture_support::walk(
            &[&[fixture_support::nt(1_u8, 0_u8, 1_u64)], &[
                fixture_support::nt(2_u8, 0_u8, 2_u64),
            ]],
            &[st(9_u8, 9_u64)],
        ),
    );
    assert!(
        matches!(
            WalkIndex::build(&capped),
            Err(WalkBuildError::ChainLengthExceeded { max, actual }) if max == WalkChainLength::from(1) && actual == WalkChainLength::from(3)
        ),
        "direct rows must enforce the cap before indexing"
    );
    Ok(())
}
#[test]
fn seen_key_verdicts_separate_safe_and_legacy_closure() -> Result<(), Box<dyn Error>>
{
    const DIVERGENT_START_KEY: u64 = 71;
    const DIVERGENT_ALIAS_KEY: u64 = 72;
    const DIVERGENT_NEXT_KEY: u64 = 81;
    const DIVERGENT_EMIT_KEY: u64 = 91;

    let mut equivalent = WalkSpec::<Sym>::new(WalkChainLength::from(5))?;
    equivalent.insert_swing_seed(Dir::Left, End::Root, fixture_support::nt(1_u8, 0_u8, 1_u64));
    let equivalent_arc = SwingArc::new(
        fixture_support::nt(1_u8, 0_u8, 1_u64),
        SwingAdvance::Extend(fixture_support::nt(2_u8, 0_u8, 2_u64)),
        Some(End::Node(st(2_u8, 2_u64))),
        None,
    )?;
    equivalent.insert_swing_arc(equivalent_arc);
    let equivalent_verdict = WalkIndex::compare_seen_keys(&equivalent)?;
    assert_eq!(SeenKeyVerdict::Equivalent, equivalent_verdict);

    let mut divergent = WalkSpec::<Sym>::new(WalkChainLength::from(5))?;
    divergent.insert_swing_seed(
        Dir::Left,
        End::Root,
        fixture_support::nt(7_u8, 1_u8, DIVERGENT_START_KEY),
    );

    let divergent_alias_arc = SwingArc::new(
        fixture_support::nt(7_u8, 1_u8, DIVERGENT_START_KEY),
        SwingAdvance::Stay,
        None,
        Some(fixture_support::nt(7_u8, 2_u8, DIVERGENT_ALIAS_KEY)),
    )?;
    divergent.insert_swing_arc(divergent_alias_arc);

    let divergent_next_arc = SwingArc::new(
        fixture_support::nt(7_u8, 2_u8, DIVERGENT_ALIAS_KEY),
        SwingAdvance::Stay,
        None,
        Some(fixture_support::nt(8_u8, 1_u8, DIVERGENT_NEXT_KEY)),
    )?;
    divergent.insert_swing_arc(divergent_next_arc);

    let divergent_emit_arc = SwingArc::new(
        fixture_support::nt(8_u8, 1_u8, DIVERGENT_NEXT_KEY),
        SwingAdvance::Extend(fixture_support::nt(9_u8, 1_u8, DIVERGENT_EMIT_KEY)),
        Some(End::Node(st(9_u8, 9_u64))),
        None,
    )?;
    divergent.insert_swing_arc(divergent_emit_arc);
    let divergent_verdict = WalkIndex::compare_seen_keys(&divergent)?;
    assert_eq!(SeenKeyVerdict::Divergent, divergent_verdict);
    Ok(())
}
#[test]
fn same_sort_bounds_different_identity_continuation_is_suppressed() -> Result<(), Box<dyn Error>>
{
    const START_KEY: u64 = 401;
    const ALIAS_KEY: u64 = 402;
    const AFTER_ALIAS_KEY: u64 = 501;
    const EMITTED_KEY: u64 = 601;

    let start = fixture_support::nt(4_u8, 7_u8, START_KEY);
    let alias = fixture_support::nt(4_u8, 7_u8, ALIAS_KEY);
    let after_alias = fixture_support::nt(5_u8, 8_u8, AFTER_ALIAS_KEY);
    let emitted = fixture_support::nt(6_u8, 9_u8, EMITTED_KEY);
    let dst = End::Node(st(6_u8, 6_u64));
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(5))?;
    spec.insert_swing_seed(Dir::Left, End::Root, start);
    let alias_arc = SwingArc::new(start, SwingAdvance::Stay, None, Some(alias))?;
    spec.insert_swing_arc(alias_arc);
    let after_alias_arc = SwingArc::new(alias, SwingAdvance::Stay, None, Some(after_alias))?;
    spec.insert_swing_arc(after_alias_arc);
    let emitted_arc = SwingArc::new(
        after_alias,
        SwingAdvance::Extend(emitted),
        Some(dst.clone()),
        None,
    )?;
    spec.insert_swing_arc(emitted_arc);

    let verdict = WalkIndex::compare_seen_keys(&spec)?;
    assert_eq!(
        SeenKeyVerdict::Equivalent,
        verdict,
        "sort+bounds and legacy sort-only seen keys should both suppress the alias continuation"
    );
    let index = WalkIndex::build(&spec)?;
    assert!(
        index.walks(Dir::Left, &End::Root, &dst).is_empty(),
        "no row should emit unless the seen key incorrectly includes identity"
    );
    Ok(())
}
#[test]
fn insertion_permutation_duplicate_canonicalization_and_fingerprint_are_stable()
-> Result<(), Box<dyn Error>>
{
    let a = End::Node(st(1_u8, 1_u64));
    let b = End::Node(st(2_u8, 2_u64));
    let c = End::Node(st(3_u8, 3_u64));
    let w_ab = fixture_support::walk(&[&[fixture_support::nt(1_u8, 0_u8, 1_u64)]], &[]);
    let w_bc = fixture_support::walk(&[&[fixture_support::nt(2_u8, 0_u8, 2_u64)]], &[]);
    let mut first = WalkSpec::<Sym>::new(WalkChainLength::from(7))?;
    first.insert_direct(Dir::Left, a.clone(), b.clone(), w_ab.clone());
    first.insert_direct(Dir::Left, a.clone(), b.clone(), w_ab.clone());
    first.insert_direct(Dir::Left, b.clone(), c.clone(), w_bc.clone());
    let mut second = WalkSpec::<Sym>::new(WalkChainLength::from(7))?;
    second.insert_direct(Dir::Left, b.clone(), c.clone(), w_bc);
    second.insert_direct(Dir::Left, a.clone(), b, w_ab);
    let left = WalkIndex::build(&first)?;
    let right = WalkIndex::build(&second)?;
    let composed = left.walks(Dir::Left, &a, &c);
    assert_eq!(
        1,
        composed.len(),
        "permutation fixture should materialize exactly one composed a -> c walk"
    );
    assert_eq!(
        shape(&composed[0]),
        (vec![vec![1], vec![2]], vec![2]),
        "composed a -> c walk should pass through b with the expected nonempty alternating shape"
    );
    assert_eq!(
        composed,
        right.walks(Dir::Left, &a, &c),
        "permuted insertion should preserve the exact composed a -> c row"
    );
    assert_eq!(
        left.fingerprint(),
        right.fingerprint(),
        "permuted insertion should not change the fixture fingerprint"
    );
    Ok(())
}
#[test]
fn converged_equality_prefixes_all_expand_through_shared_endpoint() -> Result<(), Box<dyn Error>>
{
    let a = End::Node(st(1_u8, 1_u64));
    let b = End::Node(st(2_u8, 2_u64));
    let c = End::Node(st(3_u8, 3_u64));
    let ab_first = fixture_support::walk(&[&[fixture_support::nt(1_u8, 0_u8, 1_u64)]], &[]);
    let ab_second = fixture_support::walk(&[&[fixture_support::nt(2_u8, 0_u8, 2_u64)]], &[]);
    let bc = fixture_support::walk(&[&[fixture_support::nt(3_u8, 0_u8, 3_u64)]], &[]);
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(5))?;
    spec.insert_direct(Dir::Left, a.clone(), b.clone(), ab_second);
    spec.insert_direct(Dir::Left, a.clone(), b.clone(), ab_first);
    spec.insert_direct(Dir::Left, b, c.clone(), bc);

    let index = WalkIndex::build(&spec)?;
    let rows: Vec<_> = index.walks(Dir::Left, &a, &c).iter().map(shape).collect();
    assert_eq!(
        rows,
        vec![
            (vec![vec![1], vec![3]], vec![2]),
            (vec![vec![2], vec![3]], vec![2]),
        ],
        "each distinct all-equality prefix converging at b should compose with b -> c"
    );
    Ok(())
}
#[test]
fn molds_projection_is_reachable_canonical_and_label_indexed() -> Result<(), Box<dyn Error>>
{
    const MOLD_B_STANCE: u8 = 11;
    const OTHER_MOLD_STANCE: u8 = 12;
    const UNREACHABLE_MOLD_STANCE: u8 = 13;

    let root_entry = fixture_support::nt(1_u8, 0_u8, 1_u64);
    let bridge = End::Node(st(9_u8, 9_u64));
    let mold_a = End::Node(fixture_support::mold_st(10_u8, 10_u64, 7_u8, 1_u8));
    let mold_b = End::Node(fixture_support::mold_st(
        MOLD_B_STANCE,
        u64::from(MOLD_B_STANCE),
        7_u8,
        2_u8,
    ));
    let other = End::Node(fixture_support::mold_st(
        OTHER_MOLD_STANCE,
        u64::from(OTHER_MOLD_STANCE),
        8_u8,
        3_u8,
    ));
    let unreachable = End::Node(fixture_support::mold_st(
        UNREACHABLE_MOLD_STANCE,
        u64::from(UNREACHABLE_MOLD_STANCE),
        7_u8,
        9_u8,
    ));
    let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(5))?;
    spec.set_root_entry(root_entry);
    spec.insert_direct(
        Dir::Left,
        End::Root,
        bridge.clone(),
        fixture_support::walk(&[&[root_entry]], &[]),
    );
    spec.insert_direct(
        Dir::Left,
        bridge.clone(),
        mold_b.clone(),
        fixture_support::walk(&[&[fixture_support::nt(2_u8, 0_u8, 2_u64)]], &[]),
    );
    spec.insert_direct(
        Dir::Left,
        bridge.clone(),
        mold_a.clone(),
        fixture_support::walk(&[&[fixture_support::nt(3_u8, 0_u8, 3_u64)]], &[]),
    );
    spec.insert_direct(
        Dir::Left,
        bridge,
        other.clone(),
        fixture_support::walk(&[&[fixture_support::nt(4_u8, 0_u8, 4_u64)]], &[]),
    );
    spec.insert_end(unreachable);
    let index = WalkIndex::build(&spec)?;
    assert_eq!(
        &[(mold_a, TestMold(1)), (mold_b, TestMold(2))],
        index.molds(&TestLabel(7)),
        "transitively reachable molded endpoints should appear in canonical label order"
    );
    assert_eq!(
        &[(other, TestMold(3))],
        index.molds(&TestLabel(8)),
        "transitively reachable endpoints for other labels should remain indexed"
    );
    assert!(
        index.molds(&TestLabel(99)).is_empty(),
        "unreachable labels should have no mold projection rows"
    );
    Ok(())
}
/// Builds a stance that is neither tile-sorted nor molded.
///
/// # Specification
/// trivial.
fn st<S, K>(
    sort: S,
    key: K,
) -> St
where
    S: Into<TestSort>,
    K: Into<TestKey>,
{
    St {
        sort: sort.into(),
        key: key.into(),
        tile: false,
        label: None,
        mold: None,
    }
}

/// The assertion that two walks in one row come back in a given order.
mod assertion_support
{
    use super::*;

    /// Asserts that the canonical order puts `expected_first` before
    /// `expected_second`, inserting them in the opposite order.
    ///
    /// # Specification
    /// - requires: both walks are minimal inequalities with distinct canonical
    ///   keys and alternating lengths at most nine.
    /// - ensures: returns only when the transitive row and the less projection
    ///   both list the two walks in the expected order.
    /// - panics: when either list differs, naming the case.
    ///
    /// # Adequacy
    /// - hypothesis: For independently ordered inequality pairs and
    ///   deliberately reversed evidence, L3 acceptance or assertion failure
    ///   distinguishes a disabled observer and a reversed expected order. The
    ///   predicate checks inequality shape, distinct walks and the fixture cap;
    ///   canonical-key distinctness and minimality remain caller obligations.
    /// - witness: `tests::walk::canonical_order_keys_are_isolated_pairwise_witnesses`
    /// - witness: `tests::walk::ordered_observer_refuses_reversed_evidence`
    #[spec(requires: expected_first != expected_second && [&expected_first, &expected_second].into_iter().all(|walk| walk.is_neq().is_ok_and(bool::from) && walk.chain_len().is_ok_and(|length| u32::from(length) <= 9)))]
    pub(super) fn assert_ordered_walks<'case, C>(
        case: C,
        expected_first: Walk<Nt, St>,
        expected_second: Walk<Nt, St>,
    ) -> Result<(), Box<dyn Error>>
    where
        C: Into<OrderCase<'case>>,
    {
        const ORDER_ASSERT_SRC: u8 = 200;
        const ORDER_ASSERT_DST: u8 = 201;

        let case = case.into();

        let src = End::Node(st(ORDER_ASSERT_SRC, u64::from(ORDER_ASSERT_SRC)));
        let dst = End::Node(st(ORDER_ASSERT_DST, u64::from(ORDER_ASSERT_DST)));
        let expected_shapes = vec![shape(&expected_first), shape(&expected_second)];
        let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(9))?;
        spec.insert_direct(Dir::Left, src.clone(), dst.clone(), expected_second);
        spec.insert_direct(Dir::Left, src.clone(), dst.clone(), expected_first);

        let index = WalkIndex::build(&spec)?;
        let rows: Vec<_> = index
            .walks(Dir::Left, &src, &dst)
            .iter()
            .map(shape)
            .collect();
        assert_eq!(
            rows, expected_shapes,
            "{case}: canonical order should reject the targeted broken comparator"
        );
        let lt_rows: Vec<_> = index.lt(&src, &dst).iter().map(shape).collect();
        assert_eq!(
            lt_rows, expected_shapes,
            "{case}: lt projection should preserve canonical direct row order"
        );
        Ok(())
    }
}

/// Reads a walk back as its symbols' keys.
///
/// # Specification
/// - requires: nothing.
/// - ensures: preserves swing boundaries and symbol order while projecting
///   keys.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For hand-written walk shapes, L3 literal key sequences
///   distinguish flattening swings, reversing traversal and dropping stance
///   keys. The predicate compares each borrowed projection; it does not assert
///   that distinct symbols always have distinct keys.
/// - witness: `tests::walk::construction_guards_refuse_malformed_shapes`
/// - witness: `tests::walk::figure_33_fragments_are_literate_external_oracle`
#[spec(ensures: |ref result| result.swings.len() == walk.swings().len() && result.swings.iter().zip(walk.swings()).all(|(keys, swing)| keys.iter().copied().eq(swing.nonterminals().iter().map(|nt| nt.key.0))) && result.stances.iter().copied().eq(walk.stances().iter().map(|stance| stance.key.0)))]
fn shape(walk: &Walk<Nt, St>) -> WalkShape
{
    WalkShape {
        swings: walk
            .swings()
            .iter()
            .map(|swing| swing.nonterminals().iter().map(|nt| nt.key.0).collect())
            .collect(),
        stances: walk.stances().iter().map(|stance| stance.key.0).collect(),
    }
}

/// Builds a tile-sorted stance without a mold.
///
/// # Specification
/// trivial.
fn tile<S, K>(
    sort: S,
    key: K,
) -> St
where
    S: Into<TestSort>,
    K: Into<TestKey>,
{
    St {
        sort: sort.into(),
        key: key.into(),
        tile: true,
        label: None,
        mold: None,
    }
}

/// Builds a swing.
///
/// # Specification
/// - requires: `nonterminals` is non-empty.
/// - ensures: returns the swing.
/// - panics: on an empty swing, which is a fixture defect.
///
/// # Adequacy
/// - hypothesis: For nonempty singleton and rising symbol sequences, L3 literal
///   walk shapes distinguish lost or reordered symbols. The predicate checks
///   the full borrowed payload; empty fixture slices are outside the admitted
///   domain.
/// - witness: `tests::walk::construction_guards_refuse_malformed_shapes`
/// - witness: `tests::walk::figure_33_fragments_are_literate_external_oracle`
#[spec(requires: !nonterminals.is_empty(), ensures: |ref result| result.nonterminals() == nonterminals)]
fn swing(nonterminals: &[Nt]) -> Swing<Nt>
{
    Swing::new(nonterminals.to_vec()).expect("test swings are non-empty")
}

proptest! {
    #[test]
    fn small_chain_keyings_agree_under_permuted_insertion(length in 1_u8..5) {
        let mut forward = WalkSpec::<Sym>::new(WalkChainLength::from(9)).expect("positive cap");
        forward.insert_swing_seed(Dir::Left, End::Root, fixture_support::nt(1_u8,  1_u8,  1_u64));
        for i in 1..=length {
            let current = fixture_support::nt(i,  i,  u64::from(i));
            let next = fixture_support::nt(i.saturating_add(1),  i.saturating_add(1),  u64::from(i.saturating_add(1)));
            forward.insert_swing_arc(SwingArc::new(
                current,
                SwingAdvance::Extend(next),
                Some(End::Node(st(i,  u64::from(i)))),
                Some(next),
            ).expect("arc emits"));
        }
        let mut reverse = WalkSpec::<Sym>::new(WalkChainLength::from(9)).expect("positive cap");
        reverse.insert_swing_seed(Dir::Left, End::Root, fixture_support::nt(1_u8,  1_u8,  1_u64));
        for i in (1..=length).rev() {
            let current = fixture_support::nt(i,  i,  u64::from(i));
            let next = fixture_support::nt(i.saturating_add(1),  i.saturating_add(1),  u64::from(i.saturating_add(1)));
            reverse.insert_swing_arc(SwingArc::new(
                current,
                SwingAdvance::Extend(next),
                Some(End::Node(st(i,  u64::from(i)))),
                Some(next),
            ).expect("arc emits"));
        }
        prop_assert_eq!(SeenKeyVerdict::Equivalent, WalkIndex::compare_seen_keys(&forward).expect("builds"));
        let a = WalkIndex::build(&forward).expect("forward builds");
        let b = WalkIndex::build(&reverse).expect("reverse builds");
        prop_assert_eq!(a.walks(Dir::Left, &End::Root, &End::Node(st(length,  u64::from(length)))), b.walks(Dir::Left, &End::Root, &End::Node(st(length,  u64::from(length)))));
        prop_assert_eq!(a.fingerprint(), b.fingerprint());
    }
}

#[test]
#[cfg(target_pointer_width = "64")]
fn zero_sized_shapes_preserve_overflow_and_short_circuit_boundaries() -> Result<(), Box<dyn Error>>
{
    let oversized_count = usize::try_from(u32::MAX)?
        .checked_add(1)
        .ok_or(WalkBuildError::ArithmeticOverflow)?;
    let oversized = Swing::new(vec![(); oversized_count])?;
    assert_eq!(oversized.height(), Err(WalkBuildError::ArithmeticOverflow));
    let walk = Walk::<(), ()>::new(vec![oversized], vec![])?;
    assert_eq!(
        walk.is_eq().map(bool::from),
        Err(WalkBuildError::ArithmeticOverflow)
    );
    assert_eq!(
        walk.is_neq().map(bool::from),
        Err(WalkBuildError::ArithmeticOverflow)
    );
    assert_eq!(walk.height(), Err(WalkBuildError::ArithmeticOverflow));
    assert_eq!(walk.chain_len().map(u32::from), Ok(1));
    let prefix = Walk::new(
        vec![
            Swing::new(vec![(); 2])?,
            Swing::new(vec![(); oversized_count])?,
        ],
        vec![()],
    )?;
    assert_eq!(prefix.is_eq().map(bool::from), Ok(false));
    assert_eq!(
        prefix.is_neq().map(bool::from),
        Err(WalkBuildError::ArithmeticOverflow)
    );
    assert_eq!(prefix.chain_len().map(u32::from), Ok(3));
    assert_eq!(
        Walk::<(), ()>::new(vec![], vec![(); usize::MAX]),
        Err(WalkBuildError::InvalidWalkShape)
    );
    assert_eq!(
        Walk::new(vec![Swing::new(vec![()])?], vec![(); usize::MAX]),
        Err(WalkBuildError::ArithmeticOverflow)
    );
    Ok(())
}

#[test]
fn empty_machine_preserves_root_and_empty_projections() -> Result<(), Box<dyn Error>>
{
    let spec = WalkSpec::<Sym>::new(WalkChainLength::from(1))?;
    let index = WalkIndex::build(&spec)?;
    let absent = End::Node(st(1_u8, 1_u64));
    assert_eq!(index.ends(), &[End::Root]);
    assert_eq!(
        WalkIndex::compare_seen_keys(&spec)?,
        SeenKeyVerdict::Equivalent
    );
    for dir in [Dir::Left, Dir::Right] {
        assert!(index.walks(dir, &End::Root, &End::Root).is_empty());
        assert!(index.walks(dir, &End::Root, &absent).is_empty());
    }
    assert!(index.eq(&End::Root, &End::Root).is_empty());
    assert!(index.lt(&End::Root, &absent).is_empty());
    assert!(index.gt(&absent, &End::Root).is_empty());
    assert!(index.molds(&TestLabel(1)).is_empty());
    assert_eq!(u64::from(index.fingerprint()), 0xc749_02ca_177d_edaf_u64);
    Ok(())
}

#[test]
fn fingerprint_matches_independently_framed_directional_machines() -> Result<(), Box<dyn Error>>
{
    // The digests frame the documented words directly, independently of the
    // accumulator helpers.
    for (dir, expected) in [
        (Dir::Left, 0x10b3_bc21_fc87_fcd1_u64),
        (Dir::Right, 0x3df8_3d0e_b32f_2121_u64),
    ] {
        let a = fixture_support::nt(1_u8, 0_u8, 0x0102_0304_0506_0708_u64);
        let b = fixture_support::nt(2_u8, 0_u8, 0x1112_1314_1516_1718_u64);
        let c = fixture_support::nt(3_u8, 0_u8, 0x2122_2324_2526_2728_u64);
        let middle = st(4_u8, 0x3132_3334_3536_3738_u64);
        let dst = End::Node(fixture_support::mold_st(
            5_u8,
            0x4142_4344_4546_4748_u64,
            7_u8,
            11_u8,
        ));
        let mut spec = WalkSpec::<Sym>::new(WalkChainLength::from(3))?;
        spec.set_root_entry(a);
        spec.insert_direct(
            dir,
            End::Root,
            dst,
            fixture_support::walk(&[&[a], &[b, c]], &[middle]),
        );
        assert_eq!(u64::from(WalkIndex::build(&spec)?.fingerprint()), expected);
    }
    Ok(())
}

#[test]
fn ordered_observer_refuses_reversed_evidence()
{
    let a = fixture_support::nt(1_u8, 0_u8, 1_u64);
    let b = fixture_support::nt(2_u8, 0_u8, 2_u64);
    let lower = fixture_support::walk(&[&[a, b]], &[]);
    let higher = fixture_support::walk(&[&[a, b], &[a, b]], &[st(3_u8, 3_u64)]);
    assert!(
        std::panic::catch_unwind(|| assertion_support::assert_ordered_walks(
            "reversed evidence",
            higher,
            lower
        ))
        .is_err()
    );
}
