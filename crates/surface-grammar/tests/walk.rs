//! The mold table and the walk index over the built-in surface and two
//! synthetic grammars: the pinned inventory and fingerprint, lookups and
//! their bounds, the form-membership answers, the walk projection, and the
//! comparison table's coherence with the precedence DAG.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::error::Error;

use gandr_surface_grammar::Comparison;
use gandr_surface_grammar::MAX_WALK_CHAIN_LEN;
use gandr_surface_grammar::MoldCount;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::PrecName;
use gandr_surface_grammar::Regex;
use gandr_surface_grammar::Rule;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::StepSym;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::built_in;
use gandr_surface_grammar::comparison_table;
use gandr_surface_grammar::reachable_molds;
use gandr_surface_grammar::seen_key_verdict;
use gandr_surface_grammar::walk_index;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::MoldId;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::Bound;
use gandr_theory_graphs::Dir;
use gandr_theory_graphs::End;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecSpec;
use gandr_theory_graphs::SeenKeyVerdict;
use gandr_theory_graphs::WalkChainLength;

/// The built-in surface's fingerprint: the precedence DAG folded with every
/// mold and context. Any change to a form, a tile occurrence or a precedence
/// group moves it; a deliberate change re-pins it and says why.
const BUILT_IN_FINGERPRINT: u64 = 0x6a74_f2ef_1d8a_5c07;

/// The built-in surface's mold count: one mold per tile occurrence, so a form
/// inlined at many sites (the statement alternation, inlined at every block
/// position) costs one copy per site, while a form reached through a hole of
/// its own sort (a nested module's members) costs nothing per level.
const BUILT_IN_MOLD_COUNT: MoldCount = MoldCount(2364);

/// How many labels the walk index projects to more than one mold.
const BUILT_IN_MULTI_MOLD_LABELS: usize = 77;

/// The built-in surface's molds per label, ascending by label.
const DECLARED_CANDIDATE_INVENTORY: &[(&str, usize)] = &[
    ("!", 21),
    ("!=", 1),
    ("\"", 16),
    ("#!{", 1),
    ("#{", 7),
    ("$", 3),
    ("${", 3),
    ("&", 3),
    ("&&", 2),
    ("'", 2),
    ("(", 183),
    (")", 186),
    ("*", 2),
    ("*/", 1),
    ("+", 3),
    ("++", 1),
    (",", 100),
    ("-", 2),
    ("-->", 24),
    ("->", 15),
    (".", 7),
    ("..", 3),
    ("/*", 1),
    ("/\\", 1),
    (":", 235),
    (":>", 2),
    (";", 224),
    ("<", 4),
    ("<&", 1),
    ("<-", 20),
    ("<->", 22),
    ("<=", 1),
    ("<=>", 22),
    ("<>", 1),
    ("=", 82),
    ("==", 1),
    ("==>", 26),
    ("=>", 8),
    (">", 3),
    (">&", 1),
    (">=", 1),
    (">>", 1),
    ("?", 4),
    ("@[", 7),
    ("Any", 1),
    ("Boolean", 1),
    ("Char", 1),
    ("F", 1),
    ("Integer", 1),
    ("Never", 1),
    ("Path", 1),
    ("String", 1),
    ("Symbol", 1),
    ("U", 1),
    ("Unit", 1),
    ("Unknown", 1),
    ("Void", 1),
    ("[", 13),
    ("]", 20),
    ("_", 43),
    ("acquire", 20),
    ("as", 83),
    ("at", 1),
    ("block_comment", 1),
    ("block_comment_content", 1),
    ("break", 1),
    ("case", 1),
    ("character", 1),
    ("close", 1),
    ("co", 1),
    ("codata", 1),
    ("command_substitution_start", 1),
    ("constructor", 6),
    ("continue", 1),
    ("data", 12),
    ("def", 5),
    ("double_string_fragment", 1),
    ("drop", 1),
    ("dup", 1),
    ("else", 2),
    ("end", 1),
    ("environment_assignment", 1),
    ("escape_sequence", 9),
    ("extern", 1),
    ("f32", 1),
    ("f64", 1),
    ("false", 3),
    ("feed", 3),
    ("file_descriptor", 1),
    ("fn", 1),
    ("for", 1),
    ("forall", 1),
    ("force", 1),
    ("fork", 40),
    ("from", 1),
    ("glob", 1),
    ("hold", 1),
    ("hole_name", 2),
    ("i32", 1),
    ("i64", 1),
    ("identifier", 351),
    ("if", 2),
    ("import", 1),
    ("in", 1),
    ("infix", 1),
    ("infixl", 1),
    ("infixr", 1),
    ("leta", 20),
    ("line_comment", 1),
    ("list_operator", 3),
    ("loop", 1),
    ("migrate", 1),
    ("module", 2),
    ("mu", 1),
    ("negation", 1),
    ("newline", 1),
    ("node", 3),
    ("number", 21),
    ("offer", 1),
    ("op", 3),
    ("oper", 6),
    ("pack", 1),
    ("package", 1),
    ("pipeline_operand", 2),
    ("postfix", 1),
    ("prefix", 1),
    ("rec", 2),
    ("recv", 20),
    ("release", 20),
    ("ret", 1),
    ("rule", 16),
    ("run", 20),
    ("select", 1),
    ("send", 1),
    ("shebang", 1),
    ("shell_and", 2),
    ("shell_list", 1),
    ("shell_or", 2),
    ("shell_word", 1),
    ("sign", 1),
    ("single_quoted_content", 1),
    ("sort", 1),
    ("string_fragment", 7),
    ("subshell_close", 1),
    ("subshell_open", 1),
    ("tail", 1),
    ("then", 1),
    ("thunk", 1),
    ("true", 3),
    ("type", 9),
    ("type_identifier", 47),
    ("type_variable", 53),
    ("typed_number", 3),
    ("u32", 1),
    ("u64", 1),
    ("unpack", 20),
    ("val", 20),
    ("variable_name", 5),
    ("while", 1),
    ("with", 1),
    ("{", 35),
    ("|", 4),
    ("|&", 1),
    ("||", 2),
    ("}", 49),
    ("~>", 4),
    ("ω", 16),
];

/// A grammar of one group, with the infix form `E + E` and the atom `x`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the grammar and its one group, named `group`.
/// - fails: never for these rules.
/// - panics: none.
fn synthetic_pbg(group: PrecName) -> Result<(Pbg, Prec), Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let base = spec.insert(group.0, Assoc::Non)?;
    let dag = PrecDag::build(&spec)?;
    let pbg = Pbg::build(dag, vec![
        Rule::new(
            RuleName("infix"),
            Sort::Expression,
            base,
            Regex::seq([
                Regex::sort(Sort::Expression),
                Regex::tile(TileLabel("+")),
                Regex::sort(Sort::Expression),
            ]),
        ),
        Rule::new(
            RuleName("atom"),
            Sort::Expression,
            base,
            Regex::tile(TileLabel("x")),
        ),
    ])?;
    Ok((pbg, base))
}

/// A grammar of one group, with the bracket form `( E )` and the atom `x`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the grammar.
/// - fails: never for these rules.
/// - panics: none.
fn paren_pbg() -> Result<Pbg, Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let base = spec.insert("base", Assoc::Non)?;
    let dag = PrecDag::build(&spec)?;
    let pbg = Pbg::build(dag, vec![
        Rule::new(
            RuleName("group"),
            Sort::Expression,
            base,
            Regex::seq([
                Regex::tile(TileLabel("(")),
                Regex::sort(Sort::Expression),
                Regex::tile(TileLabel(")")),
            ]),
        ),
        Rule::new(
            RuleName("atom"),
            Sort::Expression,
            base,
            Regex::tile(TileLabel("x")),
        ),
    ])?;
    Ok(pbg)
}

/// The one mold `label` takes in `pbg`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the label's mold.
/// - panics: when the label takes no mold or more than one.
fn only_mold(
    pbg: &Pbg,
    label: TileLabel,
) -> MoldId
{
    let &[mold] = pbg.candidates(label)
    else {
        panic!("{label} takes exactly one mold");
    };
    mold
}

/// Each `(sort, precedence)` form group's representative: its smallest mold.
///
/// # Specification
/// trivial.
fn group_reps(pbg: &Pbg) -> BTreeMap<(Sort, Prec), MoldId>
{
    let mut reps: BTreeMap<(Sort, Prec), MoldId> = BTreeMap::new();
    for (id, def) in pbg.iter_molds() {
        reps.entry((def.sort, def.prec)).or_insert(id);
    }
    reps
}

#[test]
fn declared_mold_candidate_inventory_is_exact() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let counts = pbg.candidate_counts();

    assert!(
        counts.windows(2).all(|pair| match *pair {
            | [(left, _), (right, _)] => left < right,
            | _ => true,
        }),
        "the inventory is strictly ascending by label"
    );

    let observed: Vec<(&str, usize)> = counts
        .iter()
        .map(|&(label, count)| (label.0, count.0))
        .collect();
    assert_eq!(DECLARED_CANDIDATE_INVENTORY, observed.as_slice());

    let total = counts
        .iter()
        .try_fold(0_usize, |sum, &(_label, count)| sum.checked_add(count.0))
        .expect("the mold total fits");
    assert_eq!(BUILT_IN_MOLD_COUNT.0, total);
    assert_eq!(BUILT_IN_MOLD_COUNT, pbg.mold_count());
    Ok(())
}

#[test]
fn pbg_fingerprint_is_stable_and_folds_precdag() -> Result<(), Box<dyn Error>>
{
    let first = built_in()?;
    let second = built_in()?;
    assert_eq!(
        GrammarFingerprint::from(BUILT_IN_FINGERPRINT),
        first.fingerprint()
    );
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_ne!(
        GrammarFingerprint::from(u64::from(first.dag().fingerprint())),
        first.fingerprint(),
        "the grammar fingerprint folds more than the DAG"
    );

    let (named, _base) = synthetic_pbg(PrecName("base"))?;
    let (renamed, _base) = synthetic_pbg(PrecName("renamed"))?;
    assert_ne!(
        named.fingerprint(),
        renamed.fingerprint(),
        "the same rules over a renamed group fingerprint differently"
    );
    Ok(())
}

#[test]
fn mold_lookup_checks_bounds() -> Result<(), Box<dyn Error>>
{
    let (pbg, base) = synthetic_pbg(PrecName("base"))?;
    let plus = only_mold(&pbg, TileLabel("+"));
    let mold = pbg.mold(plus)?;
    assert_eq!("+", mold.label);
    assert_eq!(base, mold.prec);
    assert_eq!(Sort::Expression, mold.sort);

    let last = MoldId::try_from(pbg.mold_count().0.checked_sub(1).expect("non-empty"))?;
    assert!(pbg.mold(last).is_ok());
    let past = MoldId::try_from(pbg.mold_count().0)?;
    assert_eq!(Err(PbgError::UnknownMold { id: past }), pbg.mold(past));
    assert_eq!(Err(PbgError::UnknownMold { id: past }), pbg.bounds(past));
    Ok(())
}

#[test]
fn mold_bounds_follow_context_nullability() -> Result<(), Box<dyn Error>>
{
    let (pbg, base) = synthetic_pbg(PrecName("base"))?;
    assert_eq!(
        (Bound::Value(base), Bound::Value(base)),
        pbg.bounds(only_mold(&pbg, TileLabel("+")))?,
        "an infix operator faces a hole on both sides"
    );
    assert_eq!(
        (Bound::Root, Bound::Root),
        pbg.bounds(only_mold(&pbg, TileLabel("x")))?,
        "an atom faces a hole on neither side"
    );

    let paren = paren_pbg()?;
    let open = only_mold(&paren, TileLabel("("));
    let open_def = paren.mold(open)?;
    assert_eq!(
        (Bound::Root, Bound::Value(open_def.prec)),
        paren.bounds(open)?,
        "an opener faces its operand on the right only"
    );
    Ok(())
}

#[test]
fn rctx_steps_cross_adjacent_symbols() -> Result<(), Box<dyn Error>>
{
    let (pbg, _base) = synthetic_pbg(PrecName("base"))?;
    let plus = pbg.mold(only_mold(&pbg, TileLabel("+")))?;
    let left: Vec<StepSym> = pbg
        .step(plus.rctx, Dir::Left)?
        .iter()
        .map(|step| step.crossed)
        .collect();
    let right: Vec<StepSym> = pbg
        .step(plus.rctx, Dir::Right)?
        .iter()
        .map(|step| step.crossed)
        .collect();
    assert_eq!(vec![StepSym::Sort(Sort::Expression)], left);
    assert_eq!(vec![StepSym::Sort(Sort::Expression)], right);

    let paren = paren_pbg()?;
    let open = paren.mold(only_mold(&paren, TileLabel("(")))?;
    assert!(paren.step(open.rctx, Dir::Left)?.is_empty());
    assert_eq!(
        vec![StepSym::Sort(Sort::Expression)],
        paren
            .step(open.rctx, Dir::Right)?
            .iter()
            .map(|step| step.crossed)
            .collect::<Vec<_>>()
    );
    Ok(())
}

#[test]
fn same_form_adjacency_is_the_eq_relation() -> Result<(), Box<dyn Error>>
{
    // A bracket form yields exactly `( ≐ )`, across the hole.
    let paren = paren_pbg()?;
    let open = only_mold(&paren, TileLabel("("));
    let close = only_mold(&paren, TileLabel(")"));
    assert_eq!(&[(open, close)], paren.adjacencies());

    // A one-tile form has no same-form partner.
    let (infix, _base) = synthetic_pbg(PrecName("base"))?;
    assert!(infix.adjacencies().is_empty());

    // The comparison table's `≐` face is that pair.
    let index = walk_index(&paren)?;
    let table = comparison_table(&paren, &index);
    let equal: BTreeSet<(MoldId, MoldId)> = table
        .iter()
        .filter(|row| row.cmp == Comparison::Equal)
        .map(|row| (row.left, row.right))
        .collect();
    assert_eq!(BTreeSet::from([(open, close)]), equal);
    Ok(())
}

#[test]
fn fresh_menus_keep_exactly_the_form_openers() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let mut dropped = 0_usize;
    for (label, _count) in pbg.candidate_counts() {
        let candidates = pbg.candidates(label);
        let expected: Vec<MoldId> = candidates
            .iter()
            .copied()
            .filter(|&mold| {
                !bool::from(pbg.mold_has_predecessor(mold))
                    || bool::from(pbg.mold_is_form_first(mold))
            })
            .collect();
        assert_eq!(
            expected.as_slice(),
            pbg.fresh_candidates(label),
            "the fresh menu of {label}"
        );
        dropped = dropped
            .checked_add(
                candidates
                    .len()
                    .checked_sub(expected.len())
                    .expect("a subset"),
            )
            .expect("the drop count fits");
    }
    assert!(dropped > 0, "some mold needs an open form");
    assert!(pbg.fresh_candidates(TileLabel("no such label")).is_empty());
    Ok(())
}

#[test]
fn form_membership_flags_agree_with_their_lists() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let ascending = |molds: &[MoldId]| {
        molds.windows(2).all(|pair| match *pair {
            | [left, right] => left < right,
            | _ => true,
        })
    };
    assert!(ascending(pbg.form_first()));
    assert!(ascending(pbg.form_last()));
    assert!(pbg.adjacencies().windows(2).all(|pair| match *pair {
        | [left, right] => left < right,
        | _ => true,
    }));

    let mut required_tails = 0_usize;
    for (mold, _def) in pbg.iter_molds() {
        assert_eq!(
            pbg.adjacencies().iter().any(|&(_, right)| right == mold),
            bool::from(pbg.mold_has_predecessor(mold))
        );
        assert_eq!(
            pbg.adjacencies().iter().any(|&(left, _)| left == mold),
            bool::from(pbg.mold_has_successor(mold))
        );
        assert_eq!(
            pbg.form_first().contains(&mold),
            bool::from(pbg.mold_is_form_first(mold))
        );
        let complete = bool::from(pbg.mold_is_form_last(mold));
        let required = bool::from(pbg.mold_has_required_tail(mold));
        if pbg.form_last().contains(&mold) {
            assert!(complete != required, "mold {mold:?} ends its form one way");
        }
        else {
            assert!(!complete && !required, "mold {mold:?} cannot end its form");
        }
        if required {
            required_tails = required_tails.checked_add(1).expect("the count fits");
        }
    }
    assert!(
        required_tails > 0,
        "some form ends only once its tail is filled"
    );

    let past = MoldId::try_from(pbg.mold_count().0)?;
    assert!(!bool::from(pbg.mold_has_predecessor(past)));
    assert!(!bool::from(pbg.mold_has_successor(past)));
    assert!(!bool::from(pbg.mold_is_form_first(past)));
    assert!(!bool::from(pbg.mold_is_form_last(past)));
    assert!(!bool::from(pbg.mold_has_required_tail(past)));
    Ok(())
}

#[test]
fn walk_index_projects_every_mold_once() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let index = walk_index(&pbg)?;
    for (mold_id, def) in pbg.iter_molds() {
        let count = index
            .molds(&TileLabel(def.label))
            .iter()
            .filter(|&&(_, projected)| projected == mold_id)
            .count();
        assert_eq!(1, count, "mold {mold_id:?} of {} projects once", def.label);
    }

    let reachable = reachable_molds(&pbg, &index);
    let mut by_label: BTreeMap<TileLabel, BTreeSet<MoldId>> = BTreeMap::new();
    for (mold_id, def) in pbg.iter_molds() {
        by_label
            .entry(TileLabel(def.label))
            .or_default()
            .insert(mold_id);
    }
    assert_eq!(by_label, reachable, "the projection is the table by label");
    assert_eq!(
        BUILT_IN_MULTI_MOLD_LABELS,
        reachable.values().filter(|molds| molds.len() > 1).count()
    );
    Ok(())
}

#[test]
fn seen_key_verdict_is_recorded() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    assert_eq!(SeenKeyVerdict::Equivalent, seen_key_verdict(&pbg)?);
    Ok(())
}

#[test]
fn comparison_table_coheres_with_precedence() -> Result<(), Box<dyn Error>>
{
    // Annotation-comparison coherence (Moon, Blinn, Porter and Omar 2025,
    // Theorem 3.1), comparable-pair form: `t_L ⋖ t_R ⟺ p_L <_s p_R` and
    // `t_L ⋗ t_R ⟺ p_L >_s p_R` at the mediating sort; incomparable pairs
    // derive nothing.
    let pbg = built_in()?;
    let index = walk_index(&pbg)?;
    let table = comparison_table(&pbg, &index);
    let dag = pbg.dag();

    // Soundness: every row agrees with the DAG and stays in one sort.
    for row in &table {
        let left = pbg.mold(row.left)?;
        let right = pbg.mold(row.right)?;
        assert_eq!(left.sort, right.sort, "a comparison mediates one sort");
        assert_eq!(row.sort, left.sort);
        match row.cmp {
            | Comparison::Yields => {
                assert!(bool::from(dag.lt(left.prec, right.prec, Assoc::Non)));
            },
            | Comparison::Takes => {
                assert!(bool::from(dag.gt(left.prec, right.prec, Assoc::Non)));
            },
            | Comparison::Equal => {},
        }
    }

    // Completeness: every comparable same-sort group pair derives exactly the
    // matching relation over its representatives.
    let reps = group_reps(&pbg);
    let mut expected: BTreeSet<(MoldId, MoldId, Comparison)> = BTreeSet::new();
    for (&(sort_l, prec_l), &rep_l) in &reps {
        for (&(sort_r, prec_r), &rep_r) in &reps {
            if sort_l != sort_r {
                continue;
            }
            if bool::from(dag.lt(prec_l, prec_r, Assoc::Non)) {
                expected.insert((rep_l, rep_r, Comparison::Yields));
            }
            else if bool::from(dag.gt(prec_l, prec_r, Assoc::Non)) {
                expected.insert((rep_l, rep_r, Comparison::Takes));
            }
        }
    }
    let observed: BTreeSet<(MoldId, MoldId, Comparison)> = table
        .iter()
        .filter(|row| row.cmp != Comparison::Equal)
        .map(|row| (row.left, row.right, row.cmp))
        .collect();
    assert!(!expected.is_empty());
    assert_eq!(expected, observed);

    let equal: BTreeSet<(MoldId, MoldId)> = table
        .iter()
        .filter(|row| row.cmp == Comparison::Equal)
        .map(|row| (row.left, row.right))
        .collect();
    assert_eq!(
        pbg.adjacencies().iter().copied().collect::<BTreeSet<_>>(),
        equal,
        "the `≐` face is the same-form adjacency"
    );
    Ok(())
}

#[test]
fn comparison_table_is_conflict_free() -> Result<(), Box<dyn Error>>
{
    // At most one comparison per ordered pair: a `≐` conflict (the
    // dangling-else family) would show as a second, different relation.
    let pbg = built_in()?;
    let index = walk_index(&pbg)?;
    let table = comparison_table(&pbg, &index);

    let mut seen: BTreeMap<(MoldId, MoldId), Comparison> = BTreeMap::new();
    for row in &table {
        if let Some(previous) = seen.insert((row.left, row.right), row.cmp) {
            assert_eq!(
                previous, row.cmp,
                "pair ({:?}, {:?}) derives two comparisons",
                row.left, row.right
            );
        }
    }
    assert!(table.windows(2).all(|pair| match *pair {
        | [left, right] => left <= right,
        | _ => true,
    }));
    Ok(())
}

#[test]
fn walk_lengths_respect_the_chain_cap() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let index = walk_index(&pbg)?;
    let cap = WalkChainLength::from(MAX_WALK_CHAIN_LEN);
    let ends: Vec<End<_>> = index.ends().to_vec();
    let mut walks = 0_usize;
    for left in &ends {
        for right in &ends {
            for dir in [Dir::Left, Dir::Right] {
                for walk in index.walks(dir, left, right) {
                    assert!(walk.chain_len()? <= cap, "a walk exceeds the cap");
                    walks = walks.checked_add(1).expect("the walk count fits");
                }
            }
        }
    }
    assert!(walks > 0, "the index materialises walks");
    Ok(())
}
