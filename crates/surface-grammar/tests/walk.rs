//! The mold table and the walk index over the built-in surface and two
//! synthetic grammars: the pinned inventory and fingerprint, lookups and
//! their bounds, the form-membership answers, the walk projection, and the
//! comparison table's coherence with the precedence DAG.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::error::Error;

use anodized::spec;
use gandr_surface_grammar::Comparison;
use gandr_surface_grammar::LabelText;
use gandr_surface_grammar::MAX_WALK_CHAIN_LEN;
use gandr_surface_grammar::MoldCount;
use gandr_surface_grammar::MoldWord;
use gandr_surface_grammar::MoldWordIndex;
use gandr_surface_grammar::Observation;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::PrecName;
use gandr_surface_grammar::RCtxId;
use gandr_surface_grammar::Regex;
use gandr_surface_grammar::Rule;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::StepSym;
use gandr_surface_grammar::TileKind;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::TileSet;
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
/// group moves it; a deliberate change re-pins it and says why. Last moved by
/// the receiver's mode: `shared` or `consumed` opening a parameter's type.
const BUILT_IN_FINGERPRINT: u64 = 0x2d0b_04cf_367e_aec8;

/// The built-in surface's mold count: one mold per tile occurrence, so a form
/// inlined at many sites (the statement alternation, inlined at every block
/// position) costs one copy per site, while a form reached through a hole of
/// its own sort (a nested module's members) costs nothing per level.
const BUILT_IN_MOLD_COUNT: MoldCount = MoldCount(2976);

/// How many labels the walk index projects to more than one mold.
const BUILT_IN_MULTI_MOLD_LABELS: usize = 86;

/// The built-in surface's molds per label, ascending by label.
const DECLARED_CANDIDATE_INVENTORY: &[(&str, usize)] = &[
    ("!", 20),
    ("!=", 1),
    ("\"", 14),
    ("#!{", 1),
    ("#{", 9),
    ("$", 3),
    ("${", 3),
    ("&", 4),
    ("&&", 1),
    ("'", 2),
    ("(", 202),
    (")", 206),
    ("*", 2),
    ("+", 7),
    ("++", 1),
    ("+U", 1),
    (",", 225),
    ("-", 4),
    ("-->", 26),
    ("->", 14),
    ("-F", 2),
    (".", 26),
    ("..", 3),
    ("/\\", 1),
    (":", 256),
    (":>", 2),
    (";", 237),
    ("<", 12),
    ("<&", 1),
    ("<-", 19),
    ("<->", 24),
    ("<=", 1),
    ("<=>", 28),
    ("<>", 1),
    ("=", 116),
    ("==", 1),
    ("==>", 28),
    ("=>", 23),
    (">", 3),
    (">&", 1),
    (">=", 1),
    (">>", 1),
    ("?", 4),
    ("@[", 6),
    ("Any", 1),
    ("Boolean", 1),
    ("Buf", 1),
    ("Cap", 1),
    ("Char", 1),
    ("Integer", 1),
    ("Never", 1),
    ("Path", 1),
    ("String", 1),
    ("Symbol", 1),
    ("Type", 2),
    ("Type+", 1),
    ("Unit", 1),
    ("Unknown", 1),
    ("Void", 1),
    ("[", 39),
    ("\\", 1),
    ("]", 45),
    ("_", 43),
    ("abort", 1),
    ("access", 1),
    ("acquire", 19),
    ("as", 80),
    ("at", 2),
    ("become", 1),
    ("break", 2),
    ("case", 1),
    ("character", 1),
    ("close", 1),
    ("co", 1),
    ("codata", 1),
    ("command_substitution_start", 1),
    ("constructor", 6),
    ("consumed", 20),
    ("continue", 1),
    ("data", 12),
    ("def", 4),
    ("double_string_fragment", 1),
    ("drop", 1),
    ("dup", 1),
    ("else", 2),
    ("end", 1),
    ("environment_assignment", 1),
    ("escape_sequence", 7),
    ("exclusive", 1),
    ("ext", 1),
    ("extern", 1),
    ("f32", 1),
    ("f64", 1),
    ("false", 2),
    ("feed", 3),
    ("file_descriptor", 1),
    ("fn", 1),
    ("for", 1),
    ("forall", 1),
    ("force", 1),
    ("fork", 38),
    ("from", 1),
    ("glob", 1),
    ("handle", 1),
    ("hold", 20),
    ("hole_name", 2),
    ("i32", 1),
    ("i64", 1),
    ("identifier", 407),
    ("if", 2),
    ("import", 1),
    ("in", 1),
    ("include", 1),
    ("infix", 1),
    ("infixl", 1),
    ("infixr", 1),
    ("is", 1),
    ("leta", 19),
    ("loop", 1),
    ("migrate", 1),
    ("mobile", 10),
    ("module", 2),
    ("mu", 1),
    ("newline", 1),
    ("node", 3),
    ("number", 54),
    ("obs", 1),
    ("offer", 1),
    ("on", 1),
    ("op", 3),
    ("oper", 8),
    ("pack", 2),
    ("package", 1),
    ("pi+", 8),
    ("postfix", 1),
    ("prefix", 1),
    ("pure", 3),
    ("rec", 2),
    ("recv", 19),
    ("release", 19),
    ("resume", 1),
    ("return", 1),
    ("rule", 16),
    ("run", 20),
    ("select", 1),
    ("send", 1),
    ("shape", 1),
    ("shared", 21),
    ("shell_word", 1),
    ("single_quoted_content", 1),
    ("sort", 7),
    ("string_fragment", 6),
    ("subshell_close", 1),
    ("subshell_open", 1),
    ("tail", 1),
    ("then", 1),
    ("theory", 1),
    ("thunk", 1),
    ("true", 2),
    ("type", 23),
    ("type(", 1),
    ("type_identifier", 88),
    ("type_variable", 61),
    ("typed_number", 2),
    ("u32", 1),
    ("u64", 1),
    ("unit", 2),
    ("unpack", 19),
    ("unwind", 1),
    ("val", 19),
    ("variable_name", 5),
    ("while", 1),
    ("with", 8),
    ("world", 1),
    ("{", 45),
    ("|", 10),
    ("|&", 1),
    ("||", 1),
    ("}", 61),
    ("~>", 4),
    ("ω", 17),
    ("⇝", 1),
    ("∷", 2),
    ("≃", 1),
    ("≅", 1),
];

/// A grammar of one group, with the infix form `E + E` and the atom `x`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the grammar and its one group, named `group`.
/// - fails: never for these rules.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the two finite fixture grammars, L2 bounds, steps and
///   comparison observations catch wrong labels, group identities and context
///   edges. The predicate checks their declared inventories; arbitrary grammar
///   sizes and failing fixture construction are not exhausted.
/// - witness: `tests::walk::mold_bounds_follow_context_nullability`
/// - witness: `tests::walk::comparison_table_coheres_with_precedence`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|&(ref pbg, base)| pbg.dag().groups().count() == 1 && pbg.dag().name(base).is_some_and(|name| name == group.0) && pbg.dag().assoc(base) == Some(Assoc::Non) && pbg.rules().len() == 2 && pbg.rules().iter().all(|rule| rule.sort() == Sort::Expression && rule.prec() == base) && pbg.mold_count() == MoldCount(2) && pbg.candidates(TileLabel("+")).len() == 1 && pbg.candidates(TileLabel("x")).len() == 1))]
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
///
/// # Adequacy
/// - hypothesis: For the two finite fixture grammars, L2 bounds, steps and
///   comparison observations catch wrong labels, group identities and context
///   edges. The predicate checks their declared inventories; arbitrary grammar
///   sizes and failing fixture construction are not exhausted.
/// - witness: `tests::walk::rctx_steps_cross_adjacent_symbols`
/// - witness: `tests::walk::same_form_adjacency_is_the_eq_relation`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|pbg| pbg.rules().len() == 2 && pbg.mold_count() == MoldCount(3) && ["(", ")", "x"].into_iter().all(|label| pbg.candidates(TileLabel(label)).len() == 1) && pbg.adjacencies().len() == 1 && pbg.adjacencies().first().is_some_and(|&(left, right)| pbg.mold(left).is_ok_and(|mold| mold.label == "(") && pbg.mold(right).is_ok_and(|mold| mold.label == ")"))))]
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
///
/// # Adequacy
/// - hypothesis: For the synthetic singleton label menus, L2 lookup and bound
///   observations catch a wrong returned occurrence. The predicate observes
///   exact singleton identity; missing and ambiguous labels are outside the
///   witnesses.
/// - witness: `tests::walk::mold_bounds_follow_context_nullability`
/// - witness: `tests::walk::rctx_steps_cross_adjacent_symbols`
#[spec(ensures: |ret| pbg.candidates(label) == [ret])]
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
/// - requires: nothing.
/// - ensures: covers every inhabited sort/band group with its least mold id.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in and synthetic inventories, L2
///   comparison-table observations catch absent groups and nonminimal or
///   foreign representatives. The predicate proves coverage, membership and
///   minimality over the supplied inventory; very large tables are not
///   exercised.
/// - witness: `tests::walk::comparison_table_coheres_with_precedence`
#[spec(ensures: |ret| pbg.iter_molds().all(|(id, def)| ret.get(&(def.sort, def.prec)).is_some_and(|&representative| representative <= id)) && ret.iter().all(|(&(sort, prec), &id)| pbg.mold(id).is_ok_and(|def| def.sort == sort && def.prec == prec)))]
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
            [(left, _), (right, _)] => left < right,
            _ => true,
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
    // Every declared label resolves from its spelling to itself, and neither
    // an undeclared spelling nor a declared one's prefix resolves at all.
    for &(label, _count) in &counts {
        assert_eq!(Some(label), pbg.tile_label(LabelText(label.0)));
    }
    assert_eq!(None, pbg.tile_label(LabelText("no such label")));
    assert_eq!(None, pbg.tile_label(LabelText("identifie")));
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
fn a_data_member_colon_after_a_constructor_name_reads_one_way() -> Result<(), Box<dyn Error>>
{
    // `None : Maybe(a)` is a generator without a telescope; the declined
    // Haskell-style tail annotates a result only after its field tuple, so no
    // second `:` reading follows the constructor name.
    let pbg = built_in()?;
    let mut members = 0_usize;
    let mut colons: Vec<MoldId> = Vec::new();
    for (id, def) in pbg.iter_molds() {
        if def.label != "constructor"
            || !pbg
                .rule_of(id)
                .is_ok_and(|rule| rule.name() == RuleName("data_declaration"))
        {
            continue;
        }
        colons.clear();
        colons.extend(
            pbg.mold_successors(id)
                .iter()
                .filter(|&&(_, right)| pbg.mold(right).is_ok_and(|next| next.label == ":"))
                .map(|&(_, right)| right),
        );
        assert!(
            colons.len() == 1,
            "constructor mold {id:?} has the `:` successors {colons:?}"
        );
        members = members.saturating_add(1);
    }
    assert!(
        members > 0,
        "the data declaration names its members' constructors"
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
    let mut expected: Vec<MoldId> = Vec::new();
    for (label, _count) in pbg.candidate_counts() {
        let candidates = pbg.candidates(label);
        expected.clear();
        expected.extend(candidates.iter().copied().filter(|&mold| {
            !bool::from(pbg.mold_has_predecessor(mold)) || bool::from(pbg.mold_is_form_first(mold))
        }));
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
    // The grammar is immutable; borrow each full-table view once.
    let form_first = pbg.form_first();
    let form_last = pbg.form_last();
    let adjacencies = pbg.adjacencies();
    let ascending = |molds: &[MoldId]| {
        molds.windows(2).all(|pair| match *pair {
            [left, right] => left < right,
            _ => true,
        })
    };
    assert!(ascending(form_first));
    assert!(ascending(form_last));
    assert!(adjacencies.windows(2).all(|pair| match *pair {
        [left, right] => left < right,
        _ => true,
    }));

    let preceded: BTreeSet<MoldId> = adjacencies.iter().map(|&(_, right)| right).collect();
    let succeeded: BTreeSet<MoldId> = adjacencies.iter().map(|&(left, _)| left).collect();
    let mut required_tails = 0_usize;
    for (mold, _def) in pbg.iter_molds() {
        assert_eq!(
            preceded.contains(&mold),
            bool::from(pbg.mold_has_predecessor(mold))
        );
        assert_eq!(
            succeeded.contains(&mold),
            bool::from(pbg.mold_has_successor(mold))
        );
        assert!(
            pbg.mold_successors(mold).iter().copied().eq(adjacencies
                .iter()
                .copied()
                .filter(|&(left, _)| left == mold)),
            "mold {mold:?} reads exactly its own successor run"
        );
        assert_eq!(
            form_first.binary_search(&mold).is_ok(),
            bool::from(pbg.mold_is_form_first(mold))
        );
        let complete = bool::from(pbg.mold_is_form_last(mold));
        let required = bool::from(pbg.mold_has_required_tail(mold));
        if form_last.binary_search(&mold).is_ok() {
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
    assert!(pbg.mold_successors(past).is_empty());
    for &(left, right) in adjacencies {
        assert!(bool::from(pbg.molds_adjacent(left, right)));
        assert_eq!(
            bool::from(pbg.molds_adjacent(right, left)),
            adjacencies.binary_search(&(right, left)).is_ok()
        );
        assert!(!bool::from(pbg.molds_adjacent(left, past)));
    }
    Ok(())
}

/// Every mold reads exactly as its least interchangeable mold on each
/// component a pushed tile is read by, and the lowercase parameter-name molds
/// of a definition (`identifier`, `type_variable`) fall in one class.
#[test]
fn interchangeable_molds_differ_only_in_label() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let adjacencies = pbg.adjacencies();
    let predecessors = |mold: MoldId| {
        adjacencies
            .iter()
            .filter(move |&&(_, right)| right == mold)
            .map(|&(left, _)| left)
    };
    let successors = |mold: MoldId| pbg.mold_successors(mold).iter().map(|&(_, right)| right);
    let mut merged = 0_usize;
    let mut parameter_names = false;
    for (mold, def) in pbg.iter_molds() {
        let twin = pbg.least_interchangeable(mold);
        assert!(twin <= mold);
        assert_eq!(twin, pbg.least_interchangeable(twin));
        if twin == mold {
            continue;
        }
        merged = merged.saturating_add(1);
        let other = pbg.mold(twin)?;
        assert_eq!(pbg.rule_of(twin)?.name(), pbg.rule_of(mold)?.name());
        assert_eq!((other.prec, other.sort), (def.prec, def.sort));
        assert_eq!(pbg.bounds(twin)?, pbg.bounds(mold)?);
        for dir in [Dir::Left, Dir::Right] {
            assert_eq!(pbg.step(other.rctx, dir)?, pbg.step(def.rctx, dir)?);
        }
        assert_eq!(pbg.closing_class(twin), pbg.closing_class(mold));
        assert_eq!(
            [
                bool::from(pbg.mold_is_form_first(twin)),
                bool::from(pbg.mold_is_form_last(twin)),
                bool::from(pbg.mold_has_required_tail(twin)),
            ],
            [
                bool::from(pbg.mold_is_form_first(mold)),
                bool::from(pbg.mold_is_form_last(mold)),
                bool::from(pbg.mold_has_required_tail(mold)),
            ]
        );
        assert!(successors(twin).eq(successors(mold)));
        assert!(predecessors(twin).eq(predecessors(mold)));
        assert_ne!(
            other.label, def.label,
            "two occurrences of one label never share a class"
        );
        parameter_names |= pbg.rule_of(mold)?.name() == RuleName("def_value")
            && (other.label, def.label) == ("identifier", "type_variable");
    }
    assert!(merged > 0);
    assert!(parameter_names);
    Ok(())
}

/// Every mold's tile kind, observation class and tile-set memberships read
/// back from the neighbour, tail, membership, step and bound queries: the
/// kind follows the neighbour flags and holes, two molds share a class
/// exactly when their readings agree, classes are numbered by their least
/// mold, and each set holds exactly the molds its kind and sort put there.
/// The first id past the table has no kind and no class, and its word is
/// empty.
#[test]
fn tile_kinds_observations_and_sets_agree_with_the_table() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let sorts = [
        Sort::Item,
        Sort::Pattern,
        Sort::Expression,
        Sort::Type,
        Sort::Instantiation,
        Sort::ModuleMember,
    ];
    let shape = |bound: Bound<Prec>| match bound {
        Bound::Bottom => 0_u8,
        Bound::Value(_) => 1,
        Bound::Root => 2,
    };
    let mut readings: BTreeMap<_, Observation> = BTreeMap::new();
    let mut classes: BTreeMap<Observation, MoldId> = BTreeMap::new();
    let mut merged_rules = false;
    let mut held = Vec::new();
    for (mold, def) in pbg.iter_molds() {
        let (left, right) = pbg.bounds(mold)?;
        let has_pred = bool::from(pbg.mold_has_predecessor(mold));
        let has_succ = bool::from(pbg.mold_has_successor(mold));
        let tail = bool::from(pbg.mold_has_required_tail(mold));
        let left_hole = matches!(left, Bound::Value(_));
        let right_hole = matches!(right, Bound::Value(_));
        let kind = match (has_pred, has_succ) {
            (false, true) if left_hole => TileKind::AbsorbingStart,
            (false, true) => TileKind::Start,
            (true, true) => TileKind::Mid,
            (true, false) if tail => TileKind::Mid,
            (true, false) => TileKind::End,
            (false, false) => match (left_hole, right_hole) {
                (false, false) => TileKind::Operand,
                (false, true) => TileKind::Prefix,
                (true, false) => TileKind::Postfix,
                (true, true) => TileKind::Infix,
            },
        };
        assert_eq!(kind, pbg.tile_kind(mold)?, "mold {mold:?}'s kind");
        let first = bool::from(pbg.mold_is_form_first(mold));
        let hole = pbg
            .step(def.rctx, Dir::Right)?
            .iter()
            .find_map(|step| match step.crossed {
                StepSym::Sort(sort) => Some(sort),
                StepSym::Tile(_) => None,
            });
        let reading = (
            kind,
            def.sort,
            def.prec,
            (has_pred, has_succ),
            (first, bool::from(pbg.mold_is_form_last(mold)), tail),
            hole,
            (shape(left), shape(right)),
        );
        let class = pbg.observation(mold)?;
        let next = classes.len();
        if let Some(&held) = readings.get(&reading) {
            assert_eq!(held, class, "mold {mold:?} reads as its class");
        }
        else {
            assert_eq!(
                usize::try_from(u32::from(class))?,
                next,
                "a new reading takes the next class number"
            );
            readings.insert(reading, class);
        }
        match classes.get(&class) {
            Some(&least) => {
                merged_rules |= pbg.rule_of(least)?.name() != pbg.rule_of(mold)?.name();
            },
            None => {
                classes.insert(class, mold);
            },
        }
        let word = MoldWordIndex::of(mold);
        held.clear();
        for sort in sorts {
            for set in [TileSet::Fills(sort), TileSet::Absorbs(sort)] {
                let view = pbg.tile_set(set);
                assert_eq!(view.contains(mold), view.word(word).contains(mold));
                if bool::from(view.contains(mold)) {
                    held.push(set);
                }
            }
        }
        for set in [
            TileSet::Prefixes,
            TileSet::LeftOperators,
            TileSet::FirstMids,
            TileSet::Continuations,
        ] {
            if bool::from(pbg.tile_set(set).contains(mold)) {
                held.push(set);
            }
        }
        let expected = match kind {
            TileKind::Operand | TileKind::Start => vec![TileSet::Fills(def.sort)],
            TileKind::AbsorbingStart => vec![TileSet::Absorbs(def.sort)],
            TileKind::Prefix => vec![TileSet::Prefixes],
            TileKind::Infix | TileKind::Postfix => vec![TileSet::LeftOperators],
            TileKind::Mid if first => vec![TileSet::FirstMids, TileSet::Continuations],
            TileKind::Mid | TileKind::End => vec![TileSet::Continuations],
        };
        assert_eq!(expected, held, "mold {mold:?}'s sets");
    }
    assert_eq!(readings.len(), classes.len());
    assert!(merged_rules, "a class spans molds of different rules");
    let past = MoldId::try_from(pbg.mold_count().0)?;
    assert!(matches!(pbg.tile_kind(past), Err(PbgError::UnknownMold { id }) if id == past));
    assert!(matches!(pbg.observation(past), Err(PbgError::UnknownMold { id }) if id == past));
    let beyond = MoldId::try_from(pbg.mold_count().0.saturating_add(64))?;
    assert_eq!(
        MoldWord::default(),
        pbg.tile_set(TileSet::Continuations)
            .word(MoldWordIndex::of(beyond))
    );
    assert!(!bool::from(
        pbg.tile_set(TileSet::Continuations).contains(past)
    ));
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
            Comparison::Yields => {
                assert!(bool::from(dag.lt(left.prec, right.prec, Assoc::Non)));
            },
            Comparison::Takes => {
                assert!(bool::from(dag.gt(left.prec, right.prec, Assoc::Non)));
            },
            Comparison::Equal => {},
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
        [left, right] => left <= right,
        _ => true,
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

#[test]
fn unknown_context_preserves_its_identity() -> Result<(), Box<dyn Error>>
{
    let (pbg, _) = synthetic_pbg(PrecName("base"))?;
    let rctx = RCtxId::from(u32::MAX);
    for dir in [Dir::Left, Dir::Right] {
        assert_eq!(Err(PbgError::UnknownRCtx { rctx }), pbg.step(rctx, dir));
    }
    Ok(())
}
