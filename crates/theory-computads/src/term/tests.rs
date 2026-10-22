use core::cmp::Ordering;

use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::normalize;
use gandr_theory_coherent_resolutions::replay_path;
use gandr_theory_levitation::SurfaceSpan;

use super::*;

/// A metavariable term.
///
/// # Specification
/// trivial.
fn var<N>(name: N) -> Term
where
    N: Into<Name>,
{
    Term::from(&FreeTerm::var(name))
}

/// A constructor application.
///
/// # Specification
/// trivial.
fn ctor<N, const M: usize>(
    name: N,
    args: [FreeTerm; M],
) -> FreeTerm
where
    N: Into<Name>,
{
    FreeTerm::ctor(name, args)
}

/// The circle's word `name(inner)`.
///
/// # Specification
/// trivial.
fn turn<N>(
    name: N,
    inner: FreeTerm,
) -> FreeTerm
where
    N: Into<Name>,
{
    FreeTerm::ctor(name, [inner])
}

#[test]
fn positions_preserve_prefix_boundaries_and_splice_siblings()
{
    for (before, after) in [
        (0, 1),
        (7, 8),
        (usize::MAX - 1, usize::MAX),
        (usize::MAX, usize::MAX),
    ] {
        assert_eq!(Count(after), Count(before).next(), "{before} steps once");
    }
    let x = FreeTerm::var("x");
    let right = FreeTerm::op("add", [ctor("Zero", []), x.clone()]);
    let free = FreeTerm::results([turn("Succ", x.clone()), right.clone()]);
    let term = Term::from(&free);
    let paths = [
        alloc::vec![],
        alloc::vec![0],
        alloc::vec![1],
        alloc::vec![0, 0],
        alloc::vec![1, 0],
        alloc::vec![1, 1],
    ];
    let positions: Vec<_> = paths
        .iter()
        .map(|path| {
            TermAlphabet::position_at_path(
                &path
                    .iter()
                    .copied()
                    .map(PositionStep::from)
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    assert_eq!(
        positions,
        TermAlphabet::command_positions(&term),
        "every node is a position, breadth first"
    );
    assert_eq!(
        alloc::vec![TermAlphabet::root_position()],
        TermAlphabet::command_positions(&Term::from(&ctor("Zero", []))),
        "a leaf is its own root"
    );
    let subterms = [
        free.clone(),
        turn("Succ", x.clone()),
        right,
        x.clone(),
        ctor("Zero", []),
        x.clone(),
    ];
    for (pos, expected) in positions.iter().zip(subterms) {
        let expected = Term::from(&expected);
        assert_eq!(
            Maybe::Present(expected.clone()),
            TermAlphabet::subterm_cmd_at(&term, pos),
            "the read at {pos:?}"
        );
        assert_eq!(
            Ok(term.clone()),
            TermAlphabet::splice_cmd_at(&term, pos, expected),
            "splicing the read back at {pos:?}"
        );
    }
    for (start, end) in [(0, 6), (1, 3), (2, 3), (3, 6), (4, 5), (5, 6), (6, 6)] {
        assert_eq!(
            Count(end),
            term.end_of(Count(start)),
            "the end from {start}"
        );
    }
    assert_eq!(
        Count(2),
        Term(alloc::vec![
            Head::Results(Count(2)),
            Head::Var(Name::from("y"))
        ])
        .end_of(Count(0)),
        "a table cut short ends at its length"
    );
    let first = TermAlphabet::position_at_path(&[PositionStep::from(0_usize)]);
    let inner =
        TermAlphabet::position_at_path(&[PositionStep::from(1_usize), PositionStep::from(1_usize)]);
    assert_eq!(
        Ok(Term::from(&FreeTerm::results([
            ctor("Zero", []),
            FreeTerm::op("add", [ctor("Zero", []), x.clone()]),
        ]))),
        TermAlphabet::splice_cmd_at(&term, &first, Term::from(&ctor("Zero", []))),
        "a shrinking splice keeps its siblings"
    );
    assert_eq!(
        Ok(Term::from(&FreeTerm::results([
            turn("Succ", x),
            FreeTerm::op("add", [ctor("Zero", []), free]),
        ]))),
        TermAlphabet::splice_cmd_at(&term, &inner, term.clone()),
        "a growing splice keeps its siblings"
    );
    for path in [alloc::vec![2], alloc::vec![0, 1], alloc::vec![1, 1, 0]] {
        let pos = TermAlphabet::position_at_path(
            &path.into_iter().map(PositionStep::from).collect::<Vec<_>>(),
        );
        assert_eq!(
            Maybe::Absent(command_subterm::Absent::OffTerm),
            TermAlphabet::subterm_cmd_at(&term, &pos),
            "{pos:?} leaves the term"
        );
        assert_eq!(
            Err(CommandSpliceRefusal::OffTerm),
            TermAlphabet::splice_cmd_at(&term, &pos, Term::from(&ctor("Zero", []))),
            "{pos:?} splices nothing"
        );
    }
}

#[test]
fn substitution_walks_are_transactional_and_bounded()
{
    let x = Name::from("x");
    let y = Name::from("y");
    let zero = || Term::from(&ctor("Zero", []));
    let pair = |left: FreeTerm, right: FreeTerm| Term::from(&FreeTerm::op("add", [left, right]));
    let subst = TermSubst(BTreeMap::from([(x.clone(), var("y")), (y.clone(), zero())]));
    let term = pair(FreeTerm::var("x"), FreeTerm::var("y"));
    assert_eq!(
        pair(FreeTerm::var("y"), ctor("Zero", [])),
        subst.apply_once(&term),
        "one pass replaces each bound variable once"
    );
    assert_eq!(
        pair(ctor("Zero", []), ctor("Zero", [])),
        subst.apply_fully(&term),
        "the fixpoint follows the chain"
    );
    assert_eq!(
        zero(),
        subst.walk(var("x")),
        "a bare variable walks its chain"
    );
    assert_eq!(
        term,
        subst.walk(term.clone()),
        "a compound term is not walked into"
    );
    assert_eq!(var("free"), subst.walk(var("free")), "a free leaf stays");
    assert_eq!(
        term,
        TermSubst::default().apply_fully(&term),
        "no binding, no change"
    );
    assert_eq!(
        TermSubst::default(),
        TermAlphabet::restrict_subst(&subst, &[]),
        "nothing kept"
    );
    assert_eq!(
        TermSubst::default(),
        TermAlphabet::restrict_subst(&subst, &[Name::from("missing")]),
        "an absent key keeps nothing"
    );
    assert_eq!(
        TermSubst(BTreeMap::from([(x.clone(), var("y"))])),
        TermAlphabet::restrict_subst(&subst, &[x.clone(), x.clone()]),
        "a repeated key keeps one binding"
    );
    assert_eq!(
        subst,
        TermAlphabet::restrict_subst(&subst, &[x, y]),
        "every key keeps every binding"
    );
    let self_cycle = TermSubst(BTreeMap::from([(Name::from("self"), var("self"))]));
    assert_eq!(
        var("self"),
        self_cycle.walk(var("self")),
        "a self-cycle stops"
    );
    assert_eq!(
        var("self"),
        self_cycle.apply_fully(&var("self")),
        "a self-cycle is bounded"
    );
    let seed = TermSubst(BTreeMap::from([(
        Name::from("held"),
        Term::from(&turn("Succ", ctor("Zero", []))),
    )]));
    let pattern = pair(FreeTerm::var("p"), FreeTerm::var("p"));
    let target = pair(ctor("Zero", []), ctor("Zero", []));
    let mut matched = seed.clone();
    assert!(
        bool::from(TermAlphabet::match_cmd(&pattern, &target, &mut matched)),
        "a repeated variable matches equal subterms"
    );
    assert_eq!(
        target,
        matched.apply_once(&pattern),
        "the match rebuilds the target"
    );
    assert_eq!(
        Some(&Term::from(&turn("Succ", ctor("Zero", [])))),
        matched.0.get(&Name::from("held")),
        "the seed binding is kept"
    );
    let saved = matched.clone();
    let konst = TermAlphabet::skolemize(&var("k"));
    for (left, right) in [
        (
            pattern.clone(),
            pair(ctor("Zero", []), turn("Succ", ctor("Zero", []))),
        ),
        (Term::from(&turn("Succ", FreeTerm::var("p"))), zero()),
        (zero(), Term::from(&turn("Succ", ctor("Zero", [])))),
        (zero(), konst.clone()),
        (
            Term::from(&ctor("Zero", [])),
            Term::from(&FreeTerm::op("Zero", [])),
        ),
    ] {
        assert!(
            !bool::from(TermAlphabet::match_cmd(&left, &right, &mut matched)),
            "{left:?} does not match {right:?}"
        );
        assert_eq!(saved, matched, "a refused match leaves the map");
    }
    let mut constant = TermSubst::default();
    assert!(
        bool::from(TermAlphabet::match_cmd(&var("v"), &konst, &mut constant)),
        "a metavariable matches a skolem constant"
    );
    let left = pair(FreeTerm::var("a"), FreeTerm::var("b"));
    let right = pair(turn("Succ", FreeTerm::var("b")), ctor("Zero", []));
    let mut unified = seed.clone();
    assert!(
        bool::from(TermAlphabet::unify_cmd(&left, &right, &mut unified)),
        "the two sides unify"
    );
    assert_eq!(
        pair(turn("Succ", ctor("Zero", [])), ctor("Zero", [])),
        unified.apply_fully(&left),
        "the unifier's image"
    );
    assert_eq!(
        unified.apply_fully(&left),
        unified.apply_fully(&right),
        "the unifier equates both sides"
    );
    for (left, right) in [
        (
            var("cycle"),
            Term::from(&turn("Succ", FreeTerm::var("cycle"))),
        ),
        (
            pair(ctor("Zero", []), FreeTerm::var("fresh")),
            pair(turn("Succ", ctor("Zero", [])), ctor("Zero", [])),
        ),
    ] {
        let mut refused = seed.clone();
        assert!(
            !bool::from(TermAlphabet::unify_cmd(&left, &right, &mut refused)),
            "{left:?} and {right:?} do not unify"
        );
        assert_eq!(seed, refused, "a refused unification leaves the map");
    }
}

/// #654: a match is applied once, all at once. Firing associativity at a term
/// that carries a variable named as one of the rule's own reads that variable
/// as the term's, never as the rule's to replace again; a unifier, applied
/// once, is already its fixpoint.
#[test]
fn a_substitution_replaces_each_variable_once_all_at_once_654()
{
    let mul = |left: FreeTerm, right: FreeTerm| FreeTerm::op("mul", [left, right]);
    let v = FreeTerm::var;
    let lhs = Term::from(&mul(mul(v("x"), v("y")), v("z")));
    let rhs = Term::from(&mul(v("x"), mul(v("y"), v("z"))));
    let target = Term::from(&mul(mul(v("a"), v("b")), mul(v("c"), v("z"))));
    let mut matched = TermSubst::default();
    assert!(bool::from(TermAlphabet::match_cmd(
        &lhs,
        &target,
        &mut matched
    )));
    assert_eq!(
        Term::from(&mul(v("a"), mul(v("b"), mul(v("c"), v("z"))))),
        TermAlphabet::apply_subst(&matched, &rhs),
        "the target's own `z` is not the rule's"
    );
    let mut unified = TermSubst::default();
    let chained = Term::from(&mul(v("p"), v("q")));
    let ground = Term::from(&mul(v("q"), ctor("Zero", [])));
    assert!(bool::from(TermAlphabet::unify_cmd(
        &chained,
        &ground,
        &mut unified
    )));
    let both = Term::from(&mul(ctor("Zero", []), ctor("Zero", [])));
    assert_eq!(
        (both.clone(), both),
        (
            TermAlphabet::apply_subst(&unified, &chained),
            TermAlphabet::apply_subst(&unified, &ground)
        ),
        "a chained unifier is resolved, so one pass equates both sides"
    );
}

#[test]
fn metadata_names_and_orders_observe_boundaries()
{
    let x = Name::from("x");
    let doubled = || FreeTerm::op("add", [FreeTerm::var("x"), FreeTerm::var("x")]);
    let term = Term::from(&doubled());
    assert_eq!(
        BTreeMap::from([(&x, Occurrences(2))]),
        occurrences(&term),
        "two occurrences of one name"
    );
    assert!(
        occurrences(&Term::from(&ctor("Zero", []))).is_empty(),
        "a ground term"
    );
    let counts = occurrences(&term);
    assert_eq!(
        HoleDomination::Dominates,
        dominates(&counts, &BTreeMap::new()),
        "nothing to dominate"
    );
    for (name, count, expected) in [
        (&x, 1, HoleDomination::Dominates),
        (&x, 2, HoleDomination::Dominates),
        (&x, 3, HoleDomination::FallsShort),
        (&Name::from("missing"), 1, HoleDomination::FallsShort),
    ] {
        assert_eq!(
            expected,
            dominates(&counts, &BTreeMap::from([(name, Occurrences(count))])),
            "{name} at {count}"
        );
    }
    for (left, right, expected) in [
        (
            turn("Succ", FreeTerm::var("x")),
            FreeTerm::var("x"),
            Ordering::Greater,
        ),
        (
            turn("Succ", ctor("Zero", [])),
            FreeTerm::var("x"),
            Ordering::Equal,
        ),
        (
            turn("Succ", turn("Succ", FreeTerm::var("x"))),
            doubled(),
            Ordering::Equal,
        ),
        (
            turn("Succ", turn("Succ", turn("Succ", FreeTerm::var("x")))),
            doubled(),
            Ordering::Equal,
        ),
    ] {
        let (left, right) = (Term::from(&left), Term::from(&right));
        assert_eq!(
            expected,
            TermAlphabet::reduction_cmp(&left, &right),
            "{left:?} against {right:?}"
        );
        assert_eq!(
            expected.reverse(),
            TermAlphabet::reduction_cmp(&right, &left),
            "{right:?} against {left:?}"
        );
    }
    for invertible in [false, true] {
        let meta = TermAlphabet::derive_meta(
            &term,
            &Term::from(&FreeTerm::op("add", [
                FreeTerm::var("new"),
                FreeTerm::var("x"),
            ])),
            CellInvertibility::from(invertible),
        );
        assert_eq!(
            alloc::vec![x.clone(), Name::from("new")],
            meta.vars,
            "first occurrence"
        );
        assert_eq!(invertible, bool::from(meta.invertible), "the flag is kept");
        assert_eq!(
            alloc::vec![(x.clone(), SeamRole::Forward)],
            TermAlphabet::hole_flow(&meta, &x),
            "one forward endpoint"
        );
        assert!(
            TermAlphabet::hole_flow(&meta, &Name::from("missing")).is_empty(),
            "an absent hole flows nowhere"
        );
    }
    let constants = Term(alloc::vec![
        Head::Op(Name::from("add"), Count(2)),
        Head::Konst(x.clone()),
        Head::Konst(x)
    ]);
    assert_eq!(
        constants,
        TermAlphabet::skolemize(&term),
        "each variable its constant"
    );
    assert_eq!(
        constants,
        TermAlphabet::skolemize(&constants),
        "a ground term is kept"
    );
    for name in ["", "r'"] {
        let source = var(name);
        let expected = var(alloc::format!("{name}'"));
        assert_eq!(
            (expected.clone(), expected),
            TermAlphabet::rename_apart((&source, &source), (&source, &source)),
            "{name} primed once"
        );
    }
    let anchor = Term::from(&FreeTerm::op("add", [
        FreeTerm::var("r"),
        FreeTerm::op("add", [FreeTerm::var("r'"), FreeTerm::var("r''")]),
    ]));
    let lhs = Term::from(&FreeTerm::op("add", [
        FreeTerm::var("r"),
        FreeTerm::var("r'"),
    ]));
    let rhs = Term::from(&FreeTerm::op("add", [
        FreeTerm::var("r"),
        FreeTerm::var("r"),
    ]));
    assert_eq!(
        (
            Term::from(&FreeTerm::op("add", [
                FreeTerm::var("r'''"),
                FreeTerm::var("r''''")
            ])),
            Term::from(&FreeTerm::op("add", [
                FreeTerm::var("r'''"),
                FreeTerm::var("r'''")
            ])),
        ),
        TermAlphabet::rename_apart((&anchor, &anchor), (&lhs, &rhs)),
        "a collision chain is primed past"
    );
    let zero = Term::from(&ctor("Zero", []));
    assert_eq!(
        (lhs.clone(), rhs.clone()),
        TermAlphabet::rename_apart((&zero, &zero), (&lhs, &rhs)),
        "a cell already apart is kept"
    );
}

#[test]
fn a_family_generalizes_to_its_least_general_pattern()
{
    let zero = ctor("Zero", []);
    let one = turn("Succ", zero.clone());
    let member = |left: FreeTerm, right: FreeTerm| {
        alloc::vec![
            Term::from(&FreeTerm::op("add", [left.clone(), left])),
            Term::from(&right)
        ]
    };
    let first = member(zero.clone(), one.clone());
    let second = member(one.clone(), one.clone());
    let family: [&[Term]; 2] = [&first, &second];
    let Maybe::Present(generalized) = TermAlphabet::anti_unify_cmd(&family)
    else {
        panic!("a nonempty even family generalizes");
    };
    assert_eq!(
        alloc::vec![
            Term::from(&FreeTerm::op("add", [
                FreeTerm::var("$g$0"),
                FreeTerm::var("$g$0")
            ])),
            Term::from(&one),
        ],
        generalized.patterns,
        "the shared head is kept and the repeated disagreement stands one point"
    );
    assert_eq!(1, generalized.points.len(), "one point");
    for (member, arms) in family.iter().zip(0_usize ..) {
        let rebuilt: Vec<Term> = generalized
            .patterns
            .iter()
            .map(|pattern| {
                generalized
                    .points
                    .iter()
                    .filter_map(|point| point.arms.get(arms))
                    .fold(pattern.clone(), |term, arm| arm.binding.apply_fully(&term))
            })
            .collect();
        assert_eq!(
            member.to_vec(),
            rebuilt,
            "each member is its generalization"
        );
    }
    let taken = alloc::vec![var("$g$0")];
    let other = alloc::vec![Term::from(&zero)];
    let Maybe::Present(apart) = TermAlphabet::anti_unify_cmd(&[&taken, &other])
    else {
        panic!("a two-member family generalizes");
    };
    assert_eq!(
        alloc::vec![var("$g$1")],
        apart.patterns,
        "a point's name avoids every member's"
    );
    assert_eq!(
        Maybe::Absent(anti_unification::Absent::EmptyFamily),
        TermAlphabet::anti_unify_cmd(&[]),
        "no member"
    );
    assert_eq!(
        Maybe::Absent(anti_unification::Absent::RaggedFamily),
        TermAlphabet::anti_unify_cmd(&[&first, &other]),
        "members of different lengths"
    );
}

#[test]
fn a_rule_keeps_growing_where_no_rule_rewrites_its_wrapping()
{
    let v = FreeTerm::var;
    let nil = || FreeTerm::op("nil", []);
    let par = |p: FreeTerm, q: FreeTerm| FreeTerm::op("par", [p, q]);
    let cat = |p: FreeTerm, q: FreeTerm| FreeTerm::op("cat", [p, q]);
    let nu = |p: FreeTerm| FreeTerm::op("nu", [p]);
    let grows = |earlier: &(FreeTerm, FreeTerm), later: &(FreeTerm, FreeTerm)| {
        bool::from(rule_keeps_growing(earlier, later, &[]))
    };
    // A scope-extrusion round: the seed under `nu` and beside `q`, extruded.
    let round = |seed: FreeTerm| (nu(par(seed.clone(), v("q"))), par(seed, v("q")));
    let first = round(nil());
    let second = round(par(nil(), v("q'")));
    let third = round(par(par(nil(), v("q'")), v("q''")));
    assert!(grows(&first, &second), "the seed wrapped in `par(□, q')`");
    assert!(
        grows(&second, &third),
        "and again, the inner variable renamed"
    );
    assert!(!grows(&second, &first), "no rule grows from a larger one");
    assert!(!grows(&first, &round(nil())), "no rule grows from itself");
    assert!(
        !grows(&first, &round(par(FreeTerm::op("stop", []), v("r")))),
        "a wrapping that does not hold the seed is no growth"
    );
    let two = |left: FreeTerm, right: FreeTerm| {
        (
            FreeTerm::op("f", [left.clone(), right.clone()]),
            FreeTerm::op("g", [left, right]),
        )
    };
    assert!(
        !grows(
            &two(nil(), nil()),
            &two(par(nil(), v("r")), par(nil(), v("s")))
        ),
        "two subterms wrapped at once"
    );
    let beside = |x: &'static str, y: &'static str, seed: FreeTerm| {
        (
            FreeTerm::op("f", [v(x), v(y), seed.clone()]),
            FreeTerm::op("g", [v(x), v(y), seed]),
        )
    };
    assert!(
        grows(
            &beside("x", "y", nil()),
            &beside("z", "w", par(nil(), v("r")))
        ),
        "the variables beside the seed renamed one to one"
    );
    assert!(
        !grows(
            &beside("x", "y", nil()),
            &beside("z", "z", par(nil(), v("r")))
        ),
        "two variables merged"
    );
    let pair = round(cat(v("x"), v("y")));
    assert!(
        grows(&pair, &round(par(cat(v("x'"), v("y'")), v("r")))),
        "a seed holding two variables, found renamed inside its wrapping"
    );
    assert!(
        !grows(&pair, &round(par(cat(v("x'"), v("x'")), v("r")))),
        "and not once the wrapping merges them"
    );
    // The block's own left sides, `nu(nil)` and `par(nu(p), q)`, and the two
    // rules derived so far match no repetition, so the family grows on.
    let mut lefts = alloc::vec![
        nu(nil()),
        par(nu(v("p")), v("q")),
        first.0.clone(),
        second.0.clone(),
    ];
    assert!(
        bool::from(rule_keeps_growing(&first, &second, &lefts)),
        "the family grows beside its rules"
    );
    let flattening = |depth: usize| {
        (0 .. depth).fold(nil(), |inner, layer| {
            par(inner, FreeTerm::var(alloc::format!("p{layer}")))
        })
    };
    for depth in [3_usize, 4] {
        lefts.push(flattening(depth));
        assert!(
            !bool::from(rule_keeps_growing(&first, &second, &lefts)),
            "a rule rewriting the wrapping {depth} deep stops the family"
        );
        let _flattening = lefts.pop();
    }
}

#[test]
fn a_free_term_reads_back_through_the_alphabet()
{
    let nested = FreeTerm::results([
        FreeTerm::op("add", [turn("Succ", FreeTerm::var("x")), ctor("Zero", [])]),
        FreeTerm::ctor("Pair", [FreeTerm::var("y"), ctor("Zero", [])]),
    ]);
    let term = Term::from(&nested);
    assert_eq!(
        Maybe::Present(nested),
        term.read(),
        "the term reads back as itself"
    );
    assert_eq!(
        Term(alloc::vec![
            Head::Results(Count(2)),
            Head::Op(Name::from("add"), Count(2)),
            Head::Ctor(Name::from("Succ"), Count(1)),
            Head::Var(Name::from("x")),
            Head::Ctor(Name::from("Zero"), Count(0)),
            Head::Ctor(Name::from("Pair"), Count(2)),
            Head::Var(Name::from("y")),
            Head::Ctor(Name::from("Zero"), Count(0)),
        ]),
        term,
        "prefix order, each head its own kind"
    );
    assert_ne!(
        Term::from(&FreeTerm::op("Zero", [])),
        Term::from(&ctor("Zero", [])),
        "an operation and a constructor of one spelling are two heads"
    );
    assert_eq!(
        Maybe::Absent(term_reading::Absent::Skolem),
        TermAlphabet::skolemize(&term).read(),
        "a skolem constant spells no free term"
    );
}

#[test]
fn the_circles_rules_fire_below_the_root()
{
    let base = || ctor("Base", []);
    let word = |turns: &[&str]| {
        turns
            .iter()
            .rev()
            .fold(base(), |inner, name| turn(*name, inner))
    };
    let x = || FreeTerm::var("x");
    let faces = [
        RuleFace::new(
            turn("Loop", turn("Unloop", x())),
            x(),
            Vec::new(),
            SurfaceSpan::default(),
        ),
        RuleFace::new(
            turn("Unloop", turn("Loop", x())),
            x(),
            Vec::new(),
            SurfaceSpan::default(),
        ),
    ];
    let mut store = CellStore::new();
    for face in &faces {
        let cell = face_cell(face);
        assert_eq!(
            (
                Maybe::Present(face.lhs.clone()),
                Maybe::Present(face.rhs.clone())
            ),
            (cell.lhs().read(), cell.rhs().read()),
            "the cell's faces are the written ones"
        );
        assert_eq!(TermOrient::Written, cell.orient(), "as written");
        store.insert(cell);
    }
    for (written, normal, steps) in [
        (word(&["Loop", "Unloop", "Loop"]), word(&["Loop"]), 1),
        (word(&["Loop", "Loop", "Unloop"]), word(&["Loop"]), 1),
        (word(&["Unloop", "Loop"]), word(&[]), 1),
        (
            word(&["Loop", "Unloop", "Unloop", "Loop", "Loop"]),
            word(&["Loop"]),
            2,
        ),
        (word(&["Loop", "Loop"]), word(&["Loop", "Loop"]), 0),
    ] {
        let start = Term::from(&written);
        let reached = normalize(&store, &start, NormalizationBudget::from(16_usize));
        assert!(
            !bool::from(reached.exhausted),
            "{written} reaches a normal form"
        );
        assert_eq!(
            Maybe::Present(normal.clone()),
            reached.normal.read(),
            "{written} normalizes"
        );
        assert_eq!(steps, reached.path.len(), "{written} takes {steps} steps");
        assert!(
            bool::from(replay_path(&store, &start, &reached.normal, &reached.path)),
            "{written}'s path replays"
        );
    }
    let deep = Term::from(&word(&["Loop", "Loop", "Unloop"]));
    let reached = normalize(&store, &deep, NormalizationBudget::from(16_usize));
    assert_eq!(
        Some(&TermAlphabet::position_at_path(&[PositionStep::from(
            0_usize
        )])),
        reached.path.first().map(|step| &step.at),
        "the redex stands below the root"
    );
}
