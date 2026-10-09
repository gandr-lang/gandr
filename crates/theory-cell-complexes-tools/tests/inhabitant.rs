//! The inhabitant laws every engine above the substrate spends, checked over
//! both inhabitants through the generic interface alone: the sequent alphabet
//! and the toy alphabet, whose terms nest commands.
//!
//! A cell fires by matching its left-hand side and substituting into its
//! right-hand side, and an engine rewrites below the root by reading and
//! splicing at a position. An inhabitant whose match and substitution
//! disagree, or whose splice and read disagree, would make every
//! alphabet-generic result measured over it meaningless. The copy search the
//! substrate's linearity boundary runs is read through the same interface, so
//! it is checked over the toy alphabet too, and so is anti-unification, whose
//! law is the match law read backward: each member of a family is its
//! generalization under its own arms.

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Generalization;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::PositionStep;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_cell_complexes::anti_unification;
use gandr_theory_cell_complexes::copied_hole;
use gandr_theory_cell_complexes::copy_search;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToyVar;
use gandr_theory_cell_complexes_tools::toy_cell;
use quenchant_shape::shape::Maybe;

/// `pattern` matched against `target`, and the substitution it found.
///
/// # Specification
/// - panics: when the match is refused, which is a fixture defect.
fn matched<A>(
    pattern: &A::Cmd,
    target: &A::Cmd,
) -> A::Subst
where
    A: CellAlphabet,
{
    let mut subst = A::Subst::default();
    assert!(
        bool::from(A::match_cmd(pattern, target, &mut subst)),
        "the schematic pattern matches the term"
    );
    subst
}

/// The match law: substituting the match into its pattern reproduces the
/// matched term.
///
/// # Specification
/// - panics: when the law fails.
fn match_reproduces<A>(
    pattern: &A::Cmd,
    target: &A::Cmd,
) where
    A: CellAlphabet,
{
    let subst = matched::<A>(pattern, target);
    assert_eq!(
        *target,
        A::apply_subst(&subst, pattern),
        "applying the match to the pattern reproduces the term it matched"
    );
}

/// The binding law: a successful match leaves no metavariable of the pattern
/// free, except one the target itself carries.
///
/// # Specification
/// - panics: when the law fails.
fn match_binds_every_metavariable<A>(
    pattern: &A::Cmd,
    target: &A::Cmd,
) where
    A: CellAlphabet,
{
    let subst = matched::<A>(pattern, target);
    let left_free = A::metavariables(&A::apply_subst(&subst, pattern));
    let target_vars = A::metavariables(target);
    for var in A::metavariables(pattern) {
        assert!(
            target_vars.contains(&var) || !left_free.contains(&var),
            "every metavariable the pattern names is bound by the match"
        );
    }
}

/// The splice law at one position, both ways: splicing back what was read
/// there is the identity, and reading after a splice returns what was spliced.
///
/// # Specification
/// - panics: when either direction fails.
fn splice_agrees_with_read<A>(
    term: &A::Cmd,
    pos: &A::Pos,
    replacement: &A::Cmd,
) where
    A: CellAlphabet,
{
    let Maybe::Present(read) = A::subterm_cmd_at(term, pos)
    else {
        panic!("the position addresses a command");
    };
    assert_eq!(
        Ok(term.clone()),
        A::splice_cmd_at(term, pos, read),
        "splicing a subterm back where it came from is the identity"
    );
    let spliced =
        A::splice_cmd_at(term, pos, replacement.clone()).expect("the slot takes a command");
    assert_eq!(
        Maybe::Present(replacement.clone()),
        A::subterm_cmd_at(&spliced, pos),
        "reading where a command was spliced returns that command"
    );
}

/// The anti-unification law: each member of `family` is its generalization
/// with its own arm applied at every point; the generalization is returned for
/// the caller's further reading.
///
/// # Specification
/// - panics: when the family is refused or the law fails.
fn generalization_reproduces<A>(family: &[&[A::Cmd]]) -> Generalization<A>
where
    A: CellAlphabet,
{
    let Maybe::Present(generalization) = A::anti_unify_cmd(family)
    else {
        panic!("the family generalizes");
    };
    for (index, member) in family.iter().enumerate() {
        let rebuilt: Vec<A::Cmd> = generalization
            .patterns
            .iter()
            .map(|pattern| {
                generalization
                    .points
                    .iter()
                    .fold(pattern.clone(), |term, point| {
                        A::apply_subst(&point.arms[index].binding, &term)
                    })
            })
            .collect();
        assert_eq!(
            member.to_vec(),
            rebuilt,
            "member {index} is its generalization under its arms"
        );
    }
    generalization
}

/// `⟨Succ(m) | add(n; α)⟩`, the successor rule's left-hand side.
///
/// # Specification
/// trivial.
fn successor_lhs() -> CmdPat
{
    CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Succ", [ProdPat::meta("m")]),
        ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
    )
}

/// `⟨Succ(Zero) | add(Succ(Zero); ★)⟩`, a configuration it matches.
///
/// # Specification
/// trivial.
fn successor_configuration() -> CmdPat
{
    let one = || ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]);
    CmdPat::cut(
        Polarity::Positive,
        one(),
        ConsPat::op("add", [one()], ConsPat::top()),
    )
}

#[test]
fn matching_then_substituting_returns_the_matched_term()
{
    match_reproduces::<SequentAlphabet>(&successor_lhs(), &successor_configuration());
    match_reproduces::<ToyAlphabet>(
        &Toy::add(Toy::var("x"), Toy::var("y")),
        &Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
    );
    // A repeated metavariable matches equal subterms and reproduces them.
    match_reproduces::<ToyAlphabet>(
        &Toy::add(Toy::var("x"), Toy::var("x")),
        &Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero())),
    );
}

#[test]
fn a_successful_match_binds_every_metavariable_the_pattern_names()
{
    match_binds_every_metavariable::<SequentAlphabet>(&successor_lhs(), &successor_configuration());
    match_binds_every_metavariable::<ToyAlphabet>(
        &Toy::add(Toy::var("x"), Toy::var("y")),
        &Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
    );
    // A target carrying a metavariable of its own: the pattern's are bound,
    // the target's are what remains.
    match_binds_every_metavariable::<ToyAlphabet>(
        &Toy::add(Toy::var("x"), Toy::var("y")),
        &Toy::add(Toy::var("z"), Toy::zero()),
    );
}

#[test]
fn splicing_at_a_position_agrees_with_reading_it()
{
    splice_agrees_with_read::<SequentAlphabet>(
        &successor_configuration(),
        &SequentAlphabet::root_position(),
        &successor_lhs(),
    );
    let term = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    for path in [&[][..], &[0][..], &[0, 0][..], &[1][..]] {
        let steps: Vec<PositionStep> = path.iter().copied().map(PositionStep::from).collect();
        splice_agrees_with_read::<ToyAlphabet>(
            &term,
            &ToyAlphabet::position_at_path(&steps),
            &Toy::add(Toy::var("w"), Toy::zero()),
        );
    }
}

#[test]
fn the_copy_search_is_alphabet_neutral()
{
    assert_eq!(
        Maybe::Present(ToyVar::from("x")),
        copied_hole(&toy_cell(
            Toy::add(Toy::var("x"), Toy::var("x")),
            Toy::var("x")
        )),
        "the toy's repeated hole is the copy"
    );
    assert_eq!(
        Maybe::Absent(copy_search::Absent::Linear),
        copied_hole(&toy_cell(
            Toy::add(Toy::var("x"), Toy::var("y")),
            Toy::add(Toy::var("y"), Toy::var("y")),
        )),
        "and a toy cell linear on the left copies nothing, whatever its right-hand side repeats"
    );
}

#[test]
fn each_member_is_its_generalization_under_its_arms()
{
    generalization_reproduces::<SequentAlphabet>(&[&[successor_lhs()], &[
        successor_configuration(),
    ]]);
    let one = || Toy::succ(Toy::zero());
    generalization_reproduces::<ToyAlphabet>(&[
        &[Toy::add(one(), Toy::var("x")), Toy::succ(Toy::var("x"))],
        &[
            Toy::add(Toy::succ(one()), Toy::zero()),
            Toy::succ(Toy::zero()),
        ],
        &[
            Toy::add(Toy::zero(), Toy::add(one(), one())),
            Toy::succ(Toy::add(one(), one())),
        ],
    ]);
}

#[test]
fn a_repeated_disagreement_stands_one_point()
{
    let twice = |term: Toy| Toy::add(term.clone(), term);
    let repeated = generalization_reproduces::<ToyAlphabet>(&[&[twice(Toy::zero())], &[twice(
        Toy::succ(Toy::zero()),
    )]]);
    assert_eq!(
        (1_usize, &[Toy::add(Toy::var("$g$0"), Toy::var("$g$0"))][..]),
        (repeated.points.len(), repeated.patterns.as_slice()),
        "one disagreement met twice stands one point at both places"
    );
    let crossed = generalization_reproduces::<ToyAlphabet>(&[
        &[Toy::add(Toy::zero(), Toy::succ(Toy::zero()))],
        &[Toy::add(Toy::succ(Toy::zero()), Toy::zero())],
    ]);
    assert_eq!(
        2,
        crossed.points.len(),
        "two disagreements that differ member by member stand two points"
    );
}

#[test]
fn a_point_takes_a_name_no_member_wears()
{
    let generalization =
        generalization_reproduces::<ToyAlphabet>(&[&[Toy::succ(Toy::var("$g$0"))], &[Toy::succ(
            Toy::zero(),
        )]]);
    assert_eq!(
        ToyVar::from("$g$1"),
        generalization.points[0].var,
        "the first fresh name is worn by a member, so the next is taken"
    );
}

#[test]
fn a_family_without_a_generalization_is_refused_by_name()
{
    assert_eq!(
        Maybe::Absent(anti_unification::Absent::EmptyFamily),
        ToyAlphabet::anti_unify_cmd(&[]).map(|generalization| generalization.patterns),
        "a family with no member"
    );
    assert_eq!(
        Maybe::Absent(anti_unification::Absent::RaggedFamily),
        ToyAlphabet::anti_unify_cmd(&[&[Toy::zero()], &[Toy::zero(), Toy::zero()]])
            .map(|generalization| generalization.patterns),
        "members of two lengths"
    );
}
