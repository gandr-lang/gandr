//! The built-in surface: its precedence bands, its named-kind coverage, its
//! sort tags, its adaptation records, and the completion shape of its type
//! formers.

use alloc::collections::BTreeSet;
use alloc::format;
use core::error::Error;

use anodized::spec;
use gandr_surface_grammar::NamedKind;
use gandr_surface_grammar::NamedKindRealization;
use gandr_surface_grammar::PBG_ONLY_KINDS;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::PrecName;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::TREE_SITTER_NAMED_KINDS;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::built_in;
use gandr_surface_grammar::built_in_prec_table;
use gandr_surface_grammar::named_kind_parity;
use gandr_surface_grammar::named_kind_realization;
use gandr_surface_parser::parse;
use gandr_surface_syntax::GroutSort;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::PrecDag;

/// The built-in groups with their associativity, in dense id order.
const EXPECTED_PRECEDENCE_GROUPS: &[(&str, Assoc)] = &[
    ("item.singleton", Assoc::Non),
    ("expression.atom", Assoc::Non),
    ("expression.postfix", Assoc::Left),
    ("expression.unary", Assoc::Non),
    ("expression.mul", Assoc::Left),
    ("expression.add", Assoc::Left),
    ("expression.cmp", Assoc::Left),
    ("expression.and", Assoc::Left),
    ("expression.or", Assoc::Left),
    ("expression.ret", Assoc::Right),
    ("pattern.atom", Assoc::Non),
    ("pattern.as", Assoc::Left),
    ("pattern.or", Assoc::Left),
    ("type.atom", Assoc::Non),
    ("type.application", Assoc::Non),
    ("type.product", Assoc::Right),
    ("type.sum", Assoc::Right),
    ("type.union", Assoc::Right),
    ("type.intersection", Assoc::Right),
    ("type.lazy_product", Assoc::Right),
    ("type.arrow", Assoc::Right),
];

/// The built-in tighter-than edges, in the DAG's edge order.
const EXPECTED_PRECEDENCE_EDGES: &[(&str, &str)] = &[
    ("expression.atom", "expression.postfix"),
    ("expression.postfix", "expression.unary"),
    ("expression.unary", "expression.mul"),
    ("expression.mul", "expression.add"),
    ("expression.add", "expression.cmp"),
    ("expression.cmp", "expression.and"),
    ("expression.and", "expression.or"),
    ("expression.or", "expression.ret"),
    ("pattern.atom", "pattern.as"),
    ("pattern.as", "pattern.or"),
    ("type.atom", "type.application"),
    ("type.application", "type.product"),
    ("type.product", "type.sum"),
    ("type.sum", "type.union"),
    ("type.sum", "type.intersection"),
    ("type.sum", "type.lazy_product"),
    ("type.union", "type.arrow"),
    ("type.intersection", "type.arrow"),
    ("type.lazy_product", "type.arrow"),
];

/// The group of `dag` named `name`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the group named `name`.
/// - panics: when `dag` has no such group.
///
/// # Adequacy
/// - hypothesis: For the built-in bands and forms, L2 exact edge, associativity
///   and opener observations catch missing groups, reversed comparisons and
///   extra candidates. The predicate observes the claimed relation on normal
///   return; deliberately failing assertion inputs are not exhausted.
/// - witness: `tests::surface::built_in_precedence_bands_are_exact`
#[spec(ensures: |ret| dag.name(ret).is_some_and(|actual| actual == name.0))]
fn prec(
    dag: &PrecDag,
    name: PrecName,
) -> Prec
{
    dag.groups()
        .find_map(|(prec, candidate, _assoc)| (candidate == name.0).then_some(prec))
        .unwrap_or_else(|| panic!("missing precedence group `{name}`"))
}

/// Asserts each group of `names` binds tighter than the next.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns when every consecutive pair is ordered both ways round.
/// - panics: on the first pair that is not.
///
/// # Adequacy
/// - hypothesis: For the built-in bands and forms, L2 exact edge, associativity
///   and opener observations catch missing groups, reversed comparisons and
///   extra candidates. The predicate observes the claimed relation on normal
///   return; deliberately failing assertion inputs are not exhausted.
/// - witness: `tests::surface::built_in_precedence_bands_are_exact`
#[spec(ensures: |()| names.windows(2).all(|pair| pair.first().zip(pair.last()).is_some_and(|(tighter, looser)| bool::from(dag.gt(prec(dag, *tighter), prec(dag, *looser), Assoc::Non)) && bool::from(dag.lt(prec(dag, *looser), prec(dag, *tighter), Assoc::Non)))))]
fn assert_chain(
    dag: &PrecDag,
    names: &[PrecName],
)
{
    for pair in names.windows(2) {
        let &[tighter_name, looser_name] = pair
        else {
            continue;
        };
        let tighter = prec(dag, tighter_name);
        let looser = prec(dag, looser_name);
        assert!(
            bool::from(dag.gt(tighter, looser, Assoc::Non)),
            "{tighter_name} binds tighter than {looser_name}"
        );
        assert!(
            bool::from(dag.lt(looser, tighter, Assoc::Non)),
            "{looser_name} binds looser than {tighter_name}"
        );
    }
}

/// Asserts the group `name` has associativity `assoc`, and that the
/// reflexive comparisons answer exactly as that associativity says.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns when non-associativity admits only `eq`, left
///   associativity only `gt`, and right associativity only `lt`.
/// - panics: on the first comparison that disagrees.
///
/// # Adequacy
/// - hypothesis: For the built-in bands and forms, L2 exact edge, associativity
///   and opener observations catch missing groups, reversed comparisons and
///   extra candidates. The predicate observes the claimed relation on normal
///   return; deliberately failing assertion inputs are not exhausted.
/// - witness: `tests::surface::built_in_precedence_bands_are_exact`
#[spec(ensures: |()| { let group = prec(dag, name); dag.assoc(group) == Some(assoc) && bool::from(dag.eq(group, group, Assoc::Non)) == (assoc == Assoc::Non) && bool::from(dag.gt(group, group, Assoc::Left)) == (assoc == Assoc::Left) && bool::from(dag.lt(group, group, Assoc::Right)) == (assoc == Assoc::Right) })]
fn assert_assoc(
    dag: &PrecDag,
    name: PrecName,
    assoc: Assoc,
)
{
    let group = prec(dag, name);
    assert_eq!(Some(assoc), dag.assoc(group), "{name} associativity");
    assert_eq!(
        assoc == Assoc::Non,
        bool::from(dag.eq(group, group, Assoc::Non)),
        "{name} meets itself as equal exactly when non-associative"
    );
    assert_eq!(
        assoc == Assoc::Left,
        bool::from(dag.gt(group, group, Assoc::Left)),
        "{name} takes itself exactly when left-associative"
    );
    assert_eq!(
        assoc == Assoc::Right,
        bool::from(dag.lt(group, group, Assoc::Right)),
        "{name} yields to itself exactly when right-associative"
    );
}

/// Asserts the groups `left` and `right` are incomparable.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns when neither is tighter than the other.
/// - panics: when one is.
///
/// # Adequacy
/// - hypothesis: For the built-in bands and forms, L2 exact edge, associativity
///   and opener observations catch missing groups, reversed comparisons and
///   extra candidates. The predicate observes the claimed relation on normal
///   return; deliberately failing assertion inputs are not exhausted.
/// - witness: `tests::surface::built_in_precedence_bands_are_exact`
#[spec(ensures: |()| !bool::from(dag.comparable(prec(dag, left), prec(dag, right))) && !bool::from(dag.lt(prec(dag, left), prec(dag, right), Assoc::Non)) && !bool::from(dag.gt(prec(dag, left), prec(dag, right), Assoc::Non)))]
fn assert_incomparable(
    dag: &PrecDag,
    left: PrecName,
    right: PrecName,
)
{
    let left_prec = prec(dag, left);
    let right_prec = prec(dag, right);
    assert!(
        !bool::from(dag.comparable(left_prec, right_prec)),
        "{left} and {right} are incomparable"
    );
    assert!(!bool::from(dag.lt(left_prec, right_prec, Assoc::Non)));
    assert!(!bool::from(dag.gt(left_prec, right_prec, Assoc::Non)));
}

/// Asserts `pbg` has a checked form of `sort`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns when some form group has sort `sort`.
/// - panics: when none has.
///
/// # Adequacy
/// - hypothesis: For the built-in bands and forms, L2 exact edge, associativity
///   and opener observations catch missing groups, reversed comparisons and
///   extra candidates. The predicate observes the claimed relation on normal
///   return; deliberately failing assertion inputs are not exhausted.
/// - witness: `tests::surface::named_kind_coverage_is_semantic`
#[spec(ensures: |()| pbg.forms().keys().any(|&(form_sort, _)| form_sort == sort))]
fn assert_has_checked_form(
    pbg: &Pbg,
    sort: Sort,
)
{
    assert!(
        pbg.forms()
            .keys()
            .any(|&(form_sort, _prec)| form_sort == sort),
        "the built-in surface has a checked {} form",
        sort.name()
    );
}

/// The one type-sort mold of `label` that opens a form.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns that mold.
/// - panics: when there is not exactly one.
///
/// # Adequacy
/// - hypothesis: For the built-in bands and forms, L2 exact edge, associativity
///   and opener observations catch missing groups, reversed comparisons and
///   extra candidates. The predicate observes the claimed relation on normal
///   return; deliberately failing assertion inputs are not exhausted.
/// - witness: `tests::surface::prefix_formers_keep_required_type_tails_unclosed`
#[spec(ensures: |ret| pbg.candidates(label).iter().copied().filter(|&id| pbg.mold(id).is_ok_and(|mold| mold.sort == Sort::Type) && bool::from(pbg.mold_is_form_first(id))).eq([ret]))]
fn only_type_opener(
    pbg: &Pbg,
    label: TileLabel,
) -> MoldId
{
    let openers: Vec<MoldId> = pbg
        .candidates(label)
        .iter()
        .copied()
        .filter(|&mold| {
            pbg.mold(mold).is_ok_and(|def| def.sort == Sort::Type)
                && bool::from(pbg.mold_is_form_first(mold))
        })
        .collect();
    let &[mold] = openers.as_slice()
    else {
        panic!("{label} has exactly one type-form opener: {openers:?}");
    };
    mold
}

#[test]
fn built_in_precedence_bands_are_exact() -> Result<(), Box<dyn Error>>
{
    let precs = built_in_prec_table()?;
    let dag = precs.dag();
    let groups: Vec<(&str, Assoc)> = dag
        .groups()
        .map(|(_prec, name, assoc)| {
            let name = EXPECTED_PRECEDENCE_GROUPS
                .iter()
                .find(|&&(expected, _)| name == expected)
                .map_or("<unexpected>", |&(expected, _)| expected);
            (name, assoc)
        })
        .collect();
    assert_eq!(EXPECTED_PRECEDENCE_GROUPS, groups.as_slice());

    for &(name, _assoc) in EXPECTED_PRECEDENCE_GROUPS {
        assert_eq!(Ok(prec(dag, PrecName(name))), precs.prec(PrecName(name)));
    }
    assert_eq!(
        Err(PbgError::MissingPrec { name: "missing" }),
        precs.prec(PrecName("missing"))
    );

    let edges: Vec<(Prec, Prec)> = dag.edges().collect();
    let expected_edges: Vec<(Prec, Prec)> = EXPECTED_PRECEDENCE_EDGES
        .iter()
        .map(|&(tighter, looser)| (prec(dag, PrecName(tighter)), prec(dag, PrecName(looser))))
        .collect();
    assert_eq!(expected_edges, edges);

    assert_chain(dag, &[
        PrecName("expression.atom"),
        PrecName("expression.postfix"),
        PrecName("expression.unary"),
        PrecName("expression.mul"),
        PrecName("expression.add"),
        PrecName("expression.cmp"),
        PrecName("expression.and"),
        PrecName("expression.or"),
        PrecName("expression.ret"),
    ]);
    assert_chain(dag, &[
        PrecName("pattern.atom"),
        PrecName("pattern.as"),
        PrecName("pattern.or"),
    ]);
    assert_chain(dag, &[
        PrecName("type.atom"),
        PrecName("type.application"),
        PrecName("type.product"),
        PrecName("type.sum"),
    ]);
    for middle in ["type.union", "type.intersection", "type.lazy_product"] {
        assert_chain(dag, &[
            PrecName("type.sum"),
            PrecName(middle),
            PrecName("type.arrow"),
        ]);
    }

    for &(name, assoc) in EXPECTED_PRECEDENCE_GROUPS {
        assert_assoc(dag, PrecName(name), assoc);
    }

    for (left, right) in [
        ("item.singleton", "expression.atom"),
        ("item.singleton", "pattern.atom"),
        ("item.singleton", "type.atom"),
        ("expression.ret", "pattern.or"),
        ("expression.atom", "type.arrow"),
        ("pattern.atom", "type.atom"),
        ("type.union", "type.intersection"),
        ("type.union", "type.lazy_product"),
        ("type.intersection", "type.lazy_product"),
    ] {
        assert_incomparable(dag, PrecName(left), PrecName(right));
    }
    Ok(())
}

#[test]
fn named_kind_coverage_is_semantic() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let committed: BTreeSet<&str> = TREE_SITTER_NAMED_KINDS.iter().copied().collect();
    assert_eq!(124, TREE_SITTER_NAMED_KINDS.len());
    assert_eq!(124, committed.len(), "named kinds are unique");

    let pbg_only: BTreeSet<&str> = PBG_ONLY_KINDS.iter().copied().collect();
    assert_eq!(
        PBG_ONLY_KINDS.len(),
        pbg_only.len(),
        "grammar-only kinds are unique"
    );
    assert!(pbg_only.is_disjoint(&committed));
    let recognised: BTreeSet<&str> = committed.union(&pbg_only).copied().collect();

    // Every provenance and every adaptation surface is a recognised kind.
    let provenances: BTreeSet<&str> = pbg.rules().iter().map(|rule| rule.provenance().0).collect();
    assert!(provenances.is_subset(&recognised));
    let folded: BTreeSet<&str> = pbg
        .adaptations()
        .iter()
        .map(|adaptation| adaptation.surface)
        .collect();
    assert!(folded.is_subset(&recognised));

    // Every grammar-only kind is realised, so the list carries no dead entry.
    let realised: BTreeSet<&str> = provenances.union(&folded).copied().collect();
    assert!(
        pbg_only.is_subset(&realised),
        "grammar-only kinds are realised"
    );

    // Every inventoried kind is realised as classified.
    let item_has_forms = pbg
        .forms()
        .keys()
        .any(|&(form_sort, _prec)| form_sort == Sort::Item);
    for entry in named_kind_parity() {
        match entry.realization {
            | NamedKindRealization::StructuralForms => assert!(
                realised.contains(entry.kind),
                "named kind {} is realised by a form or an adaptation",
                entry.kind
            ),
            | NamedKindRealization::FileRoot => assert!(item_has_forms),
        }
    }
    let inventoried: Vec<&str> = named_kind_parity()
        .into_iter()
        .map(|entry| entry.kind)
        .collect();
    assert_eq!(TREE_SITTER_NAMED_KINDS, inventoried.as_slice());
    assert_eq!(
        NamedKindRealization::FileRoot,
        named_kind_realization(NamedKind("source_file"))
    );
    assert_eq!(
        NamedKindRealization::StructuralForms,
        named_kind_realization(NamedKind("def_value"))
    );
    for kind in ["", "source", "source_file ", "Source_file", "unknown_kind"] {
        assert_eq!(
            NamedKindRealization::StructuralForms,
            named_kind_realization(NamedKind(kind))
        );
    }

    for sort in [
        Sort::Item,
        Sort::Pattern,
        Sort::Expression,
        Sort::Type,
        Sort::Instantiation,
        Sort::ModuleMember,
    ] {
        assert_has_checked_form(&pbg, sort);
    }
    Ok(())
}

#[test]
fn every_mold_resolves_to_its_rule_and_named_kind() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let recognised: BTreeSet<&str> = TREE_SITTER_NAMED_KINDS
        .iter()
        .chain(PBG_ONLY_KINDS)
        .copied()
        .collect();
    let positions: Vec<&str> = pbg.rules().iter().map(|rule| rule.name).collect();
    let mut previous = 0_usize;
    for (id, def) in pbg.iter_molds() {
        let rule = pbg.rule_of(id)?;
        assert_eq!(
            (rule.sort, rule.prec),
            (def.sort, def.prec),
            "mold {id:?} carries its rule's sort and precedence"
        );
        let position = positions
            .iter()
            .position(|&name| name == rule.name)
            .expect("the rule is one of the grammar's");
        assert!(position >= previous, "ids meet the rules in order");
        previous = position;
        let kind = pbg.named_kind(id)?;
        assert_eq!(NamedKind(rule.provenance), kind);
        assert!(
            recognised.contains(kind.0),
            "mold {id:?} names the known kind {}",
            kind.0
        );
    }

    let past = MoldId::try_from(pbg.mold_count().0)?;
    assert_eq!(
        Err(PbgError::UnknownMold { id: past }),
        pbg.named_kind(past)
    );
    assert_eq!(
        Some(PbgError::UnknownMold { id: past }),
        pbg.rule_of(past).err()
    );

    let members: Vec<MoldId> = pbg
        .candidates(TileLabel("def"))
        .iter()
        .copied()
        .filter(|&mold| {
            pbg.mold(mold)
                .is_ok_and(|def| def.sort == Sort::ModuleMember)
        })
        .collect();
    assert!(!members.is_empty(), "a module member opens with `def`");
    for mold in members {
        assert_eq!(NamedKind("module_declaration"), pbg.named_kind(mold)?);
    }
    Ok(())
}

#[test]
fn sort_decode_contract()
{
    let cases = [
        (0, Sort::Item),
        (1, Sort::Pattern),
        (2, Sort::Expression),
        (3, Sort::Type),
        (4, Sort::Instantiation),
        (5, Sort::ModuleMember),
    ];
    for (tag, sort) in cases {
        assert_eq!(GroutSort::from(tag), sort.grout_sort());
        assert_eq!(Ok(sort), Sort::try_from_tag(GroutSort::from(tag)));
    }
    assert_eq!(
        Err(PbgError::InvalidSort {
            sort: GroutSort::from(6)
        }),
        Sort::try_from_tag(GroutSort::from(6))
    );
}

#[test]
fn built_in_adaptations_name_their_rules() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    assert!(!pbg.adaptations().is_empty());
    for adaptation in pbg.adaptations() {
        assert!(
            pbg.rule_names().contains(adaptation.rule),
            "adaptation rule {} is a checked rule",
            adaptation.rule
        );
        assert!(!adaptation.reason.is_empty(), "an adaptation says why");
    }
    Ok(())
}

/// The prefix type formers `-F` and `+U` end their form only once their operand
/// is filled, and open no delimiter, so they name no closing class.
#[test]
fn prefix_formers_keep_required_type_tails_unclosed() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    for label in ["-F", "+U"] {
        let mold = only_type_opener(&pbg, TileLabel(label));
        assert!(
            !bool::from(pbg.mold_is_form_last(mold)),
            "{label} cannot close before its operand"
        );
        assert!(
            bool::from(pbg.mold_has_required_tail(mold)),
            "{label} carries a required type tail"
        );
        assert_eq!(None, pbg.closing_class(mold), "{label} opens no delimiter");
    }
    Ok(())
}

/// The type arrow completes cleanly: its required right operand is matched
/// by its required left operand.
#[test]
fn infix_type_operator_keeps_clean_completion() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let arrows: Vec<MoldId> = pbg
        .candidates(TileLabel("->"))
        .iter()
        .copied()
        .filter(|&mold| pbg.mold(mold).is_ok_and(|def| def.sort == Sort::Type))
        .collect();
    let &[arrow] = arrows.as_slice()
    else {
        panic!("the type arrow has one mold: {arrows:?}");
    };
    assert!(bool::from(pbg.mold_is_form_last(arrow)));
    assert!(!bool::from(pbg.mold_has_required_tail(arrow)));
    Ok(())
}

#[test]
fn circuit_arrows_stay_inside_complete_declarations()
{
    let grammar = built_in().expect("checked grammar");
    for arrow in ["-->", "<->", "==>", "<=>"] {
        let source = format!("oper step : () {arrow} ()");
        let parsed =
            parse(&grammar, SourceText::from(source.as_str())).expect("complete declaration");
        assert!(
            bool::from(parsed.is_clean()),
            "{arrow}: {:?}",
            parsed.obligations()
        );
        let tree = parsed.tree();
        let forms: Vec<_> = tree
            .children(tree.root())
            .filter_map(|position| {
                let node = tree.node(position)?;
                if let NodeLabel::Meld(id) = node.label() {
                    Some((id, node.span()))
                }
                else {
                    None
                }
            })
            .collect();
        let &[(root_mold, span)] = forms.as_slice()
        else {
            panic!("one complete circuit form");
        };
        assert_eq!(
            "circuit_declaration",
            grammar.rule_of(root_mold).expect("known form").name().0
        );
        assert_eq!(0, usize::from(span.start()));
        assert_eq!(source.len(), usize::from(span.end()));
        let arrow_owners: Vec<_> = tree
            .positions()
            .filter_map(|position| {
                let node = tree.node(position)?;
                let NodeLabel::Tile(id) = node.label()
                else {
                    return None;
                };
                let mold = grammar.mold(id).ok()?;
                (mold.label == arrow).then(|| grammar.rule_of(id).expect("known arrow").name())
            })
            .collect();
        assert_eq!([RuleName("circuit_declaration")], arrow_owners.as_slice());
    }
}

#[test]
fn module_member_repetition_preserves_siblings_and_nesting() -> Result<(), Box<dyn Error>>
{
    let grammar = built_in()?;
    let source = "module M { def one = 1; module N { def two = 2; } def three = 3; }";
    let parsed = parse(&grammar, SourceText::from(source))?;
    assert!(bool::from(parsed.is_clean()), "{:?}", parsed.obligations());
    let tree = parsed.tree();
    let roots: Vec<_> = tree
        .children(tree.root())
        .filter_map(|position| {
            let node = tree.node(position)?;
            if let NodeLabel::Meld(id) = node.label() {
                Some((position, grammar.rule_of(id).expect("known root").name()))
            }
            else {
                None
            }
        })
        .collect();
    let &[(outer, owner)] = roots.as_slice()
    else {
        panic!("one complete module");
    };
    assert_eq!(RuleName("module_declaration"), owner);
    let outer_span = tree.node(outer).expect("outer module").span();
    assert_eq!(0, usize::from(outer_span.start()));
    assert_eq!(source.len(), usize::from(outer_span.end()));
    let members: Vec<_> = tree
        .children(outer)
        .filter_map(|position| {
            let node = tree.node(position)?;
            if let NodeLabel::Meld(id) = node.label() {
                Some((position, grammar.rule_of(id).expect("known member").name()))
            }
            else {
                None
            }
        })
        .collect();
    let &[
        (first, first_kind),
        (nested, nested_kind),
        (last, last_kind),
    ] = members.as_slice()
    else {
        panic!("three sibling members");
    };
    assert_eq!(
        [
            RuleName("module_definition_member"),
            RuleName("nested_module_member"),
            RuleName("module_definition_member")
        ],
        [first_kind, nested_kind, last_kind]
    );
    for (position, expected) in [
        (first, "def one = 1;"),
        (nested, "module N { def two = 2; }"),
        (last, "def three = 3;"),
    ] {
        let span = tree.node(position).expect("member").span();
        assert_eq!(
            Some(expected),
            source.get(usize::from(span.start()) .. usize::from(span.end()))
        );
    }
    let nested_members: Vec<_> = tree
        .children(nested)
        .filter_map(|position| {
            let node = tree.node(position)?;
            if let NodeLabel::Meld(id) = node.label() {
                Some((
                    grammar.rule_of(id).expect("known nested member").name(),
                    node.span(),
                ))
            }
            else {
                None
            }
        })
        .collect();
    let &[(kind, span)] = nested_members.as_slice()
    else {
        panic!("one nested definition");
    };
    assert_eq!(RuleName("module_definition_member"), kind);
    assert_eq!(
        Some("def two = 2;"),
        source.get(usize::from(span.start()) .. usize::from(span.end()))
    );
    Ok(())
}
