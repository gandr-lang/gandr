//! Where the grammar decides a token as it reads it, and where it reads on.
//!
//! # Two places a token can wait
//!
//! The molder decides a token from the molds its label can take. It decides
//! the token as it reads it when one mold fits. It reads on, ranking
//! candidates or opening a window, where two fit. The mold table names both
//! places, so the ledger reads them off the table and never off a sample.
//!
//! | Place | Read from | When the molder reads on |
//! | ----- | --------- | ------------------------ |
//! | an opener | each label's fresh candidates | two rules of one sort open on the label, a hole facing both openers alike or neither |
//! | a fork | each mold's same-form successors | one label continues the form at two molds after it |
//!
//! A rule with no shared opener and no fork is decided at each of its own
//! tokens as the molder reads it. The tokens inside its holes are their own
//! rules' to decide.
//!
//! - Choice: the table alone, so the analysis is a function of the grammar and
//!   `check:syntax-ledger` holds it; a spelling change shows its move in
//!   review.
//! - Alternatives: the molder's counters over the corpus, which measure what
//!   the corpus writes and miss a form it never writes.
//! - Reversal: a molder that decides an opener or a fork by a rule the table
//!   does not carry, such as a precedence the molder reads before admission,
//!   moves that place out of the analysis.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;

use anodized::spec;
use gandr_surface_grammar::LabelId;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_syntax::MoldId;
use gandr_theory_graphs::Bound;

use super::Decision;
use super::LedgerFault;
use super::Menu;

/// What two openers of one label must agree on to tie: the sort the form
/// produces, and whether a hole faces the opener on its left.
type OpenerKey = (LabelId, Sort, bool);

/// Each rule's decision, in grammar order.
///
/// # Specification
/// - requires: `molds` holds one list per rule of `pbg`, in grammar order, as
///   [`molds_by_rule`](super::molds_by_rule) builds it.
/// - ensures: one decision per rule. Its molds are its list's length. Its
///   openers are the labels of its molds that are fresh candidates of their
///   label. It shares an opener with every other rule of its sort holding a
///   fresh mold of the same label whose left side a hole faces exactly when its
///   own does. Its forks count its molds after which some label stands at two
///   same-form successors or more.
/// - fails: a lookup the grammar refuses.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Grammar`] for a refused lookup.
///
/// # Adequacy
/// - hypothesis: L3 — over the built-in grammar, a rule decided at every token
///   reads no shared opener and no fork, a prefix and an infix opener of one
///   label do not tie, two rules of one sort opening on one label tie both
///   ways, and a parameter list that reads a name two ways forks. The census
///   gives one decision per rule whose molds sum to the table's.
/// - witness: `ledger::decisions::tests::each_rule_reads_its_openers_and_forks`
/// - witness: `ledger::decisions::tests::a_shared_opener_is_shared_both_ways`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |decided| decided.len() == molds.len() && decided.iter().zip(molds).all(|(decision, list)| decision.molds == list.len())))]
pub(super) fn decisions(
    pbg: &Pbg,
    molds: &[Vec<MoldId>],
) -> Result<Vec<Decision>, LedgerFault>
{
    let mut openers: BTreeMap<OpenerKey, BTreeSet<usize>> = BTreeMap::new();
    let mut keys: Vec<BTreeSet<OpenerKey>> = vec![BTreeSet::new(); molds.len()];
    let mut decided: Vec<Decision> = Vec::with_capacity(molds.len());
    for (index, (list, rule)) in molds.iter().zip(pbg.rules()).enumerate() {
        let mut opens: BTreeSet<&'static str> = BTreeSet::new();
        let mut forks = 0_usize;
        for &mold in list {
            let def = pbg.mold(mold).map_err(LedgerFault::Grammar)?;
            let label = pbg.mold_label(mold).ok_or(LedgerFault::Grammar(
                gandr_surface_grammar::PbgError::UnknownMold { id: mold },
            ))?;
            if pbg
                .label_fresh_candidates(label)
                .binary_search(&mold)
                .is_ok()
            {
                let (left, _right) = pbg.bounds(mold).map_err(LedgerFault::Grammar)?;
                let key = (label, rule.sort, matches!(left, Bound::Value(_)));
                let _first = openers.entry(key).or_default().insert(index);
                if let Some(held) = keys.get_mut(index) {
                    let _first = held.insert(key);
                }
                let _first = opens.insert(def.label);
            }
            let mut next: BTreeMap<LabelId, usize> = BTreeMap::new();
            for &(_, successor) in pbg.mold_successors(mold) {
                if let Some(successor_label) = pbg.mold_label(successor) {
                    let count = next.entry(successor_label).or_default();
                    *count = count.saturating_add(1);
                }
            }
            if next.values().any(|&count| count > 1) {
                forks = forks.saturating_add(1);
            }
        }
        decided.push(Decision {
            molds: list.len(),
            opens: opens.into_iter().collect(),
            shares: Vec::new(),
            forks,
        });
    }
    for (index, held) in keys.iter().enumerate() {
        let shares: BTreeSet<&'static str> = held
            .iter()
            .filter_map(|key| openers.get(key))
            .flatten()
            .filter(|&&other| other != index)
            .filter_map(|&other| pbg.rules().get(other).map(|rule| rule.name))
            .collect();
        if let Some(decision) = decided.get_mut(index) {
            decision.shares = shares.into_iter().collect();
        }
    }
    Ok(decided)
}

/// Every label's menu, the largest first and then by label.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one menu per label a mold carries. Its molds are the label's
///   candidates, its rules the distinct rules they belong to, and its opening
///   molds the label's fresh candidates. The menus descend by molds, ties
///   ascending by label.
/// - fails: a lookup the grammar refuses.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Grammar`] for a refused lookup.
///
/// # Adequacy
/// - hypothesis: L3 — over the built-in grammar, the menus' molds sum to the
///   table's, the identifier's menu is the largest, and a keyword one rule
///   writes once has a menu of one mold in one rule that opens it.
/// - witness: `ledger::decisions::tests::each_label_has_one_menu`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |menus| menus.iter().map(|menu| menu.molds).sum::<usize>() == pbg.iter_molds().count() && menus.windows(2).all(|pair| match *pair { [ref first, ref second] => (second.molds, first.label) < (first.molds, second.label), _ => true })))]
pub(super) fn menus(pbg: &Pbg) -> Result<Vec<Menu>, LedgerFault>
{
    let mut labels: BTreeMap<&'static str, LabelId> = BTreeMap::new();
    for (mold, def) in pbg.iter_molds() {
        let label = pbg.mold_label(mold).ok_or(LedgerFault::Grammar(
            gandr_surface_grammar::PbgError::UnknownMold { id: mold },
        ))?;
        let _held = labels.entry(def.label).or_insert(label);
    }
    let mut menus = Vec::with_capacity(labels.len());
    for (text, label) in labels {
        let candidates = pbg.label_candidates(label);
        let rules: BTreeSet<&'static str> = candidates
            .iter()
            .map(|&mold| pbg.rule_of(mold).map(|rule| rule.name))
            .collect::<Result<_, _>>()
            .map_err(LedgerFault::Grammar)?;
        menus.push(Menu {
            label: text,
            molds: candidates.len(),
            rules: rules.len(),
            opening: pbg.label_fresh_candidates(label).len(),
        });
    }
    menus.sort_by(|first, second| {
        second
            .molds
            .cmp(&first.molds)
            .then_with(|| first.label.cmp(second.label))
    });
    Ok(menus)
}

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::RuleName;
    use gandr_surface_grammar::built_in;

    use super::Decision;
    use super::decisions;
    use super::menus;
    use crate::ledger::molds_by_rule;

    /// The built-in grammar and each rule's decision, by rule name.
    ///
    /// # Specification
    /// trivial.
    fn decided() -> (Pbg, Vec<(RuleName, Decision)>)
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let molds = molds_by_rule(&pbg).expect("every mold has its rule");
        let decided = decisions(&pbg, &molds).expect("the table answers every lookup");
        let named = pbg
            .rules()
            .iter()
            .map(|rule| RuleName(rule.name))
            .zip(decided)
            .collect();
        (pbg, named)
    }

    /// The decision of the rule named `name`.
    ///
    /// # Specification
    /// trivial.
    fn of(
        decided: &[(RuleName, Decision)],
        name: RuleName,
    ) -> &Decision
    {
        decided
            .iter()
            .find(|&&(rule, _)| rule == name)
            .map(|&(_, ref decision)| decision)
            .expect("the rule is built in")
    }

    /// A prefix and an infix opener of `-` do not tie, nor two rules of
    /// different sorts opening on `{`; a name pattern and a cons pattern
    /// do; a parameter list forks; a keyword alone is decided at its token;
    /// and the molds sum to the table's.
    #[test]
    fn each_rule_reads_its_openers_and_forks()
    {
        let (pbg, decided) = decided();
        for name in ["unary_expression", "binary_expression.add.minus"] {
            let decision = of(&decided, RuleName(name));
            assert_eq!(decision.opens, ["-"], "{name}");
            assert!(decision.shares.is_empty(), "{name}: {:?}", decision.shares);
        }
        for name in ["block", "statement_block"] {
            let decision = of(&decided, RuleName(name));
            assert_eq!(decision.opens, ["{"], "{name}");
            assert!(decision.shares.is_empty(), "{name}: {:?}", decision.shares);
        }
        assert_eq!(of(&decided, RuleName("cons_pattern")).shares, [
            "identifier.pattern"
        ]);
        assert_eq!(of(&decided, RuleName("identifier.pattern")).shares, [
            "cons_pattern"
        ]);
        let def = of(&decided, RuleName("def_value"));
        assert_eq!((def.opens.as_slice(), def.shares.len()), (&["def"][..], 0));
        assert!(def.forks > 0, "a parameter's name reads two ways");
        assert_eq!(of(&decided, RuleName("return_expression")), &Decision {
            molds: 1,
            opens: vec!["return"],
            shares: Vec::new(),
            forks: 0,
        });
        assert_eq!(
            decided
                .iter()
                .map(|&(_, ref decision)| decision.molds)
                .sum::<usize>(),
            pbg.iter_molds().count()
        );
    }

    /// Every shared opener is shared from both sides, between rules of one
    /// sort.
    #[test]
    fn a_shared_opener_is_shared_both_ways()
    {
        let (pbg, decided) = decided();
        let sort = |name: RuleName| {
            pbg.rules()
                .iter()
                .find(|rule| RuleName(rule.name) == name)
                .map(|rule| rule.sort)
        };
        let mut pairs = 0_usize;
        for &(rule, ref decision) in &decided {
            for &other in &decision.shares {
                assert!(
                    of(&decided, RuleName(other)).shares.contains(&rule.0),
                    "{} and {other}",
                    rule.0
                );
                assert_eq!(sort(rule), sort(RuleName(other)), "{} and {other}", rule.0);
                pairs = pairs.saturating_add(1);
            }
        }
        assert!(pairs > 0, "the built-in grammar ties at some opener");
    }

    /// Each label has one menu, the identifier's the largest, a keyword one
    /// rule writes once a menu of one opening mold, and the menus' molds sum
    /// to the table's.
    #[test]
    fn each_label_has_one_menu()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let menus = menus(&pbg).expect("the table answers every lookup");
        assert_eq!(menus.first().map(|menu| menu.label), Some("identifier"));
        let ret = menus
            .iter()
            .find(|menu| menu.label == "return")
            .expect("`return` is a label");
        assert_eq!((ret.molds, ret.rules, ret.opening), (1, 1, 1));
        assert_eq!(
            menus.iter().map(|menu| menu.molds).sum::<usize>(),
            pbg.iter_molds().count()
        );
        let mut labels: Vec<&str> = menus.iter().map(|menu| menu.label).collect();
        labels.sort_unstable();
        labels.dedup();
        assert_eq!(labels.len(), menus.len());
    }
}
