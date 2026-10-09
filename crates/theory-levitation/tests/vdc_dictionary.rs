//! The virtual double category dictionary: the laws of a split cartesian
//! fibrant virtual double category, checked on the crate's own structures,
//! with a verdict per law.
//!
//! Every locator cites Hayato Nasu, *Logical Aspects of Virtual Double
//! Categories*, arXiv:2501.17869: Definition 3.2.6 is the split cartesian
//! fibrant virtual double category, Lemma 3.2.8 its splitness lemma.
//!
//! # What is the crate's, and what is a stand-in
//!
//! Objects (`harness::SigObj` over real `SignDesc`s), tight arrows (renamings
//! of real constructor and operation symbols, checked against their real
//! `Code`s and `BridgeArity`s) and restriction (real `RuleFace`s recomputed
//! through the real `derive_cell_var_meta`, judged by the real `check_desc`)
//! are built directly on the crate. The multi-ary cell machinery
//! (`harness::Cell`, `harness::replay`, `harness::graft`) and the term
//! machinery (`terms`) are stand-ins: the crate carries neither, and these
//! tests fix what a consumer's must satisfy.
//!
//! # Verdicts
//!
//! | Law | Verdict | Strict or up to replay | Obligation located |
//! | --- | --- | --- | --- |
//! | 1, tight category | holds | strict, structural | none |
//! | 2, multicategorical cells | holds | up to replay | none; symbolic grafting is partial (the unital cases and the linear single-clause chain), and other shapes defer to replay-level composition |
//! | 3, restriction | holds | (a) strict on the crate's `RuleFace`; (b) the four Definition 3.2.6 equalities strict by construction; (c) split fibrationality from the representation; (d) strict | none |
//! | 4, cartesian | holds | pairing and β up to replay; local `⊤` and `∧` strict through law 3 | none; pairing uniqueness is checked on pair-shaped cells only |
//! | 5, units | partial | β strict on `refl` | path induction declines on a non-empty path: instances must be closed under path action, a saturation invariant on a cell store, and the saturation probe shows it sufficient |
//!
//! Laws 1 to 4 hold, 1 and 3 strictly, 2 and 4 up to replay-equivalence,
//! the identity of cells. Law 5's decline locates a precise cell-store
//! invariant rather than a defect.
//!
//! # What the crate leaves to its consumers
//!
//! * No matching or substitution on `FreeTerm`: the first-order matcher,
//!   substitution, rewriter and bounded path search are the suite's
//!   (`law3::matching_and_substitution_are_supplied_test_side`).
//! * `RuleFace` and `check_desc` are single-signature: a loose arrow between
//!   distinct signatures has no well-formedness support, and the unbound-rhs
//!   rule is a rewrite discipline, not the condition for a two-sided relation
//!   (`law3::check_desc_is_single_signature_homogeneous`,
//!   `law3::unbound_rhs_rule_is_a_rewrite_discipline_not_a_relation_condition`).
//! * No signature-morphism type: `SigMorphism` and its checker live in the
//!   harness (`law1::check_morphism_accepts_a_role_matched_renaming`,
//!   `law1::check_morphism_rejects_code_and_arity_violations`).
//!
//! # The split form
//!
//! All four Definition 3.2.6 equalities hold by construction, because a
//! formal restriction `base[left # right]` never touches its base under
//! restriction; it only composes into the tight frames. `α[id # id] = α`
//! because composing with an identity is the identity; `α[s # t][s′ # t′] =
//! α[s∘s′ # t∘t′]` because tight composition is associative (law 1); `⊤[s #
//! t] = ⊤` because the empty `∧`-tuple has no factors to restrict; and `(α ∧
//! β)[s # t] = α[s # t] ∧ β[s # t]` because restriction maps over the tuple.
//! Law 3(a) carries the content on the crate's own structure: the face
//! action is split on `RuleFace` itself.

mod fixtures;
mod harness;
mod law1_tight;
mod law2_cells;
mod law3_restriction;
mod law4_cartesian;
mod law5_units;
mod terms;
