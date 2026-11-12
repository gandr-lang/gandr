//! One description over the sorts of a mutual block's data families.

use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::CodeNode;
use gandr_theory_levitation::CodeView;
use gandr_theory_levitation::CtorDesc;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::SortDesc;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::ValueTypeView;

use super::DescribedDeclaration;
use super::DescriptionGrade;
use crate::form::Placed;

/// The data families of one mutual block, read as one description: one sort
/// for each family, each constructor at its family's sort, and a field at a
/// sibling family a recursive occurrence at that family's sort.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `members` and `description.sorts` name the same families, in
///   written order.
/// - fails: none as a data value.
/// - panics: none as a data value.
/// - executable: none — the members' declarations are not retained; [`group`]
///   states the relation it builds.
///
/// # Adequacy
/// - hypothesis: L3 — a tree and its forest read as one description of two
///   sorts.
/// - witness: `description::tests::a_mutual_block_s_data_families_read_as_one_description_5018`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MutualDescription
{
    /// Where each family is written, in written order.
    pub members: Vec<Placed>,
    /// The description over the families' sorts.
    pub description: TheoryDesc<DescriptionGrade>,
}

/// The one description over the data families `members` of a mutual block,
/// when there are two or more and they share their parameters.
///
/// # Specification
/// - requires: `members` are the readable declarations of one mutual block, in
///   written order.
/// - ensures: present exactly when at least two members are well-formed,
///   unindexed data families that state the same parameters, and the universe's
///   check admits the description they read as. Then the sorts are those
///   families, in order, and the constructors are theirs, in order. A field
///   whose type is a sibling applied to the shared parameters, in order, is a
///   recursive occurrence at the sibling's sort.
/// - fails: none.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a tree and its forest read as one description, and a lone
///   family reads as none.
/// - witness: `description::tests::a_mutual_block_s_data_families_read_as_one_description_5018`
/// - witness: `description::tests::a_mutual_block_with_one_data_family_reads_no_group_5018`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|group| group.members.len() >= 2 && group.members.len() == group.description.sorts.len()))]
pub(super) fn group(members: &[&DescribedDeclaration]) -> Option<MutualDescription>
{
    let families: Vec<&DescribedDeclaration> = members
        .iter()
        .copied()
        .filter(|member| {
            member.description.polarity == DeclPolarity::Data
                && !member.ill_formed
                && member
                    .description
                    .sorts
                    .iter()
                    .all(|sort| sort.indices.is_empty())
        })
        .collect();
    let [first, _, ..] = *families.as_slice()
    else {
        return None;
    };
    let parameters: Vec<&Name> = first
        .description
        .params
        .iter()
        .map(|parameter| &parameter.name)
        .collect();
    let shared = families.iter().all(|family| {
        family
            .description
            .params
            .iter()
            .map(|parameter| &parameter.name)
            .eq(parameters.iter().copied())
    });
    if !shared {
        return None;
    }
    let names: Vec<&Name> = families
        .iter()
        .map(|family| &family.description.id.name)
        .collect();
    let sorts: Vec<SortDesc> = names
        .iter()
        .map(|&name| SortDesc::new(name.clone(), DeclPolarity::Data))
        .collect();
    let ctors: Vec<CtorDesc<DescriptionGrade>> = families
        .iter()
        .flat_map(|family| family.description.ctors.iter())
        .map(|ctor| CtorDesc {
            code: sorted(&ctor.code, &names, &parameters),
            ..ctor.clone()
        })
        .collect();
    let description = TheoryDesc::new(
        first.description.id.clone(),
        first.description.params.clone(),
        ctors,
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        first.description.attrs.clone(),
    )
    .with_sorts(sorts);
    if !gandr_theory_levitation::check_desc(&description).is_empty() {
        return None;
    }
    Some(MutualDescription {
        members: families.iter().map(|family| family.at).collect(),
        description,
    })
}

/// The payload code `code` with each field at a family of `names`, applied
/// to `parameters` in order, read as a recursive occurrence at that family's
/// sort, alone or as the body of a function former.
///
/// # Specification
/// - requires: `code` is a constructor's payload: a right-nested product of
///   field codes, each a field, a recursive occurrence or a function former
///   over one.
/// - ensures: the same product, each field rewritten as stated and every other
///   code kept.
/// - fails: none.
/// - panics: none.
/// - executable: none — the clause restates the walk over the product.
///
/// # Termination
/// Each turn takes one factor off the product, which is finite.
///
/// # Adequacy
/// - hypothesis: L3 — `More`'s field `head` at `Rose` is an occurrence at
///   `Rose`, and its field at `Forest` one at `Forest`.
/// - witness: `description::tests::a_mutual_block_s_data_families_read_as_one_description_5018`
fn sorted(
    code: &Code<DescriptionGrade>,
    names: &[&Name],
    parameters: &[&Name],
) -> Code<DescriptionGrade>
{
    // The sibling a field's type names at the shared parameters, if any.
    let sibling = |node: CodeNode<'_, DescriptionGrade>| {
        let CodeView::Field { ty, .. } = node.view()
        else {
            return None;
        };
        let ValueTypeView::Ctor { head, args } = ty.view()
        else {
            return None;
        };
        let applied = args.len() == parameters.len()
            && args.zip(parameters).all(|(argument, &name)| {
                matches!(argument.view(), ValueTypeView::Param(written) if written == name)
            });
        (applied && names.contains(&head)).then(|| Code::var(head.clone()))
    };
    let mut factors = Vec::new();
    let mut rest = code.to_node();
    while let CodeView::Prod(mut children) = rest.view() {
        let (Some(left), Some(right)) = (children.next(), children.next())
        else {
            break;
        };
        factors.push(left);
        rest = right;
    }
    factors.push(rest);
    let fields: Vec<Code<DescriptionGrade>> = factors
        .into_iter()
        .map(|factor| match factor.view() {
            CodeView::Field { .. } => sibling(factor).unwrap_or_else(|| factor.to_code()),
            CodeView::Fun { domains, mut body } => body.next().and_then(sibling).map_or_else(
                || factor.to_code(),
                |occurrence| Code::fun(domains.to_vec(), occurrence),
            ),
            CodeView::Unit
            | CodeView::Var(_)
            | CodeView::Prod(_)
            | CodeView::Sum(_)
            | CodeView::Bind { .. } => factor.to_code(),
        })
        .collect();
    Code::product_of(fields)
}
