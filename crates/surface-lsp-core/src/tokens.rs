//! Semantic tokens of a judged copy: each written use classified by what the
//! checker resolved it to. The `tokens` module of `gandr-surface-lsp-base`
//! encodes the spans as the protocol's integer stream.
//!
//! # Uses are classified by what they refer to
//!
//! Once a copy is judged, each written use the referent index resolves is sent
//! as what it refers to rather than as its syntactic guess
//! ([`classified`]): a family as `type`, a constructor as `enumMember`, any
//! other declaration as `function`, and a binder's use as its binder's own
//! role makes it, a parameter's as `parameter`. A use the lowering refused as
//! naming nothing (`UnresolvedName`, `UnresolvedTypeHead`) is sent as
//! `unresolvedReference`, the one type outside the standard set: the legend
//! declares it, a client with no style for it paints the token unstyled, and
//! an editor extension contributes its colour. A copy not yet judged is sent
//! as the highlighter classified it.
//!
//! # Names carry the table's reading
//!
//! A judged copy's names also carry how the judgement reads them
//! ([`Resolved::marks`]): `declaration` on each binder's own name and each
//! declaration's — a parameter, a pattern variable, a `let` or lambda binder,
//! a constructor, a definition's name — and the custom pair `value` and
//! `computation` by the name's polarity. A called name, which the lowering
//! forces, is a `computation`; a binder, a constructor's name and an argument
//! passed along are `value`s. The legend declares the pair, and the editor
//! extension declares it too, so a theme can select `*.computation`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::Binding;
use gandr_surface_dispatcher::NameKind;
use gandr_surface_dispatcher::Polarity;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_lsp_base::tokens::Resolved;
use gandr_surface_lsp_base::tokens::TokenModifiers;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use quenchant_shape::shape::Maybe;

/// The roles of a span that is a written use the referent index may resolve.
const USES: [HlRole; 6] = [
    HlRole::Variable,
    HlRole::VariableParam,
    HlRole::FunctionCall,
    HlRole::Constructor,
    HlRole::Type,
    HlRole::TypeVariable,
];

/// The roles of a span that writes a name: a use's, and a definition's.
const NAMES: [HlRole; 8] = [
    HlRole::Variable,
    HlRole::VariableParam,
    HlRole::FunctionCall,
    HlRole::Constructor,
    HlRole::Type,
    HlRole::TypeVariable,
    HlRole::FunctionDef,
    HlRole::VariableDef,
];

/// The highlighter's spans of the text that `table` judged, each written use
/// classified by its referent.
///
/// `spans` gives the classification. Each written use takes what `table`
/// resolved it to, each use inside a name that `table` records as unresolved
/// takes that mark, and each name takes the modifiers that `table` reads it
/// with.
///
/// # Specification
/// - requires: `spans` are the highlighter's spans of the text `table`'s own
///   source holds.
/// - ensures: one span per span of `spans`, at the same range. A span of a
///   use's role ([`HlRole::Variable`], [`HlRole::VariableParam`],
///   [`HlRole::FunctionCall`], [`HlRole::Constructor`], [`HlRole::Type`],
///   [`HlRole::TypeVariable`]) whose range is exactly a use `table` resolves
///   takes the role of its referent: [`HlRole::Type`] for a family,
///   [`HlRole::Constructor`] for a constructor, [`HlRole::FunctionCall`] for
///   any other declaration, and for a binder the use's role its binder's own
///   span declares ([`HlRole::VariableParam`] for a parameter,
///   [`HlRole::TypeVariable`] for a type variable, [`HlRole::FunctionCall`] for
///   a function, [`HlRole::Variable`] for any other binder), its own role when
///   the binder has no span. Every other span keeps its role. Such a use
///   `table` does not resolve, lying wholly inside a span of
///   [`TypeTable::unresolved`], is listed in `unresolved`, in order. Every
///   other span of a name's role ([`USES`]' roles, [`HlRole::FunctionDef`],
///   [`HlRole::VariableDef`]) is listed in `marks` when it carries a modifier:
///   `declaration` when its range is exactly a binder's name in
///   [`TypeTable::readings`] or a declared name of the table's own source, and
///   `value` or `computation` by the polarity [`TypeTable::readings`] reads at
///   exactly its range.
/// - provides: the classification the semantic tokens of a judged copy send.
/// - fails: never.
/// - panics: none.
/// - intension: one sort of the unit's declared names, then one lookup in the
///   referent index and one binary search per use, and two binary searches per
///   name.
///
/// # Adequacy
/// - hypothesis: L3 — a family, a constructor, a declaration and a parameter
///   each written where the highlighter guesses another role are sent as what
///   they refer to, a name no declaration answers as unresolved, and a span
///   that is no use keeps its role; a binder's name and a declaration's carry
///   `declaration`, a called name `computation` and an argument `value`.
/// - witness: `gandr-surface-lsp::server::tests::a_use_is_sent_as_what_it_refers_to`
/// - witness: `gandr-surface-lsp::server::tests::a_name_is_sent_with_its_reading`
#[spec(ensures: |ret| ret.spans.len() == spans.len()
    && ret.spans.iter().zip(spans).all(|(kept, written)| kept.range == written.range)
    && ret.unresolved.is_sorted()
    && ret.marks.is_sorted_by_key(|mark| mark.0)
    && ret.marks.iter().all(|mark| ret.unresolved.binary_search(&mark.0).is_err()))]
#[must_use]
#[inline]
pub fn classified(
    spans: &[HlSpan],
    table: &TypeTable,
) -> Resolved
{
    let mut kinds: Vec<(Referent, NameKind)> = table.declared_names().to_vec();
    kinds.sort_unstable();
    let own = table.own_source();
    let mut declaring: Vec<(usize, usize)> = kinds
        .iter()
        .filter(|&&(referent, _)| referent.source() == own)
        .map(|&(referent, _)| {
            (
                usize::from(referent.named().start()),
                usize::from(referent.named().end()),
            )
        })
        .collect();
    declaring.sort_unstable();
    let readings = table.readings();
    let refused = table.unresolved();
    let mut unresolved = Vec::new();
    let mut marks = Vec::new();
    let classified = spans
        .iter()
        .map(|&span| {
            let start = usize::from(span.range.start());
            let end = usize::from(span.range.end());
            let mut mark = |resolved: bool| {
                let reading = readings
                    .binary_search_by_key(&(start, end), |&(read, _)| {
                        (usize::from(read.start()), usize::from(read.end()))
                    })
                    .ok()
                    .and_then(|found| readings.get(found))
                    .map(|&(_, reading)| reading);
                let declares = !resolved
                    && (declaring.binary_search(&(start, end)).is_ok()
                        || reading.is_some_and(|read| read.binding == Binding::Binds));
                let added = TokenModifiers::NONE
                    .with(if declares {
                        TokenModifiers::DECLARATION
                    }
                    else {
                        TokenModifiers::NONE
                    })
                    .with(match reading.map(|read| read.polarity) {
                        Some(Polarity::Value) => TokenModifiers::VALUE,
                        Some(Polarity::Computation) => TokenModifiers::COMPUTATION,
                        None => TokenModifiers::NONE,
                    });
                if added != TokenModifiers::NONE {
                    marks.push((span.range, added));
                }
            };
            if !USES.contains(&span.role) {
                if NAMES.contains(&span.role) {
                    mark(false);
                }
                return span;
            }
            match table.referent(gandr_surface_syntax::ByteOffset::from(start)) {
                Maybe::Present((used, referent))
                    if (usize::from(used.start()), usize::from(used.end())) == (start, end) =>
                {
                    mark(true);
                    HlSpan {
                        role: referred(span.role, referent, &kinds, spans),
                        ..span
                    }
                },
                Maybe::Present(_) | Maybe::Absent(_) => {
                    if refused.iter().any(|within| {
                        usize::from(within.start()) <= start && end <= usize::from(within.end())
                    }) {
                        unresolved.push(span.range);
                    }
                    else {
                        mark(false);
                    }
                    span
                },
            }
        })
        .collect();
    Resolved {
        spans: classified,
        unresolved,
        marks,
    }
}

/// The role a use written as `role` takes for referring to `referent`.
///
/// # Specification
/// - requires: `kinds` is sorted; `spans` are the highlighter's spans of the
///   use's own text.
/// - ensures: as [`classified`] states for one resolved use.
/// - fails: never.
/// - panics: none.
/// - executable: none — the role is read off the declared kinds and the
///   binder's own span, which the arguments do not carry back; [`classified`]
///   states the whole classification, checked through its witness.
///
/// # Adequacy
/// - hypothesis: L3 — as [`classified`].
/// - witness: `gandr-surface-lsp::server::tests::a_use_is_sent_as_what_it_refers_to`
fn referred(
    role: HlRole,
    referent: Referent,
    kinds: &[(Referent, NameKind)],
    spans: &[HlSpan],
) -> HlRole
{
    if let Ok(found) = kinds.binary_search_by_key(&referent, |&(declared, _)| declared) {
        return match kinds.get(found).map(|&(_, kind)| kind) {
            Some(NameKind::Family) => HlRole::Type,
            Some(NameKind::Constructor) => HlRole::Constructor,
            Some(NameKind::Value) => HlRole::FunctionCall,
            None => role,
        };
    }
    let named = usize::from(referent.named().start());
    spans
        .binary_search_by_key(&named, |site| usize::from(site.range.start()))
        .ok()
        .and_then(|found| spans.get(found))
        .map_or(role, |site| match site.role {
            HlRole::VariableParam => HlRole::VariableParam,
            HlRole::TypeVariable => HlRole::TypeVariable,
            HlRole::FunctionDef => HlRole::FunctionCall,
            HlRole::VariableDef => HlRole::Variable,
            HlRole::Keyword
            | HlRole::Boolean
            | HlRole::Operator
            | HlRole::FunctionCall
            | HlRole::Variable
            | HlRole::Member
            | HlRole::Constructor
            | HlRole::Type
            | HlRole::TypeBuiltin
            | HlRole::Number
            | HlRole::StringLit
            | HlRole::Character
            | HlRole::Escape
            | HlRole::Path
            | HlRole::Comment
            | HlRole::Hole
            | HlRole::Directive
            | HlRole::Label
            | HlRole::Other => role,
        })
}
