//! The names the source writes for the binders a declaration's nodes stand
//! under, read off the lowering's origin table: a lambda's or a bind's
//! binder where it is written, a split component by its pattern variable or
//! the label of the field it leaves unwritten, a dependent record's pair by
//! its field's label, and any other binder by a use resolving to it.
//!
//! Every face that spells a node inside a declaration under the binders
//! around it reads them here: a hover's type, a diagnostic's, and the
//! formatter's motive of a path composite written as its transport.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::identity::Relation;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_lowering::ComponentName;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Provenance;
use gandr_surface_lowering::SplitComponent;
use gandr_surface_pretty::BinderIndex;
use gandr_surface_pretty::ChildSlot;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::Scopes;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

/// The name a split component binds, as the record keeps it: where the
/// pattern variable for it is written, or the label of the field a labelled
/// pattern leaves unwritten.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Named
{
    /// The pattern variable, at its span.
    Written(ByteSpan),
    /// The field's label.
    Labelled(String),
}

/// What a lowered module keeps to name the binders its declarations' nodes
/// stand under.
///
/// It holds each declaration's roots, and where the source writes each binder
/// and each use. The scopes are walked one declaration at a time by the reader
/// that needs them, never while the record is built.
///
/// # Specification
/// - requires: built by [`Naming::of`].
/// - ensures: every list is ascending by its key; the text is the source the
///   spans index.
/// - panics: none.
/// - executable: none — this data type has no call boundary; [`Naming::of`] and
///   [`Naming::scoped`] carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Naming::scoped`].
/// - witness: `tests::diagnostics::a_declaration_s_binders_are_named_as_written_803`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Naming
{
    /// The source text the spans index.
    text: String,
    /// Each declaration's declared type and body, ascending by constant.
    roots: Vec<(ConstantIndex, [Option<CoreNode>; 2])>,
    /// Each lambda and bind with where the binder it opens is written,
    /// ascending by id.
    openers: Vec<(ComputationId, ByteSpan)>,
    /// Each split component with the name it binds, ascending by split and
    /// component.
    components: Vec<((ComputationId, SplitComponent), Named)>,
    /// Each dependent arrow with where the name it binds is written,
    /// ascending by id.
    arrows: Vec<(CompTypeId, ByteSpan)>,
    /// Each dependent pair a dependent record's field opens with where the
    /// field's label is written, ascending by id.
    pairs: Vec<(ValueTypeId, ByteSpan)>,
    /// Each type written as a relation between types, with the relation,
    /// ascending by id.
    relations: Vec<(ValueTypeId, Relation)>,
    /// Each written use of a variable with where a name for its binder is
    /// written: first where the origin table records the binder a use
    /// resolves to, then the use itself, which a type's variables have and no
    /// binding records.
    uses: Vec<(ValueId, ByteSpan)>,
}

impl Naming
{
    /// What `module`, lowered from `source`, keeps for naming binders.
    ///
    /// # Specification
    /// - requires: `module` was lowered from `source`.
    /// - ensures: the source text, each value declaration's roots by its
    ///   constant, the origin table's binders, split components, dependent
    ///   arrows, dependent record pairs and relations, and its bindings then
    ///   its written values as uses.
    /// - provides: the input of [`Self::scoped`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder or use left out spells `?` where a node
    ///   under it is spelled, which the test fails on.
    /// - witness: `tests::diagnostics::a_declaration_s_binders_are_named_as_written_803`
    #[spec(ensures: |ret| ret.text == <&str>::from(source)
        && ret.roots.is_sorted_by_key(|&(constant, _)| constant))]
    #[inline]
    #[must_use]
    pub fn of(
        module: &LoweredModule<'_>,
        source: SourceText<'_>,
    ) -> Self
    {
        let origins = module.origins();
        let mut roots: Vec<(ConstantIndex, [Option<CoreNode>; 2])> = module
            .declarations()
            .iter()
            .filter_map(|declaration| {
                let roots = match declaration.outcome() {
                    DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    } => [
                        Some(CoreNode::ValueType(declared_type)),
                        Some(CoreNode::Value(body)),
                    ],
                    DeclarationOutcome::Uncompleted { declared_type } => {
                        [Some(CoreNode::ValueType(declared_type)), None]
                    },
                    DeclarationOutcome::Bodied { body } => [Some(CoreNode::Value(body)), None],
                    DeclarationOutcome::Data(_)
                    | DeclarationOutcome::Codata(_)
                    | DeclarationOutcome::Abstract(_)
                    | DeclarationOutcome::World
                    | DeclarationOutcome::Refused(_) => return None,
                };
                Some((declaration.constant(), roots))
            })
            .collect();
        roots.sort_by_key(|&(constant, _)| constant);
        let mut openers: Vec<(ComputationId, ByteSpan)> = origins
            .binders()
            .iter()
            .map(|&(opener, origin)| (opener, origin.span()))
            .collect();
        openers.sort_by_key(|&(opener, _)| opener);
        let components = origins
            .components()
            .iter()
            .map(|&(component, ref name)| {
                (component, match *name {
                    ComponentName::Written(origin) => Named::Written(origin.span()),
                    ComponentName::Labelled(ref label) => {
                        Named::Labelled(String::from(label.as_ref()))
                    },
                })
            })
            .collect();
        let uses = origins
            .bindings()
            .iter()
            .copied()
            .chain(
                origins
                    .values()
                    .iter()
                    .filter(|&&(_, origin)| origin.provenance() == Provenance::Written)
                    .map(|&(variable, origin)| (variable, origin.span())),
            )
            .collect();
        let arrows = origins
            .arrows()
            .iter()
            .map(|&(arrow, origin)| (arrow, origin.span()))
            .collect();
        let pairs = origins
            .pairs()
            .iter()
            .map(|&(pair, origin)| (pair, origin.span()))
            .collect();
        let mut relations = origins.relations().to_vec();
        relations.sort_by_key(|&(related, _)| related);
        Self {
            text: String::from(<&str>::from(source)),
            roots,
            openers,
            components,
            arrows,
            pairs,
            relations,
            uses,
        }
    }

    /// The source text the record's spans index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn text(&self) -> SourceText<'_>
    {
        SourceText::from(self.text.as_str())
    }

    /// The text the source writes at `span`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn written(
        &self,
        span: ByteSpan,
    ) -> Option<String>
    {
        self.text
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .map(String::from)
    }

    /// The declared type and body of the declaration `constant`, where it is
    /// a value declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn roots(
        &self,
        constant: ConstantIndex,
    ) -> Option<[Option<CoreNode>; 2]>
    {
        self.roots
            .binary_search_by_key(&constant, |&(held, _)| held)
            .ok()
            .and_then(|at| self.roots.get(at))
            .map(|&(_, roots)| roots)
    }

    /// Each value declaration's constant and roots, ascending by constant.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn declarations(&self) -> impl Iterator<Item = (ConstantIndex, [Option<CoreNode>; 2])>
    {
        self.roots.iter().copied()
    }

    /// Each dependent arrow with where the name it binds is written,
    /// ascending by arrow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arrows(&self) -> &[(CompTypeId, ByteSpan)]
    {
        &self.arrows
    }

    /// Each type written as a relation between types, ascending by type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn relations(&self) -> &[(ValueTypeId, Relation)]
    {
        &self.relations
    }

    /// The binders of one declaration, whose declared type and body are
    /// `roots`, each named by what the record keeps for it.
    ///
    /// # Specification
    /// - requires: `arena` holds the declaration's nodes and `names` its
    ///   module's constants'.
    /// - ensures: the scopes of every node reachable from `roots`, and for each
    ///   binder, at its position, the intuitionistic binder around it and its
    ///   name: the one written for the lambda or bind that opens it, or for the
    ///   split component it is, counted from the split's outermost binder, or
    ///   the label of the dependent record field whose pair opens it, else the
    ///   one written at a use's binder; a split component a label pattern
    ///   leaves unwritten is named by its field's label, primed (`′`) until no
    ///   other binder of the declaration holds the name.
    /// - provides: the context a node inside the declaration is spelled in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder left unnamed spells `?` where a node under
    ///   it is spelled, which the test fails on.
    /// - witness: `tests::diagnostics::a_declaration_s_binders_are_named_as_written_803`
    #[spec(ensures: |ret| ret.bound.len() == ret.scopes.binders().len())]
    #[inline]
    #[must_use]
    pub fn scoped(
        &self,
        arena: &CoreArena,
        names: &[String],
        roots: [Option<CoreNode>; 2],
    ) -> Scoped
    {
        let names: Vec<Name<'_>> = names.iter().map(|name| Name::from(name.as_str())).collect();
        let printer = CoreSource::new(arena, &names);
        let scopes = Scopes::of(&printer, roots.into_iter().flatten());
        // A split's binders are consecutive, its outermost component first.
        let mut split: Option<(ComputationId, usize)> = None;
        // The binders a label names, primed apart once every binder is named.
        let mut labelled: Vec<usize> = Vec::new();
        let mut bound: Vec<Bound> = scopes
            .binders()
            .enumerate()
            .map(|(at, (_, binder))| {
                let (name, scope) = match binder.opener() {
                    CoreNode::Computation(opener) => {
                        let component = match split {
                            Some((held, count)) if held == opener => count.saturating_add(1),
                            Some(_) | None => 0,
                        };
                        split = Some((opener, component));
                        let key = (opener, SplitComponent::from(component));
                        let opened = self
                            .openers
                            .binary_search_by_key(&opener, |&(held, _)| held)
                            .ok()
                            .and_then(|at| self.openers.get(at))
                            .and_then(|&(_, span)| self.written(span));
                        let name = opened.or_else(|| {
                            let held = self
                                .components
                                .binary_search_by_key(&key, |&(held, _)| held)
                                .ok()
                                .and_then(|at| self.components.get(at))?;
                            match held.1 {
                                Named::Written(span) => self.written(span),
                                Named::Labelled(ref label) => {
                                    labelled.push(at);
                                    Some(label.clone())
                                },
                            }
                        });
                        (
                            name,
                            binder.slot() == ChildSlot::FIRST
                                && matches!(
                                    arena.computation(opener),
                                    Some(&Computation::Scope { .. })
                                ),
                        )
                    },
                    CoreNode::ValueType(opener) => {
                        split = None;
                        let labelled = self
                            .pairs
                            .binary_search_by_key(&opener, |&(held, _)| held)
                            .ok()
                            .and_then(|at| self.pairs.get(at))
                            .and_then(|&(_, span)| self.written(span));
                        (labelled, false)
                    },
                    CoreNode::Value(_) | CoreNode::CompType(_) => {
                        split = None;
                        (None, false)
                    },
                };
                Bound {
                    around: intuitionistic(&scopes, binder.parent()),
                    name,
                    scope,
                    opener: binder.opener(),
                }
            })
            .collect();
        // A use names the binder it counts out to.
        for &(variable, written_at) in &self.uses {
            let (Some(Some(innermost)), Some(&Value::Variable { zone, index })) = (
                scopes.innermost(CoreNode::Value(variable)),
                arena.value(variable),
            )
            else {
                continue;
            };
            let Some(name) = self.written(written_at).filter(|name| {
                !name.is_empty()
                    && name
                        .chars()
                        .all(|glyph| glyph.is_alphanumeric() || glyph == '_')
            })
            else {
                continue;
            };
            let chain = scopes.around(Some(innermost), zone);
            if let Some(entry) = usize::try_from(u32::from(index))
                .ok()
                .and_then(|index| chain.get(index))
                .and_then(|&at| bound.get_mut(usize::from(at)))
                && entry.name.is_none()
            {
                entry.name = Some(name);
            }
        }
        // A label is the record's own name for the field, so it stands unless
        // a written name already holds it.
        for at in labelled {
            while bound
                .get(at)
                .and_then(|held| held.name.as_deref())
                .is_some_and(|name| {
                    bound
                        .iter()
                        .enumerate()
                        .any(|(other, held)| other != at && held.name.as_deref() == Some(name))
                })
            {
                if let Some(name) = bound.get_mut(at).and_then(|held| held.name.as_mut()) {
                    name.push('′');
                }
            }
        }
        Scoped { scopes, bound }
    }
}

/// One intuitionistic binder a node stands under: the binder around it, the
/// name the source writes for it, whether it is a capability scope's own,
/// whose region a capability type may name, and the former opening it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Bound
{
    /// The intuitionistic binder around this one.
    around: Option<BinderIndex>,
    /// The name written at the binder, or at a use resolving to it; none
    /// where the source writes none.
    name: Option<String>,
    /// Whether the binder is the capability a scope binds over its subject.
    scope: bool,
    /// The former that opens it, whose type, or whose judgement's, states
    /// the type it binds.
    opener: CoreNode,
}

/// One binder a node stands under, as [`Scoped::around`] answers it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Around<'scoped>
{
    /// The name written at the binder, or at a use resolving to it; none
    /// where the source writes none.
    pub name: Option<&'scoped str>,
    /// Whether the binder is the capability a scope binds over its subject.
    pub scope: bool,
    /// The former that opens it.
    pub opener: CoreNode,
}

/// The binders of one declaration with the names the source writes for
/// them, as [`Naming::scoped`] reads them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct Scoped
{
    /// Every binder of the declaration's nodes.
    scopes: Scopes<CoreNode>,
    /// Each binder's name and place, by its position in `scopes`.
    bound: Vec<Bound>,
}

impl Scoped
{
    /// The intuitionistic binders `node` stands under, outermost first;
    /// none when the declaration's roots do not reach `node`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `None` exactly when the scopes hold no position for `node`;
    ///   otherwise each intuitionistic binder from the outermost around `node`
    ///   to the innermost, with its name, whether it is a capability scope's
    ///   own and its opener.
    /// - provides: the context `node` is spelled in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// A binder's parent precedes it, so the chain strictly descends.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Naming::scoped`].
    /// - witness: `tests::diagnostics::a_declaration_s_binders_are_named_as_written_803`
    #[spec(ensures: |ret| ret.is_none() == self.scopes.innermost(node).is_none())]
    #[inline]
    #[must_use]
    pub fn around(
        &self,
        node: CoreNode,
    ) -> Option<Vec<Around<'_>>>
    {
        let innermost = self.scopes.innermost(node)?;
        let mut around = Vec::new();
        let mut at = intuitionistic(&self.scopes, innermost);
        while let Some(index) = at {
            let Some(binder) = self.bound.get(usize::from(index))
            else {
                break;
            };
            around.push(Around {
                name: binder.name.as_deref(),
                scope: binder.scope,
                opener: binder.opener,
            });
            at = binder.around.filter(|&around| around < index);
        }
        around.reverse();
        Some(around)
    }
}

/// The intuitionistic binder at or around `at`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first intuitionistic binder of the chain from `at` outward;
///   none when the chain holds none.
/// - provides: a node's context, which skips a fork's linear binders.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// A binder's parent precedes it, so the chain strictly descends.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Naming::scoped`].
/// - witness: `tests::diagnostics::a_declaration_s_binders_are_named_as_written_803`
#[spec(ensures: |ret| ret.is_none_or(|index| scopes.binder(index).is_some_and(|binder| binder.zone() == Zone::Intuitionistic)))]
fn intuitionistic(
    scopes: &Scopes<CoreNode>,
    at: Option<BinderIndex>,
) -> Option<BinderIndex>
{
    let mut at = at;
    while let Some(index) = at {
        let binder = scopes.binder(index)?;
        if binder.zone() == Zone::Intuitionistic {
            return Some(index);
        }
        at = binder.parent().filter(|&parent| parent < index);
    }
    None
}
