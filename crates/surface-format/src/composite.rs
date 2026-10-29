//! The transports of the derived path operations a source writes, as its
//! lowering derived them, for the explicit spelling of `p then q`, `back(p)`
//! and `cong(f, p)`.
//!
//! `p then q` is the transport `transport(\y. Path(A, a, y), q, p)`, `back(p)`
//! is `transport(\y. Path(A, y, a), p, here(a))` and `cong(f, p)` is
//! `transport(\y. Path(B, f(a), f(y)), p, here(f(a)))`: their carrier and
//! fixed endpoint the type of `p`, which the lowering derives from the
//! operands; the syntax does not hold them. So the explicit spelling reads
//! them from the lowering: the transport the lowering minted at the
//! operation's span, spelled through the shared printer in the explicit
//! form, its first argument the motive and its third the value it moves,
//! under the names the source writes for the binders around the operation.
//! An operation whose transport the printer cannot spell faithfully — one
//! standing under a binder the source names nothing — has none, keeps its
//! spelling and is reported.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::Naming;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::label;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Fidelity;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::present_computation;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// One token of a spelled motive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token
{
    /// Its text.
    pub text: String,
    /// Whether the printer wrote whitespace before it.
    pub spaced: Spaced,
}

/// Whether whitespace stands before a token.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Spaced
{
    /// It does.
    Yes,
    /// It does not.
    No,
}

/// How the lowering holds a composite the source writes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Standing
{
    /// A transport returned as a value: the printer writes it `p then q`.
    Returned,
    /// A transport otherwise, a body's last step among them: the printer
    /// writes it as written.
    Run,
    /// A composite of flows, which the core holds as written: its explicit
    /// spelling is its own.
    Flows,
}

/// A transport the lowering derived at a span of the source, its arguments
/// as the printer spells them in the explicit form.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Derived
{
    /// The span of the operation that derives it.
    span: ByteSpan,
    /// Its motive.
    motive: Vec<Token>,
    /// The value it moves.
    value: Vec<Token>,
}

/// The motive of each path composite the source writes, by the composite's
/// span in the source, and the spans of the transports the lowering returns
/// as values.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Motives
{
    /// The transports the lowering derived and the printer spells.
    derived: Vec<Derived>,
    /// The spans of the transports, written or derived, the lowering returns
    /// as values: those the printer writes as `p then q`. A transport standing
    /// as a computation, a body's last step, it writes as written.
    returned: Vec<ByteSpan>,
    /// The spans of the flow composites, which the core holds as written.
    flows: Vec<ByteSpan>,
    /// Which composites have one.
    reach: Reach,
}

/// Which forms a table the lowering derived answers for: [`Motives`]'
/// composites, `crate::tail::Tails`' exits.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Reach
{
    /// Those the lowering derived: a motive the printer spells, an exit the
    /// lowering would infer.
    #[default]
    Derived,
    /// Every one, an empty motive standing in where none was derived: the
    /// writing that asks which forms a rewrite would enter, never laid out.
    Any,
}

impl Motives
{
    /// A motive for every composite, empty where none was derived: for the
    /// writing that asks which forms a rewrite would enter.
    ///
    /// # Specification
    /// trivial.
    pub const fn any() -> Self
    {
        Self {
            derived: Vec::new(),
            returned: Vec::new(),
            flows: Vec::new(),
            reach: Reach::Any,
        }
    }

    /// How the lowering holds the composite spanning exactly `span`.
    ///
    /// # Specification
    /// trivial.
    pub fn standing(
        &self,
        span: ByteSpan,
    ) -> Standing
    {
        if self.flows.contains(&span) {
            return Standing::Flows;
        }
        let returned = match self.reach {
            Reach::Derived => self.returned.contains(&span),
            Reach::Any => true,
        };
        if returned {
            Standing::Returned
        }
        else {
            Standing::Run
        }
    }

    /// The motive's tokens of the transport derived at exactly `span`.
    ///
    /// # Specification
    /// trivial.
    pub fn of(
        &self,
        span: ByteSpan,
    ) -> Option<&[Token]>
    {
        self.read(span, |derived| derived.motive.as_slice())
    }

    /// The tokens of the value the transport derived at exactly `span`
    /// moves: the reflexivity an inverse or an action on a path moves.
    ///
    /// # Specification
    /// trivial.
    pub fn value(
        &self,
        span: ByteSpan,
    ) -> Option<&[Token]>
    {
        self.read(span, |derived| derived.value.as_slice())
    }

    /// What `part` reads of the transport derived at exactly `span`; empty
    /// where none was derived when every composite has one.
    ///
    /// # Specification
    /// trivial.
    fn read<'motives>(
        &'motives self,
        span: ByteSpan,
        part: impl Fn(&'motives Derived) -> &'motives [Token],
    ) -> Option<&'motives [Token]>
    {
        let derived = self
            .derived
            .iter()
            .find(|derived| derived.span == span)
            .map(part);
        match self.reach {
            Reach::Derived => derived,
            Reach::Any => Some(derived.unwrap_or_default()),
        }
    }
}

/// The motives of the path composites `module`, lowered into `arena` from
/// `text`, of which the formatted source starts at `base`, derived: each
/// transport the lowering minted at a span of the source, spelled in the
/// explicit form under the binders the source opens around it, by that span;
/// and the span of every transport it returns as a value.
///
/// # Specification
/// - requires: `module` was lowered from `text` into `arena`.
/// - ensures: a motive for each span's transport minted last, when the printer
///   spells it faithfully under the names the source writes for the binders
///   around it, in a type or a body alike, read from a declaration a form of
///   the source writes; none for one standing under a binder the source names
///   nothing, outside every value declaration's roots, or only in a functor
///   instantiation's copy of a member, which no form writes and whose names are
///   the argument's.
/// - provides: the motives the explicit form writes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a motive spelled outside its binders names them `?` and
///   is withheld, so the explicit form keeps `then`; the test spells one under
///   a declaration's parameter, in its type and its body, and one a functor's
///   instantiation alone could spell; and a composite beside a call whose
///   result type holds composites at the composite's own span.
/// - witness: `tests::rewrite::a_composite_under_a_parameter_takes_its_motive_803`
/// - witness: `tests::rewrite::a_functor_s_composite_takes_no_motive_from_its_instantiation_2166`
/// - witness: `tests::rewrite::a_composite_beside_a_call_takes_its_own_motive_3772`
#[spec(ensures: |ret| ret.reach == Reach::Derived)]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "one binder buffer per declaration, reused across its composites: its names \
                  borrow that declaration's scopes, which the next pass replaces"
    )
)]
pub fn motives(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    text: SourceText<'_>,
    base: ByteOffset,
) -> Motives
{
    let owned = constant_names(module, module.unit().source_at(base));
    let names: Vec<Name<'_>> = owned.iter().map(|name| Name::from(name.as_str())).collect();
    let families = Families::of(module);
    let constructors = families.naming();
    let style = Style {
        form: Form::Explicit,
        spelling: Spelling::Ascii,
    };
    let origins = module.origins();
    let mut returned = Vec::new();
    let mut flows = Vec::new();
    for &(id, origin) in origins.values() {
        let Some(span) = within(origin.span(), base)
        else {
            continue;
        };
        match arena.value(id) {
            Some(&Value::Returned(transport))
                if matches!(
                    arena.computation(transport),
                    Some(&Computation::PathTransport { .. })
                ) =>
            {
                returned.push(span);
            },
            Some(&Value::Then(..)) => flows.push(span),
            Some(_) | None => {},
        }
    }
    let mut composites: Vec<(ByteSpan, ComputationId)> = origins
        .computations()
        .iter()
        .filter(|&&(id, _)| {
            matches!(
                arena.computation(id),
                Some(&Computation::PathTransport { .. })
            )
        })
        .filter_map(|&(id, origin)| Some((within(origin.span(), base)?, id)))
        .collect();
    // A functor's instantiation copies the functor's members, origins and
    // all, under a name the application binds and no form writes: a
    // composite is spelled only from a declaration a form writes, never from
    // a copy, whose spelling names the argument's members rather than the
    // parameter's.
    let written: BTreeSet<ConstantIndex> = module
        .declarations()
        .iter()
        .filter(|declaration| {
            [
                declaration.signature(),
                declaration.definition(),
                declaration.refused_form(),
            ]
            .iter()
            .any(|half| matches!(*half, Maybe::Present(_)))
        })
        .map(LoweredDeclaration::constant)
        .collect();
    let naming = Naming::of(module, text);
    let mut found: Vec<(ByteSpan, ComputationId, Option<Derived>)> = Vec::new();
    for (constant, roots) in naming.declarations() {
        if composites.is_empty() {
            break;
        }
        if !written.contains(&constant) {
            continue;
        }
        let scoped = naming.scoped(arena, &owned, roots);
        let mut binders: Vec<Option<Name<'_>>> = Vec::new();
        composites.retain(|&(span, transport)| {
            let Some(around) = scoped.around(CoreNode::Computation(transport))
            else {
                return true;
            };
            binders.clear();
            binders.extend(around.iter().map(|binder| binder.name.map(Name::from)));
            let source = CoreSource::new(arena, &names)
                .naming(&constructors)
                .within(&binders);
            let spelled = present_computation(
                &source,
                CoreNode::Computation(transport),
                PageWidth::from(u32::MAX),
                style,
            );
            let derived = match spelled {
                Ok(spelled)
                    if spelled.fidelity() == Fidelity::Faithful
                        && spelled.unspelled().is_empty() =>
                {
                    arguments(SourceFragment::from(spelled.as_ref())).map(|(motive, value)| {
                        Derived {
                            span,
                            motive,
                            value,
                        }
                    })
                },
                Ok(_) | Err(_) => None,
            };
            found.push((span, transport, derived));
            false
        });
    }
    // Everything a composite's lowering mints takes its span, the types it
    // reads among them: a call's result type, instantiated at the call, holds
    // the callee's composites. The composite's own transport is minted last,
    // once those types are read, so each span takes its latest, or none when
    // that one has no faithful spelling (#3772).
    found.sort_unstable_by_key(|&(span, transport, _)| (span, core::cmp::Reverse(transport)));
    found.dedup_by_key(|&mut (span, ..)| span);
    Motives {
        derived: found
            .into_iter()
            .filter_map(|(.., derived)| derived)
            .collect(),
        returned,
        flows,
        reach: Reach::Derived,
    }
}

/// `span`, of a unit's text, as a span of the source starting at `base` in
/// it; none when it starts before the source.
///
/// # Specification
/// trivial.
pub fn within(
    span: ByteSpan,
    base: ByteOffset,
) -> Option<ByteSpan>
{
    let start = usize::from(span.start()).checked_sub(usize::from(base))?;
    let end = usize::from(span.end()).checked_sub(usize::from(base))?;
    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
}

/// The tokens of the first and the third argument of `transport(…)` as
/// `text` spells it: the motive and the value it moves.
///
/// # Specification
/// trivial.
fn arguments(spelled: SourceFragment<'_>) -> Option<(Vec<Token>, Vec<Token>)>
{
    let text = <&str>::from(spelled);
    let mut arguments: [Vec<Token>; 3] = Default::default();
    let mut index = 0_usize;
    let mut spaced = Spaced::No;
    let mut depth = 0_usize;
    let mut read = label(spelled).into_iter().filter_map(|token| {
        let written =
            text.get(usize::try_from(token.start).ok()? .. usize::try_from(token.end).ok()?)?;
        Some((token.lexeme, written))
    });
    let (Some((_, "transport")), Some((_, "("))) = (read.next(), read.next())
    else {
        return None;
    };
    for (lexeme, written) in read {
        if lexeme == Lexeme::Space {
            spaced = Spaced::Yes;
            continue;
        }
        match written {
            "," if depth == 0 => {
                index = index.checked_add(1_usize)?;
                spaced = Spaced::No;
                continue;
            },
            ")" | "]" | "}" if depth == 0 => break,
            "(" | "type(" | "[" | "{" | "#{" | "+{" | "&{" => depth = depth.saturating_add(1),
            ")" | "]" | "}" => depth = depth.checked_sub(1)?,
            _ => {},
        }
        let argument = arguments.get_mut(index)?;
        // An argument's first token stands after the separator the
        // writer places itself.
        let before = if argument.is_empty() {
            Spaced::No
        }
        else {
            spaced
        };
        argument.push(Token {
            text: String::from(written),
            spaced: before,
        });
        spaced = Spaced::No;
    }
    let [motive, _, value] = arguments;
    (!motive.is_empty() && !value.is_empty()).then_some((motive, value))
}

/// The tokens of `spelled`, each with whether the printer wrote whitespace
/// before it, the first with none; none when it spells no token.
///
/// # Specification
/// trivial.
pub fn tokens(spelled: SourceFragment<'_>) -> Option<Vec<Token>>
{
    let text = <&str>::from(spelled);
    let mut found: Vec<Token> = Vec::new();
    let mut spaced = Spaced::No;
    for token in label(spelled) {
        if token.lexeme == Lexeme::Space {
            spaced = Spaced::Yes;
            continue;
        }
        let written =
            text.get(usize::try_from(token.start).ok()? .. usize::try_from(token.end).ok()?)?;
        found.push(Token {
            text: String::from(written),
            spaced: if found.is_empty() { Spaced::No } else { spaced },
        });
        spaced = Spaced::No;
    }
    (!found.is_empty()).then_some(found)
}
