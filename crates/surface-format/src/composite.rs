//! The motives of the path composites a source writes, as its lowering
//! derived them, for the explicit spelling of `p then q`.
//!
//! `p then q` is the transport `transport(\y. Path(A, a, y), q, p)`, its
//! carrier `A` and fixed endpoint `a` the type of `p`, which the lowering
//! derives from the operands; the syntax does not hold them. So the explicit
//! spelling reads them from the lowering: the returned transport the lowering
//! minted at the composite's span, spelled through the shared printer in the
//! explicit form, its first argument the motive. A composite whose motive the
//! printer cannot spell faithfully — one naming a binder the source opened
//! around it — has none, keeps its spelling and is reported (#803).

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_lowering::Insertion;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Provenance;
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
use gandr_surface_pretty::present_value;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;

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

/// The motive of each path composite the source writes, by the composite's
/// span in the source.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Motives
{
    /// The motives the lowering derived and the printer spells.
    derived: Vec<(ByteSpan, Vec<Token>)>,
    /// Which composites have one.
    reach: Reach,
}

/// Which composites [`Motives`] holds a motive for.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Reach
{
    /// Those whose motive the lowering derived and the printer spells.
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
            reach: Reach::Any,
        }
    }

    /// The motive's tokens of the composite spanning exactly `span`.
    ///
    /// # Specification
    /// trivial.
    pub fn of(
        &self,
        span: ByteSpan,
    ) -> Option<&[Token]>
    {
        let derived = self
            .derived
            .iter()
            .find(|&&(at, _)| at == span)
            .map(|&(_, ref tokens)| tokens.as_slice());
        match self.reach {
            Reach::Derived => derived,
            Reach::Any => Some(derived.unwrap_or_default()),
        }
    }
}

/// The motives of the path composites `module`, lowered into `arena` from a
/// unit whose source starts at `base`, derived: each returned transport the
/// lowering inserted as a composite's endpoint, spelled in the explicit form,
/// by its span in the source.
///
/// # Specification
/// trivial.
pub fn motives(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    base: ByteOffset,
) -> Motives
{
    let owned = constant_names(module);
    let names: Vec<Name<'_>> = owned.iter().map(|name| Name::from(name.as_str())).collect();
    let families = Families::of(module);
    let constructors = families.naming(&names);
    let source = CoreSource::new(arena, &names).naming(&constructors);
    let style = Style {
        form: Form::Explicit,
        spelling: Spelling::Ascii,
    };
    let mut found = Vec::new();
    for &(id, origin) in module.origins().values() {
        if origin.provenance() != Provenance::Inserted(Insertion::Endpoint) {
            continue;
        }
        let span = origin.span();
        let (Some(start), Some(end)) = (
            usize::from(span.start()).checked_sub(usize::from(base)),
            usize::from(span.end()).checked_sub(usize::from(base)),
        )
        else {
            continue;
        };
        let Some(&Value::Returned(transport)) = arena.value(id)
        else {
            continue;
        };
        if !matches!(
            arena.computation(transport),
            Some(&Computation::PathTransport { .. })
        ) {
            continue;
        }
        let Ok(spelled) = present_value(
            &source,
            CoreNode::Value(id),
            PageWidth::from(u32::MAX),
            style,
        )
        else {
            continue;
        };
        if spelled.fidelity() != Fidelity::Faithful || !spelled.unspelled().is_empty() {
            continue;
        }
        let (Some(tokens), Ok(span)) = (
            motive(SourceFragment::from(spelled.as_ref())),
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)),
        )
        else {
            continue;
        };
        found.push((span, tokens));
    }
    Motives {
        derived: found,
        reach: Reach::Derived,
    }
}

/// The tokens of the first argument of `transport(…)` as `text` spells it.
///
/// # Specification
/// trivial.
fn motive(spelled: SourceFragment<'_>) -> Option<Vec<Token>>
{
    let text = <&str>::from(spelled);
    let mut tokens = Vec::new();
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
            "," if depth == 0 => return (!tokens.is_empty()).then_some(tokens),
            "(" | "[" | "{" | "#{" | "+{" | "&{" => depth = depth.saturating_add(1),
            ")" | "]" | "}" => depth = depth.checked_sub(1)?,
            _ => {},
        }
        tokens.push(Token {
            text: String::from(written),
            spaced,
        });
        spaced = Spaced::No;
    }
    None
}
