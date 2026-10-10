//! Temporary replay of the captured, pre-interning equation occurrences.
#[path = "frozen_data.rs"]
mod data;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Child;
use gandr_kernel_term::stage::Natural;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Step;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::Type;

/// Import the old coordinates through the current allocator before timing.
///
/// # Specification
/// - ensures: preserves occurrence multiplicity and exact equation content.
/// - fails: an invalid captured edge.
/// - panics: only on corrupt generated fixture data.
///
/// # Errors
/// Returns the originating staging refusal.
pub(super) fn load(
    case: &str,
    index: Natural,
) -> Result<Option<(Arena, Vec<Step>)>, StageError>
{
    let Some((types, terms, steps)) = data::data(case, index.0)
    else {
        return Ok(None);
    };
    let mut arena = Arena::default();
    let mut classifiers = Vec::new();
    for ty in types {
        let ty = match ty {
            | Type::Arrow(a, b) => Type::Arrow(classifiers[a.0], classifiers[b.0]),
            | Type::Lift(inner) => Type::Lift(classifiers[inner.0]),
            | leaf => leaf,
        };
        classifiers.push(arena.alloc_type(ty)?);
    }
    let mut coordinates = Vec::new();
    for term in terms {
        let term = match term {
            | Term::Code(ty) => Term::Code(classifiers[ty.0]),
            | Term::Lambda(ty, body) => Term::Lambda(classifiers[ty.0], body),
            | Term::Eliminate(body, ty) => Term::Eliminate(body, classifiers[ty.0]),
            | term => term,
        };
        let mut children = [Child::Vacant; 3];
        for (child, output) in term.children().into_iter().zip(&mut children) {
            if let Child::Present(child) = child {
                *output = Child::Present(coordinates[child.0]);
            }
        }
        coordinates.push(arena.alloc(term.rebuild(children)?)?);
    }
    let steps = steps
        .into_iter()
        .map(|step| Step {
            source: coordinates[step.source.0],
            target: coordinates[step.target.0],
            rule: step.rule,
        })
        .collect();
    Ok(Some((arena, steps)))
}
