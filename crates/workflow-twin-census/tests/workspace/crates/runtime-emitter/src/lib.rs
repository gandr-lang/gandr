//! The emitter of the fixture: one generic public function and one that is
//! not generic.

/// The first item of `items`.
pub fn first<T>(items: &[T]) -> Option<&T>
{
    items.first()
}

/// One.
pub fn one() -> u64
{
    1
}
