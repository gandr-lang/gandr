//! The crate's integration suites, one module per area.
//!
//! One target rather than one per area, so a witness path names the area it
//! belongs to (`tests::maps::…`) instead of a file.

/// One wire end: `o` for open, a vertex number otherwise.
macro_rules! end {
    (o) => {
        gandr_theory_sites::End::Open
    };
    ($vertex:literal) => {
        gandr_theory_sites::End::Vertex(gandr_theory_circuit_algebras::Edge::from($vertex))
    };
}

/// The shape over the given vertex count whose wires run between the given
/// ends, producer first: `shape!(2; o > 0, 0 > 1)`.
macro_rules! shape {
    ($vertices:literal $(; $($producer:tt > $consumer:tt),+)?) => {
        gandr_theory_sites::Shape::from_ends(
            gandr_theory_circuit_algebras::EdgeCount::from($vertices),
            vec![$($(gandr_theory_sites::Ends::new(end!($producer), end!($consumer))),+)?],
        )
        .expect("the carrier admits the fixture")
    };
}

/// The candidate map with the given vertex images and wire images:
/// `site_map!([{0, 1}, {}], [0, 0])`.
macro_rules! site_map {
    ([$({$($member:literal),*}),*], [$($wire:literal),*]) => {
        gandr_theory_sites::SiteMap::new(
            vec![$(
                [$(gandr_theory_circuit_algebras::Edge::from($member)),*]
                    .into_iter()
                    .fold(gandr_theory_sites::VertexSet::EMPTY, |set, vertex| {
                        set.union(gandr_theory_sites::VertexSet::single(vertex))
                    })
            ),*],
            vec![$(gandr_theory_circuit_algebras::Wire::from($wire)),*],
        )
    };
}

#[cfg(test)]
mod maps;
#[cfg(test)]
mod point_count;
#[cfg(test)]
mod reedy;
#[cfg(test)]
mod shapes;
#[cfg(test)]
mod units;
