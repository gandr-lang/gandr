//! The identity layer's own boundary wrappers: every index, count and verdict
//! a signature of this crate crosses, so no signature passes a bare primitive.
//!
//! Each wrapper is transparent and converts with the standard `From` traits
//! both ways, so a primitive is unpacked only where a comparison, an index or
//! a count needs it. The vocabulary is this crate's alone; the substrate's
//! [`PositionStep`](gandr_theory_cell_complexes::PositionStep) and
//! [`FiringPermission`](gandr_theory_cell_complexes::FiringPermission) and the
//! engine's [`StepIndependence`](gandr_theory_coherent_resolutions::StepIndependence)
//! are read from below rather than restated.

/// Defines a transparent newtype over one primitive with `From` conversions
/// both ways.
macro_rules! wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident($raw:ty);) => {
        $(#[$meta])*
        #[repr(transparent)]
        $vis struct $name($raw);

        impl From<$raw> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $raw) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $raw
        {
            /// Unwraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

wrapper! {
    /// The layer of one event in the dependence order of a derivation: the
    /// length of the longest dependence chain strictly below it.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CausalDepth(usize);
}

wrapper! {
    /// The index of one event in a derivation's finite event order, in
    /// recorded order.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct EventIndex(usize);
}

wrapper! {
    /// The number of events in a derivation's finite event order.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct EventCount(usize);
}

wrapper! {
    /// Whether one event of a derivation depends directly on an earlier one.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct EventDependence(bool);
}

wrapper! {
    /// Whether one event of a derivation causally precedes another.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct EventPrecedence(bool);
}

wrapper! {
    /// Whether two distinct events of a derivation are causally unordered.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct EventConcurrency(bool);
}

wrapper! {
    /// The index of one position in a sequentialization of a derivation's
    /// events.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct SchedulePosition(usize);
}

wrapper! {
    /// The number of adjacent transpositions an exchange witness performs.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct TranspositionCount(usize);
}

wrapper! {
    /// The zero-based dependency level of a certified derivation's replay
    /// plan.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ReplayLevel(usize);
}

wrapper! {
    /// Whether two tracelet normal forms are the same normal form.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct NormalFormEquality(bool);
}

wrapper! {
    /// The number of occurrences of one primitive certificate in a normalized
    /// derivation: the integer grade of the factorization.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PrimMultiplicity(u32);
}

wrapper! {
    /// Whether both sequentializations of a shift-equivalence witness replay
    /// to its join.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct ShiftReplay(bool);
}

wrapper! {
    /// Whether two atom-occurrence flows are the same flow.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct FlowEquality(bool);
}

wrapper! {
    /// The index of one atom incidence among a flow vertex's upper or lower
    /// edges.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FlowPortIndex(usize);
}

wrapper! {
    /// The index of one cell-application event among an atom-occurrence
    /// flow's vertices.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FlowVertexIndex(usize);
}

wrapper! {
    /// The index of one atom occurrence in the enumerated addresses of a
    /// derivation's peak.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PeakOccurrenceIndex(usize);
}

wrapper! {
    /// A coordinate into a causal web's canonical event list.
    ///
    /// A web coordinate, not a second event identity: the identity is the
    /// event key the web holds at the coordinate.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct WebVertex(usize);
}

wrapper! {
    /// The number of vertices in a causal web.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct WebVertexCount(usize);
}

wrapper! {
    /// The number of licensed weakenings in a slice-chain refinement witness.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct SliceStepCount(usize);
}

wrapper! {
    /// Whether one web vertex precedes another.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct WebPrecedence(bool);
}

wrapper! {
    /// Whether two distinct web vertices are in the white independence
    /// relation.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct WebIndependence(bool);
}

wrapper! {
    /// Whether a web's precedence relation is square over its event list.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct WebShapeValidity(bool);
}
