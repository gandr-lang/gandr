//! The finite affine map category, including its missing diagonal.

use gandr_theory_shapes::affine::AffineMap;
use gandr_theory_shapes::affine::BridgeTerm;
use gandr_theory_shapes::affine::Endpoint;
use gandr_theory_shapes::boundary::Dimension;
use gandr_theory_shapes::boundary::DimensionCount;
use gandr_theory_shapes::boundary::ShapeError;

/// Enumerates every admitted map between two small affine contexts.
///
/// # Specification
/// - provides: all endpoint-or-variable vectors, filtered by independent
///   variable-occurrence counting, checked against the production admission.
/// - panics: any disagreement about admission or refusal identity.
///
/// # Adequacy
/// - hypothesis: L2 exhaustive maps expose copying, missed bounds and constants
///   incorrectly treated as resources.
/// - witness: `tests::affine::small_affine_maps_compose_without_contraction`
fn maps(
    source: DimensionCount,
    target: DimensionCount,
) -> Vec<AffineMap>
{
    let mut alphabet = vec![
        BridgeTerm::Endpoint(Endpoint::Zero),
        BridgeTerm::Endpoint(Endpoint::One),
    ];
    alphabet.extend(
        (0 .. usize::from(source)).map(|index| BridgeTerm::Variable(Dimension::from(index))),
    );
    let mut vectors = vec![Vec::new()];
    for _ in 0 .. usize::from(target) {
        let mut product = Vec::new();
        for prefix in &vectors {
            for &term in &alphabet {
                let mut vector = prefix.clone();
                vector.push(term);
                product.push(vector);
            }
        }
        vectors = product;
    }
    let mut admitted = Vec::new();
    for vector in vectors {
        let mut expected = Ok(());
        for (index, term) in vector.iter().enumerate() {
            if let BridgeTerm::Variable(dim) = *term
                && vector.iter().take(index).any(|earlier| earlier == term)
            {
                expected = Err(ShapeError::Contraction(dim));
                break;
            }
        }
        match AffineMap::new(source, vector) {
            | Ok(map) => {
                assert_eq!(expected, Ok(()));
                admitted.push(map);
            },
            | Err(error) => assert_eq!(expected, Err(error)),
        }
    }
    admitted
}

#[test]
fn small_affine_maps_compose_without_contraction()
{
    for source in 0_usize ..= 3 {
        for middle in 0_usize ..= 3 {
            for target in 0_usize ..= 3 {
                let first = maps(DimensionCount::from(source), DimensionCount::from(middle));
                let second = maps(DimensionCount::from(middle), DimensionCount::from(target));
                for f in &first {
                    let identity = AffineMap::new(
                        DimensionCount::from(source),
                        (0 .. source)
                            .map(|dim| BridgeTerm::Variable(Dimension::from(dim)))
                            .collect(),
                    )
                    .expect("identity");
                    assert_eq!(identity.then(f), Ok(f.clone()));
                    for g in &second {
                        let composite = f.then(g).expect("composition");
                        let expected: Vec<BridgeTerm> = g
                            .images()
                            .iter()
                            .map(|term| match *term {
                                | BridgeTerm::Endpoint(_) => *term,
                                | BridgeTerm::Variable(dim) => f.images()[usize::from(dim)],
                            })
                            .collect();
                        assert_eq!(composite.images(), expected);
                        assert_eq!(
                            AffineMap::new(DimensionCount::from(source), expected),
                            Ok(composite.clone())
                        );
                        // Every one-coordinate outgoing map tests associativity,
                        // observing each coordinate and both constants.
                        for h in maps(DimensionCount::from(target), DimensionCount::from(1)) {
                            assert_eq!(composite.then(&h), f.then(&g.then(&h).expect("g then h")));
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn diagonal_and_bad_maps_are_refused()
{
    let variable = BridgeTerm::Variable(Dimension::from(0));
    assert_eq!(
        AffineMap::new(DimensionCount::from(1), vec![variable, variable]),
        Err(ShapeError::Contraction(Dimension::from(0)))
    );
    assert_eq!(
        AffineMap::new(DimensionCount::from(0), vec![variable]),
        Err(ShapeError::DimensionOutside(Dimension::from(0)))
    );
    let constants = AffineMap::new(DimensionCount::from(0), vec![
        BridgeTerm::Endpoint(
            Endpoint::Zero
        );
        2
    ])
    .expect("constants can repeat");
    assert_eq!(
        constants.dimensions(),
        (DimensionCount::from(0), DimensionCount::from(2))
    );
    let empty = AffineMap::new(DimensionCount::from(0), vec![]).expect("empty identity");
    assert_eq!(constants.then(&empty), Err(ShapeError::DifferentContext));
}
