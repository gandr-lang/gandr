use alloc::vec::Vec;

use super::AtomType;
use super::Position;
use super::pick;
use super::rotated;

#[test]
fn wrapped_pool_positions_preserve_rotation_candidates()
{
    let pool = [AtomType::Integer, AtomType::String, AtomType::Unit];
    assert_eq!(pick(&pool, Position(5)), AtomType::Unit);
    assert_eq!(rotated(&pool, Position(5)).collect::<Vec<_>>(), [
        AtomType::Unit,
        AtomType::Integer,
        AtomType::String
    ]);
    assert_eq!(
        Position(usize::MAX).within(&pool).0,
        usize::MAX % pool.len()
    );
    assert_eq!(
        pick(&[AtomType::String], Position(usize::MAX)),
        AtomType::String
    );
    assert_eq!(
        rotated(&[AtomType::String], Position(usize::MAX)).collect::<Vec<_>>(),
        [AtomType::String]
    );
}
