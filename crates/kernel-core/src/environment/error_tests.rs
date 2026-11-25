//! The tests of `error` that build their fixtures with the judgement: each
//! one admits through `Environment` or reads through conversion, which stand
//! above the record, so it runs in this crate.

use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::ValueType;

use crate::Environment;
use crate::error::KernelError;

#[test]
fn universe_successor_overflow_refuses_admission_without_truncating_prior_content()
{
    let mut environment = Environment::new();
    let (unit, first) = {
        let mut staging = environment.stage();
        let unit = staging.arena().value_type_unit();
        (unit, staging.axiom(LevelSignature::monomorphic(), unit))
    };
    assert_eq!(
        environment
            .add_decl(first)
            .expect("the unit type forms")
            .position(),
        ConstantIndex::from(0_usize)
    );
    for sort in [GroundSort::Value, GroundSort::Computation] {
        let position = ConstantIndex::from(environment.entries().len());
        let admitted = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_universe(
                sort,
                Level::constant(LevelConstant::from(u64::MAX.saturating_sub(1))),
            );
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert_eq!(
            environment
                .add_decl(admitted)
                .expect("the successor fits")
                .position(),
            position
        );
        let watermark = environment.arena().watermark();
        let entries = environment.entries().admitted();
        let refused = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_universe(sort, Level::constant(LevelConstant::from(u64::MAX)));
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        assert_eq!(
            environment.add_decl(refused),
            Err(KernelError::LevelArithmetic)
        );
        assert_eq!(environment.arena().watermark(), watermark);
        assert_eq!(environment.entries().admitted(), entries);
        assert_eq!(
            environment.arena().value_type(unit),
            Some(&ValueType::unit())
        );
    }
}
