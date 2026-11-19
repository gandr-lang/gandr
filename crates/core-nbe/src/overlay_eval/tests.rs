use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;

use super::Definitions;
use super::DomainArena;
use super::DuplicationPolicy;
use super::EvalFault;
use super::Fuel;
use super::Overlay;
use super::OverlayEvalFault;
use super::OverlayId;
use super::eval_overlay_computation;
use super::eval_overlay_shared;
use super::eval_overlay_value;
use crate::CompGraft;
use crate::CompNode;
use crate::CompTypeGraft;
use crate::CompTypeNode;
use crate::LoweredChain;
use crate::ValueGraft;
use crate::ValueNode;
use crate::ValueTypeGraft;
use crate::ValueTypeNode;

#[test]
fn refusals_preserve_the_erasure_and_evaluation_boundaries()
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut overlay = Overlay::new();
    let floor = overlay.watermark();
    let value = overlay
        .mint_value(ValueNode::Grafted(ValueGraft::Unit))
        .expect("the unit is closed");
    let comp = overlay
        .mint_computation(CompNode::Grafted(CompGraft::Return(value)))
        .expect("the child lives");
    let preserved = overlay.clone();
    let mut value_core = CoreArena::new();
    let unit = value_core.value_unit();
    let mut comp_core = value_core.clone();
    let _returned = comp_core.computation_return(unit);
    let mut domain = DomainArena::new();
    let _existing = domain.value_unit(crate::TermFace::Reduced);
    let domain_before = domain.clone();
    let mut core = CoreArena::new();
    assert_eq!(
        Err(OverlayEvalFault::Evaluation(EvalFault::OutOfFuel)),
        eval_overlay_value(
            &overlay,
            &mut core,
            &mut domain,
            definitions,
            Fuel::from(0_u32),
            value
        )
    );
    assert_eq!(
        value_core, core,
        "evaluation refusal keeps the erased value"
    );
    assert_eq!(domain_before, domain);
    let mut core = CoreArena::new();
    assert_eq!(
        Err(OverlayEvalFault::Evaluation(EvalFault::OutOfFuel)),
        eval_overlay_computation(
            &overlay,
            &mut core,
            &mut domain,
            definitions,
            Fuel::from(0_u32),
            comp
        )
    );
    assert_eq!(
        comp_core, core,
        "evaluation refusal keeps the erased computation"
    );
    assert_eq!(domain_before, domain);
    for (root, expected) in [
        (OverlayId::Value(value), &value_core),
        (OverlayId::Computation(comp), &comp_core),
    ] {
        let mut core = CoreArena::new();
        assert_eq!(
            Err(OverlayEvalFault::Evaluation(EvalFault::OutOfFuel)),
            eval_overlay_shared(
                &mut overlay,
                &mut core,
                &mut domain,
                definitions,
                Fuel::from(0_u32),
                DuplicationPolicy::default(),
                root
            )
        );
        assert_eq!(*expected, core);
        assert_eq!(domain_before, domain);
        assert_eq!(
            preserved, overlay,
            "the duplicate is scratch even when evaluation fails"
        );
    }
    overlay.truncate_to(floor);
    let missing = overlay.clone();
    let mut core = comp_core.clone();
    assert!(matches!(
        eval_overlay_value(
            &overlay,
            &mut core,
            &mut domain,
            definitions,
            Fuel::from(20_u32),
            value
        ),
        Err(OverlayEvalFault::Erasure(_))
    ));
    assert_eq!(comp_core, core);
    assert_eq!(domain_before, domain);
    assert!(matches!(
        eval_overlay_computation(
            &overlay,
            &mut core,
            &mut domain,
            definitions,
            Fuel::from(20_u32),
            comp
        ),
        Err(OverlayEvalFault::Erasure(_))
    ));
    assert_eq!(comp_core, core);
    assert_eq!(domain_before, domain);
    for root in [OverlayId::Value(value), OverlayId::Computation(comp)] {
        assert!(matches!(
            eval_overlay_shared(
                &mut overlay,
                &mut core,
                &mut domain,
                definitions,
                Fuel::from(20_u32),
                DuplicationPolicy::default(),
                root
            ),
            Err(OverlayEvalFault::Duplication(_))
        ));
        assert_eq!(comp_core, core);
        assert_eq!(domain_before, domain);
        assert_eq!(missing, overlay);
    }
}

#[test]
fn type_roots_are_refused_before_evaluation()
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut overlay = Overlay::new();
    let value_type = overlay
        .mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Unit))
        .expect("the unit type is closed");
    let comp_type = overlay
        .mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Returner(value_type)))
        .expect("the unit child lives");
    let original = overlay.clone();
    let mut value_core = CoreArena::new();
    let unit = value_core.value_type_unit();
    let mut comp_core = value_core.clone();
    let returner = comp_core.comp_type_returner(unit);
    for erased in [
        super::CoreId::ValueType(unit),
        super::CoreId::CompType(returner),
    ] {
        assert_eq!(
            Err(OverlayEvalFault::Evaluation(EvalFault::MachineInvariant)),
            super::core_term(erased)
        );
    }
    for root in [
        OverlayId::ValueType(value_type),
        OverlayId::CompType(comp_type),
    ] {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();
        let empty = domain.clone();
        assert_eq!(
            Err(OverlayEvalFault::Duplication(
                super::DuplicationFault::MachineInvariant
            )),
            eval_overlay_shared(
                &mut overlay,
                &mut core,
                &mut domain,
                definitions,
                Fuel::from(20_u32),
                DuplicationPolicy::default(),
                root
            )
        );
        assert_eq!(
            CoreArena::new(),
            core,
            "a type is refused before erasure or evaluation"
        );
        assert_eq!(empty, domain);
        assert_eq!(original, overlay, "the refused root leaves no duplicate");
    }
}
