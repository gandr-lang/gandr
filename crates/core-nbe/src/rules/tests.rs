use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;

use super::DomainArena;
use super::Frozen;
use super::Glued;
use super::Head;
use super::NeutralHead;
use super::Unfolding;
use crate::TermFace;

#[test]
fn freezing_is_idempotent_and_local_to_one_side()
{
    let mut domain = DomainArena::new();
    let floor = domain.watermark();
    let first = ConstantIndex::from(0_usize);
    let second = ConstantIndex::from(1_usize);
    let loaded = domain
        .neutral_node(
            NeutralHead::Constant(first),
            Vec::new(),
            Unfolding::Unforced(GlobalIndex::from(0_u32)),
        )
        .expect("a declaration can unfold");
    let opaque = domain
        .neutral_node(NeutralHead::Constant(first), Vec::new(), Unfolding::Rigid)
        .expect("the same name can stand opaque");
    let mut frozen = Frozen::default();
    frozen.freeze(ConversionSide::Left, first);
    let once = frozen.clone();
    frozen.freeze(ConversionSide::Left, first);
    assert_eq!(once, frozen, "freezing is idempotent in the goal key");
    frozen.freeze(ConversionSide::Right, second);
    assert_eq!(
        super::Membership::Absent,
        frozen.holds(ConversionSide::Left, second)
    );
    assert_eq!(
        super::Membership::Held,
        frozen.holds(ConversionSide::Right, second)
    );
    assert_eq!(
        Ok(Head::Frozen(first)),
        super::head(&domain, &frozen, ConversionSide::Left, loaded)
    );
    assert_eq!(
        Ok(Head::Defined(first)),
        super::head(&domain, &frozen, ConversionSide::Right, loaded)
    );
    assert_eq!(
        Ok(Head::Rigid),
        super::head(&domain, &frozen, ConversionSide::Left, opaque)
    );
    let value = domain.value_unit(TermFace::Reduced);
    domain
        .force_neutral(loaded, Glued::Value(value))
        .expect("the face is initially unforced");
    assert_eq!(
        Ok(Head::Defined(first)),
        super::head(&domain, &frozen, ConversionSide::Right, loaded)
    );
    domain.truncate_to(floor);
    assert_eq!(
        Err(super::ConversionFault::Domain(super::DomainFault::Dangling)),
        super::head(&domain, &frozen, ConversionSide::Left, loaded)
    );
}

#[test]
fn payloads_refuse_nonliteral_and_missing_nodes()
{
    let mut core = CoreArena::new();
    let floor = core.watermark();
    let unit = core.value_unit();
    let literal = core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::zero(),
    )));
    assert!(matches!(
        super::payload(&core, literal),
        Ok(Literal::Integer(_))
    ));
    assert_eq!(
        Err(super::ConversionFault::LiteralPayload { literal: unit }),
        super::payload(&core, unit)
    );
    core.truncate_to(floor);
    assert_eq!(
        Err(super::ConversionFault::LiteralPayload { literal }),
        super::payload(&core, literal)
    );
}

#[test]
fn opposite_polarities_are_refused_in_both_orders()
{
    let core = CoreArena::new();
    let mut domain = DomainArena::new();
    let value = domain.value_unit(TermFace::Reduced);
    let computation = domain.comp_return(value, crate::CompTermFace::Reduced);
    let chain = crate::LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = crate::Definitions::new(&chain, &environment, environment.root());
    for (left, right) in [
        (Glued::Value(value), Glued::Computation(computation)),
        (Glued::Computation(computation), Glued::Value(value)),
    ] {
        assert_eq!(
            Err(super::ConversionFault::Polarity),
            super::plan(&core, &domain, definitions, &Frozen::default(), left, right)
        );
    }
}
