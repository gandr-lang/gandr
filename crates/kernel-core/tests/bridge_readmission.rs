//! A module of bridges, persisted and readmitted.
//!
//! The producing environment admits a relation at the universe, a lifting
//! at a list of Bools and a family at a function code. The artifact decodes
//! to the same nodes and replays in a fresh environment; a copy whose
//! evidence was tampered with is refused at the declaration that broke.
//!
//! The readmission cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use alloc::vec::Vec;

use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_core::Admission;
use gandr_kernel_core::Environment;
use gandr_kernel_core::ExpectedValueShape;
use gandr_kernel_core::IdentityError;
use gandr_kernel_core::KernelError;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::ReplayDecline;
use gandr_kernel_core::ReplayRefusal;
use gandr_kernel_core::ValueTypeHead;
use gandr_kernel_core::identity_recursion::Component;
use gandr_kernel_core::identity_recursion::EvaluationSide;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::EvaluationComponent;
use gandr_kernel_term::EvaluationDialogues;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::decode;
use gandr_kernel_term::encode;

/// The module's positions, in admission order.
const RELATION: usize = 0;
/// `lifting : Br (List Bool) [true] [true]`.
const LIFTING: usize = 1;
/// `family : Br (U (Unit → F Bool)) (λ_. true) (λ_. true)`.
const FAMILY: usize = 2;

/// Every declaration the environment admitted, marked as it was admitted,
/// encoded over its arena.
///
/// # Specification
/// trivial.
fn export(environment: &Environment) -> EncodedArtifact
{
    let marked: Vec<_> = environment
        .entries()
        .iter()
        .map(|entry| {
            let mark = match entry.admission() {
                Admission::Checked => AdmissionMark::Checked,
                Admission::Unchecked => AdmissionMark::UncheckedBypass,
            };
            MarkedDeclaration::new(mark, entry.declaration().clone())
        })
        .collect();
    encode(environment.arena(), &marked)
}

/// Bool's type and its two constructors.
///
/// # Specification
/// trivial.
fn boolean(arena: &mut TermArena) -> (ValueTypeId, [ValueId; 2])
{
    let unit_type = arena.value_type_unit();
    let boolean = arena.value_type_sum(&[unit_type, unit_type]);
    let unit = arena.value_unit();
    (boolean, [
        arena.value_injection(Side::Left.into(), unit),
        arena.value_injection(Side::Right.into(), unit),
    ])
}

/// `thunk (λ_. λ_. return code)`, relating every pair by the one code.
///
/// # Specification
/// trivial.
fn relating_by(
    arena: &mut TermArena,
    code: ValueId,
) -> ValueId
{
    let body = arena.computation_return(code);
    let inner = arena.computation_lambda(body);
    let outer = arena.computation_lambda(inner);
    arena.value_thunk(outer)
}

/// The family over `Unit`'s one argument bridge for two functions
/// constantly at Bools: one component, claiming `outputs`, each side's
/// evaluation the two forces of `force f ⋆` against `return o` and the
/// comparison of their shared result.
///
/// # Specification
/// trivial.
fn family(
    arena: &mut TermArena,
    (left, right): (ValueId, ValueId),
) -> ValueId
{
    let evaluation = || {
        Vec::from([
            ConversionDecision::Force { thunk: () },
            ConversionDecision::Force { thunk: () },
            ConversionDecision::ComparedShared {
                left: (),
                right: (),
            },
        ])
    };
    let dialogues = [EvaluationDialogues {
        left: evaluation(),
        right: evaluation(),
    }];
    let evidence = arena.value_unit();
    let components = [EvaluationComponent {
        left,
        right,
        evidence,
    }];
    arena.value_higher_evaluation(dialogues.into(), components.into())
}

/// Admit one definition, minted by `build` in a staging arena.
///
/// # Specification
/// trivial.
fn define(
    environment: &mut Environment,
    build: impl FnOnce(&mut TermArena) -> (ValueTypeId, ValueId),
)
{
    let mut staging = environment.stage();
    let (declared, body) = build(staging.arena());
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    let _admitted = environment.add_decl(staged).expect("the bridge admits");
}

/// The module: a relation, a lifting and a family.
///
/// # Specification
/// trivial.
fn module() -> Environment
{
    let mut environment = Environment::new();
    define(&mut environment, |arena| {
        let (boolean, _) = boolean(arena);
        let unit_type = arena.value_type_unit();
        let kinds = arena.value_type_universe(GroundSort::Value, Level::zero());
        let unit_code = arena.value_quote(unit_type);
        let bool_code = arena.value_quote(boolean);
        let declared = arena.value_type_bridge(kinds, unit_code, bool_code);
        (declared, relating_by(arena, unit_code))
    });
    define(&mut environment, |arena| {
        let (boolean, [truth, _]) = boolean(arena);
        let lists = arena.value_type_list(boolean);
        let nil = arena.value_list_nil();
        let list = arena.value_list_cons(truth, nil);
        let declared = arena.value_type_bridge(lists, list, list);
        let unit = arena.value_unit();
        (declared, arena.value_tuple(&[unit, unit]))
    });
    define(&mut environment, |arena| {
        let (boolean, [truth, _]) = boolean(arena);
        let unit_type = arena.value_type_unit();
        let returner = arena.comp_type_returner(boolean);
        let arrow = arena.comp_type_arrow(unit_type, returner);
        let functions = arena.value_type_thunk(arrow);
        let body = arena.computation_return(truth);
        let lambda = arena.computation_lambda(body);
        let constant = arena.value_thunk(lambda);
        let declared = arena.value_type_bridge(functions, constant, constant);
        (declared, family(arena, (truth, truth)))
    });
    environment
}

/// Replace the definition at `position` in a decoded copy of the module
/// with the body `tamper` forges, re-encode, decode and replay it, and
/// return the refusal met at that position.
///
/// # Specification
/// trivial.
fn tampered(
    bytes: &EncodedArtifact,
    position: ConstantIndex,
    tamper: impl FnOnce(&mut TermArena) -> ValueId,
) -> gandr_kernel_core::ArtifactRefusal
{
    let artifact = decode(bytes.as_image()).expect("the module decodes");
    let mut arena = artifact.arena().clone();
    let mut declarations = artifact.declarations().to_vec();
    let slot = usize::from(position);
    let DeclarationContent::Def { declared, .. } = *declarations[slot].declaration().content()
    else {
        panic!("a definition at the tampered position");
    };
    let forged = tamper(&mut arena);
    let declaration =
        DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), declared, forged);
    declarations[slot] = MarkedDeclaration::new(AdmissionMark::Checked, declaration);
    let rewritten = encode(&arena, &declarations);
    let decoded = decode(rewritten.as_image()).expect("the copy is well formed on the wire");
    let refusal = Environment::replay(decoded.arena().clone(), decoded.declarations())
        .expect_err("a tampered bridge does not readmit");
    assert_eq!(refusal.position(), position);
    refusal
}

#[test]
fn every_bridge_persists_decodes_and_replays()
{
    let environment = module();
    let bytes = export(&environment);
    let artifact = decode(bytes.as_image()).expect("the module decodes");
    for position in [RELATION, LIFTING, FAMILY] {
        let DeclarationContent::Def { declared, .. } =
            *artifact.declarations()[position].declaration().content()
        else {
            panic!("a definition at every position");
        };
        assert!(matches!(
            artifact.arena().value_type(declared),
            Some(&ValueType::Bridge { .. })
        ));
    }
    assert_eq!(
        Vec::from(encode(artifact.arena(), artifact.declarations())),
        Vec::from(bytes.clone()),
        "the decoded nodes re-encode to the same bytes"
    );
    let replayed = Environment::replay(artifact.arena().clone(), artifact.declarations())
        .expect("every bridge readmits by replay");
    assert_eq!(Vec::from(export(&replayed)), Vec::from(bytes));
}

#[test]
fn a_tampered_bridge_refuses_at_its_declaration()
{
    let bytes = export(&module());

    // A relation into a non-code: `()` is no type.
    let relation = tampered(&bytes, ConstantIndex::from(RELATION), |arena| {
        let unit = arena.value_unit();
        relating_by(arena, unit)
    });
    assert!(matches!(
        relation.error(),
        &KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            actual,
        } if actual.head() == ValueTypeHead::Universe
    ));
    // A lifting missing its tail's bridge.
    let lifting = tampered(&bytes, ConstantIndex::from(LIFTING), TermArena::value_unit);
    assert!(matches!(
        lifting.error(),
        &KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            actual,
        } if actual.head() == ValueTypeHead::Product
    ));
    // A family whose component claims `false` on the left: its replay
    // contradicts the claim where the shared result is compared.
    let forged = tampered(&bytes, ConstantIndex::from(FAMILY), |arena| {
        let (_, [truth, falsity]) = boolean(arena);
        family(arena, (falsity, truth))
    });
    assert!(matches!(
        forged.error(),
        &KernelError::Identity(IdentityError::Evaluation {
            component: Component(0),
            side: EvaluationSide::Left,
            verdict: KernelVerdict::Declined(ReplayDecline::Refused(
                ReplayRefusal::Contradicted { .. }
            )),
        })
    ));
}
