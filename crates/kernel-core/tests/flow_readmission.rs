//! A module of every directed certificate kind, persisted and readmitted.
//!
//! The producing environment admits a forward flow, a composition, `stay`, a
//! function flow, a session simulation, a ride, a telescope ride, a flow
//! product and a ride along it. The artifact decodes to the same nodes and
//! replays in a fresh environment; a copy whose image, seam, boundary or
//! product order was tampered with is refused at the declaration that broke.

extern crate alloc;

/// The readmission cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod flow_readmission
{
    use alloc::sync::Arc;

    use gandr_kernel_core::Admission;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::flow_universe::Boundary;
    use gandr_kernel_core::flow_universe::FlowError;
    use gandr_kernel_core::flow_universe::PatternPosition;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::AdmissionMark;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::EncodedArtifact;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::Seam;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::StringLiteral;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueId;
    use gandr_kernel_term::ValueTypeId;
    use gandr_kernel_term::decode;
    use gandr_kernel_term::encode;
    use gandr_kernel_term::session::Evidence;
    use gandr_kernel_term::session::Graph;
    use gandr_kernel_term::session::Node;
    use gandr_kernel_term::session::State;
    use gandr_kernel_term::session::StatePair;

    /// The module's positions, in admission order.
    const TERMINAL: usize = 0;
    /// `select : Flow_U(Unit, Bool)`.
    const SELECT: usize = 1;
    /// `not : Flow_U(Bool, Bool)`.
    const NOT: usize = 2;
    /// `constant : Flow_U(Bool, Bool)`, the terminal map then `select`.
    const CONSTANT: usize = 3;
    /// `funext : Flow_U(U (Bool → F Bool), U (Unit → F Bool))`.
    const FUNEXT: usize = 5;
    /// `product : Flow_U(⌜Bool × Bool⌝, ⌜Bool × Unit⌝)`, negation beside the
    /// terminal map.
    const PRODUCT: usize = 9;

    /// Every declaration the environment admitted, marked as it was
    /// admitted, encoded over its arena.
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
                    | Admission::Checked => AdmissionMark::Checked,
                    | Admission::Unchecked => AdmissionMark::UncheckedBypass,
                };
                MarkedDeclaration::new(mark, entry.declaration().clone())
            })
            .collect();
        encode(environment.arena(), &marked)
    }

    /// Bool's type and code, Unit's code and value, and Bool's constructors.
    struct Codes
    {
        /// `Unit + Unit`.
        boolean_type: ValueTypeId,
        /// Its quote.
        boolean: ValueId,
        /// Unit's quote.
        unit_code: ValueId,
        /// The empty tuple.
        unit: ValueId,
        /// `inl ()` and `inr ()`.
        constructors: [ValueId; 2],
    }

    /// Mint the codes every declaration shares.
    ///
    /// # Specification
    /// trivial.
    fn codes(arena: &mut TermArena) -> Codes
    {
        let unit_type = arena.value_type_unit();
        let boolean_type = arena.value_type_sum(&[unit_type, unit_type]);
        let boolean = arena.value_quote(boolean_type);
        let unit_code = arena.value_quote(unit_type);
        let unit = arena.value_unit();
        let constructors = [
            arena.value_injection(Side::Left.into(), unit),
            arena.value_injection(Side::Right.into(), unit),
        ];
        Codes {
            boolean_type,
            boolean,
            unit_code,
            unit,
            constructors,
        }
    }

    /// A closed thunk of a lambda returning `output`.
    ///
    /// # Specification
    /// trivial.
    fn returning(
        arena: &mut TermArena,
        output: ValueId,
    ) -> ValueId
    {
        let body = arena.computation_return(output);
        let lambda = arena.computation_lambda(body);
        arena.value_thunk(lambda)
    }

    /// A forward flow over Bool-shaped codes whose patterns bind no leaf: one
    /// image `thunk(return o)` per output, each with an empty dialogue.
    ///
    /// # Specification
    /// trivial.
    fn forward(
        arena: &mut TermArena,
        (source, target): (ValueId, ValueId),
        translator: ValueId,
        outputs: &[ValueId],
    ) -> ValueId
    {
        let classifier = arena.value_type_flow_universe(source, target);
        let images: Vec<ValueId> = outputs
            .iter()
            .map(|&output| {
                let returned = arena.computation_return(output);
                arena.value_thunk(returned)
            })
            .collect();
        let dialogues = vec![Vec::new(); outputs.len()];
        arena.value_forward_flow(classifier, translator, images.into(), dialogues.into())
    }

    /// Bool negation as a closed translator.
    ///
    /// # Specification
    /// trivial.
    fn negation(
        arena: &mut TermArena,
        [left, right]: [ValueId; 2],
    ) -> ValueId
    {
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let to_right = arena.computation_return(right);
        let to_left = arena.computation_return(left);
        let case = arena.computation_case(variable, &[to_right, to_left]);
        let lambda = arena.computation_lambda(case);
        arena.value_thunk(lambda)
    }

    /// The quoted function code `U (domain → F codomain)`.
    ///
    /// # Specification
    /// trivial.
    fn arrow(
        arena: &mut TermArena,
        domain: ValueTypeId,
        codomain: ValueTypeId,
    ) -> ValueId
    {
        let returner = arena.comp_type_returner(codomain);
        let body = arena.comp_type_arrow(domain, returner);
        let thunk = arena.value_type_thunk(body);
        arena.value_quote(thunk)
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
        let _admitted = environment
            .add_decl(staged)
            .expect("the certificate admits");
    }

    /// The module: every certificate kind, a ride, a telescope ride, a flow
    /// product and a ride along it.
    ///
    /// # Specification
    /// trivial.
    fn module() -> Environment
    {
        let mut environment = Environment::new();
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let translator = returning(arena, codes.unit);
            let flow = forward(arena, (codes.boolean, codes.unit_code), translator, &[
                codes.unit, codes.unit,
            ]);
            let declared = arena.value_type_flow_universe(codes.boolean, codes.unit_code);
            (declared, flow)
        });
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let [left, _] = codes.constructors;
            let translator = returning(arena, left);
            let flow = forward(arena, (codes.unit_code, codes.boolean), translator, &[left]);
            let declared = arena.value_type_flow_universe(codes.unit_code, codes.boolean);
            (declared, flow)
        });
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let [left, right] = codes.constructors;
            let translator = negation(arena, codes.constructors);
            let flow = forward(arena, (codes.boolean, codes.boolean), translator, &[
                right, left,
            ]);
            let declared = arena.value_type_flow_universe(codes.boolean, codes.boolean);
            (declared, flow)
        });
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let first = arena.value_constant(ConstantIndex::from(TERMINAL));
            let second = arena.value_constant(ConstantIndex::from(SELECT));
            let flow = arena.value_then(first, second, Seam::Sequence);
            let declared = arena.value_type_flow_universe(codes.boolean, codes.boolean);
            (declared, flow)
        });
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let flow = arena.value_stay(codes.boolean);
            let declared = arena.value_type_flow_universe(codes.boolean, codes.boolean);
            (declared, flow)
        });
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let unit_type = arena.value_type_unit();
            let endo = arrow(arena, codes.boolean_type, codes.boolean_type);
            let point = arrow(arena, unit_type, codes.boolean_type);
            let domain = arena.value_constant(ConstantIndex::from(SELECT));
            let codomain = arena.value_constant(ConstantIndex::from(NOT));
            let declared = arena.value_type_flow_universe(endo, point);
            let flow = arena.value_function_flow(declared, domain, codomain);
            (declared, flow)
        });
        define(&mut environment, |arena| {
            let payload = arena.value_type_unit();
            let graph = Arc::new(Graph {
                root: State(0),
                nodes: vec![Node::End],
            });
            let session = arena.value_type_session(graph, payload);
            let code = arena.value_quote(session);
            let declared = arena.value_type_flow_universe(code, code);
            let proofs = arena.value_unit();
            let evidence = Arc::new(Evidence {
                pairs: [StatePair {
                    source: State(0),
                    target: State(0),
                }]
                .into(),
                payloads: Vec::new(),
            });
            (
                declared,
                arena.value_session_flow(declared, evidence, proofs),
            )
        });
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let [left, _] = codes.constructors;
            let moving = arena.value_variable(DeBruijnIndex::from(0_u32));
            let motive = arena.value_type_element(moving, Level::zero());
            let flow = arena.value_constant(ConstantIndex::from(TERMINAL));
            let ride = arena.computation_ride(motive, flow, left);
            let landed = arena.value_type_element(codes.unit_code, Level::zero());
            let returner = arena.comp_type_returner(landed);
            (arena.value_type_thunk(returner), arena.value_thunk(ride))
        });
        define(&mut environment, |arena| {
            let string = arena.value_type_base(BaseType::String);
            let here = arena.value_literal(Literal::Text(StringLiteral::new("here".into())));
            let point = arena.value_variable(DeBruijnIndex::from(0_u32));
            let family = arena.value_type_flow(string, here, point);
            let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
            let body = arena.value_type_flow(string, here, outer);
            let returner = arena.comp_type_returner(body);
            let inner = arena.comp_type_pi(family, returner);
            let motive = arena.comp_type_pi(string, inner);
            let flow = arena.value_stay(here);
            let start = arena.value_stay(here);
            let over = arena.value_stay(start);
            let value = arena.value_stay(here);
            let ride = arena.computation_telescope_ride(motive, flow, start, over, value);
            let landed = arena.value_type_flow(string, here, here);
            let returner = arena.comp_type_returner(landed);
            (arena.value_type_thunk(returner), arena.value_thunk(ride))
        });
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let unit_type = arena.value_type_unit();
            let first = arena.value_constant(ConstantIndex::from(NOT));
            let second = arena.value_constant(ConstantIndex::from(TERMINAL));
            let flow = arena.value_flow_product(first, second);
            let source = arena.value_type_product(&[codes.boolean_type, codes.boolean_type]);
            let target = arena.value_type_product(&[codes.boolean_type, unit_type]);
            let source = arena.value_quote(source);
            let target = arena.value_quote(target);
            (arena.value_type_flow_universe(source, target), flow)
        });
        define(&mut environment, |arena| {
            let codes = codes(arena);
            let unit_type = arena.value_type_unit();
            let [left, _] = codes.constructors;
            let moving = arena.value_variable(DeBruijnIndex::from(0_u32));
            let motive = arena.value_type_element(moving, Level::zero());
            let flow = arena.value_constant(ConstantIndex::from(PRODUCT));
            let pair = arena.value_tuple(&[left, left]);
            let ride = arena.computation_ride(motive, flow, pair);
            let target = arena.value_type_product(&[codes.boolean_type, unit_type]);
            let target = arena.value_quote(target);
            let landed = arena.value_type_element(target, Level::zero());
            let returner = arena.comp_type_returner(landed);
            (arena.value_type_thunk(returner), arena.value_thunk(ride))
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
        tamper: impl FnOnce(&mut TermArena, ValueId) -> ValueId,
    ) -> gandr_kernel_core::ArtifactRefusal
    {
        let artifact = decode(bytes.as_image()).expect("the module decodes");
        let mut arena = artifact.arena().clone();
        let mut declarations = artifact.declarations().to_vec();
        let slot = usize::from(position);
        let DeclarationContent::Def { declared, body } =
            *declarations[slot].declaration().content()
        else {
            panic!("a definition at the tampered position");
        };
        let forged = tamper(&mut arena, body);
        let declaration = DeclarationBuilder::new(&mut arena).def(
            LevelSignature::monomorphic(),
            declared,
            forged,
        );
        declarations[slot] = MarkedDeclaration::new(AdmissionMark::Checked, declaration);
        let rewritten = encode(&arena, &declarations);
        let decoded = decode(rewritten.as_image()).expect("the copy is well formed on the wire");
        let refusal = Environment::replay(decoded.arena().clone(), decoded.declarations())
            .expect_err("a tampered certificate does not readmit");
        assert_eq!(refusal.position(), position);
        refusal
    }

    #[test]
    fn every_certificate_kind_persists_decodes_and_replays()
    {
        let environment = module();
        let bytes = export(&environment);
        let artifact = decode(bytes.as_image()).expect("the module decodes");
        assert_eq!(
            Vec::from(encode(artifact.arena(), artifact.declarations())),
            Vec::from(bytes.clone()),
            "the decoded nodes re-encode to the same bytes"
        );
        let replayed = Environment::replay(artifact.arena().clone(), artifact.declarations())
            .expect("every certificate readmits by replay");
        assert_eq!(Vec::from(export(&replayed)), Vec::from(bytes));
    }

    #[test]
    fn a_tampered_certificate_refuses_by_name()
    {
        let bytes = export(&module());

        // A wrong image: negation's images swapped.
        let refusal = tampered(&bytes, ConstantIndex::from(NOT), |arena, body| {
            let Some(&Value::ForwardFlow {
                flow_type,
                translator,
                ref outputs,
                ref dialogues,
            }) = arena.value(body)
            else {
                panic!("a forward flow");
            };
            let swapped: Vec<ValueId> = outputs.iter().rev().copied().collect();
            let dialogues = Arc::clone(dialogues);
            arena.value_forward_flow(flow_type, translator, swapped.into(), dialogues)
        });
        assert!(matches!(
            refusal.error(),
            &KernelError::Flow(FlowError::ForwardReplay {
                pattern: PatternPosition(0),
                ..
            })
        ));

        // A reversed seam: the composition's output fed back to its input.
        let refusal = tampered(&bytes, ConstantIndex::from(CONSTANT), |arena, body| {
            let Some(&Value::Then { first, second, .. }) = arena.value(body)
            else {
                panic!("a composition");
            };
            arena.value_then(first, second, Seam::Feedback)
        });
        assert!(matches!(
            refusal.error(),
            &KernelError::Flow(FlowError::Cycle { .. })
        ));

        // A misdirected boundary: the terminal map at the argument, running
        // the way a covariant boundary would.
        let refusal = tampered(&bytes, ConstantIndex::from(FUNEXT), |arena, body| {
            let Some(&Value::FunctionFlow {
                flow_type,
                codomain,
                ..
            }) = arena.value(body)
            else {
                panic!("a function flow");
            };
            let terminal = arena.value_constant(ConstantIndex::from(TERMINAL));
            arena.value_function_flow(flow_type, terminal, codomain)
        });
        assert_eq!(
            refusal.error(),
            &KernelError::Flow(FlowError::Boundary(Boundary::Domain))
        );

        // A product in the wrong order: its classifier relates the swapped
        // pairs, which the declared type does not.
        let refusal = tampered(&bytes, ConstantIndex::from(PRODUCT), |arena, body| {
            let Some(&Value::FlowProduct(first, second)) = arena.value(body)
            else {
                panic!("a flow product");
            };
            arena.value_flow_product(second, first)
        });
        assert!(!matches!(refusal.error(), &KernelError::Flow(_)));
    }
}
