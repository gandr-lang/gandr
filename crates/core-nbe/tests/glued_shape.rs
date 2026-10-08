//! The domain's shape through the public surface: both faces readable on the
//! nodes that carry them, both closure spaces built over one environment, and
//! the two policy parameters installed together.
//!
//! The unit suites separate each decision surface. This suite asserts that the
//! pieces compose through the re-exports a consumer reaches, which is what
//! would break first if a face or a closure space were reachable only from
//! inside the crate.

/// The glued-shape cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod glued_shape
{
    use gandr_core_nbe::CompTermFace;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::DomainComp;
    use gandr_core_nbe::DomainValue;
    use gandr_core_nbe::DuplicationPolicy;
    use gandr_core_nbe::DuplicationStance;
    use gandr_core_nbe::Environment;
    use gandr_core_nbe::Glued;
    use gandr_core_nbe::NeutralHead;
    use gandr_core_nbe::PolicyRefusal;
    use gandr_core_nbe::SchedulingPolicy;
    use gandr_core_nbe::SchedulingStance;
    use gandr_core_nbe::TermFace;
    use gandr_core_nbe::Unfolding;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionHeight;
    use gandr_core_term::Zone;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GlobalIndex;

    #[test]
    fn the_term_face_carries_the_source_term_it_came_from()
    {
        let mut core = CoreArena::new();
        let source = core.value_unit();
        let body = core.computation_return(source);

        let mut domain = DomainArena::new();
        let unreduced = domain.value_unit(TermFace::Source(source));
        let reduced = domain.value_pair(unreduced, unreduced, TermFace::Reduced);

        assert_eq!(
            Some(&DomainValue::Unit {
                face: TermFace::Source(source),
            }),
            domain.value(unreduced),
            "an unreduced value reads back as the id it came from"
        );
        assert_eq!(
            Some(&DomainValue::Pair {
                first: unreduced,
                second: unreduced,
                face: TermFace::Reduced,
            }),
            domain.value(reduced),
            "and a value something reduced inside states the absence rather than a stale id"
        );

        let produced = domain.value_unit(TermFace::Reduced);
        let returner = domain.comp_return(produced, CompTermFace::Source(body));
        assert_eq!(
            Some(&DomainComp::Return {
                value: produced,
                face: CompTermFace::Source(body),
            }),
            domain.computation(returner),
            "the negative side carries the same face over its own family"
        );
    }

    #[test]
    fn both_closure_spaces_close_over_one_environment()
    {
        let mut core = CoreArena::new();
        let value_body = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let comp_body = core.computation_return(value_body);

        let mut domain = DomainArena::new();
        let bound = domain.value_unit(TermFace::Reduced);
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, bound);

        let value_closure = domain.value_closure_node(value_body, environment.clone());
        let comp_closure = domain.comp_closure_node(comp_body, environment);

        let held = domain
            .value_closure(value_closure)
            .expect("the value closure resolves");
        assert_eq!(value_body, held.body());
        assert_eq!(
            Some(bound),
            held.environment()
                .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
            "the captured environment answers the body's free variable"
        );

        let held = domain
            .comp_closure(comp_closure)
            .expect("the computation closure resolves");
        assert_eq!(comp_body, held.body());
        assert_eq!(
            Some(bound),
            held.environment()
                .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
            "and so does the other space's, over the same environment"
        );
    }

    #[test]
    fn forcing_a_neutral_leaves_the_neutral_form_readable()
    {
        let mut domain = DomainArena::new();
        let head = NeutralHead::Constant(ConstantIndex::from(2_usize));
        let neutral = domain
            .neutral_node(
                head,
                Vec::new(),
                Unfolding::Unforced(GlobalIndex::from(4_u32)),
            )
            .expect("a declaration head may carry a body");
        let stood = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a spineless neutral stands in a value position");
        let unfolded = domain.value_unit(TermFace::Reduced);

        assert_eq!(
            Ok(()),
            domain.force_neutral(neutral, Glued::Value(unfolded))
        );
        let held = domain.neutral(neutral).expect("the neutral resolves");
        assert_eq!(
            head,
            held.head(),
            "the neutral form is still there to compare against"
        );
        assert_eq!(Unfolding::Forced(Glued::Value(unfolded)), held.unfolding());
        assert!(
            domain.value(stood).is_some(),
            "and the value standing for it is untouched by the forcing"
        );
    }

    #[test]
    fn the_two_parameters_install_side_by_side()
    {
        let scheduling = SchedulingPolicy::new(SchedulingStance::HeightWeighted);
        let duplication = DuplicationPolicy::default();
        assert_eq!(SchedulingStance::HeightWeighted, scheduling.stance());
        assert_eq!(DuplicationStance::EraseAndClone, duplication.stance());
        assert!(
            u32::from(scheduling.share(DefinitionHeight::from(0_u32))) > 0_u32,
            "the weighted stance installs without a gate, because a share forecloses nothing"
        );
        assert_eq!(
            Err(PolicyRefusal::StanceGated {
                stance: DuplicationStance::Spinal,
            }),
            DuplicationPolicy::new(DuplicationStance::Spinal),
            "while the duplication parameter's finer stance waits on its certification trace"
        );
    }
}
