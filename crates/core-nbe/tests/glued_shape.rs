// Specification backfill pending (gandr-lang/gandr#9): the executable-
// specification lints are allowed until this crate's own backfill lands.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        spec_attribute_present,
        adequacy_present,
        maybe_shape,
        erased_error_signature
    )
)]
//! The domain's source and reduced faces and its policy selection through
//! the public consumer surface.

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
    use gandr_core_nbe::Glued;
    use gandr_core_nbe::NeutralHead;
    use gandr_core_nbe::PolicyRefusal;
    use gandr_core_nbe::SchedulingPolicy;
    use gandr_core_nbe::SchedulingStance;
    use gandr_core_nbe::TermFace;
    use gandr_core_nbe::Unfolding;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionHeight;
    use gandr_kernel_term::ConstantIndex;
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
