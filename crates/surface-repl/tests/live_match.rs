//! Live matching observed through the public transcript writer.

#[cfg(test)]
mod tests
{
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::form_value_type;
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::LoweredChain;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::TermId;
    use gandr_core_term::pattern::Pattern;
    use gandr_core_term::pattern::Patterns;
    use gandr_kernel_term::Side;
    use gandr_surface_repl::encode_match;
    use gandr_surface_repl::write_block;
    use gandr_surface_session::MatchCheckpoint;

    #[test]
    fn a_fill_updates_the_external_match_transcript()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let sum = core.value_type_sum(unit, unit);
        let hole = HoleId::from(0_u32);
        let scrutinee = core.value_hole(hole);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let (mut checkpoint, _) =
            MatchCheckpoint::evaluate(&core, definitions, Fuel::from(10_000_u32), scrutinee)
                .unwrap();
        let mut patterns = Patterns::new();
        let any = patterns.mint(Pattern::Wildcard);
        let left = patterns.mint(Pattern::Injection(Side::Left, any));
        let right = patterns.mint(Pattern::Injection(Side::Right, any));
        let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
        let formed = form_value_type(&mut context, sum).unwrap();
        let before = checkpoint
            .analyze(&mut context, formed, &patterns, &[left, right])
            .unwrap();
        let mut transcript = Vec::new();
        write_block(&mut transcript, &encode_match(&before)).unwrap();
        let before = String::from_utf8(transcript).unwrap();
        assert!(before.contains("arm 0: possibly") && before.contains("arm 1: possibly"));
        assert!(before.contains("held at arm 0"));
        let value = core.value_unit();
        let value = core.value_injection(Side::Right, value);
        checkpoint
            .fill(
                &mut core,
                definitions,
                Fuel::from(10_000_u32),
                hole,
                TermId::Value(value),
            )
            .unwrap();
        let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
        let after = checkpoint
            .analyze(&mut context, formed, &patterns, &[left, right])
            .unwrap();
        let mut transcript = Vec::new();
        write_block(&mut transcript, &encode_match(&after)).unwrap();
        let after = String::from_utf8(transcript).unwrap();
        assert!(after.contains("arm 0: no") && after.contains("arm 1: yes"));
        assert!(after.contains("selected arm 1"));
        assert!(!after.contains("possibly") && !after.contains("held at"));
    }
}
