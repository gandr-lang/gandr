//! Native prelude functions through parsing, checking, kernel admission and
//! execution.

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_core_sequent::Stuck;
    use gandr_core_term::primitive::PrimitiveError;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::Evaluation;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::Unrunnable;
    use gandr_surface_dispatcher::compose;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    /// Compose a fixture and execute its final declaration.
    ///
    /// # Specification
    /// - requires: a parseable source with at least one declaration.
    /// - ensures: the real dispatcher evaluates its selected final declaration.
    /// - panics: if parsing, composition or declaration selection fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — native results, refusal, blame and source shadowing
    ///   have distinct observations.
    /// - witness: `builtins::tests::native_names_operators_and_partial_application_execute`
    /// - witness: `builtins::tests::native_errors_and_goal_blame_remain_distinct`
    /// - witness: `builtins::tests::source_and_binder_names_shadow_the_outer_prelude`
    #[spec(ensures: |ret| !matches!(ret, Evaluation::Unrunnable(Unrunnable::Undeclared(_))))]
    fn run(source: SourceText<'_>) -> Evaluation<'_>
    {
        let grammar = built_in().expect("built-in grammar");
        let mut lowerings = LoweringCount::default();
        let Composed::Settled { mut program, .. } =
            compose(&grammar, CorpusRoot::Fixture, source, &mut lowerings).expect("composition")
        else {
            panic!("module was refused");
        };
        let Maybe::Present(target) = program.target()
        else {
            panic!("final declaration");
        };
        program.evaluate(target)
    }

    #[test]
    fn native_names_operators_and_partial_application_execute()
    {
        for (source, expected) in [
            (
                "def answer : +U (-F Integer) ; def answer = thunk { 19 - 7 } ;",
                "12",
            ),
            (
                "def answer : +U (-F Integer) ; def answer = thunk { int.div(19, 4) } ;",
                "4",
            ),
            (
                "def answer : +U (-F Bool) ; def answer = thunk { 19 < 7 } ;",
                "inr(())",
            ),
            (
                "def answer : +U (-F Integer) ; def answer = thunk { -7 } ;",
                "-7",
            ),
            (
                "def partial : +U (Integer -> -F Integer) ; def partial = thunk { sub(19) } ; def answer : +U (-F Integer) ; def answer = thunk { partial(7) } ;",
                "12",
            ),
        ] {
            let Evaluation::Value(value) = run(SourceText::from(source))
            else {
                panic!("native fixture did not produce a value: {source}");
            };
            assert_eq!(value.as_ref(), expected, "{source}");
        }
    }

    #[test]
    fn native_errors_and_goal_blame_remain_distinct()
    {
        assert!(matches!(
            run(SourceText::from(
                "def answer : +U (-F Integer) ; def answer = thunk { int.div(19, 0) } ;"
            )),
            Evaluation::Stuck(Stuck::Primitive(PrimitiveError::DivisionByZero))
        ));
        assert!(matches!(
            run(SourceText::from(
                "def answer : +U (-F Integer) ; def answer = thunk { sub(\"wrong\", 7) } ;"
            )),
            Evaluation::Unrunnable(Unrunnable::Refused(_))
        ));
        assert!(
            matches!(run(SourceText::from("def owed : Integer ; def answer : +U (-F Integer) ; def answer = thunk { sub(owed, 7) } ;")), Evaluation::Blamed(name) if name.as_ref() == "owed")
        );
    }

    #[test]
    fn source_and_binder_names_shadow_the_outer_prelude()
    {
        for source in [
            "def add : +U (Integer -> Integer -> -F Integer) ; def add = thunk { fn (x) { fn (y) { ret x } } } ; def answer : +U (-F Integer) ; def answer = thunk { add(19, 7) } ;",
            "def f : +U (Integer -> -F Integer) ; def f = thunk { fn (add) { ret add } } ; def answer : +U (-F Integer) ; def answer = thunk { f(19) } ;",
        ] {
            let Evaluation::Value(value) = run(SourceText::from(source))
            else {
                panic!("shadowing fixture did not execute");
            };
            assert_eq!(value.as_ref(), "19");
        }
    }
}
