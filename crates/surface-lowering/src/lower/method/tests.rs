use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::SourceText;

use crate::CandidateCount;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::lower::access::tests::forms;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::DeclarationOutcome;
use crate::resolve::SurfaceName;

/// A counter's methods, one per receiver mode, and a block calling each on
/// one held count.
const COUNTER: &str = r"module Counter {
  def read(self : shared Integer) -> -F Integer { pure self }
  def bump(self : Integer, by : Integer) -> -F Unit {
    access self as v { resume(v, v + by) }
  }
  def spend(self : consumed Integer) -> -F Integer { pure self + 1 }
}
def used() -> -F Integer {
  hold s = 1;
  run n <- s.read();
  run _ <- s.bump(2);
  run m <- s.spend();
  pure n + m
}
";

#[test]
fn each_mode_lowers_to_its_access()
{
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(COUNTER), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("used")));
    assert_eq!(
        forms(&arena, tail),
        [
            "hold",
            "access shared @0",
            "access @0",
            "resume @0",
            "consume @0",
        ],
        "a read lends the count shared, a write lends it and writes back, and a take ends \
         its hold"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_written_through_body_returns_its_receiver()
{
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(COUNTER), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("bump")));
    assert_eq!(
        forms(&arena, tail),
        ["hold", "access @0", "resume @0"],
        "the body runs under the hold of its receiver, which it lends as a held slot"
    );
    let Some(&Computation::Memory(MemoryForm::Hold { value, .. })) = arena.computation(tail)
    else {
        panic!("the body is a hold")
    };
    assert_eq!(
        arena.value(value),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32),
        }),
        "the hold holds the receiver parameter, one past `by`"
    );
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("bump"))
    else {
        panic!("`bump` is declared")
    };
    let DeclarationOutcome::Completed { declared_type, .. } = declaration.outcome()
    else {
        panic!("`bump` lowers both halves: {:?}", declaration.outcome())
    };
    let mut current = match arena.value_type(declared_type) {
        Some(&ValueType::Thunk(computation)) => computation,
        other => panic!("a thunk type: {other:?}"),
    };
    while let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(current) {
        current = codomain;
    }
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(current)
    else {
        panic!("a returner past the arrows")
    };
    assert!(
        matches!(arena.value_type(result), Some(ValueType::Product(components)) if components.len() == 2_usize),
        "the result pairs the receiver before the answer: {:?}",
        arena.value_type(result)
    );
}

#[test]
fn a_receiver_not_held_is_passed_or_refused()
{
    let source = format!(
        "{COUNTER}def passed(t : Integer) -> -F Integer {{\n  run n <- t.read();\n  t.spend()\n}}\n\
         def written(t : Integer) -> -F Unit {{ t.bump(1) }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("passed")));
    assert_eq!(
        forms(&arena, tail),
        Vec::<String>::new(),
        "a receiver no slot holds is read through and taken as a value"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("written")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Held,
                ..
            }
        ),
        "nothing holds what a write would write back"
    );
}

#[test]
fn a_method_two_modules_declare_is_refused_naming_both()
{
    let source = "module A { def size(self : shared Integer) -> -F Integer { pure self } }\n\
                  module B { def size(self : shared Integer) -> -F Integer { pure 0 } }\n\
                  def measured() -> -F Integer { hold s = 1; s.size() }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("measured")),
            LoweringRefusal::AmbiguousMethod { method, first, second, more, .. }
                if method == SurfaceName::from("size")
                    && first == SurfaceName::from("A")
                    && second == SurfaceName::from("B")
                    && more == CandidateCount::from(0_usize)
        ),
        "the call names both modules: {:?}",
        refusal_of(&module, SurfaceName::from("measured"))
    );
}

#[test]
fn a_mode_word_off_a_receiver_is_refused()
{
    let source = "def top(x : shared Integer) -> -F Integer { pure x }\n\
                  module M { def second(self : shared Integer, y : consumed Integer) -> -F \
                  Integer { pure y } }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    for (name, mode) in [("top", "shared"), ("second", "consumed")] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::StrayReceiverMode { mode: written, .. }
                    if written == SurfaceName::from(mode)
            ),
            "`{name}` writes `{mode}` on a parameter that is no receiver"
        );
    }
}

#[test]
fn a_receiver_is_a_typed_first_self()
{
    let source = "module M {\n\
                  def untyped(self) -> -F Integer { pure 0 }\n\
                  def other(x : Integer) -> -F Integer { pure x }\n\
                  def generic @[a : Type] (self : shared a) -> -F a { pure self }\n\
                  }\n\
                  def first() -> -F Integer { hold s = 1; s.untyped() }\n\
                  def second() -> -F Integer { hold s = 1; s.other() }\n\
                  def third() -> -F Integer { hold s = 1; s.generic() }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    for name in ["first", "second"] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::OutOfFragment { .. }
            ),
            "`{name}` calls no method: {:?}",
            refusal_of(&module, SurfaceName::from(name))
        );
    }
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("third")),
            LoweringRefusal::ImplicitUnsupplied { function, .. }
                if function == SurfaceName::from("generic")
        ),
        "a receiver behind an implicit telescope is a method, called with no implicit: {:?}",
        refusal_of(&module, SurfaceName::from("third"))
    );
}
