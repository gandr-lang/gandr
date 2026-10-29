use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_checker::TermNode;
use gandr_core_checker::TypedModule;
use gandr_core_checker::Typings;
use gandr_core_checker::type_module;
use gandr_core_sequent::Independence;
use gandr_core_sequent::Writers;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_syntax::SourceText;

use super::independent;
use crate::compose::Lowered;
use crate::compose::LoweringCount;
use crate::compose::Opening;
use crate::compose::adapt;
use crate::compose::checking_context;
use crate::compose::lower_source;
use crate::compose::pattern_holes;

/// What a call's head applies, through its applications and the force of
/// the callee's thunk.
#[derive(Clone, Copy, Debug)]
enum Callee
{
    /// A declaration's thunk.
    Constant(ConstantIndex),
    /// A bound thunk: a recursive definition's own.
    Bound,
}

/// The callee of the call `head`, when `head` is one.
///
/// # Specification
/// trivial.
fn callee(
    core: &CoreArena,
    mut head: ComputationId,
) -> Option<Callee>
{
    loop {
        let computation = core.computation(head)?;
        if let Computation::Application(function, _) = *computation {
            head = function;
            continue;
        }
        let Computation::Force(value) = *computation
        else {
            return None;
        };
        let value = core.value(value)?;
        return if let Value::Constant(constant) = *value {
            Some(Callee::Constant(constant))
        }
        else if let Value::Variable { .. } = *value {
            Some(Callee::Bound)
        }
        else {
            None
        };
    }
}

/// `source` lowered, and its declarations typed over the arena the lowering
/// made.
///
/// # Specification
/// trivial.
fn typed(source: SourceText<'_>) -> (LoweredModule<'_>, CoreArena, TypedModule)
{
    let grammar = built_in().expect("the built-in grammar");
    let lowering =
        lower_source(&grammar, source, &mut LoweringCount::default()).expect("the source lowers");
    let Lowered::Module { module, mut arena } = lowering.into_lowered()
    else {
        panic!("the source is a module");
    };
    let declarations = adapt(&module);
    let mut context = checking_context(
        &mut arena,
        Opening::UNBOUNDED,
        &module,
        &pattern_holes(&module),
    );
    let typed = type_module(&mut context, &declarations);
    (module, arena, typed)
}

/// Each bind head `source`'s typed run judged, by the constant it calls,
/// beside whether [`independent`] names it a writer: sorted by name, each
/// pair once.
///
/// # Specification
/// trivial.
fn named_calls(source: SourceText<'_>) -> Vec<(String, Independence)>
{
    let (module, core, typed) = typed(source);
    let core = &core;
    let writers = independent(core, &typed);
    let name = |called: Callee| match called {
        Callee::Constant(constant) => module
            .declarations()
            .iter()
            .find(|declaration| declaration.constant() == constant)
            .map(|declaration| String::from(declaration.name().as_ref()))
            .expect("the constant is declared"),
        Callee::Bound => String::from("itself"),
    };
    let mut named: Vec<(String, Independence)> = typed
        .typings()
        .values()
        .flat_map(Typings::typings)
        .filter_map(|typing| match typing.term {
            TermNode::Computation(term) => match core.computation(term) {
                Some(&Computation::Bind(head, _)) => {
                    callee(core, head).map(|called| (name(called), writers.independence(head)))
                },
                _ => None,
            },
            TermNode::Value(_) => None,
        })
        .collect();
    named.sort_by(|one, other| one.0.cmp(&other.0));
    named.dedup();
    named
}

#[test]
fn the_tree_sum_names_each_pure_call()
{
    let named = named_calls(SourceText::from(
        r#"
data Tree : Type {
  Leaf : (n : Integer) --> Tree;
  Node : (l : Tree, r : Tree) --> Tree;
}
def rec sum(t : Tree) -> Integer {
  case t {
    Leaf(n) => n,
    Node(l, r) => { run a <- sum[<](l); run b <- sum[<](r); a + b }
  }
}
def say(s : String) -> [Console] Unit { Console.print(s) }
def shout(s : String) -> [Console] Integer { run u <- say(s); 1 }
"#,
    ));
    assert_eq!(
        named,
        Vec::from([
            (String::from("itself"), Independence::Independent),
            (String::from("say"), Independence::Sequential),
        ]),
        "each recursive call is a writer, and the call that prints is not"
    );
}

#[test]
fn a_writer_over_a_capability_stays_fused()
{
    let named = named_calls(SourceText::from(
        r#"
def count(c : Cap { read }) -> Integer { 1 }
def twice(n : Integer) -> Integer { n + n }
def both(c : Cap { read }, k : Integer) -> Integer {
  run a <- count(c);
  run b <- twice(k);
  a + b
}
"#,
    ));
    assert_eq!(
        named,
        Vec::from([
            (String::from("count"), Independence::Sequential),
            (String::from("twice"), Independence::Independent),
        ]),
        "the call over the capability stays fused, and its sibling over an integer is a writer"
    );
}

/// `kept-view.gandr`'s first run: the bind's writer lends a shared view of
/// the hold and answers a thunk kept in the scope's region, which reads the
/// view. Its row is empty. The corpus differential found its concurrent run
/// ending at a segmentation fault, since a kept value may capture a view the
/// writer's own run lent.
#[test]
fn a_writer_answering_a_kept_value_stays_fused_2954()
{
    let source = SourceText::from(
        r#"
def keptView() -> Integer {
  hold s = 3;
  handle c : Proc {
    run k : (() => Integer) at c <- access shared s as w { pure pure w };
    force k
  } with {
    pure(x) => pure x,
    oper exit(code, k) => pure 0
  }
}
"#,
    );
    let (_module, core, typed) = typed(source);
    let core = &core;
    let binds = typed
        .typings()
        .values()
        .flat_map(Typings::typings)
        .filter(|typing| {
            matches!(typing.term, TermNode::Computation(term)
                if matches!(core.computation(term), Some(&Computation::Bind(..))))
        })
        .count();
    assert!(binds > 0, "the run binds the kept thunk");
    assert_eq!(
        independent(core, &typed),
        Writers::NONE,
        "a writer whose answer keeps a view stays fused"
    );
}
