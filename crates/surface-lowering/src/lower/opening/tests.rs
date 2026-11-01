use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::SourceText;

use crate::error::LoweringRefusal;
use crate::lower::exits::tests::spelled_within;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::module::LoweredModule;
use crate::resolve::Resolution;
use crate::resolve::SurfaceName;

/// The admission position of the declaration of `module` named `name`.
///
/// # Specification
/// trivial.
fn constant_of(
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> ConstantIndex
{
    module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
        .map(crate::module::LoweredDeclaration::constant)
        .expect("the declaration is lowered")
}

/// What the name `needle`, spelled once in `context`, resolved to.
///
/// # Specification
/// trivial.
fn resolution_at(
    module: &LoweredModule<'_>,
    text: SourceText<'_>,
    context: SourceText<'_>,
    needle: SourceText<'_>,
) -> Option<Resolution>
{
    let at = spelled_within(text, context, needle);
    module
        .resolutions()
        .iter()
        .find(|&&(span, _)| span == at)
        .map(|&(_, resolution)| resolution)
}

/// `import Counting ;` opens a top-level module over the rest of its block,
/// and `import Outer.Inner ;` a nested one by its path: a name there reads
/// the member, and the program checks as its qualified spelling does. A
/// binder wins over an opened member.
#[test]
fn an_opened_module_answers_the_rest_of_its_block()
{
    let source = "module Counting where {\n\
                  def two = 2;\n\
                  }\n\
                  module Outer where {\n\
                  module Inner where {\n\
                  def three = 3;\n\
                  }\n\
                  }\n\
                  def counted() -> -F Integer { import Counting; return two }\n\
                  def nested() -> -F Integer { import Outer.Inner; return three }\n\
                  def bound(two : Integer) -> -F Integer { import Counting; return two + 1 }\n";
    let text = SourceText::from(source);
    let mut arena = CoreArena::new();
    let module = lowered(text, &mut arena);
    assert_accepted(&judged(&module, &mut arena));
    assert_eq!(
        [
            resolution_at(
                &module,
                text,
                SourceText::from("return two }"),
                SourceText::from("two")
            ),
            resolution_at(
                &module,
                text,
                SourceText::from("return three }"),
                SourceText::from("three")
            ),
        ],
        [
            Some(Resolution::Declaration(constant_of(
                &module,
                SurfaceName::from("two")
            ))),
            Some(Resolution::Declaration(constant_of(
                &module,
                SurfaceName::from("three")
            ))),
        ],
        "an opened module's member answers its name in the rest of the block"
    );
    assert_eq!(
        resolution_at(
            &module,
            text,
            SourceText::from("return two + 1"),
            SourceText::from("two")
        ),
        Some(Resolution::Binder(spelled_within(
            text,
            SourceText::from("bound(two"),
            SourceText::from("two")
        ))),
        "a binder wins over an opened member"
    );
}

/// A name read before the statement, a head no container declares a module
/// of, and a link the module before it exports no module of are refused.
#[test]
fn an_unknown_module_is_refused_at_its_path()
{
    let source = "module Counting where {\n\
                  def two = 2;\n\
                  }\n\
                  def early() -> -F Integer { let x = two; import Counting; return x }\n\
                  def missing() -> -F Integer { import Absent; return 1 }\n\
                  def linked() -> -F Integer { import Counting.two; return 1 }\n";
    let text = SourceText::from(source);
    let module = lowered(text, &mut CoreArena::new());
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("early")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("two")
        ),
        "a name before the statement is not in its scope"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("missing")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("Absent")
        ),
        "a head no container declares a module of is unresolved"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("linked")),
            LoweringRefusal::UnknownMember { module, member, .. }
                if module == SurfaceName::from("Counting") && member == SurfaceName::from("two")
        ),
        "a link naming a value, not a module, is no module the path reaches"
    );
}

/// A name an opened module and an earlier declaration both answer, and one
/// two opened modules answer, are refused at the use; a module declared
/// after the declaration opening it answers a forward reference.
#[test]
fn a_name_two_scopes_answer_is_refused_at_its_use()
{
    let source = "def two = 20;\n\
                  module Counting where {\n\
                  def two = 2;\n\
                  def four = 4;\n\
                  }\n\
                  module Other where {\n\
                  def four = 40;\n\
                  }\n\
                  def clash() -> -F Integer { import Counting; return two }\n\
                  def twice() -> -F Integer { import Counting; import Other; return four }\n\
                  def ahead() -> -F Integer { import Later; return five }\n\
                  module Later where {\n\
                  def five = 5;\n\
                  }\n";
    let text = SourceText::from(source);
    let module = lowered(text, &mut CoreArena::new());
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("clash")),
            LoweringRefusal::ImportShadows { name, .. } if name == SurfaceName::from("two")
        ),
        "an opened member and an earlier declaration of one name are refused at the use"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("twice")),
            LoweringRefusal::ImportShadows { name, .. } if name == SurfaceName::from("four")
        ),
        "two opened modules exporting one name are refused at the use"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("ahead")),
            LoweringRefusal::ForwardMemberReference { name, .. } if name == SurfaceName::from("five")
        ),
        "a member admitted after the declaration is a forward reference"
    );
}
