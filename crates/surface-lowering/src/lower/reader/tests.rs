use gandr_core_term::CoreArena;
use gandr_surface_syntax::SourceText;

use crate::lower::native::tests::preluded;
use crate::unit::Unit;

#[test]
fn a_model_of_the_prelude_s_from_nat_lends_its_reader_4528()
{
    // Each module ascribed the prelude's `Model(FromNat)` lends its `fromNat`
    // member, in declaration order; a model of another theory lends none.
    let source = "\
data Parity : Type where { | Even : Parity | Odd : Parity }
module ParityFromNat : Model(FromNat) with sort Carrier = Parity where {
  def fromNat(n : Integer) -> Parity { Even }
}
module Flag : Model(Eq) with sort Carrier = Bool where {
  def eq(a : Bool, b : Bool) -> Bool { true }
  law refl admitted;
  law sym admitted;
}
module BoolFromNat : Model(FromNat) with sort Carrier = Bool where {
  def fromNat(n : Integer) -> Bool { true }
}
";
    let (text, unit) = crate::prelude::lay(SourceText::from(source), &Unit::single()).unwrap();
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    let readers = module.readers();
    assert_eq!(
        readers.len(),
        2,
        "each model of the prelude's theory lends one reader: {readers:?}"
    );
    assert!(
        readers.windows(2).all(|pair| pair.first() < pair.get(1)),
        "the readers stand in declaration order: {readers:?}"
    );
}

#[test]
fn a_source_s_own_from_nat_lends_no_reader_4528()
{
    // A source's own theory named `FromNat` shadows the prelude's, and its
    // models lend nothing: the literal reads through the prelude's alone.
    let source = "\
theory FromNat where {
  sort Carrier : Type;
  oper fromNat : (n : Integer) --> Carrier;
}
module BoolFromNat : Model(FromNat) with sort Carrier = Bool where {
  def fromNat(n : Integer) -> Bool { true }
}
";
    let (text, unit) = crate::prelude::lay(SourceText::from(source), &Unit::single()).unwrap();
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    assert_eq!(
        module.readers(),
        &[],
        "a model of a source's own `FromNat` lends no reader"
    );
}
