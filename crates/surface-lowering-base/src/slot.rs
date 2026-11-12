//! What a slot of a lowered module stands for, and whether its source exports
//! it. The collection of the lowering fills the slots, and the description
//! route reads their roles and their visibility.

/// What a slot stands for.
///
/// # Specification
/// - requires: nothing to construct this data; its producers and consumers
///   state coordinate preconditions separately.
/// - ensures: Declared slots introduce names, witnesses check an extra type
///   without declaring a name, held slots own components or refusals without
///   becoming exports, abstract slots declare the atom an opaque ascription
///   mints without entering a name table, the generic program is named without
///   declaring anything, and an admitted or a discharged law declares its type
///   with no body.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
/// - executable: none — the enabled specification facade does not expose
///   type-invariant expansion; executable predicates cover the producing and
///   consuming operations.
///
/// # Adequacy
/// - hypothesis: L3 — a member's written signature declares it and its derived
///   type is a witness; an opaque ascription's abstract component is declared
///   before the members.
/// - witness: `tests::slot::each_slot_is_read_with_its_role`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Role
{
    /// A name the source declared: a top-level definition or a module
    /// member.
    Declared,
    /// A second type stated for a member, checked by a declaration whose body
    /// is that member; or the kind a transparent ascription states for a type
    /// member, checked by a declaration whose body is that member's code.
    Witness,
    /// A slot that declares nothing: it carries a refusal a module or a
    /// signature component raised, or owns a manifest type component's type,
    /// and yields a declaration only when it holds a refusal.
    Held,
    /// An operation a `data` family declares and the module can call: entered
    /// in no namespace, its body compiled from its rules.
    Operation,
    /// A rule a theory's completion derives, `rule T.r : l <=> r;`, or a
    /// lemma its proof rests on: entered in no name table, the statement read
    /// through its theory's path `T.r`. Also the check an extern block
    /// carrying `boundary` takes, entered in no name table either.
    Derived,
    /// The abstract type an opaque ascription declares for one abstract
    /// component of its signature: admitted before the module's members,
    /// entered in no name table, and named through the namespace as the atom
    /// it mints.
    Abstract,
    /// The words of a `data` family's loops at one point: the presented type a
    /// path at that point reads as, minted from the family's form and entered
    /// in no namespace.
    Words,
    /// The terms of a theory a source writes as `Terms(S)`: a presented type
    /// whose constructors are the theory's operations and whose rules are
    /// its rules, minted from its presentation and entered in no namespace.
    Terms,
    /// A component of a functor's parameter: the template's stand-in for the
    /// argument's component, which each application renames and which
    /// declares nothing.
    Parameter,
    /// The prelude's generic program, `Eq.generic`: entered in its module's
    /// name table under its written signature, read only as the head of a
    /// definition `def m = Eq.generic(T)`, whose body the lowering derives
    /// from `T`'s constructors, and declaring nothing itself.
    Generic,
    /// A law of a module's model the host asserts at a primitive carrier,
    /// `law refl = ~admitted;`: entered in the module's name table, declared at
    /// the law's derived type with no definition, and crossing as the axiom
    /// the report's audit lists.
    Admitted,
    /// A law of a module's model the module omits: entered in the module's
    /// name table under the law's name, introduced by the module's form,
    /// declared at the law's derived type with no definition, and discharged
    /// by the checker, `here` at the law's left side where its sides convert.
    Discharged,
}

/// Whether a source exports a declaration of its top level.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Visibility
{
    /// A `pub` mark precedes it: a source importing its source reads it.
    Public,
    /// No mark precedes it: it is read in its own source alone.
    Private,
}
