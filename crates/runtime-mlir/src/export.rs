//! The symbol of an exported definition: a function of the C convention that
//! calls the function of the definition.
//!
//! A definition is a function of the convention `tailcc`, which no caller of
//! the C convention can call. [`Export`] prints one more function of the
//! `llvm` dialect, under the C convention, with the name of the export. Its
//! parameters are the parameters of the definition. It calls the definition
//! under `tailcc` and returns its answer.
//!
//! # Boundaries
//!
//! The function of the definition has a name of its own beside the export:
//! the caller of [`Export::new`] gives the two names. An export takes and
//! gives fixed-width integers only. Any other type is outside the fragment of
//! the call from Rust, and [`Export::new`] refuses it with
//! [`Form::Signature`].

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::IntegerWidth;

use crate::lower::Form;
use crate::lower::Symbol;
use crate::lower::named;

/// The symbol of one exported definition, under the C convention.
///
/// # Specification
/// - ensures: the value names two bare identifiers, and holds the width of each
///   parameter and of the result of the definition.
/// - panics: none.
/// - executable: none — a type-level block: a data declaration has no body and
///   no call boundary to check.
///
/// # Adequacy
/// - hypothesis: L3 — an export of a definition of two words compiles beside
///   its module, and the object has the symbol of the export.
/// - witness: `lower::tests::an_export_calls_its_definition_under_the_c_convention`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Export<'name>
{
    /// The name of the symbol.
    symbol: Symbol<'name>,
    /// The name of the function of the definition.
    callee: Symbol<'name>,
    /// The width of each parameter, the first one first.
    parameters: Box<[IntegerWidth]>,
    /// The width of the result.
    result: IntegerWidth,
}

/// The width of `word`, when it is a fixed-width integer.
///
/// # Specification
/// - ensures: the width of a base type of a width.
/// - fails: [`Form::Dangling`] for a type the arena does not hold, and
///   [`Form::Signature`] for each other type.
/// - panics: none.
///
/// # Errors
///
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a `u64` gives its width, and `Unit` is refused.
/// - witness: `lower::tests::an_export_calls_its_definition_under_the_c_convention`
/// - witness: `lower::tests::an_export_outside_the_fragment_is_refused`
#[spec(ensures: |ret| ret.is_err() || types.value_type(word).is_some_and(|ty| matches!(*ty, ValueType::Base(_))))]
fn width(
    types: &CoreArena,
    word: ValueTypeId,
) -> Result<IntegerWidth, Form>
{
    match *types.value_type(word).ok_or(Form::Dangling)? {
        ValueType::Base(BaseType::Fixed(width)) => Ok(width),
        ValueType::Base(
            BaseType::Integer
            | BaseType::String
            | BaseType::Numeric
            | BaseType::Character
            | BaseType::Float64,
        )
        | ValueType::Data { .. }
        | ValueType::Record(_)
        | ValueType::Patched { .. }
        | ValueType::PathUniverse(..)
        | ValueType::Path { .. }
        | ValueType::Flow { .. }
        | ValueType::Bridge { .. }
        | ValueType::Run { .. }
        | ValueType::Prefix { .. }
        | ValueType::Dialogue { .. }
        | ValueType::Web
        | ValueType::Product(_)
        | ValueType::Sigma { .. }
        | ValueType::Sum(_)
        | ValueType::List(_)
        | ValueType::Thunk(_)
        | ValueType::Universe { .. }
        | ValueType::Lift { .. }
        | ValueType::Element { .. }
        | ValueType::Row
        | ValueType::RowTail { .. }
        | ValueType::Abstract { .. }
        | ValueType::Staged { .. }
        | ValueType::StaticPi { .. }
        | ValueType::Unknown
        | ValueType::Stack { .. }
        | ValueType::Session { .. }
        | ValueType::Capability { .. }
        | ValueType::Buffer
        | ValueType::Qubit
        | ValueType::Kept { .. }
        | ValueType::World { .. } => Err(Form::Signature),
    }
}

impl<'name> Export<'name>
{
    /// The export `symbol` of the definition whose function is `callee`, and
    /// whose type is `signature`.
    ///
    /// # Specification
    /// - ensures: on success the export names `symbol` and `callee`, with one
    ///   width for each arrow of the chain and the width of its returner.
    /// - fails: [`Form::Symbol`] for a name that is not a bare identifier;
    ///   [`Form::Dangling`] for a type the arena does not hold;
    ///   [`Form::Signature`] for a type that is not a thunk of arrows over
    ///   fixed-width integers to a returner of a fixed-width integer.
    /// - panics: none.
    /// - intension: one read of the arena for each type of the chain, with no
    ///   recursion.
    ///
    /// # Errors
    ///
    /// As the failure clause states.
    ///
    /// # Cost
    /// - allocation: the widths of the parameters, durable by the export
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition of two `u64` to a `u64` gives an export,
    ///   and a parameter of `Unit` or a result of `Unit` is refused.
    /// - witness: `lower::tests::an_export_calls_its_definition_under_the_c_convention`
    /// - witness: `lower::tests::an_export_outside_the_fragment_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |export| export.symbol == symbol && export.callee == callee))]
    #[inline]
    pub fn new(
        types: &CoreArena,
        symbol: Symbol<'name>,
        callee: Symbol<'name>,
        signature: ValueTypeId,
    ) -> Result<Self, Form>
    {
        named(symbol)?;
        named(callee)?;
        let ValueType::Thunk(mut computation) =
            *types.value_type(signature).ok_or(Form::Dangling)?
        else {
            return Err(Form::Signature);
        };
        let mut parameters = Vec::new();
        loop {
            match *types.comp_type(computation).ok_or(Form::Dangling)? {
                CompType::Arrow { domain, codomain } => {
                    parameters.push(width(types, domain)?);
                    computation = codomain;
                },
                // The row of the returner bounds the effects of the body, and
                // the lowering of the body refuses each effect node.
                CompType::Returner { result, .. } => {
                    return Ok(Self {
                        symbol,
                        callee,
                        parameters: parameters.into_boxed_slice(),
                        result: width(types, result)?,
                    });
                },
                CompType::Returns { .. }
                | CompType::LinearArrow { .. }
                | CompType::Pi { .. }
                | CompType::Element { .. }
                | CompType::Unknown
                | CompType::With { .. }
                | CompType::Codata { .. } => return Err(Form::Signature),
            }
        }
    }
}

impl fmt::Display for Export<'_>
{
    /// The function of the export, as MLIR text.
    ///
    /// # Specification
    /// - ensures: a function of the C convention with the name of the export
    ///   and the parameters `%v0` and on, a `tailcc` call of the definition
    ///   with each parameter, and the return of its answer.
    /// - fails: an error of `f`.
    /// - panics: none.
    /// - executable: none — a clause over the written text would print the
    ///   function a second time.
    ///
    /// # Errors
    ///
    /// An error of the formatter.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the text compiles with the module of its definition,
    ///   and a Rust caller links the object and gets the answer.
    /// - witness: `lower::tests::an_export_calls_its_definition_under_the_c_convention`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let result = u32::from(self.result.bits());
        write!(f, "llvm.func @{}(", self.symbol)?;
        for (place, width) in self.parameters.iter().enumerate() {
            if place > 0 {
                f.write_str(", ")?;
            }
            write!(f, "%v{place}: i{}", u32::from(width.bits()))?;
        }
        writeln!(f, ") -> i{result} {{")?;
        write!(f, "  %answer = llvm.call tailcc @{}(", self.callee)?;
        for place in 0 .. self.parameters.len() {
            if place > 0 {
                f.write_str(", ")?;
            }
            write!(f, "%v{place}")?;
        }
        f.write_str(") : (")?;
        for (place, width) in self.parameters.iter().enumerate() {
            if place > 0 {
                f.write_str(", ")?;
            }
            write!(f, "i{}", u32::from(width.bits()))?;
        }
        writeln!(f, ") -> i{result}")?;
        writeln!(f, "  llvm.return %answer : i{result}")?;
        f.write_str("}\n")
    }
}
