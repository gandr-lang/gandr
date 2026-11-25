//! The print of a term of a signature as MLIR text in the generic form.
//!
//! # Items
//!
//! [`print_term`] reads a [`BindingTerm`] against the table of its signature
//! and a [`Naming`], and against nothing else: no operation has code of its
//! own. A term is a body: each node is one operation, and its rest is the next
//! node. Each port of an operation prints by its sort.
//!
//! | Port | Print |
//! | ---- | ----- |
//! | of the result sort of the operation | the rest of the body; its binder names the result |
//! | of a representable sort | an operand: a variable of the term |
//! | of a sort that indexes a representable sort | a type: a constant of that sort, with no operand |
//! | of another sort of the table | an attribute: a constant of that sort, as its value in the [`Naming`] |
//! | of the host type `Integer` | an attribute: an integer, with the type `i64` or the type of a type port |
//! | of the host type `String` | an attribute: a text in quotes, or a reference to a symbol |
//!
//! The value of a host port is an operation with no argument whose name is
//! the literal: `4` for an `Integer`, and the text itself for a `String`. The
//! [`Naming`] gives the MLIR name of an operation and of an attribute, where
//! it is not the name in the block. It also gives the attributes that each use
//! of an operation has.
//!
//! With no MLIR name, the dialect is the name of the signature in lower case.
//! An operation `add` of `Llvm` prints as `"llvm.add"`. A type `int<N>` prints
//! as `i<N>`, and another type `t` as `!<dialect>.t`. The result `k` of the
//! body, from 0, is `%vk`.
//!
//! # Boundaries
//!
//! The print does not admit the signature through `SimplySorted`: the
//! values of the fragment have their type as an index. A port that is none of
//! the six, such as a region, has no print yet, and the print refuses it. An
//! operation gives one result at most.
//!
//! # References
//!
//! - `vault:01a21222-e4bd-74a7-82be-989aaccefe85` — dependency: §
//!   seam-changes-library, the print against the trunk.
//! - `vault:01a21222-e4bd-74a8-a918-8efd438926aa` — dependency: §
//!   halves-slices-enum, row 5, the print of a term as the text for the shim.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use core::fmt::Write as _;

use anodized::spec;
use gandr_theory_levitation::BindingTerm;
use gandr_theory_levitation::BindingView;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::SortDesc;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::VariableIndex;

use crate::naming::AttributeForm;
use crate::naming::AttributeKind;
use crate::naming::Naming;
use crate::naming::PortName;

/// A spelling of MLIR text: the name of a value with no `%`, or a type.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Spelling<'text>(&'text str);

impl<'text> From<&'text str> for Spelling<'text>
{
    /// The text as a spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

/// The name of a value of the context of a term: a text, or the number `n` of
/// the value `%vn` of the enclosing function.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueName<'text>
{
    /// A name, with no `%`.
    Text(Spelling<'text>),
    /// The value `%vn` of the function.
    Numbered(usize),
}

impl<'text> From<&'text str> for ValueName<'text>
{
    /// The text as a name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self::Text(Spelling(text))
    }
}

/// One value of the context of a term, as the enclosing function names it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Parameter<'text>
{
    /// The name of the value.
    pub name: ValueName<'text>,
    /// The type of the value, such as `i32`.
    pub ty: Spelling<'text>,
}

/// The MLIR text of a body: one operation on each line, and the type of each
/// result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Printed
{
    /// The text.
    text: String,
    /// The type of each result, in the order of the body.
    results: Vec<String>,
}

impl Printed
{
    /// The type of each result, in the order of the body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn results(&self) -> &[String]
    {
        &self.results
    }

    /// The text and the type of each result, for a caller that keeps them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (String, Vec<String>)
    {
        (self.text, self.results)
    }
}

impl AsRef<str> for Printed
{
    /// The text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.text
    }
}

impl fmt::Display for Printed
{
    /// Write the text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.text)
    }
}

/// Where a body prints: the number of its first result, and what the print
/// does with its terminator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Place
{
    /// The number `k` of the first result, which prints as `%vk`.
    pub first: usize,
    /// What the print does with the operation that has no rest.
    pub terminator: Terminator,
}

impl Place
{
    /// A body alone: its results from `%v0` on, and its terminator printed.
    pub const ALONE: Self = Self {
        first: 0,
        terminator: Terminator::Print,
    };
}

/// What the print does with the operation that ends a body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Terminator
{
    /// The operation prints, as the end of a function of its own.
    Print,
    /// The operation does not print, because the body is in place in another
    /// function.
    Omit,
}

/// Why a term has no print.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PrintError
{
    /// The term names an operation that the table does not have.
    UnknownOperation(Name),
    /// The operation has another count of arguments than of input ports, or
    /// not one output.
    Arity(Name),
    /// A variable stands where the rest of a body stands.
    NotABody,
    /// A variable counts past the context.
    UnboundVariable(VariableIndex),
    /// The argument of the operand port with this name is not a variable.
    NotAValue(Name),
    /// The argument of the type port with this name is not a constant.
    NotAType(Name),
    /// The argument of the attribute port with this name is not a constant of
    /// the sort of the port, or not a literal of its host type.
    NotAnAttribute(Name),
    /// The constant with this name has no value in the [`Naming`].
    NoMlirValue(Name),
    /// The port with this name is of a sort that has no print yet, such as a
    /// region.
    Unprinted(Name),
    /// The sort of the value of the port with this name has no type that the
    /// print can read.
    Untyped(Name),
    /// The rest of the operation with this name binds more than one result.
    Results(Name),
}

impl fmt::Display for PrintError
{
    /// Write the refusal with the name it concerns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::UnknownOperation(ref name) => write!(f, "the table has no operation `{name}`"),
            Self::Arity(ref name) => write!(f, "the arguments of `{name}` do not match its ports"),
            Self::NotABody => f.write_str("a variable stands where the rest of a body stands"),
            Self::UnboundVariable(index) => {
                write!(f, "the variable {index} counts past the context")
            },
            Self::NotAValue(ref name) => write!(f, "the operand `{name}` is not a variable"),
            Self::NotAType(ref name) => write!(f, "the type `{name}` is not a constant"),
            Self::NotAnAttribute(ref name) => {
                write!(
                    f,
                    "the attribute `{name}` is not a constant or a literal of its sort"
                )
            },
            Self::NoMlirValue(ref name) => write!(f, "the constant `{name}` has no MLIR value"),
            Self::Unprinted(ref name) => write!(f, "the port `{name}` has no print yet"),
            Self::Untyped(ref name) => write!(f, "the value of `{name}` has no type to print"),
            Self::Results(ref name) => write!(f, "`{name}` binds more than one result"),
        }
    }
}

impl core::error::Error for PrintError
{
}

/// One value in scope: a parameter, by its place in the context, or a result
/// of the body, by its place in the results.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Slot
{
    /// The parameter at this place.
    Parameter(usize),
    /// The result at this place.
    Result(usize),
}

/// The constant of each type port of one operation, by the name of the port.
#[repr(transparent)]
struct TypePorts<'table>(BTreeMap<&'table str, &'table Name>);

/// The sort of an attribute port.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AttributeSort
{
    /// A sort of constants of the table.
    Constants,
    /// The host type `Integer`.
    Integer,
    /// The host type `String`.
    Text,
}

impl AttributeSort
{
    /// The attribute sort of a port of the sort `sort`, which the table
    /// declares when `declared` holds. The caller takes the representable
    /// sorts and the sorts of types out first.
    ///
    /// # Specification
    /// - ensures: [`Self::Constants`] for a sort of the table,
    ///   [`Self::Integer`] for `Integer`, [`Self::Text`] for `String`, and
    ///   nothing for another sort.
    /// - panics: none.
    /// - executable: none — the answer selects a form of text, which the tests
    ///   read back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each attribute port of the block of `std.llvm` prints
    ///   and reads back by its sort, and a port of another sort is refused.
    /// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
    /// - witness: `print::tests::each_refusal_has_a_term_that_meets_it`
    #[inline]
    #[must_use]
    pub fn of<D>(
        sort: &Name,
        declared: D,
    ) -> Option<Self>
    where
        D: Into<bool>,
    {
        if declared.into() {
            Some(Self::Constants)
        }
        else if sort.as_ref() == INTEGER {
            Some(Self::Integer)
        }
        else if sort.as_ref() == STRING {
            Some(Self::Text)
        }
        else {
            None
        }
    }
}

/// The dialect of a signature: its name in lower case.
#[repr(transparent)]
pub struct Dialect(String);

impl Dialect
{
    /// The dialect of the signature `table`.
    ///
    /// # Specification
    /// - ensures: the name of the signature in lower case.
    /// - panics: none.
    /// - executable: none — the name is text, which the tests read back.
    ///
    /// # Cost
    /// - allocation: the name, durable by the dialect
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the signature `Llvm` prints its operations in the
    ///   dialect `llvm`, and its body reads back from that dialect.
    /// - witness: `print::tests::an_addition_prints_as_one_llvm_add`
    /// - witness: `term::tests::the_read_of_the_print_of_a_term_is_that_term`
    pub fn of<G>(table: &TheoryDesc<G>) -> Self
    {
        Self(table.id.name.as_ref().to_lowercase())
    }

    /// The name of the operation `operation` of the signature in MLIR text.
    ///
    /// # Specification
    /// - ensures: the dialect, a `.`, and the name of the operation.
    /// - panics: none.
    /// - executable: none — the name is text, which the tests read back.
    ///
    /// # Cost
    /// - allocation: the name, durable by the caller
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the facts of `llvm.add` read as the operation `add`,
    ///   and an operation of another dialect is refused by its name.
    /// - witness: `term::tests::the_read_of_the_print_of_a_term_is_that_term`
    /// - witness: `term::tests::each_refusal_has_facts_that_meet_it`
    pub fn qualified(
        &self,
        operation: &Name,
    ) -> String
    {
        format!("{}.{operation}", self.0)
    }

    /// The spelling of the type constant `constant`.
    ///
    /// # Specification
    /// - ensures: as [`Self::write_spelling`] writes it.
    /// - panics: none.
    /// - executable: none — the spelling is text, which the tests read back.
    ///
    /// # Cost
    /// - allocation: the spelling, durable by the caller
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the type of a read operation is the constant whose
    ///   spelling it is.
    /// - witness: `term::tests::the_read_of_the_print_of_a_term_is_that_term`
    pub fn spell(
        &self,
        constant: &Name,
    ) -> String
    {
        let mut spelling = String::new();
        self.write_spelling(constant, &mut spelling);
        spelling
    }

    /// Write the spelling of the type constant `constant` into `out`.
    ///
    /// # Specification
    /// - ensures: `int` and a decimal width give `i` and the width; another
    ///   constant gives `!<dialect>.<constant>`.
    /// - panics: none.
    /// - executable: none — the spelling is text, which the tests read back.
    ///
    /// # Cost
    /// - allocation: the spelling, growth within `out`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `int32` gives `i32` and `int1` gives `i1`, and the
    ///   element type of an address arithmetic prints as `i8`.
    /// - witness: `print::tests::an_addition_prints_as_one_llvm_add`
    /// - witness: `print::tests::a_result_is_the_operand_of_the_next_operation`
    /// - witness: `agreement::tests::each_operation_passes_the_verifier_and_one_operand_less_does_not`
    fn write_spelling(
        &self,
        constant: &Name,
        out: &mut String,
    )
    {
        let constant = constant.as_ref();
        let _infallible = match constant.strip_prefix("int") {
            Some(width) if !width.is_empty() && width.bytes().all(|byte| byte.is_ascii_digit()) => {
                write!(out, "i{width}")
            },
            Some(_) | None => write!(out, "!{}.{constant}", self.0),
        };
    }
}

/// What the print of one term reads: the dialect, the MLIR names, and the
/// operations of the table by name.
struct Printer<'table>
{
    /// The dialect of the signature.
    dialect: Dialect,
    /// The MLIR names of the block.
    naming: &'table Naming,
    /// The operations of the table, by name.
    opers: BTreeMap<&'table Name, &'table OperDesc>,
}

impl Printer<'_>
{
    /// The type of the value whose sort takes `arguments`, at the port `port`.
    /// `types` gives the constant of each type port of the operation.
    ///
    /// # Specification
    /// - ensures: a sort with one index: a port name gives the type of that
    ///   port, and a constant gives itself.
    /// - fails: [`PrintError::Untyped`] for another count of indices, an index
    ///   that is neither, and a name with no type port.
    /// - panics: none.
    /// - executable: none — the type is text, which the tests read back.
    ///
    /// # Errors
    /// [`PrintError::Untyped`], as listed.
    ///
    /// # Cost
    /// - allocation: the spelling, durable by the value it types
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a port name and a constant each give the type of a
    ///   result, and a name with no type port is refused.
    /// - witness: `print::tests::a_result_is_the_operand_of_the_next_operation`
    /// - witness: `print::tests::each_refusal_has_a_term_that_meets_it`
    fn value_type(
        &self,
        port: &Name,
        arguments: &[FreeTerm],
        types: &TypePorts<'_>,
    ) -> Result<String, PrintError>
    {
        let untyped = || PrintError::Untyped(port.clone());
        let [ref index] = *arguments
        else {
            return Err(untyped());
        };
        let constant = match index.view() {
            TermView::Var(name) => types.0.get(name.as_ref()).copied().ok_or_else(untyped)?,
            TermView::Op { name, args } if args.len() == 0 => name,
            TermView::Op { .. }
            | TermView::Ctor { .. }
            | TermView::Results { .. }
            | TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => return Err(untyped()),
        };
        Ok(self.dialect.spell(constant))
    }

    /// Write the attribute of the port `port` of the sort `sort`, whose
    /// argument is `argument`, into `out`, after a `, ` when `out` has an
    /// attribute already. `attribute` is the form that the [`Naming`] gives
    /// the port, and `types` the constant of each type port.
    ///
    /// # Specification
    /// - ensures: `<name> = <value>`, with the name of the form or the name of
    ///   the port. A constant gives its value in the [`Naming`]; an integer
    ///   gives itself with `i64` or the type of the type port that the form
    ///   names; a text gives itself in quotes, or `@` and itself for a symbol.
    /// - fails: [`PrintError::NotAnAttribute`] for an argument that is not a
    ///   constant of the sort of the port or a literal of its host type,
    ///   [`PrintError::NoMlirValue`] for a constant with no value, and
    ///   [`PrintError::Untyped`] for a type port that the operation does not
    ///   fill.
    /// - panics: none.
    /// - executable: none — the attribute is text, which the verifier of the
    ///   shim reads.
    ///
    /// # Errors
    /// As listed.
    ///
    /// # Cost
    /// - allocation: the attribute, growth within `out`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each attribute of the block of `std.llvm` passes the
    ///   verifier of the shim, and each refusal has a term that meets it.
    /// - witness: `agreement::tests::each_operation_passes_the_verifier_and_one_operand_less_does_not`
    /// - witness: `print::tests::each_refusal_has_a_term_that_meets_it`
    fn write_attribute(
        &self,
        port: &SortRef,
        argument: BindingView<'_>,
        sort: AttributeSort,
        attribute: Option<&AttributeForm>,
        types: &TypePorts<'_>,
        out: &mut String,
    ) -> Result<(), PrintError>
    {
        let not_attribute = || PrintError::NotAnAttribute(port.name.clone());
        let BindingView::Operation { name: value, args } = argument
        else {
            return Err(not_attribute());
        };
        if args.len() != 0 {
            return Err(not_attribute());
        }
        let (mlir, kind) = attribute.map_or_else(
            || (port.name.as_ref(), AttributeKind::Plain),
            |form| (form.mlir, form.kind),
        );
        if !out.is_empty() {
            out.push_str(", ");
        }
        let _infallible = write!(out, "{mlir} = ");
        match sort {
            AttributeSort::Constants => {
                let declared = self.opers.get(value).is_some_and(|constant| {
                    constant.arity.inputs.is_empty()
                        && matches!(*constant.arity.outputs, [ref output] if output.sort == port.sort)
                });
                if !declared {
                    return Err(not_attribute());
                }
                let form = self
                    .naming
                    .constant(value)
                    .ok_or_else(|| PrintError::NoMlirValue(value.clone()))?;
                out.push_str(form.value);
            },
            AttributeSort::Integer => {
                let literal = value.as_ref();
                let digits = literal.strip_prefix('-').unwrap_or(literal);
                if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
                    return Err(not_attribute());
                }
                let _infallible = write!(out, "{literal} : ");
                match kind {
                    AttributeKind::TypedBy(PortName(typed)) => {
                        let constant = types
                            .0
                            .get(typed)
                            .ok_or_else(|| PrintError::Untyped(port.name.clone()))?;
                        self.dialect.write_spelling(constant, out);
                    },
                    AttributeKind::Plain | AttributeKind::Symbol | AttributeKind::Type => {
                        out.push_str("i64");
                    },
                }
            },
            AttributeSort::Text => match kind {
                AttributeKind::Symbol => {
                    let _infallible = write!(out, "@{value}");
                },
                AttributeKind::Plain | AttributeKind::TypedBy(_) | AttributeKind::Type => {
                    out.push('"');
                    for character in value.as_ref().chars() {
                        match character {
                            '"' => out.push_str("\\\""),
                            '\\' => out.push_str("\\\\"),
                            '\n' => out.push_str("\\n"),
                            other => out.push(other),
                        }
                    }
                    out.push('"');
                },
            },
        }
        Ok(())
    }
}

/// The host type of an integer attribute.
const INTEGER: &str = "Integer";

/// The host type of a text attribute.
const STRING: &str = "String";

/// A printer of the terms of one signature, made one time for a table and a
/// naming. It keeps its buffers from one print to the next.
pub struct TermPrinter<'table>
{
    /// The dialect, the naming and the operations of the table.
    printer: Printer<'table>,
    /// The sorts of the table, by name.
    sorts: BTreeMap<&'table Name, &'table SortDesc>,
    /// The sorts that index a representable sort: the sorts of types.
    type_sorts: BTreeSet<&'table Name>,
    /// The values in scope, the newest last.
    scope: Vec<Slot>,
    /// The place in `scope` of each operand of one operation.
    operands: Vec<usize>,
    /// The attributes of one operation.
    attributes: String,
}

impl<'table> TermPrinter<'table>
{
    /// The printer of the terms of the signature `table`, with the MLIR names
    /// of `naming`.
    ///
    /// # Specification
    /// - ensures: the operations and the sorts of `table` by name, and the
    ///   sorts that index a representable sort.
    /// - panics: none.
    /// - executable: none — the tables are maps of the table, which each print
    ///   reads.
    ///
    /// # Cost
    /// - allocation: the tables of the signature, setup
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation of the block of `std.llvm` prints
    ///   through one printer, as text that the verifier accepts.
    /// - witness: `agreement::tests::each_operation_passes_the_verifier_and_one_operand_less_does_not`
    #[inline]
    #[must_use]
    pub fn new<G>(
        table: &'table TheoryDesc<G>,
        naming: &'table Naming,
    ) -> Self
    {
        Self {
            printer: Printer {
                dialect: Dialect::of(table),
                naming,
                opers: table.opers.iter().map(|op| (&op.name, op)).collect(),
            },
            sorts: table.sorts.iter().map(|sort| (&sort.name, sort)).collect(),
            type_sorts: table
                .sorts
                .iter()
                .filter(|sort| sort.representability == Representability::Representable)
                .flat_map(|sort| sort.indices.iter().map(|index| &index.sort))
                .collect(),
            scope: Vec::new(),
            operands: Vec::new(),
            attributes: String::new(),
        }
    }

    /// Print `term`, a body of the signature of the printer, as MLIR text in
    /// the generic form, in the context `parameters`, at `place`.
    ///
    /// A variable counts from the newest entry of the context: index 0 is the
    /// result of the last operation, or the last parameter before the first
    /// one. The result `k` of the body, from 0, prints as `%v<first + k>`.
    /// With [`Terminator::Omit`], the operation with no rest does not print, so
    /// the text goes inside a function before its own terminator.
    ///
    /// # Specification
    /// - requires: no parameter has a name `v<k>` with `k` from `place.first`
    ///   on.
    /// - ensures: one line for each operation of the body, in order, each with
    ///   its result, its operands, its attributes, the types of its operands
    ///   and the type of its result. The body ends at an operation with no
    ///   rest, which prints only with [`Terminator::Print`]. The print gives
    ///   the type of each result, in order.
    /// - fails: as the variants of [`PrintError`] state.
    /// - panics: none.
    ///
    /// # Errors
    /// The first [`PrintError`] of the body, in order.
    ///
    /// # Cost
    /// - allocation: the text and the type of each result, durable by the print
    /// - allocation: the scope, the operands and the attributes, growth within
    ///   the printer
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an addition prints as one `llvm.add` with its two
    ///   operands and their types, and its print with a return goes through the
    ///   verifier of the shim; a result is the operand of the next operation; a
    ///   comparison prints the type of its result from a constant; each
    ///   operation of the block of `std.llvm` prints, with its attributes, as
    ///   text that the verifier accepts; each refusal has a term that meets it;
    ///   a body in place numbers its results from its first one and omits its
    ///   terminator, and the function that holds it goes through the verifier.
    /// - witness: `print::tests::an_addition_prints_as_one_llvm_add`
    /// - witness: `print::tests::a_result_is_the_operand_of_the_next_operation`
    /// - witness: `print::tests::each_refusal_has_a_term_that_meets_it`
    /// - witness: `print::tests::a_body_in_place_numbers_its_results_from_the_first_and_omits_its_terminator`
    /// - witness: `agreement::tests::each_operation_passes_the_verifier_and_one_operand_less_does_not`
    #[inline]
    #[spec(ensures: |ret| place.terminator == Terminator::Omit
        || ret.as_ref().map_or(true, |printed| printed.text.lines().count() >= 1))]
    pub fn print(
        &mut self,
        term: &BindingTerm,
        (parameters, place): (&[Parameter<'_>], Place),
    ) -> Result<Printed, PrintError>
    {
        let representable = |sort: &Name| {
            self.sorts
                .get(sort)
                .is_some_and(|sort| sort.representability == Representability::Representable)
        };
        let attribute_sort = |sort: &Name| AttributeSort::of(sort, self.sorts.contains_key(sort));
        self.scope.clear();
        self.scope
            .extend((0 .. parameters.len()).map(Slot::Parameter));
        let mut text = String::new();
        let mut results: Vec<String> = Vec::new();
        let mut types = TypePorts(BTreeMap::new());
        let mut node = term.view();
        loop {
            let BindingView::Operation { name, args } = node
            else {
                return Err(PrintError::NotABody);
            };
            let op = self
                .printer
                .opers
                .get(name)
                .ok_or_else(|| PrintError::UnknownOperation(name.clone()))?;
            let [ref output] = *op.arity.outputs
            else {
                return Err(PrintError::Arity(name.clone()));
            };
            if args.len() != op.arity.inputs.len() {
                return Err(PrintError::Arity(name.clone()));
            }
            let form = self.printer.naming.operation(name);
            types.0.clear();
            self.operands.clear();
            self.attributes.clear();
            let mut rest = None;
            for (port, argument) in op.arity.inputs.iter().zip(args.clone()) {
                if port.sort == output.sort {
                    rest = Some((port, argument));
                    continue;
                }
                if !port.bindings.is_empty() || !port.abstractions.is_empty() {
                    return Err(PrintError::Unprinted(port.name.clone()));
                }
                if representable(&port.sort) {
                    let BindingView::Variable(index) = argument.view()
                    else {
                        return Err(PrintError::NotAValue(port.name.clone()));
                    };
                    let place = self
                        .scope
                        .len()
                        .checked_sub(usize::from(index).saturating_add(1))
                        .ok_or(PrintError::UnboundVariable(index))?;
                    self.operands.push(place);
                }
                else if self.type_sorts.contains(&port.sort) {
                    match argument.view() {
                        BindingView::Operation {
                            name: constant,
                            args,
                        } if args.len() == 0 => {
                            types.0.insert(port.name.as_ref(), constant);
                        },
                        BindingView::Operation { .. } | BindingView::Variable(_) => {
                            return Err(PrintError::NotAType(port.name.clone()));
                        },
                    }
                }
                else if attribute_sort(&port.sort).is_none() {
                    return Err(PrintError::Unprinted(port.name.clone()));
                }
            }
            // The attributes go after the types, because an integer can take
            // the type of a type port.
            for (port, argument) in op.arity.inputs.iter().zip(args) {
                if port.sort == output.sort || representable(&port.sort) {
                    continue;
                }
                let attribute = form.and_then(|form| form.attribute(&port.name));
                if self.type_sorts.contains(&port.sort) {
                    if let Some(&AttributeForm {
                        mlir,
                        kind: AttributeKind::Type,
                        ..
                    }) = attribute
                        && let Some(&constant) = types.0.get(port.name.as_ref())
                    {
                        if !self.attributes.is_empty() {
                            self.attributes.push_str(", ");
                        }
                        let _infallible = write!(self.attributes, "{mlir} = ");
                        self.printer
                            .dialect
                            .write_spelling(constant, &mut self.attributes);
                    }
                    continue;
                }
                if let Some(sort) = attribute_sort(&port.sort) {
                    self.printer.write_attribute(
                        port,
                        argument.view(),
                        sort,
                        attribute,
                        &types,
                        &mut self.attributes,
                    )?;
                }
            }
            if let Some(form) = form
                && !form.fixed.is_empty()
            {
                if !self.attributes.is_empty() {
                    self.attributes.push_str(", ");
                }
                self.attributes.push_str(form.fixed);
            }
            let result = match rest.map(|(port, _)| port.bindings.as_ref()) {
                None | Some(&[]) => None,
                Some(&[ref binding]) => Some(self.printer.value_type(
                    &binding.name,
                    &binding.arguments,
                    &types,
                )?),
                Some(_) => return Err(PrintError::Results(name.clone())),
            };
            if rest.is_none() && place.terminator == Terminator::Omit {
                return Ok(Printed { text, results });
            }
            if result.is_some() {
                let _infallible =
                    write!(text, "%v{} = ", place.first.saturating_add(results.len()));
            }
            match form {
                Some(form) => {
                    let _infallible = write!(text, "\"{}\"(", form.mlir);
                },
                None => {
                    let _infallible = write!(text, "\"{}.{name}\"(", self.printer.dialect.0);
                },
            }
            let slots = || {
                self.operands
                    .iter()
                    .filter_map(|&at| self.scope.get(at).copied())
            };
            for (at, slot) in slots().enumerate() {
                let separator = if at == 0 { "" } else { ", " };
                let _infallible = match slot {
                    Slot::Parameter(index) => match parameters
                        .get(index)
                        .map(|parameter| parameter.name)
                    {
                        Some(ValueName::Text(spelling)) => {
                            write!(text, "{separator}%{}", spelling.0)
                        },
                        Some(ValueName::Numbered(number)) => write!(text, "{separator}%v{number}"),
                        None => Ok(()),
                    },
                    Slot::Result(index) => {
                        write!(text, "{separator}%v{}", place.first.saturating_add(index))
                    },
                };
            }
            text.push(')');
            if !self.attributes.is_empty() {
                let _infallible = write!(text, " <{{{}}}>", self.attributes);
            }
            text.push_str(" : (");
            for (at, slot) in slots().enumerate() {
                let separator = if at == 0 { "" } else { ", " };
                let ty = match slot {
                    Slot::Parameter(index) => parameters.get(index).map(|parameter| parameter.ty.0),
                    Slot::Result(index) => results.get(index).map(String::as_str),
                };
                text.push_str(separator);
                text.push_str(ty.unwrap_or_default());
            }
            let _infallible = writeln!(text, ") -> {}", result.as_deref().unwrap_or("()"));
            if let Some(ty) = result {
                self.scope.push(Slot::Result(results.len()));
                results.push(ty);
            }
            match rest {
                Some((_, argument)) => node = argument.view(),
                None => return Ok(Printed { text, results }),
            }
        }
    }
}

/// Print `term`, a body of the signature `table`, as MLIR text in the generic
/// form, in the context `parameters`, with the MLIR names of `naming`, at
/// `place`, through a printer made for this one term.
///
/// # Specification
/// - ensures: the print of [`TermPrinter::print`] by [`TermPrinter::new`] of
///   `table` and `naming`.
/// - fails: as [`TermPrinter::print`].
/// - panics: none.
/// - executable: none — [`TermPrinter::print`] checks its own clause on the
///   same call.
///
/// # Errors
/// The first [`PrintError`] of the body, in order.
///
/// # Cost
/// - allocation: the tables of the signature, setup
/// - allocation: the text and the type of each result, durable by the print
///
/// # Adequacy
/// - hypothesis: L3 — an addition prints as one `llvm.add`, and each refusal
///   has a term that meets it.
/// - witness: `print::tests::an_addition_prints_as_one_llvm_add`
/// - witness: `print::tests::each_refusal_has_a_term_that_meets_it`
#[inline]
pub fn print_term<G>(
    table: &TheoryDesc<G>,
    naming: &Naming,
    term: &BindingTerm,
    (parameters, place): (&[Parameter<'_>], Place),
) -> Result<Printed, PrintError>
{
    TermPrinter::new(table, naming).print(term, (parameters, place))
}
