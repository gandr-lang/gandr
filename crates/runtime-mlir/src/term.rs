//! The read of the facts of a body into a term of a signature: the inverse of
//! the print.
//!
//! # Items
//!
//! [`read_term`] reads the [`Operation`]s that the entry `read` of the feature
//! `full` gives against the table of a signature and a [`Naming`], and against
//! nothing else: no operation has code of its own. Each operation is one node
//! of the term, and its rest is the node of the next operation. Each port of
//! an operation reads by its sort, as the print writes it.
//!
//! | Port | Read from |
//! | ---- | --------- |
//! | of the result sort of the operation | the next operation; its binder is the result of the operation |
//! | of a representable sort | the next operand, a hole or a result before it, as a variable |
//! | of a sort that indexes a representable sort | the type of an operand or of the result whose index names the port, or the type attribute that the [`Naming`] gives the port, as a constant |
//! | of another sort of the table | the attribute of the port: the constant whose value in the [`Naming`] it is |
//! | of the host type `Integer` | the attribute of the port: an integer with the type `i64`, or with the type of the type port that the [`Naming`] names |
//! | of the host type `String` | the attribute of the port: a text in quotes, or a reference to a symbol |
//!
//! The name of an operation is its MLIR name in the [`Naming`], or the name of
//! the dialect, a `.`, and the name of an operation of the table. An attribute
//! has the MLIR name that the [`Naming`] gives its port, or the name of the
//! port. A type reads as the constant whose print is that type: `i<N>` as
//! `int<N>`, and `!<dialect>.t` as `t`. The value of a host port is an
//! operation with no argument whose name is the literal, as in the print. The
//! shim puts `<dialect>.unreachable` after the last operation of a body, so the
//! term ends with the operation `unreachable` of the table.
//!
//! # Boundaries
//!
//! **One MLIR name, more operations.** The [`Naming`] can give one MLIR name to
//! more operations of the block, such as the load of MLIR to `load` and
//! `load_atomic`. The read keeps the operations whose count of operand ports is
//! the count of operands. Of those, with the most ports first, the node is the
//! first whose attributes are each in the facts, with each constant a value of
//! its sort. Thus an atomic load reads as `load_atomic`, and a load with no
//! ordering as `load`.
//!
//! **Integers as MLIR prints them.** MLIR prints an integer of `i1` as `true`
//! or `false`, which read as `1` and `0`. It prints an integer of another
//! width as a signed value, so the read of the print of `255` at `i8` is
//! `-1`. The read does not check the attributes that each use of an operation
//! has, and it does not read an attribute that no port names.
//!
//! A port with a binder that is not the rest, or with a sort that is none of
//! the six, such as a region, has no read yet, and the read refuses it, as
//! the print does. An operation gives one result at most. An operation with no
//! rest ends a body, and a body has no such operation, because the shim puts
//! the terminator after the body.
//!
//! # References
//!
//! - `vault:01a21222-e4bd-74a7-82be-989aaccefe85` — dependency: §
//!   seam-changes-library, the read against the trunk.
//! - `vault:01a21222-e4bd-74a8-a918-8efd438926aa` — dependency: §
//!   halves-slices-enum, row 5, the read of the facts of a body into a term.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;

use anodized::spec;
use gandr_theory_levitation::BindingTerm;
use gandr_theory_levitation::BindingView;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::VariableIndex;

use crate::naming::AttributeForm;
use crate::naming::AttributeKind;
use crate::naming::Naming;
use crate::naming::OperationForm;
use crate::naming::PortName;
use crate::print::AttributeSort;
use crate::print::Dialect;
use crate::read::Hole;
use crate::read::Operand;
use crate::read::Operation;

/// Why the facts of a body give no term.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TermReadError
{
    /// The body has an operation that the table does not have. The name has
    /// the dialect, as the body writes it.
    UnknownOperation(Name),
    /// The operation has another count of operands than of operand ports,
    /// another count of results than its rest binds, or not one output.
    Arity(Name),
    /// The operation with this name has no rest, so it ends a body.
    Terminator(Name),
    /// An operand of the operation with this name is no hole and no result of
    /// an operation before it.
    UnboundOperand(Name),
    /// The port with this name is a region, or has a binder and is not the
    /// rest, which have no read yet.
    Unread(Name),
    /// The type at the port with this name is the print of no constant, or no
    /// operand, result or attribute gives the type of this port.
    Untyped(Name),
    /// The type at the port with this name is not the type that its index
    /// names: a constant, or the type of an operand before it.
    Mistyped(Name),
    /// The operation has no attribute for the port with this name, or the
    /// attribute is the print of no value of the sort of the port.
    Unattributed(Name),
}

impl fmt::Display for TermReadError
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
            Self::Arity(ref name) => write!(f, "the facts of `{name}` do not match its ports"),
            Self::Terminator(ref name) => write!(f, "`{name}` has no rest, so it ends a body"),
            Self::UnboundOperand(ref name) => {
                write!(
                    f,
                    "an operand of `{name}` is no hole and no result before it"
                )
            },
            Self::Unread(ref name) => write!(f, "the port `{name}` has no read yet"),
            Self::Untyped(ref name) => write!(f, "the type at `{name}` is no constant"),
            Self::Mistyped(ref name) => {
                write!(f, "the type at `{name}` is not the type of its index")
            },
            Self::Unattributed(ref name) => {
                write!(f, "the attribute of `{name}` reads as no value of its sort")
            },
        }
    }
}

impl core::error::Error for TermReadError
{
}

/// The text of one fact: a type, or the value of an attribute.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Fact<'facts>(&'facts str);

impl Fact<'_>
{
    /// The literal and the type of an integer attribute.
    ///
    /// # Specification
    /// - ensures: `true` and `false` give `1` and `0` with the type `i1`;
    ///   `<literal> : <type>` gives the literal, a `-` and decimal digits, and
    ///   the type; any other text gives nothing.
    /// - panics: none.
    /// - executable: none — the answer is text, which the tests read back.
    ///
    /// # Cost
    /// - allocation: the literal, durable by the term
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the alignment of a load and the value of a constant
    ///   read back from their print.
    /// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
    fn integer(self) -> Option<(Name, Self)>
    {
        match self.0 {
            "true" => Some((Name::from("1"), Fact("i1"))),
            "false" => Some((Name::from("0"), Fact("i1"))),
            text => {
                let (literal, ty) = text.split_once(" : ")?;
                let digits = literal.strip_prefix('-').unwrap_or(literal);
                (!digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()))
                    .then(|| (Name::from(literal), Fact(ty)))
            },
        }
    }

    /// The text of a string attribute.
    ///
    /// # Specification
    /// - ensures: text in quotes gives the text, with each escape of the lexer
    ///   of MLIR read: `\\`, `\"`, `\n`, `\t`, and `\` with two hex digits for
    ///   one byte; any other text, and bytes that are not UTF-8, give nothing.
    /// - panics: none.
    /// - executable: none — the answer is text, which the tests read back.
    ///
    /// # Cost
    /// - allocation: the bytes of the text, durable by the term
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the text and the constraints of an inline assembly
    ///   read back from their print.
    /// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
    fn quoted(self) -> Option<Name>
    {
        let inner = self.0.strip_prefix('"')?.strip_suffix('"')?;
        let hex = |digit: u8| u8::try_from(char::from(digit).to_digit(16)?).ok();
        let mut bytes = Vec::with_capacity(inner.len());
        let mut rest = inner.bytes();
        while let Some(byte) = rest.next() {
            match byte {
                b'"' => return None,
                b'\\' => match rest.next()? {
                    b'\\' => bytes.push(b'\\'),
                    b'"' => bytes.push(b'"'),
                    b'n' => bytes.push(b'\n'),
                    b't' => bytes.push(b'\t'),
                    high => {
                        let low = rest.next()?;
                        bytes.push(hex(high)?.checked_mul(16)?.checked_add(hex(low)?)?);
                    },
                },
                other => bytes.push(other),
            }
        }
        String::from_utf8(bytes)
            .ok()
            .map(|text| Name::from(text.as_str()))
    }

    /// The name of a reference to a symbol.
    ///
    /// # Specification
    /// - ensures: `@` and a name gives the name, and `@` and a text in quotes
    ///   gives the text, as [`Self::quoted`] reads it; any other text gives
    ///   nothing.
    /// - panics: none.
    /// - executable: none — the answer is text, which the tests read back.
    ///
    /// # Cost
    /// - allocation: the name, durable by the term
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the callee of a tail call reads back from its print.
    /// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
    fn symbol(self) -> Option<Name>
    {
        let name = self.0.strip_prefix('@')?;
        if name.starts_with('"') {
            return Fact(name).quoted();
        }
        (!name.is_empty()).then(|| Name::from(name))
    }
}

/// The read of one port of an operation, before its rest is read.
enum Port<'table>
{
    /// The rest of the body.
    Rest,
    /// An operand: the place of its value in the scope.
    Value(usize),
    /// A type: the name of the port.
    Type(&'table Name),
    /// An attribute whose value is not read yet: the port and its sort.
    Pending(&'table SortRef, AttributeSort),
    /// An attribute: the constant or the literal of its value.
    Attribute(Name),
}

/// One node of the term before its rest: the operation and its ports.
struct Node<'table>
{
    /// The operation of the table.
    op: &'table OperDesc,
    /// The read of each input port, in the order of the ports.
    ports: Vec<Port<'table>>,
    /// The constant of each type port, by the name of the port.
    types: TypePorts<'table>,
    /// The count of values in scope before the operation.
    depth: usize,
}

/// The values in scope before an operation: the holes, then the results.
struct Scope<'facts>
{
    /// The type of each value, the oldest first.
    types: Vec<Fact<'facts>>,
    /// The place in `types` of the result of each operation before, if it
    /// has one.
    places: Vec<Option<usize>>,
    /// The count of holes, which are the first values.
    holes: usize,
}

/// One operation of the table that an MLIR name can read as.
struct Candidate<'table>
{
    /// The operation.
    op: &'table OperDesc,
    /// The count of its operand ports.
    operands: usize,
}

/// What the read of one body reads: the MLIR names and the tables of the
/// signature.
struct Reader<'table>
{
    /// The MLIR names of the block.
    naming: &'table Naming,
    /// The operations that each MLIR name can read as, the most input ports
    /// first.
    opers: BTreeMap<String, Vec<Candidate<'table>>>,
    /// The sorts that the table declares.
    sorts: BTreeSet<&'table Name>,
    /// The representable sorts: the sorts of operands.
    representable: BTreeSet<&'table Name>,
    /// The sorts that index a representable sort: the sorts of types.
    type_sorts: BTreeSet<&'table Name>,
    /// The constant of each type, by its print.
    constants: BTreeMap<String, &'table Name>,
    /// The constant of each attribute value, by its sort and its MLIR value.
    values: BTreeMap<(&'table Name, &'static str), &'table Name>,
}

/// The constant of each type port of one operation, by the name of the port.
#[repr(transparent)]
struct TypePorts<'table>(BTreeMap<&'table str, &'table Name>);

impl<'table> TypePorts<'table>
{
    /// Note that the type port `port` holds `constant`.
    ///
    /// # Specification
    /// - ensures: the port holds the constant after the call.
    /// - fails: [`TermReadError::Mistyped`] for `name` when the port holds
    ///   another constant.
    /// - panics: none.
    /// - executable: none — the answer is a refusal or nothing, which the tests
    ///   read.
    ///
    /// # Errors
    /// As listed.
    ///
    /// # Cost
    /// - allocation: the entry of the port, growth within the map
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two operands of one type port with two types are
    ///   refused.
    /// - witness: `term::tests::each_refusal_has_facts_that_meet_it`
    fn hold(
        &mut self,
        port: &'table Name,
        constant: &'table Name,
        name: &Name,
    ) -> Result<(), TermReadError>
    {
        match self.0.insert(port.as_ref(), constant) {
            Some(before) if before != constant => Err(TermReadError::Mistyped(name.clone())),
            Some(_) | None => Ok(()),
        }
    }
}

impl<'table> Reader<'table>
{
    /// The reader of the bodies of `table` with the MLIR names of `naming`.
    ///
    /// # Specification
    /// - ensures: the tables of the signature, by the keys that the facts give.
    /// - panics: none.
    /// - executable: none — the tables serve the read, which the tests check.
    ///
    /// # Cost
    /// - allocation: the tables, durable by the reader
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation of the block reads back by its MLIR
    ///   name, its types and its attributes.
    /// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
    fn new<G>(
        table: &'table TheoryDesc<G>,
        naming: &'table Naming,
    ) -> Self
    {
        let dialect = Dialect::of(table);
        let representable: BTreeSet<&Name> = table
            .sorts
            .iter()
            .filter(|sort| sort.representability == Representability::Representable)
            .map(|sort| &sort.name)
            .collect();
        let type_sorts: BTreeSet<&Name> = table
            .sorts
            .iter()
            .filter(|sort| sort.representability == Representability::Representable)
            .flat_map(|sort| sort.indices.iter().map(|index| &index.sort))
            .collect();
        let mut opers: BTreeMap<String, Vec<Candidate<'_>>> = BTreeMap::new();
        for op in &table.opers {
            let mlir = naming
                .operation(&op.name)
                .map_or_else(|| dialect.qualified(&op.name), |form| form.mlir.into());
            let operands = op
                .arity
                .inputs
                .iter()
                .filter(|port| representable.contains(&port.sort))
                .count();
            opers
                .entry(mlir)
                .or_default()
                .push(Candidate { op, operands });
        }
        for candidates in opers.values_mut() {
            candidates.sort_by_key(|candidate| core::cmp::Reverse(candidate.op.arity.inputs.len()));
        }
        let constant_of = |op: &'table OperDesc| match (&*op.arity.inputs, &*op.arity.outputs) {
            (&[], &[ref output]) => Some((op, &output.sort)),
            _ => None,
        };
        let constants = table
            .opers
            .iter()
            .filter_map(constant_of)
            .filter(|&(_, sort)| type_sorts.contains(sort))
            .map(|(op, _)| (dialect.spell(&op.name), &op.name))
            .collect();
        let values = table
            .opers
            .iter()
            .filter_map(constant_of)
            .filter_map(|(op, sort)| Some(((sort, naming.constant(&op.name)?.value), &op.name)))
            .collect();
        Self {
            naming,
            opers,
            sorts: table.sorts.iter().map(|sort| &sort.name).collect(),
            representable,
            type_sorts,
            constants,
            values,
        }
    }

    /// Check that the type `ty` at the port `port`, whose sort takes
    /// `arguments`, is the type that its index names, and note the constant of
    /// a type port of `op` that the index names.
    ///
    /// # Specification
    /// - ensures: a constant index names the constant of `ty`, and a port index
    ///   holds it after the call.
    /// - fails: [`TermReadError::Untyped`] for a type that is the print of no
    ///   constant, another count of indices, and an index that is no constant
    ///   and no type port; [`TermReadError::Mistyped`] for an index that names
    ///   another constant.
    /// - panics: none.
    /// - executable: none — the answer is a refusal or nothing, which the tests
    ///   read.
    ///
    /// # Errors
    /// As listed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type that is the print of no constant, two types at
    ///   one type port, and a result whose index is another constant are
    ///   refused.
    /// - witness: `term::tests::each_refusal_has_facts_that_meet_it`
    fn agree(
        &self,
        op: &'table OperDesc,
        types: &mut TypePorts<'table>,
        port: &Name,
        arguments: &[FreeTerm],
        ty: Fact<'_>,
    ) -> Result<(), TermReadError>
    {
        let untyped = || TermReadError::Untyped(port.clone());
        let constant = self.constants.get(ty.0).copied().ok_or_else(untyped)?;
        let [ref index] = *arguments
        else {
            return Err(untyped());
        };
        match index.view() {
            TermView::Var(variable) => {
                let type_port = op
                    .arity
                    .inputs
                    .iter()
                    .find(|input| input.name == *variable && self.type_sorts.contains(&input.sort))
                    .ok_or_else(untyped)?;
                types.hold(&type_port.name, constant, port)
            },
            TermView::Op { name, args } if args.len() == 0 => {
                if name == constant {
                    Ok(())
                }
                else {
                    Err(TermReadError::Mistyped(port.clone()))
                }
            },
            TermView::Op { .. }
            | TermView::Ctor { .. }
            | TermView::Results { .. }
            | TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => Err(untyped()),
        }
    }

    /// The value of the attribute port `port` of the sort `sort`, whose
    /// attribute in the facts is `fact`. `form` is the form of the operation
    /// `op`, and `types` the constant of each type port.
    ///
    /// # Specification
    /// - ensures: as the print writes the attribute: a constant of the sort of
    ///   the port from its value in the [`Naming`]; an integer from itself with
    ///   `i64` or the type of the type port that the form names, which that
    ///   port holds after the call; a text from itself in quotes, or from `@`
    ///   and itself for a symbol.
    /// - fails: [`TermReadError::Unattributed`] for no attribute and for a
    ///   value that is none of these; [`TermReadError::Untyped`] and
    ///   [`TermReadError::Mistyped`] for the type of an integer that its type
    ///   port does not admit.
    /// - panics: none.
    /// - executable: none — the value is a term, which the tests read back.
    ///
    /// # Errors
    /// As listed.
    ///
    /// # Cost
    /// - allocation: the name of the value, durable by the term
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each attribute port of the block of `std.llvm` reads
    ///   back from its print, and each refusal has facts that meet it.
    /// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
    /// - witness: `term::tests::each_refusal_has_facts_that_meet_it`
    fn attribute(
        &self,
        op: &'table OperDesc,
        form: Option<&OperationForm>,
        port: &'table SortRef,
        sort: AttributeSort,
        fact: Option<Fact<'_>>,
        types: &mut TypePorts<'table>,
    ) -> Result<Name, TermReadError>
    {
        let unattributed = || TermReadError::Unattributed(port.name.clone());
        let fact = fact.ok_or_else(unattributed)?;
        let kind = form
            .and_then(|form| form.attribute(&port.name))
            .map_or(AttributeKind::Plain, |form| form.kind);
        match sort {
            AttributeSort::Constants => self
                .values
                .get(&(&port.sort, fact.0))
                .map(|&constant| constant.clone())
                .ok_or_else(unattributed),
            AttributeSort::Integer => {
                let (literal, ty) = fact.integer().ok_or_else(unattributed)?;
                match kind {
                    AttributeKind::TypedBy(PortName(typed)) => {
                        let untyped = || TermReadError::Untyped(port.name.clone());
                        let constant = self.constants.get(ty.0).copied().ok_or_else(untyped)?;
                        let type_port = op
                            .arity
                            .inputs
                            .iter()
                            .find(|input| input.name.as_ref() == typed)
                            .ok_or_else(untyped)?;
                        types.hold(&type_port.name, constant, &port.name)?;
                    },
                    AttributeKind::Plain | AttributeKind::Symbol | AttributeKind::Type => {
                        if ty.0 != "i64" {
                            return Err(unattributed());
                        }
                    },
                }
                Ok(literal)
            },
            AttributeSort::Text => match kind {
                AttributeKind::Symbol => fact.symbol(),
                AttributeKind::Plain | AttributeKind::TypedBy(_) | AttributeKind::Type => {
                    fact.quoted()
                },
            }
            .ok_or_else(unattributed),
        }
    }

    /// Read the facts `operation` as one node of the operation `op`, after the
    /// values `scope`.
    ///
    /// # Specification
    /// - ensures: one port read for each input port of `op`, in order, and the
    ///   type of the result that the rest binds, if it binds one.
    /// - fails: as the variants of [`TermReadError`] state, for the first port
    ///   that the facts do not meet.
    /// - panics: none.
    /// - executable: none — the node is part of a term, which the tests read
    ///   back.
    ///
    /// # Errors
    /// As listed.
    ///
    /// # Cost
    /// - allocation: the ports and the types of the node, durable by the node
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation of the block of `std.llvm` reads back
    ///   from its print, and each refusal has facts that meet it.
    /// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
    /// - witness: `term::tests::each_refusal_has_facts_that_meet_it`
    fn node<'facts>(
        &self,
        op: &'table OperDesc,
        operation: &'facts Operation,
        scope: &Scope<'facts>,
    ) -> Result<(Node<'table>, Option<Fact<'facts>>), TermReadError>
    {
        let name = || op.name.clone();
        let [ref output] = *op.arity.outputs
        else {
            return Err(TermReadError::Arity(name()));
        };
        let form = self.naming.operation(&op.name);
        let fact = |mlir: &str| {
            operation
                .attributes
                .iter()
                .find(|&&(ref attribute, _)| attribute == mlir)
                .map(|&(_, ref value)| Fact(value.as_str()))
        };
        let mut types = TypePorts(BTreeMap::new());
        let mut operands = operation.operands.iter();
        let mut ports = Vec::with_capacity(op.arity.inputs.len());
        let mut rest = None;
        for port in &op.arity.inputs {
            if port.sort == output.sort && rest.is_none() {
                rest = Some(port);
                ports.push(Port::Rest);
                continue;
            }
            if !port.bindings.is_empty() || !port.abstractions.is_empty() {
                return Err(TermReadError::Unread(port.name.clone()));
            }
            if self.representable.contains(&port.sort) {
                let operand = operands
                    .next()
                    .ok_or_else(|| TermReadError::Arity(name()))?;
                let place = match *operand {
                    Operand::Hole(hole) => (hole < scope.holes).then_some(hole),
                    Operand::Result {
                        operation: before,
                        index: 0,
                    } => scope.places.get(before).copied().flatten(),
                    Operand::Result { .. } => None,
                }
                .ok_or_else(|| TermReadError::UnboundOperand(name()))?;
                let ty = scope
                    .types
                    .get(place)
                    .copied()
                    .ok_or_else(|| TermReadError::UnboundOperand(name()))?;
                self.agree(op, &mut types, &port.name, &port.arguments, ty)?;
                ports.push(Port::Value(place));
            }
            else if self.type_sorts.contains(&port.sort) {
                if let Some(&AttributeForm {
                    mlir,
                    kind: AttributeKind::Type,
                    ..
                }) = form.and_then(|form| form.attribute(&port.name))
                {
                    let ty =
                        fact(mlir).ok_or_else(|| TermReadError::Unattributed(port.name.clone()))?;
                    let constant = self
                        .constants
                        .get(ty.0)
                        .copied()
                        .ok_or_else(|| TermReadError::Untyped(port.name.clone()))?;
                    types.hold(&port.name, constant, &port.name)?;
                }
                ports.push(Port::Type(&port.name));
            }
            else if let Some(sort) =
                AttributeSort::of(&port.sort, self.sorts.contains(&port.sort))
            {
                ports.push(Port::Pending(port, sort));
            }
            else {
                return Err(TermReadError::Unread(port.name.clone()));
            }
        }
        if operands.next().is_some() {
            return Err(TermReadError::Arity(name()));
        }
        let rest = rest.ok_or_else(|| TermReadError::Terminator(name()))?;
        let result = match (&*rest.bindings, operation.results.as_slice()) {
            (&[], &[]) => None,
            (&[ref binding], &[ref ty]) => {
                let ty = Fact(ty.as_str());
                self.agree(op, &mut types, &binding.name, &binding.arguments, ty)?;
                Some(ty)
            },
            _ => return Err(TermReadError::Arity(name())),
        };
        // The attributes go after the types, as the print writes them, because
        // an integer can take the type of a type port.
        for port in &mut ports {
            if let Port::Pending(attribute, sort) = *port {
                let mlir = form
                    .and_then(|form| form.attribute(&attribute.name))
                    .map_or_else(|| attribute.name.as_ref(), |form| form.mlir);
                *port = Port::Attribute(self.attribute(
                    op,
                    form,
                    attribute,
                    sort,
                    fact(mlir),
                    &mut types,
                )?);
            }
        }
        for port in &ports {
            if let Port::Type(port) = *port
                && !types.0.contains_key(port.as_ref())
            {
                return Err(TermReadError::Untyped(port.clone()));
            }
        }
        Ok((
            Node {
                op,
                ports,
                types,
                depth: scope.types.len(),
            },
            result,
        ))
    }

    /// The operation of `candidates`, which share one MLIR name, that the
    /// facts `operation` read as.
    ///
    /// # Specification
    /// - requires: `candidates` has the most input ports first.
    /// - ensures: the first candidate whose count of operand ports is the count
    ///   of operands, whose attributes are each in the facts, and whose
    ///   constants each are a value of the sort of their port; else the last
    ///   candidate with the count of operands, whose read names the cause; else
    ///   nothing.
    /// - panics: none.
    /// - executable: none — the answer is a borrow of `candidates`, which the
    ///   tests read back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the load of MLIR with an ordering reads as
    ///   `load_atomic` and with none as `load`, and its inline assembly reads
    ///   by its count of operands.
    /// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
    fn select<'candidates>(
        &self,
        candidates: &'candidates [Candidate<'table>],
        operation: &Operation,
    ) -> Option<&'candidates Candidate<'table>>
    {
        let fact = |mlir: &str| {
            operation
                .attributes
                .iter()
                .find(|&&(ref attribute, _)| attribute == mlir)
                .map(|&(_, ref value)| value.as_str())
        };
        let fits = |candidate: &Candidate<'table>| {
            let form = self.naming.operation(&candidate.op.name);
            let [ref output] = *candidate.op.arity.outputs
            else {
                return false;
            };
            candidate.op.arity.inputs.iter().all(|port| {
                if port.sort == output.sort || self.representable.contains(&port.sort) {
                    return true;
                }
                let attribute = form.and_then(|form| form.attribute(&port.name));
                let mlir = attribute.map_or_else(|| port.name.as_ref(), |form| form.mlir);
                if self.type_sorts.contains(&port.sort) {
                    let from_attribute = matches!(
                        attribute,
                        Some(&AttributeForm {
                            kind: AttributeKind::Type,
                            ..
                        })
                    );
                    return !from_attribute || fact(mlir).is_some();
                }
                match AttributeSort::of(&port.sort, self.sorts.contains(&port.sort)) {
                    Some(AttributeSort::Constants) => fact(mlir)
                        .is_some_and(|value| self.values.contains_key(&(&port.sort, value))),
                    Some(AttributeSort::Integer | AttributeSort::Text) => fact(mlir).is_some(),
                    None => true,
                }
            })
        };
        let mut last = None;
        for candidate in candidates
            .iter()
            .filter(|candidate| candidate.operands == operation.operands.len())
        {
            if fits(candidate) {
                return Some(candidate);
            }
            last = Some(candidate);
        }
        last
    }
}

/// Read the facts `operations` of a body with the holes `holes` into a term of
/// the signature `table`, with the MLIR names of `naming`.
///
/// Each hole is a value of the context, the first hole the oldest. A variable
/// counts from the newest value, as [`print_term`](crate::print_term) counts
/// it. So the read of the print of a term with the holes as its parameters and
/// the same naming is that term.
///
/// # Specification
/// - requires: nothing. The facts need not come from the shim.
/// - ensures: on success one operation node for each operation of the body, in
///   order, each the rest of the one before it, and last the operation
///   `unreachable` of the table. A result is the variable 0 under the binder of
///   the rest.
/// - fails: as the variants of [`TermReadError`] state.
/// - panics: none.
///
/// # Errors
/// The first [`TermReadError`] of the body, in order. For an MLIR name of more
/// operations, the refusal of the operation that the read selects, or
/// [`TermReadError::Arity`] of the first when no operation has the count of
/// operands. The terminator is read last.
///
/// # Cost
/// - allocation: the tables of the signature, setup
/// - allocation: the scope, the ports of each operation and the term, growth
///   within the body
///
/// # Adequacy
/// - hypothesis: L3 — the print of a term of each operation of the block of
///   `std` goes through the read entry of the shim, and its facts read as that
///   term, with no naming and with the naming of `std.llvm`; a result is the
///   operand of the next operation; an operation outside the block is refused
///   by its name; each refusal has facts that meet it.
/// - witness: `term::tests::the_read_of_the_print_of_a_term_is_that_term`
/// - witness: `agreement::tests::each_operation_reads_back_from_its_print`
/// - witness: `term::tests::a_result_reads_as_the_operand_of_the_next_operation`
/// - witness: `term::tests::an_operation_outside_the_block_is_refused_by_its_name`
/// - witness: `term::tests::each_refusal_has_facts_that_meet_it`
#[inline]
#[spec(ensures: |ret| ret.as_ref().map_or(true, |term| matches!(term.view(), BindingView::Operation { .. })))]
pub fn read_term<G>(
    table: &TheoryDesc<G>,
    naming: &Naming,
    operations: &[Operation],
    holes: &[Hole<'_>],
) -> Result<BindingTerm, TermReadError>
{
    let reader = Reader::new(table, naming);
    let mut scope = Scope {
        types: holes.iter().map(|hole| Fact(hole.ty)).collect(),
        places: Vec::with_capacity(operations.len()),
        holes: holes.len(),
    };
    let mut nodes: Vec<Node<'_>> = Vec::with_capacity(operations.len());
    for operation in operations {
        let candidates = reader
            .opers
            .get(operation.name.as_str())
            .ok_or_else(|| TermReadError::UnknownOperation(Name::from(operation.name.as_str())))?;
        let candidate = reader.select(candidates, operation).ok_or_else(|| {
            candidates.first().map_or_else(
                || TermReadError::UnknownOperation(Name::from(operation.name.as_str())),
                |first| TermReadError::Arity(first.op.name.clone()),
            )
        })?;
        let (node, result) = reader.node(candidate.op, operation, &scope)?;
        scope.places.push(result.map(|_| scope.types.len()));
        scope.types.extend(result);
        nodes.push(node);
    }
    let terminator = Name::from("unreachable");
    let end = table
        .opers
        .iter()
        .find(|op| op.name == terminator && op.arity.inputs.is_empty())
        .ok_or_else(|| {
            TermReadError::UnknownOperation(Name::from(Dialect::of(table).qualified(&terminator)))
        })?;
    let mut term = BindingTerm::operation(end.name.clone(), []);
    for node in nodes.into_iter().rev() {
        let mut arguments = Vec::with_capacity(node.ports.len());
        let mut rest = Some(term);
        for port in node.ports {
            arguments.push(match port {
                Port::Rest => rest
                    .take()
                    .ok_or_else(|| TermReadError::Arity(node.op.name.clone()))?,
                Port::Value(place) => BindingTerm::variable(VariableIndex::from(
                    node.depth.saturating_sub(place.saturating_add(1)),
                )),
                Port::Type(port) => {
                    let constant = node
                        .types
                        .0
                        .get(port.as_ref())
                        .ok_or_else(|| TermReadError::Untyped(port.clone()))?;
                    BindingTerm::operation(Name::from(*constant), [])
                },
                Port::Attribute(value) => BindingTerm::operation(value, []),
                Port::Pending(attribute, _) => {
                    return Err(TermReadError::Unattributed(attribute.name.clone()));
                },
            });
        }
        term = BindingTerm::operation(node.op.name.clone(), arguments);
    }
    Ok(term)
}
