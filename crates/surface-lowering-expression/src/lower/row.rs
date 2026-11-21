//! Declarations of the given rows of the builtin table, as the lowering reads
//! them.
//!
//! A signature with no definition owes its value. `std` declares each value
//! of the native table this way, and a `builtin` mark names its row by its
//! key:
//!
//! ```text
//! @[builtin("string.append")]
//! pub def append : String -> String -> String;
//! ```
//!
//! The row gives the value, so the signature owes nothing. A name of the
//! declaration lowers as the row's own name lowers, so a call of the
//! declaration is the call of the row, and the lowered program does not
//! change. The declared type is the row's type, or the mark is refused. A
//! found row, a role, has its body, and the checker reads it.
//!
//! - see: #7961
//!
//! # References
//!
//! - `vault:01a1f320-0881-7ed1-9a54-c0c713ccf7cf` — anchor: a given row of the
//!   builtin table is a declaration of `std` with its type and no body, under
//!   `@[builtin("key")]`. The checker compares the declared type with the row,
//!   and only a package of the toolchain writes the mark.
//! - `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — anchor: §
//!   boot-data-builtins, the two directions of a binding. The toolchain gives a
//!   native value, and the library gives the declaration of a role.

use alloc::collections::BTreeSet;
use alloc::collections::btree_map::Entry;
use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::builtin::Direction;
use gandr_core_term::builtin::Key;
use gandr_core_term::builtin::Row;
use gandr_core_term::equal_type_syntax;
use gandr_core_term::primitive::Primitive;
use gandr_kernel_term::Literal;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use super::Expressions;
use super::Families;
use super::Sink;
use crate::attribute::RegisteredAttribute;
use crate::description::unknown_port_sort;
use crate::error::BuiltinFault;
use crate::error::LoweringRefusal;
use crate::form::Former;
use crate::module::Half;
use crate::module::Operand;
use crate::module::Payload;
use crate::module::SlotIndex;
use crate::origin::Origin;
use crate::resolve::SurfaceName;
use crate::resolve::type_atom;

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Read the row that each `builtin` mark of the current source names.
    ///
    /// # Specification
    /// - requires: the collection declared the current source's slots, and
    ///   their written attributes stand on them.
    /// - ensures: each slot of the current source that holds no refusal and
    ///   carries a `builtin` mark whose payload is a text takes the row that
    ///   its key names: a native value in the context's natives, and a role in
    ///   the context's roles when no earlier slot holds the role. The mark is
    ///   refused by name instead, by the first of these faults: the source is
    ///   no module of `std`; the key names no row; a given row's declaration
    ///   has a body; a found row's declaration has none; an earlier slot holds
    ///   the role. A mark whose payload is no text is left to the attribute
    ///   pass, which refuses it.
    /// - panics: none.
    /// - executable: none — the rows and the refusals are tables of the
    ///   context, and a predicate would read every slot again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a marked signature takes its row, a marked holder
    ///   takes its role, and each fault takes its own refusal.
    /// - witness: `gandr-surface-lowering::lower::row::tests::a_given_row_lowers_to_its_value_8071`
    /// - witness: `gandr-surface-lowering::lower::row::tests::each_fault_of_a_builtin_mark_is_refused_by_name_8071`
    ///
    /// # Cost
    /// - allocation: the text of each mark's payload, setup
    /// - allocation: the marks read, growth within the source's slots
    /// - allocation: the row of each mark, durable by the source
    /// - allocation: the refusal of a faulty mark, error path
    #[inline]
    pub fn read_builtins(&mut self)
    {
        let cx = self.cx_mut();
        // The prelude and each module of `std` are sources of the toolchain.
        let homed = matches!(cx.collected.unit.home(cx.current.source), Maybe::Present(_))
            || cx.collected.unit.prelude() == Some(cx.current.source);
        let mut read = Vec::new();
        for (index, slot) in cx.collected.slots.iter().enumerate().skip(cx.current.slots) {
            if let Maybe::Present(_) = slot.refusal {
                continue;
            }
            let Some(mark) = slot
                .attributes
                .iter()
                .find(|written| written.name.as_ref() == RegisteredAttribute::BUILTIN.as_ref())
            else {
                continue;
            };
            let Payload::Written(text) = mark.payload
            else {
                continue;
            };
            let Maybe::Present(Literal::Text(key)) =
                crate::lower::parse_literal(Former::Text, cx.text_at(text))
            else {
                continue;
            };
            let bodied = matches!(slot.definition, Maybe::Present(_));
            let found = match (homed, Row::named(Key(key.as_ref()))) {
                (false, _) => Err(BuiltinFault::OutsideToolchain),
                (true, Maybe::Absent(_)) => Err(BuiltinFault::NoRow),
                (true, Maybe::Present(row)) => match (row.direction(), bodied) {
                    (Direction::Given, true) => Err(BuiltinFault::Bodied),
                    (Direction::Found, false) => Err(BuiltinFault::Unbodied),
                    (Direction::Given, false) | (Direction::Found, true) => Ok(row),
                },
            };
            read.push((SlotIndex::from(index), mark.at.node, mark.span, found));
        }
        for (slot, node, span, found) in read {
            let fault = match found {
                Ok(Row::Native(primitive)) => {
                    let _first = cx.natives.insert(slot, primitive);
                    continue;
                },
                // A use of the type member reads the atom of its row, as
                // `stated_type` plans it.
                Ok(Row::Atom(_)) => continue,
                Ok(Row::Role(role)) => match cx.roles.entry(role) {
                    Entry::Vacant(vacant) => {
                        let _first = vacant.insert(slot);
                        continue;
                    },
                    Entry::Occupied(_) => BuiltinFault::Repeated,
                },
                Err(fault) => fault,
            };
            if let Some(entry) = cx.collected.slots.get_mut(usize::from(slot)) {
                entry.refuse(node, LoweringRefusal::BuiltinMark { span, fault });
            }
        }
    }

    /// Mint the declared type and the row's value of each signature of the
    /// current source that a `builtin` mark binds to a given row.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so each signature's type is minted.
    /// - ensures: each slot of the current source in the context's natives,
    ///   holding no refusal, whose minted type is the row's type, and whose row
    ///   no earlier slot holds, takes that type and the row's thunk in the
    ///   context's natived. Otherwise the slot takes the refusal of its mark:
    ///   the type differs, or the row has its holder already.
    /// - panics: none.
    /// - executable: none — the minted types and values are the arena's, and a
    ///   predicate would compare every type again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::read_builtins`].
    /// - witness: `gandr-surface-lowering::lower::row::tests::a_given_row_lowers_to_its_value_8071`
    /// - witness: `gandr-surface-lowering::lower::row::tests::each_fault_of_a_builtin_mark_is_refused_by_name_8071`
    ///
    /// # Cost
    /// - allocation: the rows that earlier sources declare, setup
    /// - allocation: the minted declarations, growth within the source's slots
    /// - allocation: the row's type, its thunk and its value, durable by the
    ///   source
    /// - allocation: the refusal of a faulty mark, error path
    #[inline]
    pub fn mint_natives(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let cx = self.cx_mut();
        let mut taken: BTreeSet<Primitive> = cx
            .natived
            .keys()
            .filter_map(|slot| cx.natives.get(slot).copied())
            .collect();
        let mut minted = Vec::new();
        for (&slot, &primitive) in cx.natives.range(SlotIndex::from(cx.current.slots) ..) {
            let Some(entry) = cx.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let Maybe::Present(Half {
                operand: Operand::Written(written),
                ..
            }) = entry.signature
            else {
                continue;
            };
            let Maybe::Present(declared) = cx.value_type_at(written.node)
            else {
                continue;
            };
            let Some(mark) = entry
                .attributes
                .iter()
                .find(|written| written.name.as_ref() == RegisteredAttribute::BUILTIN.as_ref())
            else {
                continue;
            };
            let computation = primitive.declared_type(sink.arena);
            let row = sink.arena.value_type_thunk(computation);
            let fault =
                if equal_type_syntax(sink.arena, row, declared) != CertificateEquality::Equal {
                    BuiltinFault::TypeDiffers
                }
                else if taken.contains(&primitive) {
                    BuiltinFault::Repeated
                }
                else {
                    let _first = taken.insert(primitive);
                    let origin = Origin::new(entry.named.node, entry.named.span);
                    let body = primitive.thunk(sink.arena);
                    let _value = sink.value(body, origin);
                    minted.push((slot, Ok((declared, body))));
                    continue;
                };
            minted.push((
                slot,
                Err(LoweringRefusal::BuiltinMark {
                    span: mark.span,
                    fault,
                }),
            ));
        }
        for (slot, found) in minted {
            match found {
                Ok(completed) => {
                    let _first = cx.natived.insert(slot, completed);
                },
                Err(refusal) => {
                    let _first = cx.faults.insert(slot, refusal);
                },
            }
        }
    }

    /// Resolve each port sort that a theory of the current source keeps as
    /// written, in the scope of the source, now that the scope stands.
    ///
    /// # Specification
    /// - requires: the collection declared the current source's slots and read
    ///   its builtin marks.
    /// - ensures: each theory of the current source whose presentation keeps a
    ///   port sort, or that includes a theory, takes, in the collection's port
    ///   sorts under its written declaration, the type member that the scope
    ///   binds each kept name to, and each that its included theories took. A
    ///   kept name that no member binds and that the table of atoms answers
    ///   takes nothing, and the carrier reads the atom. Each other kept name is
    ///   refused as a port at a sort that no sort declares, at its bytes.
    /// - panics: none.
    /// - executable: none — the members and the refusals are tables of the
    ///   collection, and a predicate would resolve every name again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a port at a name that its source binds reads that
    ///   source's member, in a source that uses the theory too, and a port at a
    ///   name that no scope binds is refused at its bytes.
    /// - witness: `gandr-surface-dispatcher::compose::a_port_sort_reads_the_binding_of_its_theory_s_source_8139`
    /// - witness: `gandr-surface-lowering::lower::row::tests::a_port_sort_no_scope_binds_is_refused_at_its_bytes_8139`
    ///
    /// # Cost
    /// - allocation: the members of each theory's kept names, durable by the
    ///   collection
    /// - allocation: the refusal of an unbound name, error path
    /// - allocation: the theories reached through includes and the names held
    ///   so far, growth within the included theories
    #[inline]
    pub fn resolve_ports(&mut self)
    {
        let cx = self.cx_mut();
        let mut resolved = Vec::new();
        for index in cx.current.slots .. cx.collected.slots.len() {
            let Some((_, presentation)) = cx.collected.presentation_of(SlotIndex::from(index))
            else {
                continue;
            };
            let includes = cx
                .collected
                .included
                .get(&SlotIndex::from(index))
                .is_some_and(|reached| !reached.is_empty());
            if presentation.ported.is_empty() && !includes {
                continue;
            }
            let Some(slot) = cx.collected.slots.get(index)
            else {
                continue;
            };
            let theory = slot.introduced_by.node;
            let mut members = Vec::new();
            let mut refused = Vec::new();
            for ported in &presentation.ported {
                // The kept name at its bytes, read back as a name of the
                // source, so the scope's lookups read it.
                let named = cx
                    .tree
                    .descendants(theory)
                    .into_iter()
                    .flatten()
                    .filter(|&node| {
                        cx.tree
                            .node(node)
                            .is_some_and(|held| held.span() == ported.span)
                    })
                    .find_map(|node| cx.tree.fragment(node))
                    .map(SurfaceName::from);
                let member = named.and_then(|name| {
                    match cx.collected.scoped_type_member(
                        slot.container,
                        slot.introduced_by.span.start(),
                        name,
                    ) {
                        Ok(Maybe::Present(member)) => Some(member),
                        Ok(Maybe::Absent(_)) | Err(_) => None,
                    }
                });
                match member {
                    Some(member) => members.push((ported.sort.clone(), member)),
                    // economy: a name that the table of atoms still answers
                    // reads its atom at the carrier, until #8140 declares
                    // each atom as a type member.
                    None if matches!(
                        type_atom(SurfaceName::from(ported.sort.as_ref())),
                        Maybe::Present(_)
                    ) => {},
                    None => refused.push(unknown_port_sort(
                        &ported.operation,
                        &ported.sort,
                        ported.span,
                    )),
                }
            }
            resolved.push((SlotIndex::from(index), theory, members, refused));
        }
        let mut reached = Vec::new();
        let mut held = BTreeSet::new();
        for (position, theory, mut members, refused) in resolved {
            // An included theory's ports stand in the theory's members, and
            // its source resolved them first: an earlier source, or an
            // earlier theory of this one, which this pass has stored.
            reached.clear();
            reached.extend(
                cx.collected
                    .included
                    .get(&position)
                    .into_iter()
                    .flatten()
                    .filter_map(|&(included, _)| {
                        cx.collected
                            .slots
                            .get(usize::from(included))
                            .map(|slot| slot.introduced_by.node)
                    }),
            );
            held.clear();
            held.extend(members.iter().map(|&(ref name, _)| name.clone()));
            for node in &reached {
                for &(ref name, member) in cx.collected.port_sorts.get(node).into_iter().flatten() {
                    if held.insert(name.clone()) {
                        members.push((name.clone(), member));
                    }
                }
            }
            let _first = cx.collected.port_sorts.insert(theory, members);
            // The collection read the theory's refusals before its scope
            // stood, so a port at a name that nothing binds refuses the
            // theory here, as the description read refuses its other faults.
            let written = cx
                .tree
                .fragment(theory)
                .unwrap_or_else(|| SourceFragment::from(""));
            if let Some(diagnostic) = refused.first()
                && let Some(slot) = cx.collected.slots.get_mut(usize::from(position))
            {
                slot.refuse(theory, diagnostic.lowering_refusal(written));
            }
        }
    }
}
