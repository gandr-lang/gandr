//! Extern blocks' boundary checks, as the lowering mints them.
//!
//! A block carrying `@[ boundary(r₁, …, rₙ) ]` takes one slot
//! ([`BoundarySlot`]), whose body calls `std.boundary`'s `admitBlock` on the
//! block's members and the rows:
//!
//! ```text
//! check : U(F Admission)
//! check = thunk((force admitBlock) (Member(Signature(Coded("x", Plain(U32), …), Plain(U32)), …)) (Named(r₁, … NoRow)))
//! ```
//!
//! A member's signature is each parameter's name and its type's code, then
//! the result's code. A fixed-width atom is coded as the scalar of its width,
//! `Plain(U32)` for `u32`. The rows are the payload's names, in written order.
//! Every name the call reads (`admitBlock`, `Admission`, the constructors and
//! the scalars) resolves in its home ([`Home`]): the first source declaring
//! `admitBlock`, the block's own source first, then the sources its imports
//! reach, breadth first in written order. A name reads as the home's top
//! level reads it, so a source importing `std.boundary` lists only the names
//! it writes, and the scalars reach the call through `std.boundary`'s own
//! import of `std.layout` (#4698). The checker types the call and settlement
//! runs it: the program's own answer decides the block.
//!
//! # References
//!
//! - `vault:01a178aa-6cd7-7ac2-a049-ee4124ad5576` — background: a boundary's
//!   admission is the layout program's verdict on the declared types against
//!   the row, read where the boundary is declared.

use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::IntegerWidth;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Reading;
use super::Resolved;
use super::Sink;
use super::Site;
use super::native::Native;
use super::native::NativeRef;
use crate::attribute::names;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::form::Placed;
use crate::import::ImportResolution;
use crate::module::Bare;
use crate::module::BoundarySlot;
use crate::module::Container;
use crate::module::ForeignType;
use crate::module::Payload;
use crate::module::SlotIndex;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::SurfaceName;
use crate::unit::ImportTarget;
use crate::unit::SourceIndex;

/// The function the check calls.
const ADMIT_BLOCK: &str = "admitBlock";

/// The type the check answers.
const ADMISSION: &str = "Admission";

/// Where a boundary check's names resolve.
///
/// # Specification
/// - requires: nothing; the type is a carrier.
/// - ensures: [`Self::Own`] reads each name at the payload; [`Self::Reached`]
///   reads it at the top level of `source`, then through `source`'s imports.
/// - provides: the scope [`Lowerer::boundary_home`] finds for one check.
/// - fails: never.
/// - panics: none.
/// - executable: none — a carrier with no invariant beyond its variants.
///
/// # Adequacy
/// - hypothesis: L3 — a block whose source declares `admitBlock`, and one whose
///   source lists only the names it writes from an import declaring it.
/// - witness: `lower::boundary::tests::a_boundary_block_takes_the_slot_its_check_runs_in_2901`
/// - witness: `lower::boundary::tests::a_check_reads_its_names_where_the_imports_reach_them_4698`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Home
{
    /// The block's own source declares `admitBlock`, or no source its
    /// imports reach does: each name resolves at the payload.
    Own,
    /// A source the block's source reaches declares `admitBlock`.
    Reached
    {
        /// The source declaring `admitBlock`.
        source: SourceIndex,
        /// The import of the block's source the walk to `source` starts at.
        import: ByteSpan,
    },
}

impl<'source> Lowerer<'_, 'source>
{
    /// Mint each boundary check the current source's extern blocks take.
    ///
    /// # Specification
    /// - requires: the collection filed the checks; the mint sweep has run, so
    ///   each payload's value is minted.
    /// - ensures: each check slot of the current source holding no refusal,
    ///   whose payload lowered to declared names, is minted to its type and
    ///   call, or refused at the payload by the first name the call reads that
    ///   does not resolve there. A payload that did not lower, or lowered to no
    ///   names, is left to the refusal its attribute earns.
    /// - panics: none.
    /// - executable: none — the call's type is the checker's to judge, and its
    ///   answer the run's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block of one member against one row mints the call
    ///   the checker accepts; a source that does not import `std.boundary` is
    ///   refused at the payload.
    /// - witness: `lower::boundary::tests::a_boundary_block_takes_the_slot_its_check_runs_in_2901`
    /// - witness: `lower::boundary::tests::a_check_naming_no_admission_is_refused_at_its_payload_2901`
    pub(super) fn mint_boundaries(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let checks: Vec<(SlotIndex, BoundarySlot)> = self
            .cx
            .collected
            .boundaries
            .range(SlotIndex::from(self.cx.current.slots) ..)
            .map(|(&slot, check)| (slot, check.clone()))
            .collect();
        for (slot, check) in checks {
            let Some(entry) = self.cx.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let Payload::Written(rows) = check.rows
            else {
                continue;
            };
            let origin =
                Origin::new(entry.named.node, entry.named.span).inserted(Insertion::Derived);
            match self.boundary_check(&check, rows, sink, origin) {
                Ok(Maybe::Present(minted)) => {
                    let _first = self.cx.derivations.insert(slot, minted);
                },
                Ok(Maybe::Absent(_)) => {},
                Err(refusal) => {
                    let _first = self.cx.faults.insert(slot, refusal);
                },
            }
        }
    }

    /// The type and call of the check `check`, whose payload is `rows`.
    ///
    /// # Specification
    /// - requires: `rows` is the written payload of `check`'s attribute.
    /// - ensures: `U(F Admission)` and `thunk((force admitBlock) ss rs)`, `ss`
    ///   the members' signatures and `rs` the payload's names, every node
    ///   carrying `origin`; absent when the payload lowered to no names.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at the payload for the
    ///   first name the call reads that does not resolve there.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_boundaries`].
    /// - witness: `lower::boundary::tests::a_boundary_block_takes_the_slot_its_check_runs_in_2901`
    /// - witness: `lower::boundary::tests::a_check_naming_no_admission_is_refused_at_its_payload_2901`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |minted| match *minted {
        | Maybe::Present((ty, call)) => sink.arena.value_type(ty).is_some() && sink.arena.value(call).is_some(),
        | Maybe::Absent(_) => true,
    }))]
    fn boundary_check(
        &mut self,
        check: &BoundarySlot,
        rows: Placed,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<Maybe<(ValueTypeId, ValueId), super::lowered::Absent>, LoweringRefusal<'source>>
    {
        let Maybe::Present(payload) = self.cx.value_at(rows.node)
        else {
            return Ok(Maybe::Absent(super::lowered::Absent::Unminted));
        };
        if let Maybe::Absent(_) = names(sink.arena, payload) {
            return Ok(Maybe::Absent(super::lowered::Absent::Unminted));
        }
        let named = match sink.arena.value(payload) {
            Some(&Value::Tuple(ref items)) => items.to_vec(),
            Some(_) | None => vec![payload],
        };
        let site = Site {
            at: rows,
            name: FormName::ATTRIBUTE,
            reading: Reading::Value(Frame::Outermost),
        };
        let home = self.boundary_home(site);
        let admit = self.declared(site, home, SurfaceName::from(ADMIT_BLOCK))?;
        let admission = self.declared(site, home, SurfaceName::from(ADMISSION))?;
        let mut members = self.constructed(
            site,
            home,
            SurfaceName::from("NoSignature"),
            Vec::new(),
            sink,
            origin,
        )?;
        for operation in check.interface.operations.iter().rev() {
            let result = self.atom_code(site, home, operation.result, sink, origin)?;
            let mut parameters = self.constructed(
                site,
                home,
                SurfaceName::from("NoCoded"),
                Vec::new(),
                sink,
                origin,
            )?;
            for parameter in operation.parameters.iter().rev() {
                let spelled = String::from(self.cx.name_at(parameter.named).as_ref());
                let name = sink
                    .arena
                    .value_literal(Literal::Text(StringLiteral::new(spelled)));
                sink.origins.record_value(name, origin);
                let code = self.atom_code(site, home, parameter.ty, sink, origin)?;
                parameters = self.constructed(
                    site,
                    home,
                    SurfaceName::from("Coded"),
                    vec![name, code, parameters],
                    sink,
                    origin,
                )?;
            }
            let signature = self.constructed(
                site,
                home,
                SurfaceName::from("Signature"),
                vec![parameters, result],
                sink,
                origin,
            )?;
            members = self.constructed(
                site,
                home,
                SurfaceName::from("Member"),
                vec![signature, members],
                sink,
                origin,
            )?;
        }
        let mut listed = self.constructed(
            site,
            home,
            SurfaceName::from("NoRow"),
            Vec::new(),
            sink,
            origin,
        )?;
        for &row in named.iter().rev() {
            listed = self.constructed(
                site,
                home,
                SurfaceName::from("Named"),
                vec![row, listed],
                sink,
                origin,
            )?;
        }
        let head = sink.arena.value_constant(admit);
        sink.origins.record_value(head, origin);
        let mut call = sink.arena.computation_force(head);
        sink.origins.record_computation(call, origin);
        for argument in [members, listed] {
            call = sink.arena.computation_application(call, argument);
            sink.origins.record_computation(call, origin);
        }
        let body = sink.arena.value_thunk(call);
        sink.origins.record_value(body, origin);
        let answered = sink.arena.value_type_data(admission, Vec::new());
        sink.origins.record_value_type(answered, origin);
        let returner = sink.arena.comp_type_returner(answered);
        sink.origins.record_comp_type(returner, origin);
        let declared = sink.arena.value_type_thunk(returner);
        sink.origins.record_value_type(declared, origin);

        Ok(Maybe::Present((declared, body)))
    }

    /// The home of the check whose payload stands at `site`: the first source
    /// declaring `admitBlock` at its top level, the payload's own source
    /// first, then each source its imports reach, breadth first in the order
    /// each source writes its imports.
    ///
    /// # Specification
    /// - requires: `site` is a payload's site.
    /// - ensures: [`Home::Own`] when the payload's source declares `admitBlock`
    ///   or no source its imports reach does; otherwise [`Home::Reached`] at
    ///   the nearest such source, with the import of the payload's source the
    ///   walk to it starts at. An import resolved to no source leads nowhere,
    ///   and an import's listing does not narrow it.
    /// - provides: the scope [`Self::declared`] and [`Self::constructed`] read.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is the walk itself.
    ///
    /// # Termination
    /// Each source enters the queue at most once, kept by the visited set, and
    /// a unit holds finitely many sources.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block whose source declares `admitBlock`, one whose
    ///   source imports it through a listing that leaves it out, and one that
    ///   reaches it through a source in between.
    /// - witness: `lower::boundary::tests::a_boundary_block_takes_the_slot_its_check_runs_in_2901`
    /// - witness: `lower::boundary::tests::a_check_reads_its_names_where_the_imports_reach_them_4698`
    fn boundary_home(
        &self,
        site: Site,
    ) -> Home
    {
        let admit = SurfaceName::from(ADMIT_BLOCK);
        let declares = |source: SourceIndex| {
            self.cx
                .collected
                .by_name
                .contains_key(&(Container::TopLevel(source), admit))
        };
        let own = self.cx.collected.unit.source_at(site.at.span.start());
        if declares(own) {
            return Home::Own;
        }
        let reached =
            |source: SourceIndex| {
                self.cx.collected.imports.of(source).filter_map(|import| {
                    match import.resolution() {
                        ImportResolution::Path(ImportTarget::Source(target)) => {
                            Some((target, import.span()))
                        },
                        ImportResolution::Path(
                            ImportTarget::Unresolved | ImportTarget::Cycle | ImportTarget::Unlocked,
                        )
                        | ImportResolution::Foreign => None,
                    }
                })
            };
        let mut seen = BTreeSet::from([own]);
        let mut pending: VecDeque<(SourceIndex, ByteSpan)> = reached(own).collect();
        while let Some((source, import)) = pending.pop_front() {
            if !seen.insert(source) {
                continue;
            }
            if declares(source) {
                return Home::Reached { source, import };
            }
            pending.extend(reached(source).map(|(next, _)| (next, import)));
        }
        Home::Own
    }

    /// The declaration `name` names in the check's home `home`.
    ///
    /// # Specification
    /// - requires: `site` is a payload's site, and `home` its check's home.
    /// - ensures: at [`Home::Own`], the constant of the declaration `name`
    ///   resolves to at `site`; at [`Home::Reached`], the constant of the
    ///   home's top-level declaration `name`, or else of the one its imports
    ///   answer, the import the walk starts at marked reached.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at `site` when it resolves
    ///   to none, or to a binder; the resolution's own refusal.
    /// - panics: none.
    /// - executable: none — the answer is the resolution itself.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_boundaries`], and a check whose home
    ///   is an import its source lists without `admitBlock`.
    /// - witness: `lower::boundary::tests::a_check_naming_no_admission_is_refused_at_its_payload_2901`
    /// - witness: `lower::boundary::tests::a_check_reads_its_names_where_the_imports_reach_them_4698`
    fn declared(
        &mut self,
        site: Site,
        home: Home,
        name: SurfaceName<'static>,
    ) -> Result<gandr_kernel_term::ConstantIndex, LoweringRefusal<'source>>
    {
        let unresolved = LoweringRefusal::UnresolvedName {
            span: site.at.span,
            name,
        };
        let Home::Reached { source, import } = home
        else {
            return match self.resolve_name(site, Frame::Outermost, name)? {
                Maybe::Present(Resolved::Declaration { constant, .. }) => Ok(constant),
                Maybe::Present(_) | Maybe::Absent(_) => Err(unresolved),
            };
        };
        let slot = match self
            .cx
            .collected
            .by_name
            .get(&(Container::TopLevel(source), name))
        {
            Some(&slot) => slot,
            None => match self.cx.collected.imported_slot(source, name) {
                Ok(Maybe::Present((slot, _))) => slot,
                Ok(Maybe::Absent(_)) | Err(_) => return Err(unresolved),
            },
        };
        let Some(constant) = self
            .cx
            .collected
            .slots
            .get(usize::from(slot))
            .map(|entry| entry.constant)
        else {
            return Err(unresolved);
        };
        self.cx.collected.reach(import);
        Ok(constant)
    }

    /// The constructor `name` names in the check's home `home`, applied to
    /// `fields`.
    ///
    /// # Specification
    /// - requires: `site` is a payload's site, and `home` its check's home.
    /// - ensures: the constructor value of the parameterless family `name`'s
    ///   constructor belongs to, over `fields`, carrying `origin`: at
    ///   [`Home::Own`] the constructor `name` names at `site`; at
    ///   [`Home::Reached`] the one the home declares, or else the one its
    ///   imports answer, the import the walk starts at marked reached.
    /// - fails: [`LoweringRefusal::UnresolvedName`] at `site` when `name` names
    ///   no constructor there; [`LoweringRefusal::AmbiguousConstructor`] when
    ///   more than one family there declares it, and
    ///   [`LoweringRefusal::ImportShadows`] when two imports bind it.
    /// - panics: none.
    /// - executable: none — the value is nodes of the arena, which the checker
    ///   reads at the family's type.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_boundaries`], and a scalar the home
    ///   reads through its own import.
    /// - witness: `lower::boundary::tests::a_boundary_block_takes_the_slot_its_check_runs_in_2901`
    /// - witness: `lower::boundary::tests::a_check_reads_its_names_where_the_imports_reach_them_4698`
    fn constructed(
        &mut self,
        site: Site,
        home: Home,
        name: SurfaceName<'static>,
        fields: Vec<ValueId>,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<ValueId, LoweringRefusal<'source>>
    {
        let unresolved = LoweringRefusal::UnresolvedName {
            span: site.at.span,
            name,
        };
        let found = match home {
            Home::Own => match Native::new(self).named_constructor(site, name)? {
                Maybe::Present(found) => found,
                Maybe::Absent(_) => return Err(unresolved),
            },
            Home::Reached { source, import } => {
                let bare = match self.cx.collected.bare_constructor(source, name, |_| true) {
                    Some(bare) => bare,
                    None => match self.cx.collected.imported_constructor(source, name) {
                        Ok(Maybe::Present((bare, _))) => bare,
                        Ok(Maybe::Absent(_)) => return Err(unresolved),
                        Err(ambiguity) => {
                            return Err(LoweringRefusal::ImportShadows {
                                span: site.at.span,
                                name,
                                import: ambiguity.import,
                                other: ambiguity.other,
                            });
                        },
                    },
                };
                let found = match bare {
                    Bare::One(found) => found,
                    Bare::Several {
                        first,
                        second,
                        more,
                    } => {
                        return Err(NativeRef::over(&self.cx).ambiguous_constructor(
                            site.at.span,
                            name,
                            first,
                            second,
                            more,
                        ));
                    },
                };
                self.cx.collected.reach(import);
                found
            },
        };
        let Some(family) = self
            .cx
            .collected
            .slots
            .get(usize::from(found.family))
            .map(|entry| entry.constant)
        else {
            return Err(unresolved);
        };
        let value = sink.arena.value_constructor_of(
            family,
            Vec::new(),
            ConstructorTag::from(found.tag),
            fields,
        );
        sink.origins.record_value(value, origin);
        Ok(value)
    }

    /// The code of the fixed-width atom `ty`: `Plain` of its width's scalar.
    ///
    /// # Specification
    /// - requires: `site` is a payload's site, and `home` its check's home.
    /// - ensures: `Plain(S)`, `S` the scalar `ty`'s width names: `U32`, `U64`,
    ///   `I32` or `I64`.
    /// - fails: as [`Self::constructed`].
    /// - panics: none.
    /// - executable: none — the value is nodes of the arena, which the checker
    ///   reads at `Code`.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_boundaries`].
    /// - witness: `lower::boundary::tests::a_boundary_block_takes_the_slot_its_check_runs_in_2901`
    fn atom_code(
        &mut self,
        site: Site,
        home: Home,
        ty: ForeignType,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<ValueId, LoweringRefusal<'source>>
    {
        let scalar = match ty.width {
            IntegerWidth::U32 => "U32",
            IntegerWidth::U64 => "U64",
            IntegerWidth::I32 => "I32",
            IntegerWidth::I64 => "I64",
        };
        let scalar = self.constructed(
            site,
            home,
            SurfaceName::from(scalar),
            Vec::new(),
            sink,
            origin,
        )?;
        self.constructed(
            site,
            home,
            SurfaceName::from("Plain"),
            vec![scalar],
            sink,
            origin,
        )
    }
}

#[cfg(test)]
mod tests;
