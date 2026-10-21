//! Host operation signatures, without a host implementation.
//!
//! Payload records are represented by ordered products until record types are
//! available at this seam. `Exec.exec` takes `(program, (args, mode))` and
//! returns `(stdout, (stderr, exit_code))`; `Fs.write` takes `(path, contents)`
//! and `Fs.stat` returns `(kind, size)`. List fields use the native List
//! former.
//!
//! `Ring` is the completion ring's buffer pool: `alloc` takes a byte length
//! and replies a buffer, which its performer holds live, and `free` takes one
//! back. The native handler is where a host registers the area the buffers
//! live in; a source handler shadowing it mints each buffer its `alloc`
//! clause resumes with and reclaims each one its `free` clause receives, so a
//! closed program serves its own buffers.
//!
//! `Div` is divergence: an interface with no operation, which a computation's
//! row holds when the computation may run forever. A partial fixpoint other
//! than a ruled operation's introduces it; no handler eliminates it, and a row
//! is subsumed into one holding it as into one holding any other interface.
//! The empty row is the row of a computation that returns.
//!
//! No two interfaces share an operation name, so an operation names its
//! interface: [`HostSignatures::offering`] finds it, and
//! [`HostSignatures::authority`] builds the capability authority granting a
//! set of bare operation names, each under the interface that offers it.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::BaseType;
use quenchant_shape::shape::Maybe;

use super::EffectConflict;
use super::EffectName;
use super::EffectOp;
use super::EffectRow;
use super::EffectSig;
use super::OperationName;
use super::capability::RestrictionError;
use crate::CoreArena;

/// The process execution interface.
pub const EXEC: &str = "Exec";
/// The filesystem interface.
pub const FS: &str = "Fs";
/// The early process-exit interface.
pub const PROC: &str = "Proc";
/// The read-only process environment interface.
pub const ENV: &str = "Env";
/// The completion ring's buffer interface.
pub const RING: &str = "Ring";
/// The divergence interface, with no operation.
pub const DIV: &str = "Div";

/// The six interfaces, sharing their arena-owned payload and reply types.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HostSignatures
{
    /// Run a command and capture its output or inherit the terminal.
    pub exec: EffectSig,
    /// Read and mutate the host filesystem.
    pub fs: EffectSig,
    /// Exit the process; this operation does not resume at the host boundary.
    pub proc: EffectSig,
    /// Read environment variables and the executable search path.
    pub env: EffectSig,
    /// Allocate a buffer the ring fills, and free one back.
    pub ring: EffectSig,
    /// Run forever: no operation, and no handler.
    pub div: EffectSig,
}

quenchant_shape::reason_enum! {
    /// Why the host declares nothing for a name.
    pub mod declared {
        /// The host has no interface by the name, or none offering the
        /// operation.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Nothing the host declares answers the name.
            Undeclared,
        }
    }
}

/// Why an authority over host operations could not be formed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AuthorityError
{
    /// No host interface offers this operation.
    Undeclared(OperationName),
    /// An interface's restriction refused an operation: one named twice.
    Restriction(RestrictionError),
    /// The restrictions conflict as one authority.
    Conflict(EffectConflict),
}

/// The divergence interface's signature. It has no operation, so it names no
/// type and needs no arena.
///
/// # Specification
/// - ensures: the signature named [`DIV`] with no operation, equal to the host
///   table's.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the host table's divergence interface is this one.
/// - witness: `effect::host::tests::host_interfaces_pin_names_payloads_and_replies`
#[spec(ensures: |ret| ret.name().as_ref() == DIV && ret.operations().len() == 0_usize)]
#[inline]
#[must_use]
pub fn divergence() -> EffectSig
{
    EffectSig(alloc::sync::Arc::new(super::Signature {
        name: DIV.into(),
        operations: alloc::collections::BTreeMap::new(),
    }))
}

impl HostSignatures
{
    /// Mint the host interfaces over shared native value types.
    ///
    /// # Specification
    /// - requires: nothing; the arena may already hold unrelated terms.
    /// - ensures: every operation payload and reply resolves in this arena;
    ///   list-valued fields are native Lists, and no signature is executed.
    /// - fails: conflicting operation names in the signature table.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the signature constructor's conflict if a table repeats a name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each interface's name, its operation names in order
    ///   and their payload and reply types are compared with independently
    ///   minted types; a swapped payload and reply, a missing operation or a
    ///   product in place of a List changes an answer.
    /// - witness: `effect::host::tests::host_interfaces_pin_names_payloads_and_replies`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|host|
        [&host.exec, &host.fs, &host.proc, &host.env, &host.ring, &host.div].iter().all(|signature|
            signature.operations().all(|operation|
                arena.value_type(operation.payload).is_some()
                    && arena.value_type(operation.reply).is_some()))
            && host.div.operations().len() == 0_usize) || ret.is_err())]
    #[inline]
    pub fn new(arena: &mut CoreArena) -> Result<Self, EffectConflict>
    {
        let string = arena.value_type_base(BaseType::String);
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
        let buffer = arena.value_type_buffer();
        let strings = arena.value_type_list(string);
        let args_mode = arena.value_type_product(&[strings, string]);
        let command = arena.value_type_product(&[string, args_mode]);
        let error_status = arena.value_type_product(&[string, integer]);
        let output = arena.value_type_product(&[string, error_status]);
        let write = arena.value_type_product(&[string, string]);
        let stat = error_status;
        let exec = EffectSig::new(EXEC.into(), [EffectOp {
            name: "exec".into(),
            payload: command,
            reply: output,
        }])?;
        let fs = EffectSig::new(FS.into(), [
            EffectOp {
                name: "read".into(),
                payload: string,
                reply: string,
            },
            EffectOp {
                name: "write".into(),
                payload: write,
                reply: unit,
            },
            EffectOp {
                name: "glob".into(),
                payload: string,
                reply: strings,
            },
            EffectOp {
                name: "stat".into(),
                payload: string,
                reply: stat,
            },
            EffectOp {
                name: "mkdir".into(),
                payload: string,
                reply: unit,
            },
            EffectOp {
                name: "tempdir".into(),
                payload: unit,
                reply: string,
            },
            EffectOp {
                name: "cwd".into(),
                payload: unit,
                reply: string,
            },
            EffectOp {
                name: "ls_files".into(),
                payload: string,
                reply: strings,
            },
        ])?;
        let proc = EffectSig::new(PROC.into(), [EffectOp {
            name: "exit".into(),
            payload: integer,
            reply: unit,
        }])?;
        let env = EffectSig::new(ENV.into(), [
            EffectOp {
                name: "get".into(),
                payload: string,
                reply: string,
            },
            EffectOp {
                name: "path".into(),
                payload: unit,
                reply: strings,
            },
        ])?;
        let ring = EffectSig::new(RING.into(), [
            EffectOp {
                name: "alloc".into(),
                payload: integer,
                reply: buffer,
            },
            EffectOp {
                name: "free".into(),
                payload: buffer,
                reply: unit,
            },
        ])?;
        let div = divergence();
        Ok(Self {
            exec,
            fs,
            proc,
            env,
            ring,
            div,
        })
    }

    /// The six interfaces, in the order the host declares them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn interfaces(&self) -> [&EffectSig; 6]
    {
        [
            &self.exec, &self.fs, &self.proc, &self.env, &self.ring, &self.div,
        ]
    }

    /// The interface named `name`.
    ///
    /// # Specification
    /// - ensures: the interface whose name is `name`; the undeclared absence
    ///   for any other name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each interface's own name and an undeclared one.
    /// - witness: `effect::host::tests::an_operation_names_the_interface_offering_it`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(found) => found.name() == name,
        | Maybe::Absent(_) => self.interfaces().iter().all(|each| each.name() != name),
    })]
    #[inline]
    pub fn named(
        &self,
        name: &EffectName,
    ) -> Maybe<&EffectSig, declared::Absent>
    {
        self.interfaces()
            .into_iter()
            .find(|interface| interface.name() == name)
            .map_or(Maybe::Absent(declared::Absent::Undeclared), Maybe::Present)
    }

    /// The interface offering `operation`.
    ///
    /// # Specification
    /// - ensures: the one interface declaring `operation`; the undeclared
    ///   absence when none does.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — operations of two interfaces each find their own, and
    ///   an operation of none is undeclared.
    /// - witness: `effect::host::tests::an_operation_names_the_interface_offering_it`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(found) => matches!(found.operation(operation), Maybe::Present(_)),
        | Maybe::Absent(_) => self.interfaces().iter().all(|each| matches!(each.operation(operation), Maybe::Absent(_))),
    })]
    #[inline]
    pub fn offering(
        &self,
        operation: &OperationName,
    ) -> Maybe<&EffectSig, declared::Absent>
    {
        self.interfaces()
            .into_iter()
            .find(|interface| matches!(interface.operation(operation), Maybe::Present(_)))
            .map_or(Maybe::Absent(declared::Absent::Undeclared), Maybe::Present)
    }

    /// The authority granting exactly `operations`, each under the interface
    /// offering it.
    ///
    /// # Specification
    /// - ensures: one restriction per interface any operation belongs to, in
    ///   host order, granting the named operations of it with their types.
    /// - fails: an operation no interface offers, or one named twice.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`AuthorityError::Undeclared`]: the first operation no interface
    ///   offers.
    /// - [`AuthorityError::Restriction`]: an operation named twice.
    /// - [`AuthorityError::Conflict`]: never for this table, whose restrictions
    ///   are one per interface.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — operations of two interfaces in mixed order, an
    ///   undeclared one and a repeated one, each asserted as the exact
    ///   authority or error.
    /// - witness: `effect::host::tests::an_operation_names_the_interface_offering_it`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |authority| authority.signatures().all(|restricted| matches!(self.named(restricted.name()), Maybe::Present(_)))))]
    #[inline]
    pub fn authority<'name, Operations>(
        &self,
        operations: Operations,
    ) -> Result<EffectRow, AuthorityError>
    where
        Operations: IntoIterator<Item = &'name OperationName>,
    {
        let mut offered: Vec<(&EffectName, &OperationName)> = Vec::new();
        for operation in operations {
            let Maybe::Present(interface) = self.offering(operation)
            else {
                return Err(AuthorityError::Undeclared(operation.clone()));
            };
            offered.push((interface.name(), operation));
        }
        let mut restrictions = Vec::new();
        for interface in self.interfaces() {
            let mut granted = offered
                .iter()
                .filter(|&&(held, _)| held == interface.name())
                .map(|&(_, operation)| operation)
                .peekable();
            if granted.peek().is_some() {
                restrictions.push(
                    interface
                        .restrict(granted)
                        .map_err(AuthorityError::Restriction)?,
                );
            }
        }

        EffectRow::authority(&restrictions).map_err(AuthorityError::Conflict)
    }
}

#[cfg(test)]
mod tests;
