//! Host operation signatures, without a host implementation.
//!
//! Payload records are represented by ordered products until record types are
//! available at this seam. `Exec.exec` takes `(program, (args, mode))` and
//! returns `(stdout, (stderr, exit_code))`; `Fs.write` takes `(path, contents)`
//! and `Fs.stat` returns `(kind, size)`. List fields use the native List
//! former.

use anodized::spec;
use gandr_kernel_term::BaseType;

use super::EffectConflict;
use super::EffectOp;
use super::EffectSig;
use crate::CoreArena;

/// The process execution interface.
pub const EXEC: &str = "Exec";
/// The filesystem interface.
pub const FS: &str = "Fs";
/// The early process-exit interface.
pub const PROC: &str = "Proc";
/// The read-only process environment interface.
pub const ENV: &str = "Env";

/// The four interfaces, sharing their arena-owned payload and reply types.
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
        [&host.exec, &host.fs, &host.proc, &host.env].iter().all(|signature|
            signature.operations().all(|operation|
                arena.value_type(operation.payload).is_some()
                    && arena.value_type(operation.reply).is_some()))) || ret.is_err())]
    #[inline]
    pub fn new(arena: &mut CoreArena) -> Result<Self, EffectConflict>
    {
        let string = arena.value_type_base(BaseType::String);
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
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
        Ok(Self {
            exec,
            fs,
            proc,
            env,
        })
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_term::BaseType;

    use super::ENV;
    use super::EXEC;
    use super::FS;
    use super::HostSignatures;
    use super::PROC;
    use crate::CertificateEquality;
    use crate::CoreArena;
    use crate::syntax::equal_type_syntax;

    #[test]
    fn host_interfaces_pin_names_payloads_and_replies()
    {
        let mut arena = CoreArena::new();
        let _occupied = arena.value_type_unit();
        let host = HostSignatures::new(&mut arena).expect("host interfaces");
        let string = arena.value_type_base(BaseType::String);
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
        let strings = arena.value_type_list(string);
        let args_mode = arena.value_type_product(&[strings, string]);
        let command = arena.value_type_product(&[string, args_mode]);
        let status = arena.value_type_product(&[string, integer]);
        let output = arena.value_type_product(&[string, status]);
        let write = arena.value_type_product(&[string, string]);
        let expected = [
            (&host.exec, EXEC, alloc::vec![("exec", command, output)]),
            (&host.fs, FS, alloc::vec![
                ("cwd", unit, string),
                ("glob", string, strings),
                ("ls_files", string, strings),
                ("mkdir", string, unit),
                ("read", string, string),
                ("stat", string, status),
                ("tempdir", unit, string),
                ("write", write, unit),
            ]),
            (&host.proc, PROC, alloc::vec![("exit", integer, unit)]),
            (&host.env, ENV, alloc::vec![
                ("get", string, string),
                ("path", unit, strings)
            ]),
        ];
        for (signature, name, operations) in expected {
            assert_eq!(signature.name().as_ref(), name);
            assert_eq!(signature.operations().len(), operations.len(), "{name}");
            for (operation, (wanted, payload, reply)) in signature.operations().zip(operations) {
                assert_eq!(operation.name.as_ref(), wanted, "{name}");
                for (actual, expected) in [(operation.payload, payload), (operation.reply, reply)] {
                    assert_eq!(
                        equal_type_syntax(&arena, actual, expected),
                        CertificateEquality::Equal,
                        "{name}.{wanted}"
                    );
                }
            }
        }
    }
}
