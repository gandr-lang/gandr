use gandr_kernel_term::BaseType;
use quenchant_shape::shape::Maybe;

use super::AuthorityError;
use super::CONSOLE;
use super::ENV;
use super::EXEC;
use super::FS;
use super::HostSignatures;
use super::NET;
use super::PARTIAL;
use super::PROC;
use super::STDERR;
use super::STDIN;
use super::declared;
use crate::CertificateEquality;
use crate::CoreArena;
use crate::effect::EffectName;
use crate::effect::EffectRow;
use crate::effect::OperationName;
use crate::effect::capability::RestrictionError;
use crate::syntax::equal_type_syntax;

#[test]
fn an_operation_names_the_interface_offering_it()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).expect("host interfaces");
    for (operation, interface) in [
        ("read", FS),
        ("exit", PROC),
        ("get", ENV),
        ("exec", EXEC),
        ("transmit", NET),
        ("eprint", STDERR),
        ("read_line", STDIN),
    ] {
        let Maybe::Present(found) = host.offering(&OperationName::from(operation))
        else {
            panic!("{operation} is offered");
        };
        assert_eq!(found.name().as_ref(), interface, "{operation}");
        assert_eq!(
            host.named(&EffectName::from(interface)),
            Maybe::Present(found),
            "{interface}"
        );
    }
    assert_eq!(
        host.offering(&OperationName::from("fetch")),
        Maybe::Absent(declared::Absent::Undeclared)
    );
    assert_eq!(
        host.named(&EffectName::from("Clock")),
        Maybe::Absent(declared::Absent::Undeclared)
    );

    let [read, exit, write] = ["read", "exit", "write"].map(OperationName::from);
    let expected = EffectRow::authority(&[
        host.fs.restrict([&read, &write]).expect("fs restricts"),
        host.proc.restrict([&exit]).expect("proc restricts"),
    ])
    .expect("one restriction per interface");
    assert_eq!(host.authority([&write, &exit, &read]), Ok(expected));
    let fetch = OperationName::from("fetch");
    assert_eq!(
        host.authority([&read, &fetch]),
        Err(AuthorityError::Undeclared(fetch))
    );
    assert_eq!(
        host.authority([&read, &read]),
        Err(AuthorityError::Restriction(RestrictionError::Repeated(
            read.clone()
        )))
    );
    assert_eq!(host.authority([]), Ok(EffectRow::EMPTY));
}

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
    let frame = arena.value_type_product(&[integer, string]);
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
        (&host.partial, PARTIAL, alloc::vec![]),
        (&host.console, CONSOLE, alloc::vec![("print", string, unit)]),
        (&host.stderr, STDERR, alloc::vec![("eprint", string, unit)]),
        (&host.stdin, STDIN, alloc::vec![("read_line", unit, string)]),
        (&host.net, NET, alloc::vec![
            ("accept", unit, status),
            ("connect", string, integer),
            ("disconnect", integer, unit),
            ("receive", integer, string),
            ("transmit", frame, unit),
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
    assert_eq!(
        host.partial,
        super::partiality(),
        "the divergence interface needs no arena"
    );
}

#[test]
fn an_operation_reads_the_host_only_when_it_changes_nothing()
{
    let [fs, exec, store] = [FS, EXEC, "Store"].map(EffectName::from);
    let [read, write, run] = ["read", "write", "exec"].map(OperationName::from);
    assert_eq!(
        super::access(&fs, &read),
        super::HostAccess::Reads,
        "a file read changes nothing"
    );
    assert_eq!(
        super::access(&fs, &write),
        super::HostAccess::Changes,
        "a file write changes the file system it reads"
    );
    assert_eq!(
        super::access(&exec, &run),
        super::HostAccess::Changes,
        "a command may change anything"
    );
    assert_eq!(
        super::access(&store, &read),
        super::HostAccess::Changes,
        "an interface the host does not declare holds its handler's state"
    );
}

#[test]
fn each_host_interface_but_partial_lives_in_a_std_module_4523()
{
    let home = |name: &str| super::home(&EffectName::from(name));
    assert_eq!(
        home(CONSOLE),
        Maybe::Present(super::HostHome("std.io")),
        "the console lives in `std.io`"
    );
    assert_eq!(
        home(EXEC),
        Maybe::Present(super::HostHome("std.process")),
        "execution lives in `std.process`"
    );
    assert_eq!(
        home(NET),
        Maybe::Present(super::HostHome("std.net")),
        "the network lives in `std.net`"
    );
    assert_eq!(
        home(PARTIAL),
        Maybe::Absent(super::homed::Absent::Ambient),
        "divergence stays ambient"
    );
    assert_eq!(
        home("std.io"),
        Maybe::Absent(super::homed::Absent::Ambient),
        "a module is no interface"
    );
}
