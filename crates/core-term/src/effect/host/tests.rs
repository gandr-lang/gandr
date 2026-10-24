use gandr_kernel_term::BaseType;
use quenchant_shape::shape::Maybe;

use super::AuthorityError;
use super::CONSOLE;
use super::DIV;
use super::ENV;
use super::EXEC;
use super::FS;
use super::HostSignatures;
use super::PROC;
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
    for (operation, interface) in [("read", FS), ("exit", PROC), ("get", ENV), ("exec", EXEC)] {
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
        host.offering(&OperationName::from("send")),
        Maybe::Absent(declared::Absent::Undeclared)
    );
    assert_eq!(
        host.named(&EffectName::from("Net")),
        Maybe::Absent(declared::Absent::Undeclared)
    );

    let [read, exit, write] = ["read", "exit", "write"].map(OperationName::from);
    let expected = EffectRow::authority(&[
        host.fs.restrict([&read, &write]).expect("fs restricts"),
        host.proc.restrict([&exit]).expect("proc restricts"),
    ])
    .expect("one restriction per interface");
    assert_eq!(host.authority([&write, &exit, &read]), Ok(expected));
    let send = OperationName::from("send");
    assert_eq!(
        host.authority([&read, &send]),
        Err(AuthorityError::Undeclared(send))
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
        (&host.div, DIV, alloc::vec![]),
        (&host.console, CONSOLE, alloc::vec![("print", string, unit)]),
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
        host.div,
        super::divergence(),
        "the divergence interface needs no arena"
    );
}
