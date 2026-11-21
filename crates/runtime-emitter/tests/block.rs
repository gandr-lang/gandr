//! The block compiler: a system call of three arguments compiled to the bytes
//! that a probe entered and ran on each host, a template over class operands,
//! the cache in the process and in a directory, one compile for requests at
//! once, and each refusal by name.

use core::iter;
use std::fs;
use std::path::PathBuf;
use std::sync::Barrier;
use std::thread;

use gandr_runtime_emitter::block::Answer;
use gandr_runtime_emitter::block::Assembler;
use gandr_runtime_emitter::block::Block;
use gandr_runtime_emitter::block::Blocks;
use gandr_runtime_emitter::block::Cache;
use gandr_runtime_emitter::block::Class;
use gandr_runtime_emitter::block::Description;
use gandr_runtime_emitter::block::Direction;
use gandr_runtime_emitter::block::Operand;
use gandr_runtime_emitter::block::Options;
use gandr_runtime_emitter::block::Origin;
use gandr_runtime_emitter::block::Place;
use gandr_runtime_emitter::block::Refusal;
use gandr_runtime_emitter::block::Register;
use gandr_runtime_emitter::block::Target;

/// An input in `register`.
///
/// # Specification
/// trivial.
fn input(register: Register) -> Operand
{
    Operand {
        direction: Direction::In,
        place: Place::Register(register),
    }
}

/// The system call of three arguments on `target`: the call's number and
/// its three arguments are the four operand words, and the answer is the
/// kernel's.
///
/// # Specification
/// trivial.
fn system_call(target: Target) -> Description
{
    let (template, number, arguments, answer, clobbers): (_, _, [&str; 3], _, &[&str]) =
        match target {
            Target::LinuxX86_64 => ("syscall", "rax", ["rdi", "rsi", "rdx"], "rax", &[
                "rcx", "r11",
            ]),
            Target::LinuxAarch64 => ("svc 0", "x8", ["x0", "x1", "x2"], "x0", &[]),
            Target::LinuxRiscv64 => ("ecall", "x17", ["x10", "x11", "x12"], "x10", &[]),
            Target::DarwinAarch64 => ("svc 0x80", "x16", ["x0", "x1", "x2"], "x0", &["x1"]),
        };
    Description {
        target,
        template: template.into(),
        operands: core::iter::once(number)
            .chain(arguments)
            .map(|name| input(Register::from(name)))
            .collect(),
        answer: Answer::Place(Place::Register(Register::from(answer))),
        clobbers: clobbers.iter().copied().map(Register::from).collect(),
        options: Options::DEFAULT,
    }
}

/// A block compiler on the pinned `llc` with a cache in the process.
///
/// # Specification
/// trivial.
fn compiler() -> Blocks
{
    Blocks::new(Assembler::pinned(), Cache::Process)
}

/// A fresh directory for the witness of the cache, empty.
///
/// # Specification
/// trivial.
fn scratch() -> PathBuf
{
    let directory = std::env::temp_dir().join(format!("gandr-block-{}-cache", std::process::id()));
    let _absent = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).unwrap();
    directory
}

/// The probe's bytes of the system call on the three hosts, which a C
/// program mapped executable and entered, and the bytes on Linux arm64.
#[test]
fn the_system_call_compiles_to_the_bytes_that_ran()
{
    let blocks = compiler();
    let expected: [(Target, &[u8]); 4] = [
        (Target::LinuxX86_64, &[
            0x48, 0x8b, 0x07, 0x48, 0x8b, 0x4f, 0x08, 0x48, 0x8b, 0x77, 0x10, 0x48, 0x8b, 0x57,
            0x18, 0x48, 0x89, 0xcf, 0x0f, 0x05, 0xc3,
        ]),
        (Target::LinuxAarch64, &[
            0x08, 0x24, 0x40, 0xa9, 0x01, 0x08, 0x41, 0xa9, 0xe0, 0x03, 0x09, 0xaa, 0x01, 0x00,
            0x00, 0xd4, 0xc0, 0x03, 0x5f, 0xd6,
        ]),
        (Target::LinuxRiscv64, &[
            0x83, 0x38, 0x05, 0x00, 0x14, 0x65, 0x0c, 0x69, 0x10, 0x6d, 0x36, 0x85, 0x73, 0x00,
            0x00, 0x00, 0x82, 0x80,
        ]),
        (Target::DarwinAarch64, &[
            0x10, 0x20, 0x40, 0xa9, 0x01, 0x08, 0x41, 0xa9, 0xe0, 0x03, 0x08, 0xaa, 0x01, 0x10,
            0x00, 0xd4, 0xc0, 0x03, 0x5f, 0xd6,
        ]),
    ];
    for (target, bytes) in expected {
        let block = blocks.compile(&system_call(target)).unwrap();
        assert_eq!(
            (&*block.code.0, block.origin),
            (bytes, Origin::Compiled),
            "the system call on {}",
            target
        );
    }
}

/// A template over class operands: an operand that the block reads and
/// writes, one that it reads, and an answer in a register of the class. A
/// second template differs in one instruction and gives other bytes.
#[test]
fn a_class_operand_and_an_output_take_their_words()
{
    let blocks = compiler();
    let general = Place::Class(Class::General);
    let sum = |instruction: &str| Description {
        target: Target::LinuxX86_64,
        template: format!("{instruction} {{0}}, {{1}}\nmov {{answer}}, {{0}}")
            .as_str()
            .into(),
        operands: Box::new([
            Operand {
                direction: Direction::InOut,
                place: general.clone(),
            },
            Operand {
                direction: Direction::In,
                place: general.clone(),
            },
        ]),
        answer: Answer::Place(general.clone()),
        clobbers: Box::new([]),
        options: Options::DEFAULT,
    };
    let add = blocks.compile(&sum("add")).unwrap();
    let sub = blocks.compile(&sum("sub")).unwrap();
    // mov rcx, [rdi]; mov rax, [rdi + 8]; add rcx, rax; mov rax, rcx;
    // mov [rdi], rcx; ret. Operand 0 is read from its word and written back
    // to it, operand 1 is read, and the answer shares the register of
    // operand 1, which it may.
    assert_eq!(
        &*add.code.0,
        &[
            0x48, 0x8b, 0x0f, 0x48, 0x8b, 0x47, 0x08, 0x48, 0x01, 0xc1, 0x48, 0x89, 0xc8, 0x48,
            0x89, 0x0f, 0xc3,
        ][..],
        "add"
    );
    assert_eq!(
        &*sub.code.0,
        &[
            0x48, 0x8b, 0x0f, 0x48, 0x8b, 0x47, 0x08, 0x48, 0x29, 0xc1, 0x48, 0x89, 0xc8, 0x48,
            0x89, 0x0f, 0xc3,
        ][..],
        "sub"
    );
}

/// A second request in the process reads the process's bytes, and a
/// request of another process reads the directory's. Neither starts a
/// process: the assembler is gone before them.
#[test]
fn a_second_request_starts_no_process()
{
    let directory = scratch();
    let assembler = directory.join("llc");
    std::os::unix::fs::symlink(Assembler::pinned().0, &assembler).unwrap();
    let call = system_call(Target::LinuxX86_64);
    let first = Blocks::new(
        Assembler(assembler.clone()),
        Cache::Directory(directory.join("blocks")),
    );
    let compiled = first.compile(&call).unwrap();
    fs::remove_file(&assembler).unwrap();
    let again = first.compile(&call).unwrap();
    let later = Blocks::new(
        Assembler(assembler.clone()),
        Cache::Directory(directory.join("blocks")),
    )
    .compile(&call)
    .unwrap();
    let elsewhere = Blocks::new(Assembler(assembler.clone()), Cache::Process).compile(&call);
    fs::remove_dir_all(&directory).unwrap();
    assert_eq!(compiled.origin, Origin::Compiled, "the first request");
    assert_eq!(
        again,
        Block {
            key: compiled.key,
            target: compiled.target,
            code: compiled.code.clone(),
            origin: Origin::Process
        },
        "the second request"
    );
    assert_eq!(
        later,
        Block {
            key: compiled.key,
            target: compiled.target,
            code: compiled.code,
            origin: Origin::Directory
        },
        "a request of a new compiler on the directory"
    );
    assert_eq!(
        elsewhere,
        Err(Refusal::Absent(assembler)),
        "a compiler with no directory compiles, and its assembler is gone"
    );
}

/// Eight requests of one description at once start one compile, and each
/// reads its bytes.
#[test]
fn requests_at_once_share_one_compile()
{
    let blocks = compiler();
    let call = system_call(Target::LinuxRiscv64);
    let barrier = Barrier::new(8);
    let results: Vec<Block> = thread::scope(|scope| {
        let handles: Vec<_> = iter::repeat_with(|| {
            scope.spawn(|| {
                barrier.wait();
                blocks.compile(&call).unwrap()
            })
        })
        .take(8)
        .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .collect()
    });
    let compiled = results
        .iter()
        .filter(|block| block.origin == Origin::Compiled)
        .count();
    assert_eq!(compiled, 1, "one request compiles");
    assert!(
        results
            .iter()
            .all(|block| block.origin != Origin::Directory && block.code == results[0].code),
        "each request reads the one compile's bytes"
    );
}

/// Each refusal, triggered, with its exact variant.
#[test]
fn each_refusal_names_its_cause()
{
    let blocks = compiler();
    let call = || system_call(Target::LinuxX86_64);
    let with = |description: Description| blocks.compile(&description);
    let operand = |register: &'static str| {
        let mut description = call();
        description.operands[0] = input(Register::from(register));
        description
    };
    let absent = PathBuf::from("/nonexistent/gandr/llc");
    assert_eq!(
        Blocks::new(Assembler(absent.clone()), Cache::Process)
            .compile(&system_call(Target::LinuxX86_64)),
        Err(Refusal::Absent(absent)),
        "llc is absent"
    );
    assert_eq!(
        with(Description {
            template: "bogus".into(),
            ..call()
        }),
        Err(Refusal::Assembler(
            "invalid instruction mnemonic 'bogus'".into()
        )),
        "the assembler refuses the template"
    );
    assert_eq!(
        with(operand("x17")),
        Err(Refusal::Register("x17".into())),
        "the target lacks the register of an operand"
    );
    assert_eq!(
        with(Description {
            clobbers: Box::new([Register::from("x17")]),
            ..call()
        }),
        Err(Refusal::Register("x17".into())),
        "the target lacks the register of a clobber"
    );
    assert_eq!(
        with(operand("r}")),
        Err(Refusal::Register("r}".into())),
        "a name that LLVM cannot read"
    );
    assert_eq!(
        with(Description {
            template: "mov rax, {4}".into(),
            ..call()
        }),
        Err(Refusal::Reference("4".into())),
        "a reference past the operands"
    );
    assert_eq!(
        with(Description {
            template: "call foo".into(),
            ..call()
        }),
        Err(Refusal::Relocation("foo".into())),
        "the object holds a relocation"
    );
    assert_eq!(
        with(Description {
            template: ".weak foo".into(),
            ..call()
        }),
        Err(Refusal::Undefined("foo".into())),
        "the object holds an undefined symbol"
    );
    assert_eq!(
        with(Description {
            template: ".pushsection .text.second,\"ax\",@progbits\nnop\n.popsection".into(),
            ..call()
        }),
        Err(Refusal::Sections(2)),
        "the object holds a second code section"
    );
}
