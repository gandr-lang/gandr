//! The structures of the ring that `std.io.ring` describes, against a
//! `#[repr(C)]` declaration of each in Rust: the size of each structure, the
//! count of its fields, and the offset and the width of each field.

use core::convert::Infallible;
use core::mem::offset_of;
use core::mem::size_of;
use core::mem::size_of_val;
use std::path::Path;

use gandr_core_checker::HostGrant;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Terminal;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::judge_member;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_dispatcher::lower_unit_source;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_evaluate::Runs as _;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// `struct io_sqring_offsets` of `include/uapi/linux/io_uring.h`.
#[repr(C)]
#[derive(Default)]
struct IoSqringOffsets
{
    /// `head`.
    head: u32,
    /// `tail`.
    tail: u32,
    /// `ring_mask`.
    ring_mask: u32,
    /// `ring_entries`.
    ring_entries: u32,
    /// `flags`.
    flags: u32,
    /// `dropped`.
    dropped: u32,
    /// `array`.
    array: u32,
    /// `resv1`.
    resv1: u32,
    /// `user_addr`.
    user_addr: u64,
}

/// `struct io_cqring_offsets` of `include/uapi/linux/io_uring.h`.
#[repr(C)]
#[derive(Default)]
struct IoCqringOffsets
{
    /// `head`.
    head: u32,
    /// `tail`.
    tail: u32,
    /// `ring_mask`.
    ring_mask: u32,
    /// `ring_entries`.
    ring_entries: u32,
    /// `overflow`.
    overflow: u32,
    /// `cqes`.
    cqes: u32,
    /// `flags`.
    flags: u32,
    /// `resv1`.
    resv1: u32,
    /// `user_addr`.
    user_addr: u64,
}

/// `struct io_uring_params` of `include/uapi/linux/io_uring.h`.
#[repr(C)]
#[derive(Default)]
struct IoUringParams
{
    /// `sq_entries`.
    sq_entries: u32,
    /// `cq_entries`.
    cq_entries: u32,
    /// `flags`.
    flags: u32,
    /// `sq_thread_cpu`.
    sq_thread_cpu: u32,
    /// `sq_thread_idle`.
    sq_thread_idle: u32,
    /// `features`.
    features: u32,
    /// `wq_fd`.
    wq_fd: u32,
    /// `resv`.
    resv: [u32; 3],
    /// `sq_off`.
    sq_off: IoSqringOffsets,
    /// `cq_off`.
    cq_off: IoCqringOffsets,
}

/// `struct io_uring_sqe` of `include/uapi/linux/io_uring.h`. Each union is
/// its first member, as `std.io.ring` describes it.
#[repr(C)]
#[derive(Default)]
struct IoUringSqe
{
    /// `opcode`.
    opcode: u8,
    /// `flags`.
    flags: u8,
    /// `ioprio`.
    ioprio: u16,
    /// `fd`.
    fd: i32,
    /// `off`, the first member of its union.
    off: u64,
    /// `addr`, the first member of its union.
    addr: u64,
    /// `len`.
    len: u32,
    /// `rw_flags`, the first member of its union.
    rw_flags: u32,
    /// `user_data`.
    user_data: u64,
    /// `buf_index`, the first member of its union.
    buf_index: u16,
    /// `personality`.
    personality: u16,
    /// `splice_fd_in`, the first member of its union.
    splice_fd_in: i32,
    /// `addr3`, the first word of the last union.
    addr3: u64,
    /// `__pad2`, the second word of the last union.
    pad2: [u64; 1],
}

/// `struct io_uring_cqe` of `include/uapi/linux/io_uring.h`, with no
/// flexible array `big_cqe`.
#[repr(C)]
#[derive(Default)]
struct IoUringCqe
{
    /// `user_data`.
    user_data: u64,
    /// `res`.
    res: i32,
    /// `flags`.
    flags: u32,
}

/// One field as Rust lays it out: its name in the header, its offset and its
/// width.
struct Laid
{
    /// The name of the field in the header.
    name: &'static str,
    /// The offset in bytes.
    offset: usize,
    /// The width in bytes.
    width: usize,
}

/// One structure as Rust lays it out: its name in the header, its size and
/// its fields.
struct Declared
{
    /// The name of the structure in the header.
    name: &'static str,
    /// The size in bytes.
    size: usize,
    /// The fields, in the order of the header.
    fields: Vec<Laid>,
}

/// The `Laid` of each field of a value of `$ty`, each `$field` under the
/// header's name `$name`.
macro_rules! laid {
    ($ty:ty, $value:expr, [$($field:ident as $name:literal),* $(,)?]) => {
        vec![$(Laid {
            name: $name,
            offset: offset_of!($ty, $field),
            width: size_of_val(&$value.$field),
        }),*]
    };
}

/// The five structures of the ring, as their `#[repr(C)]` declarations lay
/// them out on this host.
///
/// # Specification
/// trivial.
fn declared() -> Vec<Declared>
{
    let sq = IoSqringOffsets::default();
    let cq = IoCqringOffsets::default();
    let params = IoUringParams::default();
    let sqe = IoUringSqe::default();
    let cqe = IoUringCqe::default();
    vec![
        Declared {
            name: "io_uring_params",
            size: size_of::<IoUringParams>(),
            fields: laid!(IoUringParams, params, [
                sq_entries as "sq_entries",
                cq_entries as "cq_entries",
                flags as "flags",
                sq_thread_cpu as "sq_thread_cpu",
                sq_thread_idle as "sq_thread_idle",
                features as "features",
                wq_fd as "wq_fd",
                resv as "resv",
                sq_off as "sq_off",
                cq_off as "cq_off",
            ]),
        },
        Declared {
            name: "io_sqring_offsets",
            size: size_of::<IoSqringOffsets>(),
            fields: laid!(IoSqringOffsets, sq, [
                head as "head",
                tail as "tail",
                ring_mask as "ring_mask",
                ring_entries as "ring_entries",
                flags as "flags",
                dropped as "dropped",
                array as "array",
                resv1 as "resv1",
                user_addr as "user_addr",
            ]),
        },
        Declared {
            name: "io_cqring_offsets",
            size: size_of::<IoCqringOffsets>(),
            fields: laid!(IoCqringOffsets, cq, [
                head as "head",
                tail as "tail",
                ring_mask as "ring_mask",
                ring_entries as "ring_entries",
                overflow as "overflow",
                cqes as "cqes",
                flags as "flags",
                resv1 as "resv1",
                user_addr as "user_addr",
            ]),
        },
        Declared {
            name: "io_uring_sqe",
            size: size_of::<IoUringSqe>(),
            fields: laid!(IoUringSqe, sqe, [
                opcode as "opcode",
                flags as "flags",
                ioprio as "ioprio",
                fd as "fd",
                off as "off",
                addr as "addr",
                len as "len",
                rw_flags as "rw_flags",
                user_data as "user_data",
                buf_index as "buf_index",
                personality as "personality",
                splice_fd_in as "splice_fd_in",
                addr3 as "addr3",
                pad2 as "__pad2",
            ]),
        },
        Declared {
            name: "io_uring_cqe",
            size: size_of::<IoUringCqe>(),
            fields: laid!(IoUringCqe, cqe, [
                user_data as "user_data",
                res as "res",
                flags as "flags",
            ]),
        },
    ]
}

/// A host that answers nothing: the module performs no operation.
struct Declining;

impl HostHandler for Declining
{
    type Abort = Infallible;

    /// Decline the operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        _request: HostRequest<'_>,
        _values: &mut HostValues<'_>,
    ) -> HostReply<Infallible>
    {
        HostReply::Decline
    }
}

/// The literal of the string `text`.
///
/// # Specification
/// trivial.
fn text(text: &str) -> Literal
{
    Literal::Text(StringLiteral::new(text.to_owned()))
}

/// The literal of the count `value`.
///
/// # Specification
/// trivial.
fn integer(value: usize) -> Literal
{
    let magnitude =
        Magnitude::from_decimal_text(value.to_string()).expect("a count is decimal digits");
    Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))
}

/// The answer of a call that returns a literal, as `arena` holds it.
///
/// # Specification
/// trivial.
fn answered(
    arena: &CoreArena,
    terminal: &Terminal<'_>,
) -> Option<Literal>
{
    let Terminal::Read(read) = *terminal
    else {
        return None;
    };
    let Some(&Computation::Return(value)) = arena.computation(read)
    else {
        return None;
    };
    match arena.value(value) {
        Some(&Value::Literal(ref literal)) => Some(literal.clone()),
        _ => None,
    }
}

/// The size of each structure, the count of its fields, and the offset and
/// the width of each field that `std.io.ring` describes are those of the
/// `#[repr(C)]` declaration of the structure on this host.
#[test]
fn each_structure_of_the_ring_is_laid_out_as_rust_lays_out_its_declaration()
{
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../library/std/src/io/ring.gandr");
    let source = std::fs::read_to_string(&path).expect("the module reads");
    let grammar = built_in().expect("built-in grammar");
    let laid = lay_out(
        &grammar,
        &path,
        classify(&path),
        SourceText::from(source.as_str()),
    );
    let text_of = SourceText::from(laid.text.as_str());
    let lowering = lower_unit_source(&grammar, text_of, &laid.unit, &mut LoweringCount::default())
        .expect("the unit lowers");
    let Lowered::Module { module, arena } = lowering.into_lowered()
    else {
        panic!("the unit is read as a module");
    };
    let Composed::Settled { mut program, .. } = judge_member::<Evaluator>(
        CorpusRoot::Strict,
        (module, text_of),
        arena,
        &HostGrant::UNBOUNDED,
        laid.base,
    )
    .admit()
    .expect("composition")
    else {
        panic!("the module is refused");
    };
    let mut ask = |name: &str, arguments: &[Literal]| -> Option<Literal> {
        let Maybe::Present(constant) = program.named(SurfaceName::from(name))
        else {
            panic!("`{name}` is declared");
        };
        let mut arena = CoreArena::new();
        let values: Vec<_> = arguments
            .iter()
            .map(|argument| arena.value_literal(argument.clone()))
            .collect();
        let Ok(terminal) = program.call(constant, &values, &mut arena, &mut Declining);
        answered(&arena, &terminal)
    };
    for structure in declared() {
        let name = text(structure.name);
        assert_eq!(
            ask("size", core::slice::from_ref(&name)),
            Some(integer(structure.size)),
            "the size of `{}`",
            structure.name
        );
        assert_eq!(
            ask("count", core::slice::from_ref(&name)),
            Some(integer(structure.fields.len())),
            "the count of the fields of `{}`",
            structure.name
        );
        for field in &structure.fields {
            let field_name = text(field.name);
            assert_eq!(
                ask("offset", &[name.clone(), field_name.clone()]),
                Some(integer(field.offset)),
                "the offset of `{}.{}`",
                structure.name,
                field.name
            );
            assert_eq!(
                ask("width", &[name.clone(), field_name]),
                Some(integer(field.width)),
                "the width of `{}.{}`",
                structure.name,
                field.name
            );
        }
    }
}
