//! Definitions of a composed program called from Rust on values the caller
//! builds, each answer read back into the caller's arena.

use core::convert::Infallible;
use std::path::Path;
use std::sync::OnceLock;

use anodized::spec;
use gandr_core_checker::HostGrant;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Stuck;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::Laid;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Terminal;
use gandr_surface_dispatcher::Unrunnable;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::judge_member;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_dispatcher::lower_unit_source;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// `text`, read as the source at `path`, laid out as one unit with the sources
/// it imports.
///
/// # Specification
/// - ensures: the unit [`lay_out`] reads for `text` at `path`, its imports
///   resolved beside `path`.
/// - panics: if the built-in grammar does not build.
/// - executable: none — the layout is the dispatcher's; the calls compose it.
///
/// # Adequacy
/// - hypothesis: L3 — the exemplar's imports resolve, and a source no file
///   holds lays out alone.
/// - witness: `tests::boundary::a_definition_answers_the_integer_rust_passes`
/// - witness: `tests::boundary::an_unrunnable_definition_ends_before_a_run`
fn laid(
    path: &Path,
    text: SourceText<'_>,
) -> Laid
{
    let grammar = built_in().expect("built-in grammar");
    lay_out(&grammar, path, classify(path), text)
}

/// The exemplar whose definitions the tests call, laid out once with the `std`
/// modules it imports.
///
/// # Specification
/// - ensures: the unit of `round-trip.gandr` as the corpus holds it.
/// - panics: if the exemplar does not read.
/// - executable: none — as [`laid`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`laid`].
/// - witness: `tests::boundary::a_definition_answers_the_integer_rust_passes`
fn round_trip() -> &'static Laid
{
    static ROUND_TRIP: OnceLock<Laid> = OnceLock::new();
    ROUND_TRIP.get_or_init(|| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/interop/boundary/round-trip.gandr");
        let text = std::fs::read_to_string(&path).expect("the exemplar reads");
        laid(&path, SourceText::from(text.as_str()))
    })
}

/// The exemplar whose definitions read values Rust holds by their layouts,
/// laid out once with the modules it imports.
///
/// # Specification
/// - ensures: the unit of `by-layout.gandr` as the corpus holds it.
/// - panics: if the exemplar does not read.
/// - executable: none — as [`laid`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`laid`].
/// - witness: `tests::boundary::a_list_rust_holds_has_its_length_in_both_layouts`
/// - witness: `tests::boundary::the_null_niche_crosses_as_rust_reads_it`
fn by_layout() -> &'static Laid
{
    static BY_LAYOUT: OnceLock<Laid> = OnceLock::new();
    BY_LAYOUT.get_or_init(|| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/interop/boundary/by-layout.gandr");
        let text = std::fs::read_to_string(&path).expect("the exemplar reads");
        laid(&path, SourceText::from(text.as_str()))
    })
}

/// A definition the checker refuses, laid out alone.
///
/// # Specification
/// - ensures: the unit of one definition calling `sub` on a text.
/// - panics: none.
/// - executable: none — as [`laid`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`laid`].
/// - witness: `tests::boundary::an_unrunnable_definition_ends_before_a_run`
fn refused() -> &'static Laid
{
    static REFUSED: OnceLock<Laid> = OnceLock::new();
    REFUSED.get_or_init(|| {
        laid(
            Path::new("refused.gandr"),
            SourceText::from("def refused(x : Integer) -> Integer { sub(\"wrong\", x) }"),
        )
    })
}

/// An integer the Rust caller passes to a definition or expects back.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Integer(i64);

/// The integer literal denoting `value`.
///
/// # Specification
/// trivial.
fn literal(value: Integer) -> Literal
{
    let Integer(value) = value;
    let sign = if value < 0 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    let magnitude = Magnitude::from_decimal_text(value.unsigned_abs().to_string())
        .expect("an integer's magnitude is decimal digits");
    Literal::Integer(IntegerLiteral::new(sign, magnitude))
}

/// The value a call's answer returns, as `arena` holds it.
///
/// # Specification
/// trivial.
fn returned<'arena>(
    arena: &'arena CoreArena,
    terminal: &Terminal<'_>,
) -> Option<&'arena Value>
{
    let Terminal::Read(read) = *terminal
    else {
        return None;
    };
    let Some(&Computation::Return(value)) = arena.computation(read)
    else {
        return None;
    };
    arena.value(value)
}

/// A `u32` as the Rust side of the exemplar's extern block takes and answers
/// it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Word(u32);

/// The Rust function the exemplar's extern block declares, `add(x: u32, n:
/// u32) -> u32`, wrapping as Rust's `u32` addition does in a release build.
///
/// # Specification
/// trivial.
fn add(
    x: Word,
    n: Word,
) -> Word
{
    Word(x.0.wrapping_add(n.0))
}

/// The literal of `word`, a `u32`.
///
/// # Specification
/// trivial.
const fn word(word: Word) -> Literal
{
    Literal::Fixed(FixedInteger::U32(word.0))
}

/// A host answering nothing: every operation it is offered stays unhandled.
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

/// The Rust side of the exemplar's extern block: a host answering
/// `Boundary.add` with [`add`], keeping each pair of arguments it is passed,
/// and declining any other operation.
#[repr(transparent)]
struct RustSide
{
    /// The arguments of each `Boundary.add` answered, in order.
    received: Vec<(Word, Word)>,
}

impl HostHandler for RustSide
{
    type Abort = Infallible;

    /// Answer `Boundary.add` on two `u32` with their [`add`], declining any
    /// other operation or payload.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Infallible>
    {
        if request.signature.name().as_ref() != "Boundary" || request.operation.as_ref() != "add" {
            return HostReply::Decline;
        }
        let Some(&HeapValue::Constructed {
            tag: ConstructorTag::Tuple(_),
            ref fields,
        }) = values.value(request.payload)
        else {
            return HostReply::Decline;
        };
        let read = |at: HeapValueId| match values.value(at) {
            Some(&HeapValue::Literal(Literal::Fixed(FixedInteger::U32(value)))) => {
                Some(Word(value))
            },
            _ => None,
        };
        let (Some(x), Some(n)) = (
            fields.first().copied().and_then(read),
            fields.get(1).copied().and_then(read),
        )
        else {
            return HostReply::Decline;
        };
        self.received.push((x, n));
        match values.allocate(HeapValue::Literal(word(add(x, n)))) {
            Ok(sum) => HostReply::Resume(sum),
            Err(_spent) => HostReply::Decline,
        }
    }
}

/// Compose `laid`, call its definition `name` on `arguments` under `host`, and
/// answer the caller's arena beside how the call ended.
///
/// # Specification
/// - requires: `laid` composes and its own source declares `name` at its top
///   level.
/// - ensures: the arena holding the arguments and any read-back answer, and the
///   terminal the real dispatcher's call ended at.
/// - panics: if composition or the lookup of `name` fails.
///
/// # Adequacy
/// - hypothesis: L3 — integer answers, an order-dependent answer, a function
///   answered, a refused definition, an extern operation answered and one
///   declined have distinct observations.
/// - witness: `tests::boundary::a_definition_answers_the_integer_rust_passes`
/// - witness: `tests::boundary::an_extern_operation_is_answered_by_the_rust_caller`
/// - witness: `tests::boundary::an_extern_operation_no_host_answers_sticks_the_run`
#[spec(ensures: |ref ret| !matches!(ret.1, Terminal::Ended(Evaluation::Unrunnable(Unrunnable::Undeclared(_)))))]
fn call_under<Host>(
    laid: &'static Laid,
    name: SurfaceName<'_>,
    arguments: &[Literal],
    host: &mut Host,
) -> (CoreArena, Terminal<'static>)
where
    Host: HostHandler<Abort = Infallible>,
{
    let grammar = built_in().expect("built-in grammar");
    let source = SourceText::from(laid.text.as_str());
    let lowering = lower_unit_source(&grammar, source, &laid.unit, &mut LoweringCount::default())
        .expect("the unit lowers");
    let Lowered::Module { module, arena } = lowering.into_lowered()
    else {
        panic!("the unit is read as a module");
    };
    let Composed::Settled { mut program, .. } = judge_member(
        CorpusRoot::Fixture,
        (module, source),
        arena,
        &HostGrant::UNBOUNDED,
        laid.base,
    )
    .admit()
    .expect("composition")
    else {
        panic!("module was refused");
    };
    let Maybe::Present(constant) = program.named(name)
    else {
        panic!("`{name}` is declared");
    };
    let mut arena = CoreArena::new();
    let arguments: Vec<_> = arguments
        .iter()
        .map(|argument| arena.value_literal(argument.clone()))
        .collect();
    let Ok(terminal) = program.call(constant, &arguments, &mut arena, host);
    (arena, terminal)
}

/// Compose `source` and call its definition `name` on `arguments`, integers,
/// under a host answering nothing.
///
/// # Specification
/// - requires: as [`call_under`].
/// - ensures: as [`call_under`].
/// - panics: as [`call_under`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`call_under`].
/// - witness: `tests::boundary::the_arguments_apply_in_the_order_passed`
/// - witness: `tests::boundary::a_function_answered_is_not_forced`
/// - witness: `tests::boundary::an_unrunnable_definition_ends_before_a_run`
#[spec(ensures: |ref ret| !matches!(ret.1, Terminal::Ended(Evaluation::Unrunnable(Unrunnable::Undeclared(_)))))]
fn call(
    laid: &'static Laid,
    name: SurfaceName<'_>,
    arguments: &[Integer],
) -> (CoreArena, Terminal<'static>)
{
    let literals: Vec<Literal> = arguments
        .iter()
        .map(|&argument| literal(argument))
        .collect();
    call_under(laid, name, &literals, &mut Declining)
}

#[test]
fn a_definition_answers_the_integer_rust_passes()
{
    for (argument, answer) in [
        (Integer(21), Integer(42)),
        (Integer(-3), Integer(-6)),
        (Integer(0), Integer(0)),
    ] {
        let (arena, terminal) = call(round_trip(), SurfaceName::from("double"), &[argument]);
        assert_eq!(
            returned(&arena, &terminal),
            Some(&Value::Literal(literal(answer))),
            "double({argument:?}): {terminal:?}"
        );
    }
}

#[test]
fn the_arguments_apply_in_the_order_passed()
{
    for (arguments, answer) in [
        ([Integer(19), Integer(7)], Integer(12)),
        ([Integer(7), Integer(19)], Integer(-12)),
    ] {
        let (arena, terminal) = call(round_trip(), SurfaceName::from("less"), &arguments);
        assert_eq!(
            returned(&arena, &terminal),
            Some(&Value::Literal(literal(answer))),
            "less{arguments:?}: {terminal:?}"
        );
    }
}

#[test]
fn a_function_answered_is_not_forced()
{
    let (arena, terminal) = call(round_trip(), SurfaceName::from("adder"), &[Integer(5)]);
    assert!(
        matches!(returned(&arena, &terminal), Some(&Value::Thunk(_))),
        "{terminal:?}"
    );
}

#[test]
fn an_unrunnable_definition_ends_before_a_run()
{
    let (_, terminal) = call(refused(), SurfaceName::from("refused"), &[Integer(1)]);
    assert!(
        matches!(
            terminal,
            Terminal::Ended(Evaluation::Unrunnable(Unrunnable::Refused(name)))
                if name.as_ref() == "refused"
        ),
        "{terminal:?}"
    );
}

#[test]
fn an_extern_operation_is_answered_by_the_rust_caller()
{
    for (argument, answer, received) in [
        (Word(5), Word(20), [
            (Word(5), Word(5)),
            (Word(10), Word(10)),
        ]),
        // Rust's addition wraps where gandr's `Integer` would not.
        (Word(0x8000_0001), Word(4), [
            (Word(0x8000_0001), Word(0x8000_0001)),
            (Word(2), Word(2)),
        ]),
    ] {
        let mut rust = RustSide {
            received: Vec::new(),
        };
        let (arena, terminal) = call_under(
            round_trip(),
            SurfaceName::from("quadrupled"),
            &[word(argument)],
            &mut rust,
        );
        assert_eq!(
            returned(&arena, &terminal),
            Some(&Value::Literal(word(answer))),
            "quadrupled({argument:?}): {terminal:?}"
        );
        assert_eq!(
            rust.received, received,
            "each perform reached Rust with its arguments, in order"
        );
    }
}

#[test]
fn an_extern_operation_no_host_answers_sticks_the_run()
{
    let (_, terminal) = call_under(
        round_trip(),
        SurfaceName::from("quadrupled"),
        &[word(Word(5))],
        &mut Declining,
    );
    assert!(
        matches!(
            terminal,
            Terminal::Ended(Evaluation::Stuck(Stuck::PerformNoHandler(_)))
        ),
        "{terminal:?}"
    );
}

/// A 64-bit word as Rust's memory and gandr's `u64` hold it: an address, a
/// list's word or a cell's contents.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MemoryWord(u64);

/// An element of a list the Rust caller holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Element(i32);

/// The words a Rust caller lends for a call, each read at its own address.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Words<'memory>
{
    /// The words, in address order.
    words: &'memory [u64],
}

impl Words<'_>
{
    /// The address of the first word.
    ///
    /// # Specification
    /// trivial.
    fn base(self) -> MemoryWord
    {
        address(self.words.as_ptr())
    }

    /// The word at `address`, when it is the address of a lent word.
    ///
    /// # Specification
    /// trivial.
    fn at(
        self,
        address: MemoryWord,
    ) -> Option<MemoryWord>
    {
        let offset = address.0.checked_sub(self.base().0)?;
        if !offset.is_multiple_of(8) {
            return None;
        }
        let index = usize::try_from(offset.checked_div(8)?).ok()?;
        self.words.get(index).copied().map(MemoryWord)
    }
}

/// The address of `at`, as a word holds it.
///
/// # Specification
/// trivial.
fn address<T>(at: *const T) -> MemoryWord
{
    MemoryWord(u64::try_from(at.addr()).expect("an address fits a word"))
}

/// `element`'s two's-complement bits, zero-extended to a word.
///
/// # Specification
/// trivial.
fn bits(element: Element) -> MemoryWord
{
    MemoryWord(u64::from(element.0.cast_unsigned()))
}

/// A list laid out in words the Rust caller holds.
struct Held
{
    /// The words, in address order.
    words: Vec<u64>,
    /// The list's word.
    root: MemoryWord,
}

/// `list` laid out tagged in fresh words: a cell per element, its head in the
/// first word and its tail in the second, the empty list the word one.
///
/// # Specification
/// trivial.
fn tagged(list: &[Element]) -> Held
{
    let mut words = vec![0_u64; list.len().saturating_mul(2)];
    let cells: Vec<u64> = words
        .as_chunks::<2>()
        .0
        .iter()
        .map(|cell| address(cell.as_ptr()).0)
        .collect();
    let tails = cells.iter().skip(1).copied().chain(core::iter::once(1_u64));
    for ((cell, &head), tail) in words.as_chunks_mut::<2>().0.iter_mut().zip(list).zip(tails) {
        *cell = [bits(head).0, tail];
    }
    let root = MemoryWord(cells.first().copied().unwrap_or(1_u64));
    Held { words, root }
}

/// `list` laid out packed in fresh words: a cell per pair of elements, both in
/// its first word and the rest in its second, a pointer tagged two, a lone last
/// element inline above the tag one, and the empty list zero.
///
/// # Specification
/// trivial.
fn packed(list: &[Element]) -> Held
{
    let (pairs, lone) = list.as_chunks::<2>();
    let last = lone
        .first()
        .map_or(0_u64, |&element| (bits(element).0 << 2_u32) | 1_u64);
    let mut words = vec![0_u64; pairs.len().saturating_mul(2)];
    let cells: Vec<u64> = words
        .as_chunks::<2>()
        .0
        .iter()
        .map(|cell| address(cell.as_ptr()).0 | 2_u64)
        .collect();
    let rests = cells.iter().skip(1).copied().chain(core::iter::once(last));
    for ((cell, &[x, y]), rest) in words
        .as_chunks_mut::<2>()
        .0
        .iter_mut()
        .zip(pairs)
        .zip(rests)
    {
        *cell = [bits(x).0 | (bits(y).0 << 32_u32), rest];
    }
    let root = MemoryWord(cells.first().copied().unwrap_or(last));
    Held { words, root }
}

/// The length of the tagged list at `root`, walked over `memory` as Rust holds
/// it.
///
/// # Specification
/// trivial.
fn tagged_length(
    memory: Words<'_>,
    root: MemoryWord,
) -> Integer
{
    let mut length = 0_i64;
    let mut at = root.0;
    while at & 1 == 0 {
        length = length.checked_add(1).expect("a short list");
        let tail = at.checked_add(8).expect("a cell's tail has an address");
        at = memory.at(MemoryWord(tail)).expect("a tail word is lent").0;
    }
    Integer(length)
}

/// The length of the packed list at `root`, walked over `memory` as Rust holds
/// it.
///
/// # Specification
/// trivial.
fn packed_length(
    memory: Words<'_>,
    root: MemoryWord,
) -> Integer
{
    let mut length = 0_i64;
    let mut at = root.0;
    loop {
        match at & 3 {
            0 => return Integer(length),
            1 => return Integer(length.checked_add(1).expect("a short list")),
            _ => {
                length = length.checked_add(2).expect("a short list");
                let rest = (at & !3)
                    .checked_add(8)
                    .expect("a cell's rest has an address");
                at = memory.at(MemoryWord(rest)).expect("a rest word is lent").0;
            },
        }
    }
}

/// A layout's writer: a list laid out in fresh words.
type LaysOut = fn(&[Element]) -> Held;

/// A layout's walk: the length of the list at a word, as Rust counts it.
type Counts = fn(Words<'_>, MemoryWord) -> Integer;

/// Rust's `deref_or`, the function the exemplar's `derefOr` states.
///
/// # Specification
/// trivial.
fn deref_or(
    x: Option<&Word>,
    d: Word,
) -> Word
{
    x.copied().unwrap_or(d)
}

/// The word an `Option<&Word>` is: its reference's address, or zero for
/// `None`, as Rust guarantees for `Option<&T>`.
///
/// # Specification
/// trivial.
fn niche(x: Option<&Word>) -> MemoryWord
{
    x.map_or(MemoryWord(0), |reference| {
        address(core::ptr::from_ref(reference))
    })
}

/// The Rust side of `by-layout.gandr`'s `Memory`: a host answering
/// `Memory.word` from the words it lends and `Memory.half` from the `u32`
/// cells it lends, each at its own address, and declining any other address
/// or operation.
struct Lent<'memory>
{
    /// The words `Memory.word` reads.
    words: Words<'memory>,
    /// The cells `Memory.half` reads.
    cells: &'memory [&'memory Word],
}

impl HostHandler for Lent<'_>
{
    type Abort = Infallible;

    /// Answer `Memory.word` and `Memory.half` at a lent address, declining
    /// any other.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Infallible>
    {
        if request.signature.name().as_ref() != "Memory" {
            return HostReply::Decline;
        }
        let read = |at: HeapValueId| match values.value(at) {
            Some(&HeapValue::Literal(Literal::Fixed(FixedInteger::U64(address)))) => {
                Some(MemoryWord(address))
            },
            _ => None,
        };
        let argument = match values.value(request.payload) {
            Some(&HeapValue::Constructed {
                tag: ConstructorTag::Tuple(_),
                ref fields,
            }) => fields.first().copied().and_then(read),
            _ => read(request.payload),
        };
        let Some(address) = argument
        else {
            return HostReply::Decline;
        };
        let answer = match request.operation.as_ref() {
            "word" => self.words.at(address).map(|word| FixedInteger::U64(word.0)),
            "half" => self
                .cells
                .iter()
                .find(|&&cell| niche(Some(cell)) == address)
                .map(|&&cell| FixedInteger::U32(cell.0)),
            _ => None,
        };
        let Some(answer) = answer
        else {
            return HostReply::Decline;
        };
        match values.allocate(HeapValue::Literal(Literal::Fixed(answer))) {
            Ok(at) => HostReply::Resume(at),
            Err(_spent) => HostReply::Decline,
        }
    }
}

#[test]
fn a_list_rust_holds_has_its_length_in_both_layouts()
{
    let lists: [&[i32]; 5] = [&[], &[1], &[1, 2], &[1, 2, 3], &[
        -7,
        0,
        i32::MAX,
        i32::MIN,
        5,
    ]];
    let layouts: [(LaysOut, &str, Counts); 2] = [
        (tagged, "taggedLengthAt", tagged_length),
        (packed, "packedLengthAt", packed_length),
    ];
    for raw in lists {
        let list: Vec<Element> = raw.iter().copied().map(Element).collect();
        for (layout, definition, rust_length) in layouts {
            let held = layout(&list);
            let memory = Words { words: &held.words };
            let rust = rust_length(memory, held.root);
            assert_eq!(
                rust.0,
                i64::try_from(list.len()).expect("a short list"),
                "Rust counts {raw:?} at its {definition}"
            );
            let (arena, terminal) = call_under(
                by_layout(),
                SurfaceName::from(definition),
                &[Literal::Fixed(FixedInteger::U64(held.root.0))],
                &mut Lent {
                    words: memory,
                    cells: &[],
                },
            );
            assert_eq!(
                returned(&arena, &terminal),
                Some(&Value::Literal(literal(rust))),
                "{definition} of {raw:?}: {terminal:?}"
            );
        }
    }
}

#[test]
fn the_null_niche_crosses_as_rust_reads_it()
{
    let (seven, greatest) = (Word(7), Word(u32::MAX));
    for (x, d) in [
        (Some(&seven), Word(0)),
        (None, Word(9)),
        (Some(&greatest), Word(1)),
    ] {
        let (arena, terminal) = call_under(
            by_layout(),
            SurfaceName::from("derefOr"),
            &[Literal::Fixed(FixedInteger::U64(niche(x).0)), word(d)],
            &mut Lent {
                words: Words { words: &[] },
                cells: &[&seven, &greatest],
            },
        );
        assert_eq!(
            returned(&arena, &terminal),
            Some(&Value::Literal(word(deref_or(x, d)))),
            "derefOr({x:?}, {d:?}): {terminal:?}"
        );
    }
}

#[test]
fn an_address_the_rust_caller_did_not_lend_is_not_read()
{
    let (lent, kept) = (Word(7), Word(8));
    let (_, terminal) = call_under(
        by_layout(),
        SurfaceName::from("derefOr"),
        &[
            Literal::Fixed(FixedInteger::U64(niche(Some(&kept)).0)),
            word(Word(0)),
        ],
        &mut Lent {
            words: Words { words: &[] },
            cells: &[&lent],
        },
    );
    assert!(
        matches!(
            terminal,
            Terminal::Ended(Evaluation::Stuck(Stuck::PerformNoHandler(_)))
        ),
        "{terminal:?}"
    );
}
