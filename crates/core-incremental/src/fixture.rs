//! Fixtures the unit tests share: scratch directories and small programs.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FractionDigits;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::NumericLiteral;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use crate::checkpoint::Checkpoints;
use crate::checkpoint::check_program;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;

/// A scratch directory's label, unique among the tests.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Label(pub &'static str);

/// An item key of a fixture.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Key(pub &'static str);

/// An integer literal's decimal digits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Digits(pub &'static str);

/// How many four-family allocation batches precede a fixture's own nodes,
/// so independently built programs can differ in every arena coordinate.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Noise(pub usize);

/// An item's admission position in a fixture program.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Position(pub usize);

/// A scratch path selected using the system temporary directory and a test
/// label. Construction and drop request removal on a best-effort basis;
/// construction does not create the directory.
///
/// # Specification
/// - requires: the label is unique among concurrent tests and the selected path
///   belongs to the calling test.
/// - ensures: the owned path is available to file-store fixtures; cleanup is
///   requested on construction and drop, without a guarantee of success.
/// - executable: none — this declaration has no call boundary; filesystem
///   ownership and whether a removal succeeds are external to the path value.
///
/// # Adequacy
/// - hypothesis: L3 — file-store fixtures create and use separate labelled
///   scratch trees, including a failed write and concurrent publication. Their
///   scope exits execute cleanup, but these witnesses do not observe every
///   cleanup outcome or model hostile filesystem interference.
/// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
/// - witness: `persistence::tests::concurrent_stores_of_one_address_leave_the_record_and_no_temporary`
/// - witness: `session::tests::a_store_failure_retains_the_new_resume_for_the_next_submission`
#[repr(transparent)]
#[derive(Debug)]
pub struct Scratch(PathBuf);

impl Scratch
{
    /// The scratch directory of `label` for this process.
    ///
    /// # Specification
    /// - requires: the label is unique among concurrent tests and the selected
    ///   path belongs to the calling test.
    /// - ensures: the process-labelled scratch path is returned after a removal
    ///   attempt. No directory is created and cleanup failure is not reported.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — labelled paths support real file-store creation and
    ///   publication failures. The predicate observes the borrowed label suffix
    ///   without allocating another path or claiming that cleanup succeeded.
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    /// - witness: `session::tests::a_store_failure_retains_the_new_resume_for_the_next_submission`
    #[spec(
        ensures: |ret| ret.0.as_os_str().as_encoded_bytes().ends_with(label.0.as_bytes()),
    )]
    pub fn new(label: Label) -> Self
    {
        let path = std::env::temp_dir().join(format!(
            "gandr-core-incremental-{}-{}",
            std::process::id(),
            label.0
        ));
        drop(std::fs::remove_dir_all(&path));
        Self(path)
    }

    /// The directory's path.
    ///
    /// # Specification
    /// trivial.
    pub fn path(&self) -> &Path
    {
        &self.0
    }

    /// The names of the directory's entries, sorted.
    ///
    /// # Specification
    /// - requires: the directory and each enumerated entry are readable.
    /// - ensures: the enumerated filenames, converted lossily to text, are
    ///   returned in nondecreasing order; distinct names may map to equal text.
    /// - panics: when enumeration or reading an entry fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — singleton publication results and a directory
    ///   containing staging-name squatters exercise entry collection and the
    ///   ordering predicate. No witness assumes the operating system supplied
    ///   an unsorted enumeration; concurrent directory mutation and non-UTF-8
    ///   names are outside these cases.
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    /// - witness: `persistence::tests::a_store_never_writes_through_a_file_it_did_not_create`
    /// - witness: `persistence::tests::concurrent_stores_of_one_address_leave_the_record_and_no_temporary`
    #[spec(ensures: |ret| ret.iter().zip(ret.iter().skip(1)).all(|(left, right)| left <= right))]
    pub fn entries(&self) -> Vec<String>
    {
        let mut names: Vec<String> = std::fs::read_dir(&self.0)
            .expect("the scratch directory is readable")
            .map(|entry| {
                entry
                    .expect("a readable entry")
                    .file_name()
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
        names.sort();
        names
    }
}

impl Drop for Scratch
{
    /// Request removal of the scratch tree, ignoring cleanup failure.
    ///
    /// # Specification
    /// - requires: the selected path still belongs to this test.
    /// - ensures: removal of the tree is attempted without propagating an
    ///   error; neither absence afterwards nor successful cleanup is promised.
    /// - executable: none — there is no local result distinguishing success
    ///   from refused cleanup, and an extra filesystem operation would not
    ///   observe the original removal attempt without changing its effects.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — scope exit after file-store success and failure
    ///   invokes the destructor on owned scratch trees. Cleanup refusals and a
    ///   concurrent change of ownership remain outside the witnessed filesystem
    ///   class.
    /// - witness: `persistence::tests::concurrent_stores_of_one_address_leave_the_record_and_no_temporary`
    /// - witness: `session::tests::a_store_failure_retains_the_new_resume_for_the_next_submission`
    fn drop(&mut self)
    {
        drop(std::fs::remove_dir_all(&self.0));
    }
}

/// An arena holding `noise` unrelated batches: two values and one node of
/// each other family per batch.
///
/// # Specification
/// - requires: enough resources for the requested allocation batches.
/// - ensures: zero batches leave the arena empty; positive noise changes its
///   watermark. Each batch allocates a unit, a return, a thunk, a unit type and
///   a returner type, subject to the arena's documented id ceiling.
///
/// # Adequacy
/// - hypothesis: L3 — canonical bytes and addresses agree for quiet and noisy
///   arenas, and the former corpus is checked with zero and three batches. The
///   predicate prevents accidentally ignored noise; opaque watermark fields do
///   not expose a per-family census, and the id ceiling is not tested.
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(ensures: |ret| (ret.watermark() == CoreArena::new().watermark()) == (noise.0 == 0))]
pub fn noisy(noise: Noise) -> CoreArena
{
    let mut arena = CoreArena::new();
    for _ in 0 .. noise.0 {
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let _thunk = arena.value_thunk(returned);
        let unit_type = arena.value_type_unit();
        let _returner = arena.comp_type_returner(unit_type);
    }
    arena
}

/// The integer literal of `digits`.
///
/// # Specification
/// - requires: a nonempty sequence of ASCII decimal digits.
/// - ensures: the nonnegative integer with those digits is returned in
///   canonical magnitude form, stripping leading zeros and retaining one zero
///   for an all-zero input.
/// - panics: if the input is empty or contains a non-ASCII-digit character.
///
/// # Adequacy
/// - hypothesis: L3 — the address-change and corpus witnesses use positive
///   decimal strings and distinguish changed literal values. The borrowed
///   postcondition checks their exact canonical magnitude; padded and all-zero
///   spellings are outside this fixture corpus rather than claimed as covered.
/// - witness: `persistence::tests::meaningful_program_changes_and_source_order_change_identity`
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
#[spec(
    requires: !digits.0.is_empty() && digits.0.bytes().all(|byte| byte.is_ascii_digit()),
    ensures: |ret| {
        let canonical = digits.0.trim_start_matches('0');
        match ret {
            | Literal::Integer(ref literal) => {
                literal.sign() == Sign::NonNegative
                    && literal.magnitude().as_ref()
                        == if canonical.is_empty() { "0" } else { canonical }
            },
            | _ => false,
        }
    }
)]
pub fn integer(digits: Digits) -> Literal
{
    Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits"),
    ))
}

/// One declaration at `position`.
///
/// # Specification
/// trivial.
pub fn declaration(
    position: Position,
    signature: Maybe<ValueTypeId, signature::Absent>,
    body: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position.0),
        signature,
        body,
        OriginToken::from(position.0),
    )
}

/// The program of unsigned items `key = digits`, in order, over `arena`.
///
/// # Specification
/// - requires: every digit string is nonempty ASCII decimal text, and the arena
///   has headroom for the appended nodes within its id ceiling.
/// - ensures: keys, nonnegative literal values and input order are preserved;
///   positions and origins enumerate the input from zero, with no signatures.
/// - panics: on malformed digits or failure of the fixed ordering invariant.
///
/// # Adequacy
/// - hypothesis: L3 — changed values, keys, order, deletion and repeated keys
///   have distinct addresses, while unrelated arena allocations preserve them.
///   These finite cases do not exercise padded digits or the arena id ceiling.
/// - witness: `persistence::tests::meaningful_program_changes_and_source_order_change_identity`
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
#[spec(
    requires: entries.iter().all(|&(_, digits)| !digits.0.is_empty() && digits.0.bytes().all(|byte| byte.is_ascii_digit())),
    ensures: |ret| {
        ret.items().len() == entries.len()
        && ret.items().iter().zip(entries).enumerate().all(|(ordinal, (item, &(key, digits)))| {
            let canonical = digits.0.trim_start_matches('0');
            let gandr_core_checker::DeclarationContent::Value { ref signature, ref body } = *item.declaration().content() else { return false; };
            item.key().as_ref() == key.0.as_bytes()
                && usize::from(item.declaration().constant()) == ordinal
                && usize::from(item.declaration().origin()) == ordinal
                && *signature == Maybe::Absent(signature::Absent::Unsigned)
                && match *body {
                    Maybe::Present(id) => matches!(ret.arena().value(id), Some(&gandr_core_term::Value::Literal(Literal::Integer(ref literal))) if literal.sign() == Sign::NonNegative && literal.magnitude().as_ref() == if canonical.is_empty() { "0" } else { canonical }),
                    Maybe::Absent(_) => false,
                }
        })
    }
)]
pub fn integers(
    mut arena: CoreArena,
    entries: &[(Key, Digits)],
) -> Program
{
    let items = entries
        .iter()
        .enumerate()
        .map(|(position, &(key, digits))| {
            let literal = arena.value_literal(integer(digits));
            Item::new(
                ItemKey::from(key.0),
                declaration(
                    Position(position),
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(literal),
                ),
            )
        })
        .collect();
    Program::new(arena, items).expect("positions ascend")
}

/// The checkpoints of a batch run over `program`.
///
/// # Specification
/// - requires: the item order can be allocated; refused declarations remain
///   valid fixture inputs rather than requiring a well-typed program.
/// - ensures: one checkpoint per input item is returned under the default
///   checking budget, with references in the program's source order.
/// - panics: when the order cannot be constructed.
///
/// # Adequacy
/// - hypothesis: L3 — the finite former corpus reaches checked, synthesised,
///   owed and several refusal classes; independently noisy builds serialize
///   identically. The underlying checker and capacity-exhaustion cases are not
///   proved by this batch-fixture wrapper.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
#[spec(ensures: |ret| ret.budget() == CheckBudget::DEFAULT
    && ret.items().len() == program.items().len()
    && ret.items().iter().zip(&program.layout().references).all(|(checkpoint, reference)| checkpoint.content().reference() == reference))]
pub fn checked(program: &mut Program) -> Checkpoints
{
    check_program(program, CheckBudget::DEFAULT)
        .expect("the order builds")
        .checkpoints()
        .clone()
}

/// A finite corpus of core formers and selected verdict and refusal paths,
/// including a reader with structured support, built after `noise` unrelated
/// allocation batches.
///
/// # Specification
/// - requires: the requested noise leaves arena-id headroom for the corpus.
/// - ensures: the fixed data, function, dependent-type, universe, lift, quote
///   and type-operator cases use contiguous admission positions and resolving
///   signature and body roots. It is not a corpus of every possible refusal.
/// - panics: if the fixed small literals, levels or ordering invariant fail.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus reaches the named checked, synthesised, owed
///   and refusal classes and a structured support answer; noisy builds have
///   identical canonical bytes and decode to the same checkpoints. These finite
///   observations do not cover every constructor combination, every checker
///   refusal, arbitrary levels or the arena id ceiling.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
#[spec(ensures: |ret| {
        ret.items().iter().enumerate().all(|(ordinal, item)| {
            let gandr_core_checker::DeclarationContent::Value { ref signature, ref body } = *item.declaration().content() else { return false; };
            usize::from(item.declaration().constant()) == ordinal
                && match *signature {
                    | Maybe::Present(id) => ret.arena().value_type(id).is_some(),
                    | Maybe::Absent(_) => true,
                }
                && match *body {
                    | Maybe::Present(id) => ret.arena().value(id).is_some(),
                    | Maybe::Absent(_) => true,
                }
        })
    })]
pub fn every_former(noise: Noise) -> Program
{
    let mut arena = noisy(noise);
    let unsigned = || Maybe::Absent(signature::Absent::Unsigned);
    let hole = || Maybe::Absent(body::Absent::Hole);
    let mut items: Vec<Item> = Vec::new();
    let mut push = |key: &str, signature, body| {
        let position = items.len();
        items.push(Item::new(
            ItemKey::from(key),
            declaration(Position(position), signature, body),
        ));
    };

    // 0: (Integer × (String + Numeric)) over a pair and an injection: out of
    // the fragment, its content complete.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let string_type = arena.value_type_base(BaseType::String);
    let numeric_type = arena.value_type_base(BaseType::Numeric);
    let sum = arena.value_type_sum(string_type, numeric_type);
    let product = arena.value_type_product(integer_type, sum);
    let negative = arena.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::Negative,
        Magnitude::from_decimal_text(String::from("7")).expect("decimal digits"),
    )));
    let numeric = arena.value_literal(Literal::Numeric(NumericLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(String::from("3")).expect("decimal digits"),
        FractionDigits::from_decimal_text(String::from("25")).expect("decimal digits"),
    )));
    let injected = arena.value_injection(Side::Right, numeric);
    let pair = arena.value_pair(negative, injected);
    push("data", Maybe::Present(product), Maybe::Present(pair));

    // 1: U (Integer → F Integer) checked by λ. return v0.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer_type);
    let arrow = arena.comp_type_arrow(integer_type, returner);
    let function_type = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let function = arena.value_thunk(lambda);
    push(
        "function",
        Maybe::Present(function_type),
        Maybe::Present(function),
    );

    // 2: an unsigned thunk of a bind, a force and an application: refused,
    // its content complete.
    let data = arena.value_constant(ConstantIndex::from(0_usize));
    let function_constant = arena.value_constant(ConstantIndex::from(1_usize));
    let returned = arena.computation_return(data);
    let forced = arena.computation_force(function_constant);
    let argument = arena.value_literal(integer(Digits("4")));
    let applied = arena.computation_application(forced, argument);
    let bind = arena.computation_bind(returned, applied);
    let thunk = arena.value_thunk(bind);
    push("sequence", unsigned(), Maybe::Present(thunk));

    // 3: U (Π (x : 1 + 1). F 1) with a case: the dependent former.
    let unit_type = arena.value_type_unit();
    let unit_sum = arena.value_type_sum(unit_type, unit_type);
    let unit_returner = arena.comp_type_returner(unit_type);
    let pi = arena.comp_type_pi(unit_sum, unit_returner);
    let pi_type = arena.value_type_thunk(pi);
    let scrutinee = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let on_left = arena.computation_return(unit);
    let on_right = arena.computation_return(unit);
    let case = arena.computation_case(scrutinee, on_left, on_right);
    let lambda = arena.computation_lambda(case);
    let case_thunk = arena.value_thunk(lambda);
    push("case", Maybe::Present(pi_type), Maybe::Present(case_thunk));

    // 4: a universe at max(3, v0 + 2, v1), owed.
    let level = Level::constant(LevelConstant::from(3_u64))
        .max(
            &Level::var(LevelVar::new(LevelVarIndex::from(0_u32)))
                .succ()
                .and_then(|level| level.succ())
                .expect("small offsets"),
        )
        .max(&Level::var(LevelVar::new(LevelVarIndex::from(1_u32))));
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), level);
    push("universe", Maybe::Present(universe), hole());

    // 5: a lift of the unit type, by a lifted unit.
    let one = Level::constant(LevelConstant::from(1_u64));
    let unit_type = arena.value_type_unit();
    let lifted_type = arena.value_type_lift(unit_type, one.clone());
    let unit = arena.value_unit();
    let lifted = arena.value_lift(one, unit);
    push("lift", Maybe::Present(lifted_type), Maybe::Present(lifted));

    // 6: El 0 (universe), owed: a type position naming an item.
    let code = arena.value_constant(ConstantIndex::from(4_usize));
    let element = arena.value_type_element(code, Level::zero());
    push("element", Maybe::Present(element), hole());

    // 7: an abstract type named by an item, owed.
    let abstract_type = arena.value_type_abstract(ConstantIndex::from(0_usize));
    push("abstract", Maybe::Present(abstract_type), hole());

    // 8: Integer checked against a string: a mismatch.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let text = arena.value_literal(Literal::Text(StringLiteral::new(String::from("x"))));
    push(
        "mismatch",
        Maybe::Present(integer_type),
        Maybe::Present(text),
    );

    // 9: a constant at no item's position.
    let dangling = arena.value_constant(ConstantIndex::from(99_usize));
    push("unknown", unsigned(), Maybe::Present(dangling));

    // 10: a variable with no binder.
    let free = arena.value_variable(Zone::Linear, DeBruijnIndex::from(2_u32));
    push("unbound", unsigned(), Maybe::Present(free));

    // 11: U (F Integer) checked by forcing a literal: a shape mismatch.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer_type);
    let thunk_type = arena.value_type_thunk(returner);
    let literal = arena.value_literal(integer(Digits("1")));
    let forced = arena.computation_force(literal);
    let thunk = arena.value_thunk(forced);
    push("shape", Maybe::Present(thunk_type), Maybe::Present(thunk));

    // 12: an unsigned hole.
    push("hole", unsigned(), hole());

    // 13: a reader of item 1, synthesising its thunk type from the table.
    let reader = arena.value_constant(ConstantIndex::from(1_usize));
    push("reader", unsigned(), Maybe::Present(reader));

    // 14: Integer, owed.
    let integer_type = arena.value_type_base(BaseType::Integer);
    push("owed", Maybe::Present(integer_type), hole());

    // 15: the computation universe at zero, owed.
    let computation_universe =
        arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    push(
        "computation-universe",
        Maybe::Present(computation_universe),
        hole(),
    );

    // 16: U (El⁻ 0 (computation-universe)), owed: a computation type read off
    // an item.
    let code = arena.value_constant(ConstantIndex::from(15_usize));
    let element = arena.comp_type_element(code, Level::zero());
    let element_thunk = arena.value_type_thunk(element);
    push("computation-element", Maybe::Present(element_thunk), hole());

    // 17: the code of Integer at the value universe.
    let value_universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let integer_type = arena.value_type_base(BaseType::Integer);
    let quote = arena.value_quote(integer_type);
    push(
        "quote",
        Maybe::Present(value_universe),
        Maybe::Present(quote),
    );

    // 18: the code of F Integer at the computation universe.
    let computation_universe =
        arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer_type);
    let quoted = arena.value_quote_computation(returner);
    push(
        "computation-quote",
        Maybe::Present(computation_universe),
        Maybe::Present(quoted),
    );

    // 19: a type operator at the static Pi from the value universe to itself,
    // by the static lambda λA. A.
    let value_universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let operator_type = arena.value_type_static_pi(value_universe, value_universe);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let operator = arena.value_static_lambda(bound);
    push(
        "operator",
        Maybe::Present(operator_type),
        Maybe::Present(operator),
    );

    // 20: the operator at the code of Integer, a static application.
    let operator_constant = arena.value_constant(ConstantIndex::from(19_usize));
    let integer_type = arena.value_type_base(BaseType::Integer);
    let code = arena.value_quote(integer_type);
    let instance = arena.value_static_application(operator_constant, code);
    push("instance", unsigned(), Maybe::Present(instance));

    // 21: the operator at two codes: past its arity.
    let operator_constant = arena.value_constant(ConstantIndex::from(19_usize));
    let integer_type = arena.value_type_base(BaseType::Integer);
    let code = arena.value_quote(integer_type);
    let once = arena.value_static_application(operator_constant, code);
    let twice = arena.value_static_application(once, code);
    push("arity", unsigned(), Maybe::Present(twice));

    // 22: the operator at a literal: an argument of the wrong classifier.
    let operator_constant = arena.value_constant(ConstantIndex::from(19_usize));
    let literal = arena.value_literal(integer(Digits("2")));
    let misapplied = arena.value_static_application(operator_constant, literal);
    push("argument", unsigned(), Maybe::Present(misapplied));

    // 23: U ((Type ⇒ Type) → F 1), owed: a function of an operator.
    let value_universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let operator_type = arena.value_type_static_pi(value_universe, value_universe);
    let unit_type = arena.value_type_unit();
    let unit_returner = arena.comp_type_returner(unit_type);
    let consumer_arrow = arena.comp_type_arrow(operator_type, unit_returner);
    let consumer_type = arena.value_type_thunk(consumer_arrow);
    push("consumer", Maybe::Present(consumer_type), hole());

    // 24: U (F 1) by the consumer at λA. A: a static lambda at a dynamic
    // parameter.
    let unit_type = arena.value_type_unit();
    let unit_returner = arena.comp_type_returner(unit_type);
    let suspended = arena.value_type_thunk(unit_returner);
    let consumer = arena.value_constant(ConstantIndex::from(23_usize));
    let forced = arena.computation_force(consumer);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let identity = arena.value_static_lambda(bound);
    let applied = arena.computation_application(forced, identity);
    let thunk = arena.value_thunk(applied);
    push("dynamic", Maybe::Present(suspended), Maybe::Present(thunk));

    // 25: Integer ⇒ Type, owed: a static Pi over a classifier of no codes.
    let integer_type = arena.value_type_base(BaseType::Integer);
    let value_universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let unclassified = arena.value_type_static_pi(integer_type, value_universe);
    push("classifier", Maybe::Present(unclassified), hole());

    // Native candidates preserve evidence as data; the cache is not admission.
    let unit_type = arena.value_type_unit();
    let code = arena.value_quote(unit_type);
    let path_type = arena.value_type_path_universe(code, code);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let evidence = gandr_kernel_term::PathEvidence {
        source: vec![vec![
            gandr_kernel_term::EvidenceWord(0)
                .try_into()
                .expect("reduce-left word"),
        ]],
        target: vec![vec![], vec![
            gandr_kernel_term::EvidenceWord(0x070C)
                .try_into()
                .expect("premise word"),
        ]],
    };
    let certificate = arena.value_path_equiv(
        path_type,
        identity,
        identity,
        alloc::sync::Arc::new(evidence),
    );
    push(
        "native-path",
        Maybe::Present(path_type),
        Maybe::Present(certificate),
    );
    let reflexivity = arena.value_path_refl(code);
    let path = arena.value_path_product(certificate, reflexivity);
    let unit = arena.value_unit();
    let pair = arena.value_pair(unit, unit);
    let transport = arena.computation_transport(path, pair);
    let thunk = arena.value_thunk(transport);
    let product = arena.value_type_product(unit_type, unit_type);
    let returned = arena.comp_type_returner(product);
    let suspended = arena.value_type_thunk(returned);
    push(
        "native-transport",
        Maybe::Present(suspended),
        Maybe::Present(thunk),
    );

    Program::new(arena, items).expect("positions ascend")
}
