use alloc::string::String;

use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_surface_lowering::Arguments;
use quenchant_shape::shape::Maybe;

use super::Entered;
use super::Entry;
use super::ExitStatus;
use super::argument_list;
use super::program_entry;
use crate::evaluate::Evaluation;
use crate::evaluate::tests::program;

/// The entry is the `main` the source run declares at its top level, with
/// the arguments its type reads; a source with no `main`, and a module's
/// member named `main`, have none (#1881).
#[test]
fn the_entry_is_the_main_of_the_source_run_1881()
{
    for (source, wanted) in [
        (
            "def main() -> -F Integer { return 0 }\n",
            Maybe::Present(Entry {
                constant: ConstantIndex::from(0_usize),
                arguments: Arguments::Unread,
            }),
        ),
        (
            "def one = 1 ;\ndef main(args : List(String)) -> -F Integer { return 0 }\n",
            Maybe::Present(Entry {
                constant: ConstantIndex::from(1_usize),
                arguments: Arguments::Read,
            }),
        ),
        (
            "def one = 1 ;\n",
            Maybe::Absent(program_entry::Absent::Undeclared),
        ),
        (
            "module Tool { def main() -> -F Integer { return 0 } }\n",
            Maybe::Absent(program_entry::Absent::Undeclared),
        ),
    ] {
        assert_eq!(program(source).entry(), wanted, "{source}");
    }
}

/// An entry's integer is the exit status, whether it returns it or exits
/// early with it through `Proc.exit`; one reading its arguments counts them;
/// one reaching a goal ends short of a status (#1881).
#[test]
fn an_entry_runs_to_its_exit_status_1881()
{
    let arguments = [String::from("a"), String::from("b"), String::from("c")];
    for (source, wanted) in [
        ("def main() -> -F Integer { return 3 }\n", 3_u8),
        (
            "def rec count(xs : List(String)) -> -F Integer {\n  case xs {\n    [] => 0,\n    [x, ..rest] => { run n <- count[<](rest); n + 1 }\n  }\n}\ndef main(args : List(String)) -> -F Integer { become count(args) }\n",
            3_u8,
        ),
        (
            "def proc : Cap {exit} ;\ndef main() -> -F [Proc] Integer { proc.exit(7) ; return 0 }\n",
            7_u8,
        ),
    ] {
        let mut ran = program(source);
        let Maybe::Present(entry) = ran.entry()
        else {
            panic!("an entry: {source}");
        };
        assert_eq!(
            ran.enter(entry, &arguments),
            Entered::Exited(ExitStatus(wanted)),
            "{source}"
        );
    }
    let mut goal = program("def main() -> -F Integer { ? }\n");
    let Maybe::Present(entry) = goal.entry()
    else {
        panic!("a goal's `main` is an entry");
    };
    assert!(
        matches!(
            goal.enter(entry, &[]),
            Entered::Ended(Evaluation::Unrunnable(_) | Evaluation::Blamed { .. })
        ),
        "a goal ends the run short of a status"
    );
}

/// The arguments are a list of their strings, the first in the first cell
/// (#1881).
#[test]
fn the_arguments_are_a_list_in_their_order_1881()
{
    let mut core = CoreArena::new();
    let none = argument_list(&mut core, &[]);
    assert_eq!(core.value(none), Some(&Value::ListNil));
    let mut cells = argument_list(&mut core, &[
        String::from("a"),
        String::from("b"),
        String::from("c"),
    ]);
    for wanted in ["a", "b", "c"] {
        let Some(&Value::ListCons(head, tail)) = core.value(cells)
        else {
            panic!("a cell for {wanted}");
        };
        assert_eq!(
            core.value(head),
            Some(&Value::Literal(Literal::Text(StringLiteral::new(
                String::from(wanted)
            ))))
        );
        cells = tail;
    }
    assert_eq!(core.value(cells), Some(&Value::ListNil));
}

/// A status keeps the low byte of the integer, read in two's complement
/// (#1881).
#[test]
fn an_exit_status_keeps_the_low_byte_1881()
{
    for (sign, digits, wanted) in [
        (Sign::NonNegative, "0", 0_u8),
        (Sign::NonNegative, "3", 3_u8),
        (Sign::NonNegative, "255", 255_u8),
        (Sign::NonNegative, "256", 0_u8),
        (Sign::NonNegative, "100000000000000000000000000001", 1_u8),
        (Sign::Negative, "1", 255_u8),
        (Sign::Negative, "256", 0_u8),
    ] {
        let magnitude = Magnitude::from_decimal_text(String::from(digits)).expect("decimal digits");
        let literal = IntegerLiteral::new(sign, magnitude);
        assert_eq!(
            ExitStatus::from(&literal),
            ExitStatus(wanted),
            "{sign:?}{digits}"
        );
    }
}
