//! The reader's witnesses on the host's own toolchain: each symbol of the
//! record is a symbol of the built object, the record agrees with the
//! `define` line that rustc emits for each function, each layout equals
//! what `std.layout` computes, a leaf function has no symbol, each refusal
//! names its cause, and a second request starts no process.

use std::collections::HashMap;
use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use gandr_runtime_rust_record::Absence;
use gandr_runtime_rust_record::Answer;
use gandr_runtime_rust_record::Cache;
use gandr_runtime_rust_record::Discriminant;
use gandr_runtime_rust_record::Extension;
use gandr_runtime_rust_record::Field;
use gandr_runtime_rust_record::Function;
use gandr_runtime_rust_record::FunctionPath;
use gandr_runtime_rust_record::Identity;
use gandr_runtime_rust_record::Layout;
use gandr_runtime_rust_record::Linkage;
use gandr_runtime_rust_record::Origin;
use gandr_runtime_rust_record::Outcome;
use gandr_runtime_rust_record::Part;
use gandr_runtime_rust_record::Passage;
use gandr_runtime_rust_record::Program;
use gandr_runtime_rust_record::Refusal;
use gandr_runtime_rust_record::Request;
use gandr_runtime_rust_record::Shape;
use gandr_runtime_rust_record::TypeName;
use gandr_runtime_rust_record::Unstatable;

/// A test's own cache directory, empty at the start.
fn cache(label: &str) -> (Cache, PathBuf)
{
    let directory =
        std::env::temp_dir().join(format!("gandr-rust-reader-{label}-{}", std::process::id()));
    let _stale = fs::remove_dir_all(&directory);
    (Cache::at(directory.join("cache")), directory)
}

/// The request of the named functions of a fixture, under the build's
/// command line: a library at optimisation level 3, under the v0 mangling,
/// with a `-C metadata` value as Cargo gives, its LLVM IR and its object
/// written to `out`.
fn request(
    fixture: &str,
    functions: &[&str],
    out: &Path,
) -> Request
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(format!("{fixture}.rs"));
    let mut arguments: Vec<OsString> = [
        "--crate-type",
        "lib",
        "--crate-name",
        fixture,
        "--edition",
        "2024",
        "-C",
        "opt-level=3",
        "-C",
        "symbol-mangling-version=v0",
        "-C",
        "metadata=5eed",
        "--emit=llvm-ir,obj",
        "--out-dir",
    ]
    .into_iter()
    .map(OsString::from)
    .collect();
    arguments.push(out.as_os_str().to_owned());
    arguments.push(root.into_os_string());
    Request {
        arguments,
        functions: functions.iter().copied().map(FunctionPath::from).collect(),
    }
}

/// Runs the build of a request with plain `rustc`, word for word.
fn build(
    request: &Request,
    out: &Path,
)
{
    fs::create_dir_all(out).expect("the output directory");
    let status = Command::new("rustc")
        .args(&request.arguments)
        .status()
        .expect("rustc runs");
    assert!(status.success(), "rustc builds the crate");
}

/// The symbols that an object defines, as the toolchain's `llvm-nm` lists
/// them, without the extra underscore of a Mach-O name.
fn defined(object: &Path) -> Vec<String>
{
    let sysroot = Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc runs");
    let sysroot = String::from_utf8(sysroot.stdout).expect("the sysroot is UTF-8");
    let nm = Path::new(sysroot.trim())
        .join("lib/rustlib")
        .join(Identity::of_build().target.as_ref())
        .join("bin/llvm-nm");
    let output = Command::new(nm)
        .args(["--defined-only", "--just-symbol-name"])
        .arg(object)
        .output()
        .expect("llvm-nm runs");
    assert!(output.status.success(), "llvm-nm reads the object");
    String::from_utf8(output.stdout)
        .expect("the symbols are UTF-8")
        .lines()
        .map(|line| match line.strip_prefix('_') {
            Some(rest) if rest.starts_with("_R") => rest.to_owned(),
            Some(_) | None => line.to_owned(),
        })
        .collect()
}

/// The reader that Cargo built for the tests.
fn program() -> Program
{
    Program(PathBuf::from(env!("CARGO_BIN_EXE_gandr-rust-reader")))
}

/// The record's functions, or the test fails with the refusals.
fn read(answer: &Answer) -> &[Function]
{
    match answer.record.outcome {
        Outcome::Read(ref functions) => functions,
        Outcome::Refused(ref refusals) => panic!("the record refuses: {refusals:?}"),
    }
}

/// One LLVM value of a signature: its type, whether it is extended and how,
/// and whether it is the address of a returned aggregate.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Value
{
    ty: String,
    extension: Extension,
    returned: bool,
}

/// A signature as a `define` line spells it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Signature
{
    result: Value,
    parameters: Vec<Value>,
}

/// The extension that a run of attributes names.
fn extension_of(words: &str) -> Extension
{
    if words.split_whitespace().any(|word| word == "zeroext") {
        Extension::Zero
    }
    else if words.split_whitespace().any(|word| word == "signext") {
        Extension::Sign
    }
    else {
        Extension::Plain
    }
}

/// The text up to the first space outside brackets: a type that may hold
/// spaces, as `{ i64, i32 }` or `[2 x i64]`.
fn leading_type(text: &str) -> (&str, &str)
{
    let mut depth = 0_i32;
    for (index, character) in text.char_indices() {
        match character {
            '{' | '[' | '<' | '(' => depth += 1,
            '}' | ']' | '>' | ')' => depth -= 1,
            ' ' if depth == 0 => return (&text[.. index], &text[index ..]),
            _ => {},
        }
    }
    (text, "")
}

/// Splits a parameter list at its top-level commas.
fn parameters(list: &str) -> Vec<&str>
{
    let mut parts = Vec::new();
    let mut depth = 0_i32;
    let mut start = 0;
    for (index, character) in list.char_indices() {
        match character {
            '{' | '[' | '<' | '(' => depth += 1,
            '}' | ']' | '>' | ')' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(list[start .. index].trim());
                start = index + 1;
            },
            _ => {},
        }
    }
    if !list[start ..].trim().is_empty() {
        parts.push(list[start ..].trim());
    }
    parts
}

/// The signature of each `define` line of LLVM IR, by symbol.
fn defines(ir: &str) -> HashMap<String, Signature>
{
    let mut signatures = HashMap::new();
    for line in ir.lines().filter(|line| line.starts_with("define ")) {
        let at = line.find(" @").expect("a define line names its symbol");
        let head = &line["define ".len() .. at];
        let open = line[at ..].find('(').expect("a parameter list") + at;
        let symbol = line[at + 2 .. open].to_owned();
        let mut depth = 0_i32;
        let mut close = open;
        for (index, character) in line[open ..].char_indices() {
            match character {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        close = open + index;
                        break;
                    }
                },
                _ => {},
            }
        }
        let head_words: Vec<&str> = head.split_whitespace().collect();
        let result_ty = (*head_words.last().expect("a result type")).to_owned();
        let result = Value {
            ty: result_ty,
            extension: extension_of(head),
            returned: false,
        };
        let parameters = parameters(&line[open + 1 .. close])
            .into_iter()
            .map(|parameter| {
                let (ty, attributes) = leading_type(parameter);
                Value {
                    ty: ty.to_owned(),
                    extension: extension_of(attributes),
                    returned: attributes.contains("sret("),
                }
            })
            .collect();
        signatures.insert(symbol, Signature { result, parameters });
    }
    signatures
}

/// The signature that the record of a function implies for its `define`
/// line.
fn implied(function: &Function) -> Signature
{
    let value = |part: &Part, returned| Value {
        ty: part.ty.to_string(),
        extension: part.extension,
        returned,
    };
    let mut parameters = Vec::new();
    let result = match function.result.passage {
        Passage::Ignore => Value {
            ty: String::from("void"),
            extension: Extension::Plain,
            returned: false,
        },
        Passage::Direct(ref part) | Passage::Cast(ref part) => value(part, false),
        Passage::Pair(ref first, ref second) => Value {
            ty: format!("{{ {}, {} }}", first.ty, second.ty),
            extension: Extension::Plain,
            returned: false,
        },
        Passage::Indirect(ref part) | Passage::OnStack(ref part) => {
            parameters.push(value(part, true));
            Value {
                ty: String::from("void"),
                extension: Extension::Plain,
                returned: false,
            }
        },
    };
    for argument in &function.arguments {
        match argument.passage {
            Passage::Ignore => {},
            Passage::Direct(ref part)
            | Passage::Cast(ref part)
            | Passage::Indirect(ref part)
            | Passage::OnStack(ref part) => {
                parameters.push(value(part, false));
            },
            Passage::Pair(ref first, ref second) => {
                parameters.push(value(first, false));
                parameters.push(value(second, false));
            },
        }
    }
    Signature { result, parameters }
}

#[test]
fn the_six_agree_with_their_object_and_their_define_lines()
{
    let (cache, directory) = cache("six");
    let out = directory.join("out");
    let six = ["weigh", "pair", "wide", "narrow", "make", "opt"];
    let request = request("six", &six, &out);
    let answer = cache
        .read(&program(), &request, &Identity::of_build())
        .expect("the six read");
    assert!(!out.exists(), "the reader writes no output of the build");
    build(&request, &out);
    let defines = defines(&fs::read_to_string(out.join("six.ll")).expect("the IR"));
    let symbols = defined(&out.join("six.o"));
    let functions = read(&answer);
    assert_eq!(functions.len(), six.len());
    for function in functions {
        let Linkage::Symbol(ref symbol) = function.linkage
        else {
            panic!("{} has a symbol", function.path);
        };
        assert!(
            symbols.iter().any(|defined| defined == symbol.as_ref()),
            "{symbol} is a symbol of the object"
        );
        let define = defines
            .get(symbol.as_ref())
            .unwrap_or_else(|| panic!("{} has a define line under {symbol}", function.path));
        assert_eq!(&implied(function), define, "{}", function.path);
    }
}

#[test]
fn a_leaf_function_has_no_symbol()
{
    let (cache, directory) = cache("leaf");
    let out = directory.join("out");
    let request = request("refused", &["inlined"], &out);
    let answer = cache
        .read(&program(), &request, &Identity::of_build())
        .expect("the leaf reads");
    let leaf = read(&answer).first().expect("one function");
    assert_eq!(leaf.linkage, Linkage::Absent(Absence::Inlined));
    build(&request, &out);
    let symbols = defined(&out.join("refused.o"));
    assert!(
        !symbols
            .iter()
            .any(|symbol| symbol.ends_with("7refused7inlined")),
        "the object holds no symbol of the leaf: {symbols:?}"
    );
}

/// The fields in memory order, as `std.layout` prints them.
fn placed(fields: &[Field]) -> String
{
    let mut order: Vec<&Field> = fields.iter().collect();
    order.sort_by_key(|field| u64::from(field.offset));
    let mut text = String::from("End");
    for field in order.iter().rev() {
        let rest = if text == "End" {
            text.clone()
        }
        else {
            format!("({text})")
        };
        text = format!("At \"{}\" {} {rest}", field.name, field.offset);
    }
    text
}

/// A nested value of `std.layout`'s printed form, in parentheses unless it
/// is a bare constructor.
fn nested(text: &str) -> String
{
    if text.contains(' ') {
        format!("({text})")
    }
    else {
        text.to_owned()
    }
}

/// A layout as `std.layout` prints it.
fn printed(layout: &Layout) -> String
{
    match layout.shape {
        Shape::Struct(ref fields) => format!(
            "Layout {} {} {}",
            layout.size,
            layout.align,
            nested(&placed(fields))
        ),
        Shape::Enum {
            discriminant,
            ref arms,
        } => {
            let discriminant = match discriminant {
                Discriminant::Niche { offset } => format!("(InNiche {offset})"),
                Discriminant::Tag { size, .. } => format!("(Tag {size})"),
                Discriminant::Unneeded => String::from("Unneeded"),
            };
            let mut text = String::from("NoArm");
            for arm in arms.iter().rev() {
                text = format!(
                    "Arm \"{}\" {} {}",
                    arm.name,
                    nested(&placed(&arm.fields)),
                    nested(&text)
                );
            }
            format!(
                "EnumLayout {} {} {discriminant} ({text})",
                layout.size, layout.align
            )
        },
        Shape::Scalar => String::from("Scalar"),
    }
}

/// Each golden of `corpus/model/layouts/rust-default.gandr`, by the name of
/// its definition without `Layout`. The corpus checks each golden against
/// `std.layout`'s run.
fn goldens() -> HashMap<String, String>
{
    let corpus =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/layouts/rust-default.gandr");
    let source = fs::read_to_string(corpus).expect("the corpus source");
    let mut goldens = HashMap::new();
    let mut golden = None;
    for line in source.lines() {
        if let Some(rest) = line.strip_prefix("@[runs(\"") {
            golden = Some(rest.trim_end_matches("\")]").replace("\\\"", "\""));
        }
        else if let Some(rest) = line.strip_prefix("def ")
            && let Some(name) = rest.split("Layout()").next()
            && let Some(text) = golden.take()
        {
            goldens.insert(name.to_owned(), text);
        }
    }
    goldens
}

#[test]
fn the_eleven_layouts_equal_std_layout()
{
    let (cache, directory) = cache("eleven");
    let eleven = [
        ("mixed", "mixed"),
        ("wide", "wide"),
        ("small", "small"),
        ("flagged", "flagged"),
        ("signed", "signed"),
        ("maybe_ref", "maybeRef"),
        ("maybe_flag", "maybeFlag"),
        ("either", "either"),
        ("jagged", "jagged"),
        ("three_ref", "threeRef"),
        ("three_flag", "threeFlag"),
    ];
    let paths: Vec<&str> = eleven.iter().map(|&(path, _)| path).collect();
    let answer = cache
        .read(
            &program(),
            &request("eleven", &paths, &directory.join("out")),
            &Identity::of_build(),
        )
        .expect("the eleven read");
    let goldens = goldens();
    assert_eq!(goldens.len(), eleven.len());
    for (function, (path, golden)) in read(&answer).iter().zip(eleven) {
        assert_eq!(function.path.as_ref(), path);
        let argument = function.arguments.first().expect("one argument");
        let expected = goldens
            .get(golden)
            .unwrap_or_else(|| panic!("{golden} has a golden"));
        assert_eq!(&printed(&argument.layout), expected, "{path}");
        assert_eq!(argument.layout.stride, argument.layout.size, "{path}");
    }
}

#[test]
fn each_refusal_names_its_cause()
{
    let (cache, directory) = cache("refused");
    let request = request(
        "refused",
        &["generic", "private", "array", "absent"],
        &directory.join("out"),
    );
    let answer = cache
        .read(&program(), &request, &Identity::of_build())
        .expect("the refusal reads");
    assert_eq!(
        answer.record.outcome,
        Outcome::Refused(vec![
            Refusal::Generic(FunctionPath::from("generic")),
            Refusal::NotPublic(FunctionPath::from("private")),
            Refusal::Unstated {
                function: FunctionPath::from("array"),
                ty: TypeName::from("[u8; 4]"),
                why: Unstatable::Array
            },
            Refusal::Missing(FunctionPath::from("absent")),
        ])
    );
}

#[test]
fn a_second_request_starts_no_process()
{
    let (cache, directory) = cache("second");
    let request = request("six", &["weigh"], &directory.join("out"));
    let first = cache
        .read(&program(), &request, &Identity::of_build())
        .expect("the first read");
    let second = cache
        .read(&program(), &request, &Identity::of_build())
        .expect("the second read");
    assert_eq!(first.origin, Origin::Process);
    assert_eq!(second, Answer {
        record: first.record,
        origin: Origin::Cache
    });
}
