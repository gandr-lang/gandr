//! The record's witnesses: each entry is read back from its bytes, and each
//! request runs a reader that is a small script.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use std::fs;
use std::path::Path;
use std::path::PathBuf;

use crate::Answer;
use crate::Arm;
use crate::Available;
use crate::Bytes;
use crate::Cache;
use crate::Commit;
use crate::CrateName;
use crate::Digest;
use crate::Discriminant;
use crate::Edition;
use crate::Encoded;
use crate::Entry;
use crate::Exit;
use crate::Extension;
use crate::Field;
use crate::FieldName;
use crate::Function;
use crate::FunctionPath;
use crate::Identity;
use crate::Layout;
use crate::LlvmType;
use crate::Niche;
use crate::Offset;
use crate::Operand;
use crate::Origin;
use crate::Outcome;
use crate::Part;
use crate::Passage;
use crate::Program;
use crate::Record;
use crate::Refusal;
use crate::Request;
use crate::Shape;
use crate::SourceFile;
use crate::SourcePath;
use crate::Status;
use crate::Symbol;
use crate::Target;
use crate::TypeName;
use crate::Undecoded;
use crate::Unread;
use crate::Unstatable;
use crate::VariantName;
use crate::cache::key;

/// The length of the header of the form.
const HEADER: u64 = 18;

/// What names a test's scratch directory.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Label(&'static str);

/// A fresh, empty directory of one test, removed when the test ends.
#[repr(transparent)]
#[derive(Debug)]
struct Scratch(PathBuf);

impl Scratch
{
    /// The empty directory named for `label`.
    ///
    /// # Specification
    /// trivial.
    fn new(label: Label) -> Self
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-runtime-rust-record-{}-{}",
            label.0,
            std::process::id()
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).expect("a stale scratch directory is removed");
        }
        fs::create_dir_all(&directory).expect("the scratch directory is made");
        Self(directory)
    }

    /// The names that a directory of the scratch holds, in order.
    ///
    /// # Specification
    /// trivial.
    fn names(
        &self,
        directory: Label,
    ) -> Vec<String>
    {
        let mut names: Vec<String> = fs::read_dir(self.0.join(directory.0)).map_or_else(
            |_| Vec::new(),
            |entries| {
                entries
                    .map(|entry| {
                        entry
                            .expect("an entry")
                            .file_name()
                            .to_string_lossy()
                            .into_owned()
                    })
                    .collect()
            },
        );
        names.sort();
        names
    }
}

impl Drop for Scratch
{
    /// Removes the directory.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        let _removed: Result<(), std::io::Error> = fs::remove_dir_all(&self.0);
    }
}

/// The identity that each entry of the witnesses holds.
///
/// # Specification
/// trivial.
fn identity() -> Identity
{
    Identity {
        commit: Commit::from("c0ffee"),
        target: Target::from("x86_64-unknown-linux-gnu"),
    }
}

/// A part of a passage.
///
/// # Specification
/// trivial.
fn part(
    ty: Label,
    extension: Extension,
) -> Part
{
    Part {
        ty: LlvmType::from(ty.0),
        extension,
    }
}

/// A field at an offset.
///
/// # Specification
/// trivial.
fn field(
    name: Label,
    offset: Bytes,
) -> Field
{
    Field {
        name: FieldName::from(name.0),
        offset,
    }
}

/// A layout of a scalar of a width with no niche.
///
/// # Specification
/// trivial.
fn scalar(
    ty: Label,
    width: Bytes,
) -> Layout
{
    Layout {
        ty: TypeName::from(ty.0),
        size: width,
        stride: width,
        align: width,
        niche: Niche::None,
        shape: Shape::Scalar,
    }
}

/// An entry whose record reads one function of each passage, each
/// extension, each niche, each shape and each discriminant.
///
/// # Specification
/// trivial.
fn every_read() -> Entry
{
    let eight = Bytes::from(8_u64);
    let zero = Bytes::from(0_u64);
    let wide = Layout {
        ty: TypeName::from("Wide"),
        size: Bytes::from(24_u64),
        stride: Bytes::from(24_u64),
        align: eight,
        niche: Niche::None,
        shape: Shape::Struct(vec![
            field(Label("a"), zero),
            field(Label("b"), eight),
            field(Label("c"), Bytes::from(16_u64)),
        ]),
    };
    let maybe = Layout {
        ty: TypeName::from("MaybeRef<'_>"),
        size: eight,
        stride: eight,
        align: eight,
        niche: Niche::At {
            offset: zero,
            width: eight,
            available: Available::from(1_u128),
        },
        shape: Shape::Enum {
            discriminant: Discriminant::Niche { offset: zero },
            arms: vec![
                Arm {
                    name: VariantName::from("Some"),
                    fields: vec![field(Label("0"), zero)],
                },
                Arm {
                    name: VariantName::from("None"),
                    fields: vec![],
                },
            ],
        },
    };
    let either = Layout {
        ty: TypeName::from("Either"),
        size: eight,
        stride: eight,
        align: Bytes::from(4_u64),
        niche: Niche::At {
            offset: zero,
            width: Bytes::from(2_u64),
            available: Available::from(0xFFFE_u128),
        },
        shape: Shape::Enum {
            discriminant: Discriminant::Tag {
                offset: zero,
                size: Bytes::from(2_u64),
            },
            arms: vec![Arm {
                name: VariantName::from("Left"),
                fields: vec![field(Label("0"), Bytes::from(4_u64))],
            }],
        },
    };
    let single = Layout {
        ty: TypeName::from("Only"),
        size: eight,
        stride: eight,
        align: eight,
        niche: Niche::None,
        shape: Shape::Enum {
            discriminant: Discriminant::Unneeded,
            arms: vec![Arm {
                name: VariantName::from("Only"),
                fields: vec![field(Label("0"), zero)],
            }],
        },
    };
    let function = Function {
        path: FunctionPath::from("inner::each"),
        symbol: Symbol::from("_RNvNtCs1_5probe5inner4each"),
        arguments: vec![
            Operand {
                passage: Passage::Ignore,
                layout: Layout {
                    shape: Shape::Struct(vec![]),
                    ..scalar(Label("()"), zero)
                },
            },
            Operand {
                passage: Passage::Direct(part(Label("i8"), Extension::Zero)),
                layout: scalar(Label("u8"), Bytes::from(1_u64)),
            },
            Operand {
                passage: Passage::Pair(
                    part(Label("i32"), Extension::Plain),
                    part(Label("i64"), Extension::Sign),
                ),
                layout: Layout {
                    shape: Shape::Struct(vec![field(Label("0"), zero), field(Label("1"), eight)]),
                    ..scalar(Label("(i32, i64)"), Bytes::from(16_u64))
                },
            },
            Operand {
                passage: Passage::Cast(part(Label("[2 x i64]"), Extension::Plain)),
                layout: either,
            },
            Operand {
                passage: Passage::Indirect(part(Label("ptr"), Extension::Plain)),
                layout: wide.clone(),
            },
            Operand {
                passage: Passage::OnStack(part(Label("ptr"), Extension::Plain)),
                layout: single,
            },
            Operand {
                passage: Passage::Direct(part(Label("ptr"), Extension::Plain)),
                layout: maybe,
            },
        ],
        result: Operand {
            passage: Passage::Indirect(part(Label("ptr"), Extension::Plain)),
            layout: wide,
        },
    };
    Entry {
        sources: vec![SourceFile {
            path: SourcePath::from("/src/lib.rs"),
            digest: Digest::of(Encoded(b"pub fn each() {}")),
        }],
        record: Record {
            identity: identity(),
            outcome: Outcome::Read(vec![function]),
        },
    }
}

/// An entry whose record refuses with each refusal and each cause.
///
/// # Specification
/// trivial.
fn every_refusal() -> Entry
{
    let unstated = |why| Refusal::Unstated {
        function: FunctionPath::from("u"),
        ty: TypeName::from("[u8; 4]"),
        why,
    };
    Entry {
        sources: vec![],
        record: Record {
            identity: identity(),
            outcome: Outcome::Refused(vec![
                Refusal::Generic(FunctionPath::from("g")),
                Refusal::NotPublic(FunctionPath::from("p")),
                Refusal::Missing(FunctionPath::from("m")),
                Refusal::Inlined(FunctionPath::from("i")),
                unstated(Unstatable::Unsized),
                unstated(Unstatable::Uninhabited),
                unstated(Unstatable::Array),
                unstated(Unstatable::Union),
                unstated(Unstatable::Passage),
            ]),
        },
    }
}

/// The offset of the outcome's tag in an entry with no source.
///
/// # Specification
/// trivial.
fn outcome_offset() -> Offset
{
    let text = |label: &Commit| {
        u64::try_from(label.as_ref().len())
            .expect("a length")
            .checked_add(8)
            .expect("a sum")
    };
    let after_sources = HEADER.checked_add(8).expect("a sum");
    let after_commit = after_sources
        .checked_add(text(&identity().commit))
        .expect("a sum");
    Offset::from(
        after_commit
            .checked_add(text(&Commit::from(identity().target.as_ref())))
            .expect("a sum"),
    )
}

#[test]
fn each_variant_round_trips_through_its_bytes()
{
    for entry in [every_read(), every_refusal()] {
        let bytes = entry.encode();
        let back = Entry::decode(bytes.as_encoded(), &identity()).expect("the bytes read back");
        assert_eq!(back, entry);
        assert_eq!(back.encode(), bytes);
    }
}

#[test]
fn each_proper_prefix_is_truncated()
{
    let bytes = every_read().encode();
    let whole = bytes.as_encoded().0;
    for length in 0 .. whole.len() {
        let prefix = whole.get(.. length).expect("a prefix");
        let refused = Entry::decode(Encoded(prefix), &identity());
        if u64::try_from(length).expect("a length") < HEADER {
            assert_eq!(refused, Err(Undecoded::Header));
        }
        else {
            assert!(
                matches!(refused, Err(Undecoded::Truncated(at)) if u64::from(at) <= u64::try_from(length).expect("a length")),
                "prefix {length}: {refused:?}"
            );
        }
    }
}

#[test]
fn a_byte_past_the_end_is_trailing()
{
    let mut bytes = Vec::from(every_refusal().encode().as_encoded().0);
    let end = Offset::from(u64::try_from(bytes.len()).expect("a length"));
    bytes.push(0);
    assert_eq!(
        Entry::decode(Encoded(&bytes), &identity()),
        Err(Undecoded::Trailing(end))
    );
}

#[test]
fn a_tag_past_its_variants_is_refused_at_its_offset()
{
    let mut bytes = Vec::from(every_refusal().encode().as_encoded().0);
    let at = outcome_offset();
    *bytes
        .get_mut(usize::try_from(u64::from(at)).expect("an offset"))
        .expect("the outcome's tag") = 2;
    assert_eq!(
        Entry::decode(Encoded(&bytes), &identity()),
        Err(Undecoded::Tag(at))
    );
}

#[test]
fn text_that_is_not_utf8_is_refused()
{
    let mut bytes = Vec::from(every_refusal().encode().as_encoded().0);
    let commit = usize::try_from(HEADER + 8).expect("an offset");
    *bytes.get_mut(commit + 8).expect("the commit's first byte") = 0xff;
    assert_eq!(
        Entry::decode(Encoded(&bytes), &identity()),
        Err(Undecoded::Text(Offset::from(HEADER + 8)))
    );
}

#[test]
fn a_count_past_the_bytes_is_truncated()
{
    let mut bytes = Vec::from(every_refusal().encode().as_encoded().0);
    let sources = usize::try_from(HEADER).expect("an offset");
    bytes
        .get_mut(sources .. sources + 8)
        .expect("the count of sources")
        .copy_from_slice(&u64::MAX.to_le_bytes());
    assert_eq!(
        Entry::decode(Encoded(&bytes), &identity()),
        Err(Undecoded::Truncated(Offset::from(HEADER)))
    );
}

#[test]
fn a_refused_outcome_with_no_refusal_is_refused()
{
    let empty = Entry {
        sources: vec![],
        record: Record {
            identity: identity(),
            outcome: Outcome::Refused(vec![]),
        },
    };
    assert_eq!(
        Entry::decode(empty.encode().as_encoded(), &identity()),
        Err(Undecoded::Empty(outcome_offset()))
    );
}

#[test]
fn another_toolchain_or_target_is_refused()
{
    let bytes = every_read().encode();
    let commit = Identity {
        commit: Commit::from("decade"),
        ..identity()
    };
    let target = Identity {
        target: Target::from("riscv64gc-unknown-linux-gnu"),
        ..identity()
    };
    let both = Identity {
        commit: Commit::from("decade"),
        target: Target::from("riscv64gc-unknown-linux-gnu"),
    };
    assert_eq!(
        Entry::decode(bytes.as_encoded(), &commit),
        Err(Undecoded::Toolchain(Commit::from("c0ffee")))
    );
    assert_eq!(
        Entry::decode(bytes.as_encoded(), &target),
        Err(Undecoded::Target(Target::from("x86_64-unknown-linux-gnu")))
    );
    assert_eq!(
        Entry::decode(bytes.as_encoded(), &both),
        Err(Undecoded::Toolchain(Commit::from("c0ffee")))
    );
}

#[test]
fn each_refusal_names_its_function_and_its_cause()
{
    let Outcome::Refused(refusals) = every_refusal().record.outcome
    else {
        panic!("the entry refuses");
    };
    let lines: Vec<String> = refusals
        .iter()
        .map(|refusal| format!("{refusal}"))
        .collect();
    assert_eq!(lines, [
        "`g` is generic: the record states a function with no generic parameter",
        "`p` is not public: no caller outside its crate reaches it",
        "`m` is missing: the crate has no function at this path",
        "`i` is inlined: the build copies it into each caller, so it has no symbol",
        "`u` is unstated: the record does not state `[u8; 4]`, since it has no size",
        "`u` is unstated: the record does not state `[u8; 4]`, since it has no value",
        "`u` is unstated: the record does not state `[u8; 4]`, since it is an array",
        "`u` is unstated: the record does not state `[u8; 4]`, since it is a union",
        "`u` is unstated: the record does not state `[u8; 4]`, since its passage has no form in the record",
    ]);
}

#[test]
fn the_build_identity_is_the_toolchain_of_the_build()
{
    let output = std::process::Command::new("rustc")
        .arg("-vV")
        .output()
        .expect("rustc runs");
    let version = String::from_utf8(output.stdout).expect("the version is UTF-8");
    let field = |name: &str| {
        version
            .lines()
            .find_map(|line| line.strip_prefix(name))
            .map(String::from)
            .expect("the field")
    };
    let build = Identity::of_build();
    assert_eq!(build.commit, Commit::from(field("commit-hash: ")));
    assert_eq!(build.target, Target::from(field("host: ")));
}

/// A reader that is a shell script: it counts its runs in `runs`, then runs
/// `body` with the entry's path in `$GANDR_RUST_RECORD_ENTRY`.
///
/// # Specification
/// trivial.
fn script(
    scratch: &Scratch,
    body: &Script,
) -> Program
{
    use std::os::unix::fs::PermissionsExt as _;

    let path = scratch.0.join("reader.sh");
    let runs = scratch.0.join("runs");
    fs::write(
        &path,
        format!("#!/bin/sh\necho run >> '{}'\n{}\n", runs.display(), body.0),
    )
    .expect("the script is written");
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("the script runs");
    Program(path)
}

/// The text of a script's body.
#[repr(transparent)]
#[derive(Debug)]
struct Script(String);

/// How many times the script of a scratch directory ran.
///
/// # Specification
/// trivial.
fn runs(scratch: &Scratch) -> Vec<String>
{
    fs::read_to_string(scratch.0.join("runs"))
        .unwrap_or_default()
        .lines()
        .map(String::from)
        .collect()
}

/// A request of one function of a root file in the scratch directory, and
/// the entry that a reader of it writes, whose one source is the root.
///
/// # Specification
/// trivial.
fn request_and_entry(scratch: &Scratch) -> (Request, PathBuf)
{
    let root = scratch.0.join("lib.rs");
    fs::write(&root, "pub fn each() {}\n").expect("the root is written");
    let mut entry = every_read();
    entry.sources = vec![SourceFile {
        path: SourcePath::from(root.to_str().expect("a UTF-8 path")),
        digest: Digest::of(Encoded(b"pub fn each() {}\n")),
    }];
    let fixture = scratch.0.join("fixture.entry");
    fs::write(&fixture, entry.encode().as_encoded().0).expect("the fixture is written");
    let request = Request {
        root,
        name: CrateName::from("probe"),
        edition: Edition::E2024,
        functions: vec![FunctionPath::from("inner::each")],
    };
    (request, fixture)
}

/// The script body that copies a fixture to the entry's path.
///
/// # Specification
/// trivial.
fn copying(fixture: &Path) -> Script
{
    Script(format!(
        "cp '{}' \"$GANDR_RUST_RECORD_ENTRY\"",
        fixture.display()
    ))
}

#[test]
fn a_second_request_starts_no_process()
{
    let scratch = Scratch::new(Label("second"));
    let (request, fixture) = request_and_entry(&scratch);
    let program = script(&scratch, &copying(&fixture));
    let cache = Cache::at(scratch.0.join("cache"));
    let first = cache
        .read(&program, &request, &identity())
        .expect("the first read");
    let second = cache
        .read(&program, &request, &identity())
        .expect("the second read");
    assert_eq!(first.origin, Origin::Process);
    assert_eq!(second, Answer {
        record: first.record.clone(),
        origin: Origin::Cache
    });
    assert_eq!(first.record, every_read().record);
    assert_eq!(runs(&scratch), ["run"]);
    let name = key(&program, &request, &identity()).expect("the key");
    assert_eq!(scratch.names(Label("cache")), [name]);
}

#[test]
fn an_edited_source_reads_again()
{
    let scratch = Scratch::new(Label("edited"));
    let (request, fixture) = request_and_entry(&scratch);
    let program = script(&scratch, &copying(&fixture));
    let cache = Cache::at(scratch.0.join("cache"));
    assert_eq!(
        cache
            .read(&program, &request, &identity())
            .expect("the first read")
            .origin,
        Origin::Process
    );
    fs::write(&request.root, "pub fn each() { }\n").expect("the edit");
    assert_eq!(
        cache
            .read(&program, &request, &identity())
            .expect("the second read")
            .origin,
        Origin::Process
    );
    assert_eq!(runs(&scratch), ["run", "run"]);
}

#[test]
fn a_failing_reader_is_failed_and_caches_nothing()
{
    let scratch = Scratch::new(Label("failing"));
    let (request, _fixture) = request_and_entry(&scratch);
    let program = script(
        &scratch,
        &Script(String::from("echo 'error: no crate' >&2\nexit 3")),
    );
    let cache = Cache::at(scratch.0.join("cache"));
    assert_eq!(
        cache.read(&program, &request, &identity()),
        Err(Unread::Failed {
            exit: Exit::Status(Status::from(3_i32)),
            diagnostics: String::from("error: no crate\n")
        })
    );
    assert_eq!(scratch.names(Label("cache")), Vec::<String>::new());
}

#[test]
fn a_silent_reader_is_absent()
{
    let scratch = Scratch::new(Label("silent"));
    let (request, _fixture) = request_and_entry(&scratch);
    let program = script(&scratch, &Script(String::from("exit 0")));
    let cache = Cache::at(scratch.0.join("cache"));
    assert_eq!(
        cache.read(&program, &request, &identity()),
        Err(Unread::Absent)
    );
    assert_eq!(scratch.names(Label("cache")), Vec::<String>::new());
}

#[test]
fn a_truncated_entry_is_refused_and_caches_nothing()
{
    let scratch = Scratch::new(Label("truncated"));
    let (request, fixture) = request_and_entry(&scratch);
    let program = script(
        &scratch,
        &Script(format!(
            "head -c 40 '{}' > \"$GANDR_RUST_RECORD_ENTRY\"",
            fixture.display()
        )),
    );
    let cache = Cache::at(scratch.0.join("cache"));
    assert!(matches!(
        cache.read(&program, &request, &identity()),
        Err(Unread::Entry(Undecoded::Truncated(_)))
    ));
    assert_eq!(scratch.names(Label("cache")), Vec::<String>::new());
}

#[test]
fn an_entry_of_another_toolchain_is_refused()
{
    let scratch = Scratch::new(Label("toolchain"));
    let (request, fixture) = request_and_entry(&scratch);
    let program = script(&scratch, &copying(&fixture));
    let cache = Cache::at(scratch.0.join("cache"));
    let other = Identity {
        commit: Commit::from("decade"),
        ..identity()
    };
    assert_eq!(
        cache.read(&program, &request, &other),
        Err(Unread::Entry(Undecoded::Toolchain(Commit::from("c0ffee"))))
    );
    assert_eq!(scratch.names(Label("cache")), Vec::<String>::new());
}

#[test]
fn each_part_of_the_key_changes_the_name()
{
    let scratch = Scratch::new(Label("key"));
    let (request, fixture) = request_and_entry(&scratch);
    let program = script(&scratch, &copying(&fixture));
    let base = key(&program, &request, &identity()).expect("the key");
    assert_eq!(key(&program, &request, &identity()).expect("the key"), base);
    let changed = [
        key(&program, &request, &Identity {
            commit: Commit::from("decade"),
            ..identity()
        }),
        key(&program, &request, &Identity {
            target: Target::from("aarch64-apple-darwin"),
            ..identity()
        }),
        key(
            &program,
            &Request {
                root: scratch.0.join("main.rs"),
                ..request.clone()
            },
            &identity(),
        ),
        key(
            &program,
            &Request {
                name: CrateName::from("other"),
                ..request.clone()
            },
            &identity(),
        ),
        key(
            &program,
            &Request {
                edition: Edition::E2021,
                ..request.clone()
            },
            &identity(),
        ),
        key(
            &program,
            &Request {
                functions: vec![FunctionPath::from("each")],
                ..request.clone()
            },
            &identity(),
        ),
    ];
    for name in changed {
        assert_ne!(name.expect("the key"), base);
    }
    fs::write(&program.0, "#!/bin/sh\nexit 0\n").expect("the program changes size");
    assert_ne!(key(&program, &request, &identity()).expect("the key"), base);
}
