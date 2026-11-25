use gandr_workflow_twin_census::CensusError;
use gandr_workflow_twin_census::Workspace;
use gandr_workflow_twin_census::rustdoc::Carry;
use gandr_workflow_twin_census::rustdoc::Entry;
use gandr_workflow_twin_census::rustdoc::Surface;
use gandr_workflow_twin_census::rustdoc::read;
use gandr_workflow_twin_census::test_names;

/// The metadata of a workspace of five crates: the emitter reaches `near` by
/// a normal edge and `far` by a build edge of `near`; it reaches `tested` by a
/// dev edge alone; `apart` has no edge. `outside` is a package of no member.
/// `tested` has a binary and no library.
const METADATA: &str = r#"{
  "packages": [
    {"id": "e", "name": "gandr-runtime-emitter", "manifest_path": "/w/crates/runtime-emitter/Cargo.toml", "targets": [{"kind": ["lib"], "name": "gandr-runtime-emitter"}]},
    {"id": "n", "name": "gandr-near", "manifest_path": "/w/crates/near/Cargo.toml", "targets": [{"kind": ["lib"], "name": "gandr-near"}, {"kind": ["test"], "name": "tests"}]},
    {"id": "f", "name": "gandr-far", "manifest_path": "/w/crates/far/Cargo.toml", "targets": [{"kind": ["proc-macro"], "name": "gandr-far"}]},
    {"id": "t", "name": "gandr-tested", "manifest_path": "/w/crates/tested/Cargo.toml", "targets": [{"kind": ["bin"], "name": "tested"}]},
    {"id": "a", "name": "gandr-apart", "manifest_path": "/w/crates/apart/Cargo.toml", "targets": [{"kind": ["lib"], "name": "gandr-apart"}]},
    {"id": "o", "name": "outside", "manifest_path": "/r/outside/Cargo.toml", "targets": [{"kind": ["lib"], "name": "outside"}]}
  ],
  "workspace_members": ["e", "n", "f", "t", "a"],
  "target_directory": "/w/target",
  "resolve": {"nodes": [
    {"id": "e", "deps": [
      {"pkg": "n", "dep_kinds": [{"kind": null}]},
      {"pkg": "t", "dep_kinds": [{"kind": "dev"}]},
      {"pkg": "o", "dep_kinds": [{"kind": null}]}
    ]},
    {"id": "n", "deps": [{"pkg": "f", "dep_kinds": [{"kind": "build"}]}]},
    {"id": "f", "deps": []},
    {"id": "t", "deps": []},
    {"id": "a", "deps": [{"pkg": "e", "dep_kinds": [{"kind": null}]}]},
    {"id": "o", "deps": []}
  ]}
}"#;

/// The census of [`METADATA`], with the counts of the libraries that
/// [`a_crate_under_the_emitter_is_marked_and_a_dev_edge_is_not`] puts in.
const CENSUS: &str = "# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

An item is generic when it has a type parameter or a trait bound. An entry under the C convention carries neither, so a generic item has no twin without a wrapper. The column counts the public functions, methods, types, traits and type aliases of the crate's library that are generic.

An export carries a function that is not generic, whose operands are fixed-width integers or addresses, and whose result is one of the two. A fixed-width integer is `u8` to `u64`, `i8` to `i64`, `usize` or `isize`. An address is a reference or a raw pointer to a sized type. The column gives the count of such public functions and methods, of the count of all, and its share.

`twin-census` prints this text from `cargo metadata` and from the JSON that rustdoc writes for each library.

| Crate | Under the emitter | Generic items | Export fragment |
| ----- | ----------------- | ------------- | --------------- |
| `apart` | no | 0 | 0 of 0 |
| `far` | yes | 2 | 1 of 4 (25 %) |
| `near` | yes | 1 | 3 of 3 (100 %) |
| `runtime-emitter` | the emitter | 3 | 0 of 10 (0 %) |
| `tested` | no | no library | no library |

Crates under the emitter: 2 of 5.

Generic public items: 6.

Public functions in the export fragment: 4 of 17 (23 %).

## The next twins

A crate can take a twin when it has a test, and each of its public functions is in the export fragment or has a wrapper. A wrapper passes each operand as its words and gives the result as its words. A result of more than one word goes to an address that the caller gives. The census ranks such crates by the fewest generic public items, then by the most functions in the fragment, then by the most tests, and names the first 3.

Crates that can take a twin: 0.
";

/// The emitter reaches a crate by a normal edge and through a build edge of
/// another crate. A dev edge, a crate that depends on the emitter, and a
/// package outside the workspace are no row under it.
#[test]
fn a_crate_under_the_emitter_is_marked_and_a_dev_edge_is_not()
{
    let mut workspace = Workspace::read(METADATA.as_bytes()).expect("the metadata reads");
    assert_eq!(
        workspace.counts(),
        (2, 5),
        "two of five crates are under the emitter"
    );
    assert_eq!(
        workspace.libraries().collect::<Vec<_>>(),
        [
            ("apart", "gandr_apart"),
            ("far", "gandr_far"),
            ("near", "gandr_near"),
            ("runtime-emitter", "gandr_runtime_emitter")
        ],
        "each crate with a library, a procedural macro too, names its file"
    );
    assert_eq!(
        workspace.target_directory(),
        "/w/target",
        "the target directory is Cargo's"
    );
    assert!(
        workspace
            .render()
            .contains("| `near` | yes | not read | not read |"),
        "a library with no count is not read"
    );
    for (name, generic_items, functions, exportable) in [
        ("apart", 0, 0, 0),
        ("far", 2, 4, 1),
        ("near", 1, 3, 3),
        ("runtime-emitter", 3, 10, 0),
        ("outside", 9, 9, 9),
    ] {
        workspace.set_surface(name, Surface {
            generic_items,
            functions,
            exportable,
            entries: Vec::new(),
        });
    }
    assert_eq!(workspace.render(), CENSUS, "the census is its golden");
}

/// The JSON of rustdoc for a crate with one item of each case. Items 1, 2,
/// 3, 4 and 6 are generic public items; each other item is not. Items 1, 2
/// and 6 are its public functions, and no one has a result.
const RUSTDOC: &str = r#"{
  "format_version": 61,
  "index": {
    "1": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [], "output": null}, "generics": {"params": [{"name": "T", "kind": {"type": {"bounds": [], "default": null, "is_synthetic": false}}}], "where_predicates": []}}}},
    "2": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [], "output": null}, "generics": {"params": [{"name": "impl Read", "kind": {"type": {"bounds": [], "default": null, "is_synthetic": true}}}], "where_predicates": []}}}},
    "3": {"crate_id": 0, "visibility": "public", "inner": {"struct": {"kind": "unit", "generics": {"params": [], "where_predicates": [{"bound_predicate": {"type": {}, "bounds": [{"trait_bound": {}}], "generic_params": []}}]}, "impls": []}}},
    "4": {"crate_id": 0, "visibility": "public", "inner": {"trait": {"is_auto": false, "items": [], "generics": {"params": [], "where_predicates": []}, "bounds": [{"trait_bound": {}}]}}},
    "5": {"crate_id": 0, "visibility": "default", "inner": {"impl": {"generics": {"params": [{"name": "T", "kind": {"type": {}}}], "where_predicates": []}, "trait": null, "for": {}, "items": [6, 7]}}},
    "6": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [], "output": null}, "generics": {"params": [], "where_predicates": []}}}},
    "7": {"crate_id": 0, "visibility": {"restricted": {"parent": 0, "path": "::a"}}, "inner": {"function": {"sig": {"inputs": [], "output": null}, "generics": {"params": [], "where_predicates": []}}}},
    "8": {"crate_id": 0, "visibility": "public", "inner": {"enum": {"generics": {"params": [{"name": "'a", "kind": {"lifetime": {"outlives": []}}}, {"name": "N", "kind": {"const": {"type": {}, "default": null}}}], "where_predicates": [{"lifetime_predicate": {}}, {"bound_predicate": {"type": {}, "bounds": [{"outlives": "'a"}], "generic_params": []}}]}, "variants": [], "has_stripped_variants": false}}},
    "9": {"crate_id": 0, "visibility": "default", "inner": {"impl": {"generics": {"params": [{"name": "T", "kind": {"type": {}}}], "where_predicates": []}, "trait": {"path": "Clone"}, "for": {}, "items": [10]}}},
    "10": {"crate_id": 0, "visibility": "default", "inner": {"function": {"sig": {"inputs": [], "output": null}, "generics": {"params": [{"name": "U", "kind": {"type": {}}}], "where_predicates": []}}}},
    "11": {"crate_id": 0, "visibility": "crate", "inner": {"type_alias": {"type": {}, "generics": {"params": [{"name": "T", "kind": {"type": {}}}], "where_predicates": []}}}},
    "12": {"crate_id": 1, "visibility": "public", "inner": {"union": {"generics": {"params": [{"name": "T", "kind": {"type": {}}}], "where_predicates": []}}}},
    "13": {"crate_id": 0, "visibility": "public", "inner": "extern_type"},
    "14": {"crate_id": 0, "visibility": "public", "inner": {"module": {"is_crate": true, "items": [1, 2]}}}
  },
  "paths": {}
}"#;

/// A type parameter, an `impl Trait` parameter, a `where` bound, a
/// supertrait and a method of a generic inherent implementation each count. A
/// lifetime and a const parameter, a lifetime bound, a method of a trait
/// implementation, a restricted and a crate item, an item of a different
/// crate, a kind with no content and a module do not.
#[test]
fn a_generic_public_item_counts_and_each_other_item_does_not()
{
    let surface = read(RUSTDOC.as_bytes()).expect("the JSON reads");
    assert_eq!(
        (surface.generic_items, surface.functions, surface.exportable),
        (5, 3, 0),
        "items 1, 2, 3, 4 and 6 are generic, of three public functions"
    );
}

/// The JSON of rustdoc for a crate of public functions, each with one case
/// of an operand or a result. Items 1, 2 and 8 are in the export fragment.
const SIGNATURES: &str = r#"{
  "format_version": 61,
  "index": {
    "1": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "u64"}], ["b", {"primitive": "i8"}]], "output": {"primitive": "usize"}}, "generics": {"params": [], "where_predicates": []}}}},
    "2": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["self", {"borrowed_ref": {"lifetime": null, "is_mutable": false, "type": {"generic": "Self"}}}], ["p", {"raw_pointer": {"is_mutable": false, "type": {"primitive": "u8"}}}]], "output": {"raw_pointer": {"is_mutable": true, "type": {"resolved_path": {"path": "Place", "id": 20, "args": null}}}}}, "generics": {"params": [], "where_predicates": []}}}},
    "3": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["bytes", {"borrowed_ref": {"lifetime": null, "is_mutable": false, "type": {"slice": {"primitive": "u8"}}}}]], "output": {"primitive": "u64"}}, "generics": {"params": [], "where_predicates": []}}}},
    "4": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["text", {"borrowed_ref": {"lifetime": null, "is_mutable": false, "type": {"primitive": "str"}}}]], "output": {"primitive": "u64"}}, "generics": {"params": [], "where_predicates": []}}}},
    "5": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "u64"}]], "output": null}, "generics": {"params": [], "where_predicates": []}}}},
    "6": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "u64"}]], "output": {"resolved_path": {"path": "Place", "id": 20, "args": null}}}, "generics": {"params": [], "where_predicates": []}}}},
    "7": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "u64"}]], "output": {"primitive": "u64"}}, "generics": {"params": [{"name": "T", "kind": {"type": {}}}], "where_predicates": []}}}},
    "8": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"borrowed_ref": {"lifetime": null, "is_mutable": false, "type": {"borrowed_ref": {"lifetime": null, "is_mutable": false, "type": {"dyn_trait": {"traits": [], "lifetime": null}}}}}}]], "output": {"primitive": "u8"}}, "generics": {"params": [], "where_predicates": []}}}},
    "9": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "bool"}]], "output": {"primitive": "u64"}}, "generics": {"params": [], "where_predicates": []}}}},
    "10": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "u128"}]], "output": {"primitive": "u64"}}, "generics": {"params": [], "where_predicates": []}}}},
    "11": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"borrowed_ref": {"lifetime": null, "is_mutable": false, "type": {"dyn_trait": {"traits": [], "lifetime": null}}}}], ["b", "infer"]], "output": {"primitive": "u32"}}, "generics": {"params": [], "where_predicates": []}}}}
  },
  "paths": {}
}"#;

/// Integers of each fixed width, a reference to `Self`, raw pointers to a
/// sized type, and a reference to a reference are in the export fragment. A
/// reference to a slice, to `str` or to a trait object, a function with no
/// result or with a result of a type of the crate, a generic function, `bool`
/// and `u128` are not.
#[test]
fn an_export_carries_integers_and_addresses_of_sized_types()
{
    let surface = read(SIGNATURES.as_bytes()).expect("the JSON reads");
    assert_eq!(
        (surface.generic_items, surface.functions, surface.exportable),
        (1, 11, 3),
        "items 1, 2 and 8 are in the fragment, and item 7 is generic"
    );
}

/// The JSON of rustdoc for a crate whose functions take and give its own
/// types: a structure of an address and a length, a tuple structure, an
/// enumeration, an alias, a structure with a stripped field, and `Ordering`,
/// `Option`, `Result` and `Vec` of other crates.
const TYPES: &str = r#"{
  "format_version": 61,
  "index": {
    "20": {"crate_id": 0, "name": "Place", "visibility": "public", "inner": {"struct": {"kind": {"plain": {"fields": [21, 22], "has_stripped_fields": false}}, "generics": {"params": [], "where_predicates": []}, "impls": [50]}}},
    "21": {"crate_id": 0, "name": "base", "visibility": "public", "inner": {"struct_field": {"raw_pointer": {"is_mutable": true, "type": {"primitive": "u8"}}}}},
    "22": {"crate_id": 0, "name": "length", "visibility": "public", "inner": {"struct_field": {"resolved_path": {"path": "Length", "id": 23, "args": null}}}},
    "23": {"crate_id": 0, "name": "Length", "visibility": "public", "inner": {"struct": {"kind": {"tuple": [24]}, "generics": {"params": [], "where_predicates": []}, "impls": []}}},
    "24": {"crate_id": 0, "name": "0", "visibility": "public", "inner": {"struct_field": {"primitive": "usize"}}},
    "25": {"crate_id": 0, "name": "Found", "visibility": "public", "inner": {"enum": {"generics": {"params": [], "where_predicates": []}, "variants": [26, 27], "has_stripped_variants": false, "impls": []}}},
    "26": {"crate_id": 0, "name": "At", "visibility": "default", "inner": {"variant": {"kind": {"tuple": [28]}, "discriminant": null}}},
    "27": {"crate_id": 0, "name": "Absent", "visibility": "default", "inner": {"variant": {"kind": "plain", "discriminant": null}}},
    "28": {"crate_id": 0, "name": "0", "visibility": "default", "inner": {"struct_field": {"resolved_path": {"path": "Length", "id": 23, "args": null}}}},
    "29": {"crate_id": 0, "name": "Outcome", "visibility": "public", "inner": {"type_alias": {"type": {"resolved_path": {"path": "Found", "id": 25, "args": null}}, "generics": {"params": [], "where_predicates": []}}}},
    "30": {"crate_id": 0, "name": "Hidden", "visibility": "public", "inner": {"struct": {"kind": {"plain": {"fields": [], "has_stripped_fields": true}}, "generics": {"params": [], "where_predicates": []}, "impls": []}}},
    "50": {"crate_id": 0, "name": null, "visibility": "default", "inner": {"impl": {"generics": {"params": [], "where_predicates": []}, "trait": null, "for": {"resolved_path": {"path": "Place", "id": 20, "args": null}}, "items": [8]}}},
    "1": {"crate_id": 0, "name": "copy", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["to", {"resolved_path": {"path": "Place", "id": 20, "args": null}}], ["from", {"resolved_path": {"path": "crate::Place", "id": 20, "args": null}}]], "output": {"resolved_path": {"path": "Found", "id": 25, "args": null}}}, "generics": {"params": [], "where_predicates": []}}}},
    "2": {"crate_id": 0, "name": "check", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["flag", {"primitive": "bool"}]], "output": null}, "generics": {"params": [], "where_predicates": []}}}},
    "3": {"crate_id": 0, "name": "compare", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"resolved_path": {"path": "Place", "id": 20, "args": null}}]], "output": {"resolved_path": {"path": "core::cmp::Ordering", "id": 40, "args": null}}}, "generics": {"params": [], "where_predicates": []}}}},
    "4": {"crate_id": 0, "name": "find", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "u64"}]], "output": {"resolved_path": {"path": "Option", "id": 41, "args": {"angle_bracketed": {"args": [{"type": {"resolved_path": {"path": "Length", "id": 23, "args": null}}}], "constraints": []}}}}}, "generics": {"params": [], "where_predicates": []}}}},
    "5": {"crate_id": 0, "name": "alias", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "u64"}]], "output": {"resolved_path": {"path": "Outcome", "id": 29, "args": null}}}, "generics": {"params": [], "where_predicates": []}}}},
    "6": {"crate_id": 0, "name": "hidden", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"resolved_path": {"path": "Hidden", "id": 30, "args": null}}]], "output": {"primitive": "u64"}}, "generics": {"params": [], "where_predicates": []}}}},
    "7": {"crate_id": 0, "name": "vec", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"resolved_path": {"path": "Vec", "id": 42, "args": {"angle_bracketed": {"args": [{"type": {"primitive": "u8"}}], "constraints": []}}}}]], "output": {"primitive": "u64"}}, "generics": {"params": [], "where_predicates": []}}}},
    "8": {"crate_id": 0, "name": "length", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["self", {"borrowed_ref": {"lifetime": null, "is_mutable": false, "type": {"generic": "Self"}}}]], "output": {"primitive": "usize"}}, "generics": {"params": [], "where_predicates": []}}}},
    "9": {"crate_id": 0, "name": "result", "visibility": "public", "inner": {"function": {"sig": {"inputs": [["a", {"primitive": "u64"}]], "output": {"resolved_path": {"path": "Result", "id": 43, "args": {"angle_bracketed": {"args": [{"type": {"primitive": "u64"}}, {"type": {"resolved_path": {"path": "Found", "id": 25, "args": null}}}], "constraints": []}}}}}, "generics": {"params": [], "where_predicates": []}}}}
  },
  "paths": {
    "40": {"crate_id": 1, "path": ["core", "cmp", "Ordering"], "kind": "enum"},
    "41": {"crate_id": 1, "path": ["core", "option", "Option"], "kind": "enum"},
    "42": {"crate_id": 2, "path": ["alloc", "vec", "Vec"], "kind": "struct"},
    "43": {"crate_id": 1, "path": ["core", "result", "Result"], "kind": "enum"}
  }
}"#;

/// A wrapper passes a structure as the words of its fields, an enumeration
/// as a tag word and its widest variant, an alias as the type that it names,
/// `bool` as one word, `()` as no word, `Ordering` as one word, and `Option`
/// and `Result` as a tag word and the widest argument. A structure with a
/// stripped field and `Vec` have no words. A method has the name of its type.
#[test]
fn a_wrapper_passes_the_words_of_each_type_of_the_crate()
{
    let surface = read(TYPES.as_bytes()).expect("the JSON reads");
    let carries: Vec<(&str, Carry)> = surface
        .entries
        .iter()
        .map(|entry| (entry.name.as_str(), entry.carry.clone()))
        .collect();
    let wrapper = |operands, result| Carry::Wrapper { operands, result };
    assert_eq!(
        carries,
        [
            ("Place::length", Carry::Fragment),
            ("alias", wrapper(1, 2)),
            ("check", wrapper(1, 0)),
            ("compare", wrapper(2, 1)),
            ("copy", wrapper(4, 2)),
            ("find", wrapper(1, 2)),
            (
                "hidden",
                Carry::Refused(String::from("`Hidden` has no words"))
            ),
            ("result", wrapper(1, 3)),
            ("vec", Carry::Refused(String::from("`Vec` has no words"))),
        ],
        "each function has the words of its types"
    );
}

/// An entry that an export carries, and an entry that it refuses.
///
/// # Specification
/// trivial.
fn entry(
    name: &str,
    carry: Carry,
) -> Entry
{
    Entry {
        name: String::from(name),
        carry,
    }
}

/// Four crates can take a twin, in the order of their generic items, of
/// their functions in the fragment and of their tests. A crate with a refused
/// function, a crate with no test and a crate with no function cannot.
#[test]
fn the_next_twins_are_ranked_by_generic_items_fragment_and_tests()
{
    let mut workspace = Workspace::read(METADATA.as_bytes()).expect("the metadata reads");
    let carried = vec![
        entry("copy", Carry::Wrapper {
            operands: 4,
            result: 2,
        }),
        entry("length", Carry::Fragment),
    ];
    for (name, generic_items, exportable, tests) in [
        ("apart", 0, 1, 2),
        ("far", 0, 2, 1),
        ("near", 1, 2, 5),
        ("runtime-emitter", 0, 2, 3),
    ] {
        workspace.set_surface(name, Surface {
            generic_items,
            functions: 2,
            exportable,
            entries: carried.clone(),
        });
        workspace.set_tests(name, vec![String::from("a_test"); tests]);
    }
    workspace.set_surface("tested", Surface {
        generic_items: 0,
        functions: 1,
        exportable: 0,
        entries: vec![entry(
            "vec",
            Carry::Refused(String::from("`Vec` has no words")),
        )],
    });
    workspace.set_tests("tested", vec![String::from("a_test")]);
    assert_eq!(
        workspace.candidates(),
        ["runtime-emitter", "far", "apart", "near"],
        "the order is generic items, then the fragment, then the tests"
    );
    let text = workspace.render();
    assert!(
        text.contains(
            "Crates that can take a twin: 4.\n\n### 1. `runtime-emitter`\n\nThe carrier is the \
             object, because the crate is the emitter.\n\n| Function | What an export needs |\n| \
             -------- | -------------------- |\n| `copy` | a wrapper: 4 words in, 2 words out, at \
             an address |\n| `length` | nothing |\n\nTests: 3. `a_test`, `a_test`, `a_test`.\n"
        ),
        "the first twin has its functions and its tests: {text}"
    );
    assert!(
        text.contains("### 3. `apart`\n\nThe carrier is the object, or the record")
            && !text.contains("### 4."),
        "three crates are named: {text}"
    );
    workspace.set_tests("near", Vec::new());
    workspace.set_surface("apart", Surface::default());
    assert_eq!(
        workspace.candidates(),
        ["runtime-emitter", "far"],
        "a crate with no test or no function cannot take a twin"
    );
}

/// Each function after `#[test]` is a test, after a second attribute too. A
/// function with no attribute and an attribute in a comment are not.
#[test]
fn each_function_after_a_test_attribute_is_a_test()
{
    let source = "fn helper() {}\n#[test]\nfn first() {}\n// #[test]\nfn commented() {}\n    \
                  #[test]\n    #[should_panic]\n    fn second_one() {}\n";
    assert_eq!(
        test_names(source),
        ["first", "second_one"],
        "two tests, in order"
    );
}

/// A file of a different format of rustdoc names its format, and a text that
/// is not JSON is refused as rustdoc's JSON.
#[test]
fn rustdoc_of_another_format_or_no_json_is_refused_by_name()
{
    let other = RUSTDOC.replace("\"format_version\": 61", "\"format_version\": 62");
    assert_eq!(
        read(other.as_bytes()),
        Err(CensusError::RustdocFormat { found: 62 }),
        "the format is named"
    );
    assert!(
        matches!(read(b"not json"), Err(CensusError::Rustdoc { .. })),
        "a text that is not JSON is refused"
    );
}

/// A text that is not JSON, and a workspace with no emitter, are each refused
/// by name.
#[test]
fn metadata_with_no_emitter_or_no_json_is_refused_by_name()
{
    assert!(
        matches!(
            Workspace::read(b"not json"),
            Err(CensusError::Metadata { .. })
        ),
        "a text that is not JSON is refused as metadata"
    );
    let no_emitter = METADATA.replace("\"e\", \"n\"", "\"n\"");
    assert_eq!(
        Workspace::read(no_emitter.as_bytes()),
        Err(CensusError::NoEmitter),
        "a workspace with no emitter is refused"
    );
}
