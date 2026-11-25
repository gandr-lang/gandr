use gandr_workflow_twin_census::CensusError;
use gandr_workflow_twin_census::Workspace;
use gandr_workflow_twin_census::rustdoc::Surface;
use gandr_workflow_twin_census::rustdoc::read;
use gandr_workflow_twin_census::stale;

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

`twin-census --write` writes this file from `cargo metadata` and from the JSON that rustdoc writes for each library. `twin-census --check` refuses it when it is not the census of the workspace.

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
    "8": {"crate_id": 0, "visibility": "public", "inner": {"enum": {"generics": {"params": [{"name": "'a", "kind": {"lifetime": {"outlives": []}}}, {"name": "N", "kind": {"const": {"type": {}, "default": null}}}], "where_predicates": [{"lifetime_predicate": {}}, {"bound_predicate": {"type": {}, "bounds": [{"outlives": "'a"}], "generic_params": []}}]}, "variants": []}}},
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
    assert_eq!(
        read(RUSTDOC.as_bytes()),
        Ok(Surface {
            generic_items: 5,
            functions: 3,
            exportable: 0,
        }),
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
    assert_eq!(
        read(SIGNATURES.as_bytes()),
        Ok(Surface {
            generic_items: 1,
            functions: 11,
            exportable: 3,
        }),
        "items 1, 2 and 8 are in the fragment, and item 7 is generic"
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

/// A census with one row changed, one row missing and one row of no crate is
/// stale, and the refusal names the three crates in order. An equal text
/// passes, and a text that differs outside the rows names that text.
#[test]
fn a_stale_census_is_refused_with_the_rows_that_differ()
{
    assert_eq!(stale(CENSUS, CENSUS), Ok(()), "an equal census passes");
    let committed = CENSUS
        .replace("| `far` | yes | 2 |", "| `far` | no | 2 |")
        .replace("| `tested` | no | no library | no library |\n", "")
        .replace(
            "| `near` | yes | 1 | 3 of 3 (100 %) |",
            "| `near` | yes | 1 | 3 of 3 (100 %) |\n| `gone` | no | 0 | 0 of 0 |",
        );
    assert_eq!(
        stale(&committed, CENSUS),
        Err(CensusError::Stale {
            rows: vec![
                String::from("far"),
                String::from("gone"),
                String::from("tested")
            ],
        }),
        "the three crates are named in order"
    );
    let counted = CENSUS.replace("2 of 5", "3 of 5");
    assert_eq!(
        stale(&counted, CENSUS),
        Err(CensusError::Stale {
            rows: vec![String::from("the text outside the rows")],
        }),
        "a difference outside the rows is named as such"
    );
}
