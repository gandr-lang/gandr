use gandr_workflow_twin_census::CensusError;
use gandr_workflow_twin_census::Workspace;
use gandr_workflow_twin_census::rustdoc::generic_items;
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

/// The census of [`METADATA`], with the counts of generic items that
/// [`a_crate_under_the_emitter_is_marked_and_a_dev_edge_is_not`] puts in.
const CENSUS: &str = "# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

An item is generic when it has a type parameter or a trait bound. An entry under the C convention carries neither, so a generic item has no twin without a wrapper. The column counts the public functions, methods, types, traits and type aliases of the crate's library that are generic.

`twin-census --write` writes this file from `cargo metadata` and from the JSON that rustdoc writes for each library. `twin-census --check` refuses it when it is not the census of the workspace.

| Crate | Under the emitter | Generic items |
| ----- | ----------------- | ------------- |
| `apart` | no | 0 |
| `far` | yes | 2 |
| `near` | yes | 1 |
| `runtime-emitter` | the emitter | 3 |
| `tested` | no | no library |

Crates under the emitter: 2 of 5.

Generic public items: 6.
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
        workspace.render().contains("| `near` | yes | not read |"),
        "a library with no count is not read"
    );
    for (name, count) in [
        ("apart", 0),
        ("far", 2),
        ("near", 1),
        ("runtime-emitter", 3),
        ("outside", 9),
    ] {
        workspace.set_generic_items(name, count);
    }
    assert_eq!(workspace.render(), CENSUS, "the census is its golden");
}

/// The JSON of rustdoc for a crate with one item of each case. Items 1, 2,
/// 3, 4 and 6 are generic public items; each other item is not.
const RUSTDOC: &str = r#"{
  "format_version": 61,
  "index": {
    "1": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {}, "generics": {"params": [{"name": "T", "kind": {"type": {"bounds": [], "default": null, "is_synthetic": false}}}], "where_predicates": []}}}},
    "2": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {}, "generics": {"params": [{"name": "impl Read", "kind": {"type": {"bounds": [], "default": null, "is_synthetic": true}}}], "where_predicates": []}}}},
    "3": {"crate_id": 0, "visibility": "public", "inner": {"struct": {"kind": "unit", "generics": {"params": [], "where_predicates": [{"bound_predicate": {"type": {}, "bounds": [{"trait_bound": {}}], "generic_params": []}}]}, "impls": []}}},
    "4": {"crate_id": 0, "visibility": "public", "inner": {"trait": {"is_auto": false, "items": [], "generics": {"params": [], "where_predicates": []}, "bounds": [{"trait_bound": {}}]}}},
    "5": {"crate_id": 0, "visibility": "default", "inner": {"impl": {"generics": {"params": [{"name": "T", "kind": {"type": {}}}], "where_predicates": []}, "trait": null, "for": {}, "items": [6, 7]}}},
    "6": {"crate_id": 0, "visibility": "public", "inner": {"function": {"sig": {}, "generics": {"params": [], "where_predicates": []}}}},
    "7": {"crate_id": 0, "visibility": {"restricted": {"parent": 0, "path": "::a"}}, "inner": {"function": {"sig": {}, "generics": {"params": [], "where_predicates": []}}}},
    "8": {"crate_id": 0, "visibility": "public", "inner": {"enum": {"generics": {"params": [{"name": "'a", "kind": {"lifetime": {"outlives": []}}}, {"name": "N", "kind": {"const": {"type": {}, "default": null}}}], "where_predicates": [{"lifetime_predicate": {}}, {"bound_predicate": {"type": {}, "bounds": [{"outlives": "'a"}], "generic_params": []}}]}, "variants": []}}},
    "9": {"crate_id": 0, "visibility": "default", "inner": {"impl": {"generics": {"params": [{"name": "T", "kind": {"type": {}}}], "where_predicates": []}, "trait": {"path": "Clone"}, "for": {}, "items": [10]}}},
    "10": {"crate_id": 0, "visibility": "default", "inner": {"function": {"sig": {}, "generics": {"params": [{"name": "U", "kind": {"type": {}}}], "where_predicates": []}}}},
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
        generic_items(RUSTDOC.as_bytes()),
        Ok(5),
        "items 1, 2, 3, 4 and 6 count"
    );
}

/// A file of a different format of rustdoc names its format, and a text that
/// is not JSON is refused as rustdoc's JSON.
#[test]
fn rustdoc_of_another_format_or_no_json_is_refused_by_name()
{
    let other = RUSTDOC.replace("\"format_version\": 61", "\"format_version\": 62");
    assert_eq!(
        generic_items(other.as_bytes()),
        Err(CensusError::RustdocFormat { found: 62 }),
        "the format is named"
    );
    assert!(
        matches!(generic_items(b"not json"), Err(CensusError::Rustdoc { .. })),
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
        .replace("| `tested` | no | no library |\n", "")
        .replace(
            "| `near` | yes | 1 |",
            "| `near` | yes | 1 |\n| `gone` | no | 0 |",
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
