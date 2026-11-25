use gandr_workflow_twin_census::CensusError;
use gandr_workflow_twin_census::Workspace;
use gandr_workflow_twin_census::stale;

/// The metadata of a workspace of five crates: the emitter reaches `near` by
/// a normal edge and `far` by a build edge of `near`; it reaches `tested` by a
/// dev edge alone; `apart` has no edge. `outside` is a package of no member.
const METADATA: &str = r#"{
  "packages": [
    {"id": "e", "name": "gandr-runtime-emitter", "manifest_path": "/w/crates/runtime-emitter/Cargo.toml"},
    {"id": "n", "name": "gandr-near", "manifest_path": "/w/crates/near/Cargo.toml"},
    {"id": "f", "name": "gandr-far", "manifest_path": "/w/crates/far/Cargo.toml"},
    {"id": "t", "name": "gandr-tested", "manifest_path": "/w/crates/tested/Cargo.toml"},
    {"id": "a", "name": "gandr-apart", "manifest_path": "/w/crates/apart/Cargo.toml"},
    {"id": "o", "name": "outside", "manifest_path": "/r/outside/Cargo.toml"}
  ],
  "workspace_members": ["e", "n", "f", "t", "a"],
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

/// The census of [`METADATA`].
const CENSUS: &str = "# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

`twin-census --write` writes this file from `cargo metadata`. `twin-census --check` refuses it when it is not the census of the workspace.

| Crate | Under the emitter |
| ----- | ----------------- |
| `apart` | no |
| `far` | yes |
| `near` | yes |
| `runtime-emitter` | the emitter |
| `tested` | no |

Crates under the emitter: 2 of 5.
";

/// The emitter reaches a crate by a normal edge and through a build edge of
/// another crate. A dev edge, a crate that depends on the emitter, and a
/// package outside the workspace are no row under it.
#[test]
fn a_crate_under_the_emitter_is_marked_and_a_dev_edge_is_not()
{
    let workspace = Workspace::read(METADATA.as_bytes()).expect("the metadata reads");
    assert_eq!(
        workspace.counts(),
        (2, 5),
        "two of five crates are under the emitter"
    );
    assert_eq!(workspace.render(), CENSUS, "the census is its golden");
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
        .replace("| `far` | yes |", "| `far` | no |")
        .replace("| `tested` | no |\n", "")
        .replace("| `near` | yes |", "| `near` | yes |\n| `gone` | no |");
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
