//! A package's toolchain constraint, read from its manifest, and the
//! installed toolchain that meets it.
//!
//! # The constraint chooses among the installed toolchains
//!
//! **Choice.** The constraint is the `[toolchain]` table of the nearest
//! `gandr.toml` in the working directory or an ancestor. `gandr check` writes
//! that table from the package's model, so the proxy reads it with no build.
//! A toolchain named by `GANDR_TOOLCHAIN` or by a pin runs when it meets the
//! constraint and is refused when it does not. Otherwise the default runs
//! when it meets the constraint, else the installed toolchain of the highest
//! version that does, the first by name among equals. With none, the
//! selection is refused with each clause the nearest candidate leaves unmet.
//!
//! **Descriptions.** A candidate's version, system and features live in its
//! binary. `gandr toolchain describe` prints them, about 6 ms a run. The
//! description is kept in `gandr/described/<name>` beside the toolchains
//! directory, under the device, inode and modification time of the `gandr`
//! it describes, and taken again when that file changes. A face checks the
//! selection on every client frame, so a kept description costs it one
//! `stat` and one read where a run would cost a process.
//!
//! **Alternatives.** Each candidate could judge the constraint itself, which
//! keeps one comparison, at the cost of a run per candidate and manifest. A
//! description taken at link time would go stale when a build is rebuilt in
//! place, as `mise run install` does. A manifest that does not read asks
//! nothing here: `gandr check` reads the model again and refuses it there.
//!
//! **Reversal.** A toolchain fetched to meet a constraint, the board's
//! `toolchain-fetch` card, joins the candidates this module ranks.

use core::cmp::Reverse;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_dispatcher::Described;
use gandr_surface_dispatcher::MANIFEST;
use gandr_surface_dispatcher::Separated;
use gandr_surface_dispatcher::Toolchain;
use quenchant_shape::shape::Maybe;

use super::Name;
use super::SELECTING;
use super::Selected;
use super::Source;
use super::ToolchainFault;
use super::executable;
use super::unselected;

/// The table of a manifest that holds the constraint.
const TABLE: &str = "toolchain";

/// The directory beside the toolchains directory that keeps descriptions.
const DESCRIBED: &str = "described";

/// The word a kept description's first line opens with, before the image it
/// was taken from.
const IMAGE: &str = "image";

quenchant_shape::reason_enum! {
    /// Why no constraint applies to the selection.
    pub mod unasked {
        /// The reason the selection stands as made.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No manifest lies in the working directory or an ancestor.
            Unmanifested,
            /// The nearest manifest asks nothing, or does not read.
            Unasked,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why no candidate stands nearest a constraint none meets.
    pub mod undescribed {
        /// The reason the refusal names no clause.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No installed toolchain describes itself.
            Undescribed,
        }
    }
}

/// The nearest manifest in `working` or an ancestor, and its constraint when
/// it asks anything.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first `gandr.toml` up from `working`, with its `[toolchain]`
///   table read as `gandr check` writes it, when that table asks anything.
/// - provides: [`unasked::Absent`] otherwise.
/// - panics: none.
/// - executable: none — the answer is the file system's.
///
/// # Adequacy
/// - hypothesis: L3 — a manifest above the working directory constrains the
///   selection.
/// - witness: `tests::cli::a_package_s_constraint_chooses_among_the_toolchains`
fn asked(working: &Path) -> Maybe<(PathBuf, Toolchain), unasked::Absent>
{
    let Some(manifest) = working
        .ancestors()
        .map(|directory| directory.join(MANIFEST))
        .find(|manifest| manifest.is_file())
    else {
        return Maybe::Absent(unasked::Absent::Unmanifested);
    };
    let Ok(text) = std::fs::read_to_string(&manifest)
    else {
        return Maybe::Absent(unasked::Absent::Unasked);
    };
    let Ok(table) = text.parse::<toml::Table>()
    else {
        return Maybe::Absent(unasked::Absent::Unasked);
    };
    let Some(toolchain) = table.get(TABLE).and_then(toml::Value::as_table)
    else {
        return Maybe::Absent(unasked::Absent::Unasked);
    };
    let line = |field: &str| {
        toolchain
            .get(field)
            .and_then(toml::Value::as_array)
            .map(|entries| {
                entries
                    .iter()
                    .filter_map(toml::Value::as_str)
                    .collect::<Vec<&str>>()
                    .join(",")
            })
            .unwrap_or_default()
    };
    let gandr = toolchain
        .get("gandr")
        .and_then(toml::Value::as_str)
        .unwrap_or_default()
        .to_owned();
    let (features, systems) = (line("features"), line("systems"));
    match Toolchain::read(gandr, Separated(&features), Separated(&systems)) {
        Ok(read) => match read.asking() {
            Maybe::Present(asked) => Maybe::Present((manifest, asked)),
            Maybe::Absent(_nothing) => Maybe::Absent(unasked::Absent::Unasked),
        },
        Err(_unconstrained) => Maybe::Absent(unasked::Absent::Unasked),
    }
}

/// The description of the installed toolchain `name`, kept in `kept` under
/// the image it was taken from, or taken again by running its `gandr`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the description the toolchain's `gandr toolchain describe`
///   prints; read from `kept` when the file there names the `gandr`'s current
///   image, and written there otherwise.
/// - fails: [`ToolchainFault::Unknown`] and [`ToolchainFault::Unexecutable`] as
///   [`executable`] states, and [`ToolchainFault::Undescribed`] when the
///   `gandr` prints no description.
/// - panics: none.
/// - executable: none — the answer is another process's or the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a toolchain is described once per image.
/// - witness: `tests::cli::a_package_s_constraint_chooses_among_the_toolchains`
fn described(
    toolchains: &Path,
    selected: Selected,
) -> Result<Described, ToolchainFault>
{
    let name = selected.name.clone();
    let path = executable(toolchains, selected)?;
    let undescribed = || ToolchainFault::Undescribed {
        name: name.clone(),
        path: path.clone(),
    };
    let image = std::fs::metadata(&path).map_err(|_unread| undescribed())?;
    let image = format!("{IMAGE} {}", imaged(&image));
    let kept = toolchains.with_file_name(DESCRIBED).join(&name.0);
    if let Ok(text) = std::fs::read_to_string(&kept)
        && let Some((first, description)) = text.split_once('\n')
        && first == image
        && let Ok(described) = description.parse::<Described>()
    {
        return Ok(described);
    }
    let output = std::process::Command::new(&path)
        .args(["toolchain", "describe"])
        .env_remove(SELECTING)
        .stdin(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .output()
        .map_err(|_unrun| undescribed())?;
    let description = String::from_utf8(output.stdout).map_err(|_unreadable| undescribed())?;
    let Ok(described) = description.parse::<Described>()
    else {
        return Err(undescribed());
    };
    // A description that cannot be kept is taken again next time.
    let _kept = kept
        .parent()
        .map(std::fs::create_dir_all)
        .and_then(Result::ok)
        .map(|()| std::fs::write(&kept, format!("{image}\n{description}")));
    Ok(described)
}

/// The image of the file `metadata` describes, as a kept description names
/// it: its device, inode and modification time.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn imaged(metadata: &std::fs::Metadata) -> String
{
    use std::os::unix::fs::MetadataExt as _;

    format!(
        "{} {} {} {}",
        metadata.dev(),
        metadata.ino(),
        metadata.mtime(),
        metadata.mtime_nsec()
    )
}

/// The image of the file `metadata` describes, as a kept description names
/// it: its length and modification time.
///
/// # Specification
/// trivial.
#[cfg(not(unix))]
fn imaged(metadata: &std::fs::Metadata) -> String
{
    let modified = metadata
        .modified()
        .ok()
        .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
        .unwrap_or_default();
    format!("{} {}", metadata.len(), modified.as_nanos())
}

/// The selection `selected` made, held to the constraint of the nearest
/// manifest above `working`.
///
/// # Specification
/// - requires: `selected` is [`super::select`]'s answer for `working`.
/// - ensures: `selected` unchanged when no manifest asks anything, or when no
///   toolchain is installed. A toolchain named by the environment or a pin is
///   kept when it meets the constraint. Otherwise the default is kept when it
///   meets it, else the installed toolchain of the highest version that does,
///   the first by name among equals, under [`Source::Manifest`].
/// - fails: [`ToolchainFault::Unmet`] when a toolchain named by the environment
///   or a pin leaves the constraint unmet; [`ToolchainFault::Unmeetable`] when
///   no installed toolchain meets it; the faults [`described`] states for a
///   named toolchain.
/// - panics: none.
/// - executable: none — the answer is the file system's and the candidates'.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a default that meets the constraint runs; one that does
///   not yields to the highest that does; an unmet pin is refused by its
///   source; a constraint none meets is refused by each clause.
/// - witness: `tests::cli::a_package_s_constraint_chooses_among_the_toolchains`
pub fn constrained(
    toolchains: &Path,
    working: &Path,
    selected: Maybe<Selected, unselected::Absent>,
) -> Result<Maybe<Selected, unselected::Absent>, ToolchainFault>
{
    let Maybe::Present((manifest, asked)) = asked(working)
    else {
        return Ok(selected);
    };
    if let Maybe::Present(ref named) = selected
        && matches!(named.source, Source::Environment | Source::Pin(_))
    {
        let unmet = asked.unmet(&described(toolchains, named.clone())?.running());
        if unmet.is_empty() {
            return Ok(selected);
        }
        return Err(ToolchainFault::Unmet {
            name: named.name.clone(),
            source: named.source.clone(),
            manifest,
            unmet,
        });
    }
    let installed = super::installed()?;
    if installed.is_empty() {
        return Ok(selected);
    }
    let mut candidates: Vec<(Name, Described)> = Vec::new();
    for name in installed.into_keys() {
        let candidate = Selected {
            name: name.clone(),
            source: Source::Manifest(manifest.clone()),
        };
        if let Ok(described) = described(toolchains, candidate) {
            candidates.push((name, described));
        }
    }
    if let Maybe::Present(ref default) = selected
        && candidates.iter().any(|&(ref name, ref described)| {
            *name == default.name && asked.unmet(&described.running()).is_empty()
        })
    {
        return Ok(selected);
    }
    let meeting = candidates
        .iter()
        .filter(|&&(_, ref described)| asked.unmet(&described.running()).is_empty())
        .max_by_key(|&&(ref name, ref described)| (described.version(), Reverse(name.clone())));
    if let Some(&(ref name, _)) = meeting {
        return Ok(Maybe::Present(Selected {
            name: name.clone(),
            source: Source::Manifest(manifest),
        }));
    }
    let nearest = match selected {
        Maybe::Present(ref default) => candidates
            .iter()
            .find(|&&(ref name, _)| *name == default.name),
        Maybe::Absent(_) => None,
    }
    .or_else(|| {
        candidates
            .iter()
            .max_by_key(|&&(ref name, ref described)| (described.version(), Reverse(name.clone())))
    });
    Err(ToolchainFault::Unmeetable {
        manifest,
        nearest: nearest.map_or(
            Maybe::Absent(undescribed::Absent::Undescribed),
            |&(ref name, ref described)| {
                Maybe::Present((name.clone(), asked.unmet(&described.running())))
            },
        ),
    })
}
