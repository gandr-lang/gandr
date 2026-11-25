//! The writer's witnesses: each publication is read back through the
//! directory it publishes into.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use super::Access;
use super::Contents;
use super::Placement;
use super::Step;
use super::Unpublished;
use super::publish;
use super::publish_as;

/// The file every witness publishes.
const FILE: &str = "record";

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
    /// The empty directory named for `label`, emptied first if a run left it.
    ///
    /// # Specification
    /// trivial.
    fn new(label: Label) -> Self
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-core-publish-{}-{}",
            label.0,
            std::process::id()
        ));
        if directory.exists() {
            std::fs::remove_dir_all(&directory).expect("a stale scratch directory is removed");
        }
        std::fs::create_dir_all(&directory).expect("the scratch directory is made");
        Self(directory)
    }

    /// The directory.
    ///
    /// # Specification
    /// trivial.
    fn path(&self) -> &Path
    {
        &self.0
    }

    /// The names the directory holds, in order.
    ///
    /// # Specification
    /// trivial.
    fn entries(&self) -> Vec<String>
    {
        let mut names: Vec<String> = std::fs::read_dir(&self.0)
            .expect("the scratch directory lists")
            .map(|entry| {
                entry
                    .expect("an entry reads")
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
    /// Remove the directory and what it holds.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        drop(std::fs::remove_dir_all(&self.0));
    }
}

#[test]
fn a_published_file_holds_its_contents_and_nothing_else()
{
    let scratch = Scratch::new(Label("published"));
    assert_eq!(
        publish(scratch.path(), FILE, Contents(b"first")),
        Ok(()),
        "a writable directory publishes"
    );
    assert_eq!(
        std::fs::read(scratch.path().join(FILE)).expect("the file reads"),
        b"first",
        "the file holds the contents"
    );
    assert_eq!(scratch.entries(), [FILE], "and no temporary remains");
    assert_eq!(
        publish(scratch.path(), FILE, Contents(b"second, longer")),
        Ok(()),
        "a second publication replaces the first"
    );
    assert_eq!(
        std::fs::read(scratch.path().join(FILE)).expect("the file reads"),
        b"second, longer",
        "the file holds the new contents alone"
    );
    assert_eq!(scratch.entries(), [FILE], "and still no temporary");
}

#[test]
fn a_missing_directory_refuses_the_creation()
{
    let scratch = Scratch::new(Label("missing"));
    let absent = scratch.path().join("absent");
    assert_eq!(
        publish(&absent, FILE, Contents(b"bytes")),
        Err(Unpublished {
            path: absent.join(FILE),
            step: Step::Create,
            kind: io::ErrorKind::NotFound,
        }),
        "no temporary is created where no directory is"
    );
    assert_eq!(
        scratch.entries(),
        Vec::<String>::new(),
        "and nothing is made"
    );
}

#[test]
fn a_refused_rename_leaves_the_directory_as_it_was()
{
    let scratch = Scratch::new(Label("refused"));
    let occupied = scratch.path().join(FILE);
    std::fs::create_dir_all(&occupied).expect("a directory occupies the file's name");
    assert_eq!(
        publish(scratch.path(), FILE, Contents(b"bytes")),
        Err(Unpublished {
            path: occupied.clone(),
            step: Step::Rename,
            kind: io::ErrorKind::IsADirectory,
        }),
        "the rename onto a directory fails"
    );
    assert_eq!(
        scratch.entries(),
        [FILE],
        "only the occupying directory remains"
    );
    assert!(occupied.is_dir(), "and it is still a directory");
}

#[test]
fn a_squatted_name_is_never_written_through()
{
    let scratch = Scratch::new(Label("squatted"));
    let process = std::process::id();
    let squatters = [
        format!("{FILE}.tmp"),
        format!("{FILE}.tmp-{process}"),
        format!("{FILE}.tmp-{process}-0000000000000000"),
    ];
    for squatter in &squatters {
        std::fs::write(scratch.path().join(squatter), b"squatter").expect("a squatter is planted");
    }
    assert_eq!(
        publish(scratch.path(), FILE, Contents(b"bytes")),
        Ok(()),
        "the publication succeeds beside the squatters"
    );
    for squatter in &squatters {
        assert_eq!(
            std::fs::read(scratch.path().join(squatter)).expect("the squatter reads"),
            b"squatter",
            "{squatter} keeps its bytes"
        );
    }
    assert_eq!(
        std::fs::read(scratch.path().join(FILE)).expect("the file reads"),
        b"bytes",
        "the file holds the contents"
    );
    assert_eq!(
        scratch.entries().len(),
        squatters.len().saturating_add(1),
        "and nothing else is left"
    );
}

#[test]
fn concurrent_publications_leave_one_whole_file()
{
    let scratch = Scratch::new(Label("concurrent"));
    let contents: Vec<Vec<u8>> = (1_u8 ..= 4_u8).map(|fill| vec![fill; 1 << 16]).collect();
    std::thread::scope(|scope| {
        for own in &contents {
            let directory = scratch.path();
            let _handle = scope.spawn(move || {
                for _ in 0_u8 .. 16_u8 {
                    assert_eq!(
                        publish(directory, FILE, Contents(own)),
                        Ok(()),
                        "every publication succeeds"
                    );
                }
            });
        }
    });
    assert_eq!(scratch.entries(), [FILE], "one file, no temporary");
    let published = std::fs::read(scratch.path().join(FILE)).expect("the file reads");
    assert!(
        contents.contains(&published),
        "and it holds one publication's contents whole"
    );
}

#[test]
fn a_kept_file_refuses_a_second_publication()
{
    let scratch = Scratch::new(Label("kept"));
    let file = scratch.path().join(FILE);
    assert_eq!(
        publish_as(&file, Contents(b"first"), Placement::Keep, &Access::Default),
        Ok(()),
        "a free name takes the kept file"
    );
    assert_eq!(scratch.entries(), [FILE], "and its private name goes");
    assert_eq!(
        publish_as(
            &file,
            Contents(b"second"),
            Placement::Keep,
            &Access::Default
        ),
        Err(Unpublished {
            path: file.clone(),
            step: Step::Link,
            kind: io::ErrorKind::AlreadyExists,
        }),
        "a held name refuses the link"
    );
    assert_eq!(
        std::fs::read(&file).expect("the file reads"),
        b"first",
        "the first publication stays"
    );
    assert_eq!(scratch.entries(), [FILE], "and the second leaves nothing");
}

#[cfg(unix)]
#[test]
fn each_access_reaches_the_published_file()
{
    use std::os::unix::fs::PermissionsExt as _;

    let scratch = Scratch::new(Label("access"));
    let file = scratch.path().join(FILE);
    let mode = |path: &Path| {
        std::fs::metadata(path)
            .expect("the file is there")
            .permissions()
            .mode()
            & 0o777
    };
    assert_eq!(
        publish_as(&file, Contents(b"key"), Placement::Keep, &Access::Owner),
        Ok(()),
        "an owner's file publishes"
    );
    assert_eq!(mode(&file), 0o600, "and its owner alone reads it");
    let given = std::fs::Permissions::from_mode(0o640);
    assert_eq!(
        publish_as(
            &file,
            Contents(b"source"),
            Placement::Replace,
            &Access::Exactly(given)
        ),
        Ok(()),
        "a file given its permissions publishes over it"
    );
    assert_eq!(mode(&file), 0o640, "and carries those permissions");
    assert_eq!(scratch.entries(), [FILE], "with no temporary left");
}
