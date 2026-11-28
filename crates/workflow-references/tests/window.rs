//! The citation window over given citations, work rows and policies.

use alloc::collections::BTreeMap;

use gandr_workflow_references::cites::Citation;
use gandr_workflow_references::cites::Kind;
use gandr_workflow_references::window::Policy;
use gandr_workflow_references::window::PolicyFault;
use gandr_workflow_references::window::Work;
use gandr_workflow_references::window::findings;
use gandr_workflow_references::window::works;

/// A citation of `kind` of `key` at `module` of `krate`, at `location`.
fn cite(
    kind: Kind,
    key: &str,
    krate: &str,
    module: &str,
    location: &str,
) -> Citation
{
    Citation {
        kind,
        key: key.to_owned(),
        krate: krate.to_owned(),
        module: module.to_owned(),
        role: "background".to_owned(),
        location: location.to_owned(),
    }
}

/// The work rows of `rows`: key, year and newer work.
fn rows(rows: &[(&str, u16, Option<&str>)]) -> BTreeMap<String, Work>
{
    rows.iter()
        .map(|&(key, year, newer)| {
            (key.to_owned(), Work {
                year,
                newer: newer.map(str::to_owned),
            })
        })
        .collect()
}

/// The findings over `cites`, `works` and the policy text `policy`.
fn judged(
    cites: &[Citation],
    works: &BTreeMap<String, Work>,
    policy: &str,
) -> Vec<String>
{
    findings(
        cites,
        works,
        &Policy::read(policy).expect("the policy reads"),
    )
}

/// The tail of a finding of an older work at a site no entry keeps.
const ALLOW: &str =
    "or allow the site in .config/references/window.toml with why no newer work states it";

/// A work before the cutoff at a site no entry keeps is refused at a module
/// and at a corpus source, naming the site, the work, its year and its
/// newer work; a newer work and a vault key are not judged.
#[test]
fn an_older_work_at_a_site_no_entry_keeps_is_refused()
{
    let cites = [
        cite(
            Kind::Locator,
            "doi:10.1000/old",
            "demo-crate",
            "a",
            "crates/demo-crate/src/a.rs:3",
        ),
        cite(
            Kind::Cite,
            "Kept-2021-recent_work",
            "demo-crate",
            "a",
            "crates/demo-crate/src/a.rs:5",
        ),
        cite(
            Kind::Cite,
            "vault:01a16c8c-a658-7c31-8c33-b2e2142c0b73",
            "demo-crate",
            "a",
            "crates/demo-crate/src/a.rs:6",
        ),
        cite(
            Kind::Corpus,
            "doi:10.1000/old",
            "corpus",
            "model/demo/a.gandr",
            "corpus/model/demo/a.gandr:2",
        ),
    ];
    let works = rows(&[("doi:10.1000/old", 1999, Some("doi:10.1000/new"))]);
    assert_eq!(
        vec![
            format!(
                "corpus/model/demo/a.gandr:2: `doi:10.1000/old` appeared in 1999, before the citation window opens in 2019; cite the newest work that states what corpus/model/demo/a.gandr builds, such as `doi:10.1000/new`, {ALLOW}"
            ),
            format!(
                "crates/demo-crate/src/a.rs:3: `doi:10.1000/old` appeared in 1999, before the citation window opens in 2019; cite the newest work that states what demo-crate::a builds, such as `doi:10.1000/new`, {ALLOW}"
            ),
        ],
        judged(&cites, &works, "cutoff = 2019\n")
    );
}

/// A site entry keeps its work at its site alone: the same older work at
/// the root of the crate is refused, and a corpus source is kept by its
/// path.
#[test]
fn a_site_entry_keeps_its_work_at_its_site_alone()
{
    let cites = [
        cite(
            Kind::Cite,
            "Old-2010-construction",
            "other-crate",
            "m",
            "crates/other-crate/src/m.rs:4",
        ),
        cite(
            Kind::Cite,
            "Old-2010-construction",
            "other-crate",
            "",
            "crates/other-crate/src/lib.rs:9",
        ),
        cite(
            Kind::Corpus,
            "arXiv:1501.00001",
            "corpus",
            "model/demo/a.gandr",
            "corpus/model/demo/a.gandr:2",
        ),
    ];
    let policy = "cutoff = 2019\n\n[[site]]\nsite = \"other-crate::m\"\nwork = \"Old-2010-construction\"\nexemplar = \"no newer work states the construction\"\n\n[[site]]\nsite = \"corpus/model/demo/a.gandr\"\nwork = \"arXiv:1501.00001\"\nexemplar = \"frozen\"\n";
    assert_eq!(
        vec![format!(
            "crates/other-crate/src/lib.rs:9: `Old-2010-construction` appeared in 2010, before the citation window opens in 2019; cite the newest work that states what other-crate builds, {ALLOW}"
        )],
        judged(&cites, &BTreeMap::new(), policy)
    );
}

/// A work row's year wins over its arXiv identifier's, an old-style
/// identifier reads its century, and a citation key reads its year.
#[test]
fn a_work_row_year_wins_over_its_identifier()
{
    let cites = [
        cite(
            Kind::Locator,
            "arXiv:1812.00001",
            "demo-crate",
            "",
            "crates/demo-crate/src/lib.rs:2",
        ),
        cite(
            Kind::Locator,
            "arXiv:1812.00002",
            "demo-crate",
            "",
            "crates/demo-crate/src/lib.rs:3",
        ),
        cite(
            Kind::Locator,
            "arXiv:math/0601001",
            "demo-crate",
            "",
            "crates/demo-crate/src/lib.rs:4",
        ),
        cite(
            Kind::Locator,
            "arXiv:hep-th/9901001",
            "demo-crate",
            "",
            "crates/demo-crate/src/lib.rs:5",
        ),
        cite(
            Kind::Cite,
            "Author-2019-recent",
            "demo-crate",
            "",
            "crates/demo-crate/src/lib.rs:6",
        ),
    ];
    let works = rows(&[("arXiv:1812.00001", 2019, None)]);
    let refused = |line: u8, key: &str, year: u16| {
        format!(
            "crates/demo-crate/src/lib.rs:{line}: `{key}` appeared in {year}, before the citation window opens in 2019; cite the newest work that states what demo-crate builds, {ALLOW}"
        )
    };
    assert_eq!(
        vec![
            refused(3, "arXiv:1812.00002", 2018),
            refused(4, "arXiv:math/0601001", 2006),
            refused(5, "arXiv:hep-th/9901001", 1999),
        ],
        judged(&cites, &works, "cutoff = 2019\n")
    );
}

/// An entry missing its exemplar, a crate entry and a corpus entry are
/// refused by name; a DOI with no row has no year; an entry that keeps no
/// older work is idle.
#[test]
fn an_entry_missing_a_field_and_a_whole_crate_are_refused()
{
    let cites = [
        cite(
            Kind::Locator,
            "doi:10.1000/undated",
            "demo-crate",
            "a",
            "crates/demo-crate/src/a.rs:3",
        ),
        cite(
            Kind::Locator,
            "arXiv:2101.00001",
            "quiet-crate",
            "",
            "crates/quiet-crate/src/lib.rs:2",
        ),
    ];
    let policy = "cutoff = 2019\n\n[[crate]]\nname = \"quiet-crate\"\n\n[[corpus]]\nsubject = \"model/demo\"\n\n[[site]]\nsite = \"demo-crate::a\"\nwork = \"doi:10.1000/undated\"\n\n[[site]]\nsite = \"quiet-crate\"\nwork = \"arXiv:2101.00001\"\nexemplar = \"no newer work\"\n";
    assert_eq!(
        vec![
            "window.toml: [[corpus]] model/demo covers a corpus subject whole: write one `[[site]]` entry for each site and each older work".to_owned(),
            "window.toml: [[crate]] quiet-crate covers a crate whole: write one `[[site]]` entry for each site and each older work".to_owned(),
            "window.toml: [[site]] demo-crate::a doi:10.1000/undated needs a `site`, the `work` it keeps and its `exemplar`: why no newer work states what the site builds".to_owned(),
            "crates/demo-crate/src/a.rs:3: `doi:10.1000/undated` states no year: add its row to `work` in ledger/references.sql, the year the work appeared".to_owned(),
            "window.toml: [[site]] quiet-crate arXiv:2101.00001 covers no citation older than 2019; delete it".to_owned(),
        ],
        judged(&cites, &BTreeMap::new(), policy)
    );
}

/// A cutoff that is missing, or not on its own line, is refused, since the
/// readers of the issues read the line.
#[test]
fn a_cutoff_off_its_line_is_refused()
{
    assert_eq!(
        Err(PolicyFault::Cutoff),
        Policy::read("[[site]]\nsite = \"a\"\nwork = \"b\"\nexemplar = \"c\"\n")
    );
    assert_eq!(
        Err(PolicyFault::Cutoff),
        Policy::read("cutoff = 2019 # the year\n")
    );
    assert_eq!(
        Ok(2019),
        Policy::read("cutoff = 2019\n").map(|policy| policy.cutoff)
    );
    assert!(matches!(
        Policy::read("cutoff = \n"),
        Err(PolicyFault::Toml(_))
    ));
}

/// The work rows read their years and their newer works, with a quote in a
/// key, and a line of another table is not a row.
#[test]
fn the_work_rows_read_their_years()
{
    let ledger = "CREATE TABLE work(key TEXT);\nINSERT INTO work VALUES('doi:10.1000/old',1999,'doi:10.1000/new');\nINSERT INTO work VALUES('O''Hearn-2001-key',2001,NULL);\nINSERT INTO fidelity VALUES('a',1,NULL);\n";
    assert_eq!(
        rows(&[
            ("O'Hearn-2001-key", 2001, None),
            ("doi:10.1000/old", 1999, Some("doi:10.1000/new")),
        ]),
        works(ledger)
    );
}
