//! Notebooks: Jupyter's `.ipynb` with a `gandr` kernelspec, each code cell
//! gandr source, synchronised through `notebookDocument/didOpen`, `didChange`
//! and `didClose`, as LSP 3.17 states them.
//!
//! # One notebook, one document
//!
//! A notebook's code cells are judged as one document: the cells' texts in
//! order, each followed by a line feed, held under the notebook's URI. A cell
//! reads every name the cells before it declare and, as a gandr source reads a
//! name declared after it, those after it too; markup cells are prose and
//! never judged. The one document's publication is split by where each
//! diagnostic starts: every code cell is published its own, in its own lines
//! and characters, a range running past its cell cut at the cell's end, and a
//! related location in the notebook moved to the cell holding it. A cell the
//! change takes out, or makes markup, is published empty.
//!
//! The format is Jupyter's because every editor and viewer reads it; the
//! kernelspec names the cells' language, and the server selects a notebook
//! whose cells are `gandr`. The alternatives were a gandr notebook format of
//! its own, which no editor reads, and judging each cell as a document of its
//! own, which loses what the cells before it declare. Executing a cell is a
//! kernel's, not the server's. The choice reverses if cells are to be judged
//! in the order they ran rather than the order they are laid out: the
//! document then follows the kernel's history.
//!
//! The server answers the four notifications alone. A request naming a cell
//! names a document the server does not hold, and is answered as one.
//! `notebookDocument/didSave` is declined as `textDocument/didSave` is: every
//! change is judged as it arrives, so a save owes no check.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::LineIndex;

use crate::position::Range;
use crate::protocol::CellKind;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::protocol::Location;
use crate::protocol::NotebookCell;
use crate::protocol::NotebookChange;
use crate::protocol::NotebookDocument;
use crate::protocol::PublishParams;
use crate::protocol::TextDocumentItem;
use crate::server::edit_text;

/// A notebook a connection holds open: its cells in order and each cell's
/// text.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Notebook
{
    /// The cells, in order.
    order: Vec<NotebookCell>,
    /// Each cell's text and its version, by the cell's URI.
    texts: BTreeMap<DocumentUri, Cell>,
}

/// One cell's text, at its version.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Cell
{
    /// The version of the cell's text.
    version: DocumentVersion,
    /// The cell's text.
    text: String,
}

/// A code cell as the one document lays it out.
struct Laid<'notebook>
{
    /// The cell's URI.
    uri: &'notebook DocumentUri,
    /// The version of its text.
    version: DocumentVersion,
    /// The byte of the one document its text starts at.
    start: usize,
    /// Its text.
    text: &'notebook str,
    /// The line index of its text.
    index: LineIndex<'notebook>,
}

impl Notebook
{
    /// The notebook `document` opens, its cells' texts `texts`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn opened(
        document: NotebookDocument,
        texts: Vec<TextDocumentItem>,
    ) -> Self
    {
        Self {
            order: document.cells,
            texts: texts
                .into_iter()
                .map(|item| {
                    (item.uri, Cell {
                        version: item.version,
                        text: item.text,
                    })
                })
                .collect(),
        }
    }

    /// Apply `change` to the notebook's cells, and answer each code cell it
    /// removes or makes markup.
    ///
    /// # Specification
    /// - requires: nothing; any change is admissible input.
    /// - ensures: the structure first: each cell document it closes forgets its
    ///   text, each it opens takes its text and version, and the cells from the
    ///   splice's start, clamped to the cell count, through as many as it
    ///   deletes, clamped likewise, are replaced by the cells it inserts. Then
    ///   each cell the data names takes its kind. Then each text change applies
    ///   its changes in order to the cell's text, as [`edit_text`] states, and
    ///   takes its version; a change naming a cell with no text is ignored.
    ///   Answers, in that order, each code cell the splice removed and did not
    ///   insert again, and each code cell the data made markup.
    /// - provides: the notebook's cells as the client holds them.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a splice deleting a code cell and inserting a new
    ///   one, a code cell made markup, and a ranged edit of a cell, each
    ///   asserted at the exact text the notebook then lays out and the cells
    ///   answered.
    /// - witness: `notebook::tests::a_change_splices_retypes_and_edits_the_cells`
    #[spec(
        captures: [
            cells = self.order.len(),
            inserted = change.cells.as_ref().and_then(|cells| cells.structure.as_ref())
                .map_or(0_usize, |structure| structure.array.cells.len()),
        ],
        ensures: |ret| ret.len() <= cells.saturating_add(inserted),
    )]
    #[inline]
    pub fn change(
        &mut self,
        change: NotebookChange,
    ) -> Vec<DocumentUri>
    {
        let Some(cells) = change.cells
        else {
            return Vec::new();
        };
        let mut gone = Vec::new();
        if let Some(structure) = cells.structure {
            for closed in structure.did_close {
                let _forgotten = self.texts.remove(&closed.uri);
            }
            for opened in structure.did_open {
                let _replaced = self.texts.insert(opened.uri, Cell {
                    version: opened.version,
                    text: opened.text,
                });
            }
            let array = structure.array;
            let start = usize::try_from(array.start)
                .unwrap_or(usize::MAX)
                .min(self.order.len());
            let end = start
                .saturating_add(usize::try_from(array.delete_count).unwrap_or(usize::MAX))
                .min(self.order.len());
            let inserted: BTreeSet<DocumentUri> = array
                .cells
                .iter()
                .map(|cell| cell.document.clone())
                .collect();
            gone.extend(
                self.order
                    .splice(start .. end, array.cells)
                    .filter(|cell| {
                        cell.kind == CellKind::CODE && !inserted.contains(&cell.document)
                    })
                    .map(|cell| cell.document),
            );
        }
        if !cells.data.is_empty() {
            let at: BTreeMap<DocumentUri, usize> = self
                .order
                .iter()
                .enumerate()
                .map(|(place, cell)| (cell.document.clone(), place))
                .collect();
            for retyped in cells.data {
                let Some(cell) = at
                    .get(&retyped.document)
                    .and_then(|&place| self.order.get_mut(place))
                else {
                    continue;
                };
                if cell.kind == CellKind::CODE && retyped.kind != CellKind::CODE {
                    gone.push(retyped.document);
                }
                cell.kind = retyped.kind;
            }
        }
        for edited in cells.text_content {
            let Some(cell) = self.texts.get_mut(&edited.document.uri)
            else {
                continue;
            };
            cell.version = edited.document.version;
            for change in edited.changes {
                edit_text(&mut cell.text, change);
            }
        }
        gone
    }

    /// The one document the notebook's code cells are judged as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each code cell's text in order, each followed by a line feed;
    ///   a cell with no text is the empty text.
    /// - provides: the text the notebook's URI holds.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a notebook of two code cells around a markup cell
    ///   asserted at its exact text.
    /// - witness: `notebook::tests::a_change_splices_retypes_and_edits_the_cells`
    #[spec(ensures: |ret| ret.is_empty() || ret.ends_with('\n'))]
    #[inline]
    #[must_use]
    pub fn text(&self) -> String
    {
        let mut text = String::new();
        for laid in self.laid() {
            text.push_str(laid.text);
            text.push('\n');
        }
        text
    }

    /// The publication `publication` of the one document at `uri`, split into
    /// one for each code cell.
    ///
    /// # Specification
    /// - requires: `publication` was judged over [`Notebook::text`].
    /// - ensures: one publication per code cell, in order, at the cell's URI
    ///   and its text's version, versionless when `publication` is. Each
    ///   diagnostic goes to the cell its start lies in, a start at a cell's
    ///   trailing line feed being that cell's, its range in the cell's own
    ///   lines and characters, its end cut at the cell's end; each related
    ///   location at `uri` moves to the cell its start lies in likewise, and
    ///   every other location is kept. No code cell answers nothing.
    /// - provides: what a client holding the notebook's cells is published.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a diagnostic in the second cell, one running past the
    ///   first cell's end, one at the end of the document, and a related
    ///   location in the other cell, each asserted at its exact cell and range.
    /// - witness: `notebook::tests::a_publication_splits_into_its_cells_in_their_coordinates`
    #[spec(ensures: |ret| ret.len() <= self.order.len())]
    #[inline]
    #[must_use]
    pub fn split(
        &self,
        uri: &DocumentUri,
        publication: &PublishParams,
    ) -> Vec<PublishParams>
    {
        let text = self.text();
        let index = LineIndex::new(text.as_str().into());
        let laid = self.laid();
        let mut placed: Vec<Vec<Diagnostic>> = laid.iter().map(|_| Vec::new()).collect();
        for diagnostic in &publication.diagnostics {
            let (Place(place), range) = placed_range(&laid, &index, diagnostic.range);
            let mut moved = diagnostic.clone();
            moved.range = range;
            for related in &mut moved.related_information {
                if related.location.uri == *uri {
                    let (Place(at), range) = placed_range(&laid, &index, related.location.range);
                    if let Some(cell) = laid.get(at) {
                        related.location = Location {
                            uri: cell.uri.clone(),
                            range,
                        };
                    }
                }
            }
            if let Some(cell) = placed.get_mut(place) {
                cell.push(moved);
            }
        }
        laid.iter()
            .zip(placed)
            .map(|(cell, diagnostics)| PublishParams {
                uri: cell.uri.clone(),
                version: publication.version.map(|_| cell.version),
                diagnostics,
            })
            .collect()
    }

    /// An empty, versionless publication for each code cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cleared(&self) -> Vec<PublishParams>
    {
        self.laid()
            .iter()
            .map(|cell| PublishParams {
                uri: cell.uri.clone(),
                version: None,
                diagnostics: Vec::new(),
            })
            .collect()
    }

    /// The code cells, in order, as the one document lays them out.
    ///
    /// # Specification
    /// trivial.
    fn laid(&self) -> Vec<Laid<'_>>
    {
        let mut start = 0_usize;
        let mut laid = Vec::new();
        for cell in &self.order {
            if cell.kind != CellKind::CODE {
                continue;
            }
            let (version, text) = self.texts.get(&cell.document).map_or_else(
                || (DocumentVersion::default(), ""),
                |held| (held.version, held.text.as_str()),
            );
            laid.push(Laid {
                uri: &cell.document,
                version,
                start,
                text,
                index: LineIndex::new(text.into()),
            });
            start = start.saturating_add(text.len()).saturating_add(1_usize);
        }
        laid
    }
}

/// The index of a code cell in [`Notebook::laid`].
#[repr(transparent)]
struct Place(usize);

/// The code cell of `laid` that `range` of the one document `index` was built
/// over starts in, and `range` in that cell's own lines and characters.
///
/// # Specification
/// - requires: `laid` is [`Notebook::laid`] of the notebook whose text `index`
///   was built over, and holds a cell.
/// - ensures: the last cell starting at or before the range's start, and the
///   range's ends taken into that cell's text, each clamped to the text's end
///   and the end to no earlier than the start.
/// - provides: the placement [`Notebook::split`] makes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Notebook::split`].
/// - witness: `notebook::tests::a_publication_splits_into_its_cells_in_their_coordinates`
#[spec(ensures: |ret| ret.0.0 < laid.len().max(1_usize))]
fn placed_range(
    laid: &[Laid<'_>],
    index: &LineIndex<'_>,
    range: Range,
) -> (Place, Range)
{
    let start = usize::from(range.start.byte(index));
    let end = usize::from(range.end.byte(index)).max(start);
    let place = laid
        .partition_point(|cell| cell.start <= start)
        .saturating_sub(1_usize);
    let Some(cell) = laid.get(place)
    else {
        return (Place(place), range);
    };
    let length = cell.text.len();
    let first = start.saturating_sub(cell.start).min(length);
    let last = end.saturating_sub(cell.start).clamp(first, length);
    let local = Range::of_bytes(&cell.index, ByteOffset::from(first), ByteOffset::from(last))
        .unwrap_or_default();
    (Place(place), local)
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use serde_json::Value;
    use serde_json::json;

    use super::Notebook;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::Diagnostic;
    use crate::protocol::DidOpenNotebookParams;
    use crate::protocol::DocumentUri;
    use crate::protocol::DocumentVersion;
    use crate::protocol::Location;
    use crate::protocol::NotebookChange;
    use crate::protocol::PublishParams;
    use crate::protocol::RelatedInformation;
    use crate::protocol::Severity;

    /// The notebook `params` opens.
    ///
    /// # Specification
    /// trivial.
    fn opened(params: &Value) -> Notebook
    {
        let DidOpenNotebookParams {
            notebook_document,
            cell_text_documents,
        } = serde_json::from_value(params.clone()).expect("the parameters read");
        Notebook::opened(notebook_document, cell_text_documents)
    }

    /// The parameters opening a notebook of a code cell, a markup cell and a
    /// code cell, with the texts `first` and `second` in its code cells.
    ///
    /// # Specification
    /// trivial.
    fn three(
        first: &Value,
        second: &Value,
    ) -> Value
    {
        json!({
            "notebookDocument": { "uri": "file:///tmp/n.ipynb", "notebookType": "jupyter-notebook",
                "version": 1_i32, "cells": [
                    { "kind": 2_i32, "document": "cell:a" },
                    { "kind": 1_i32, "document": "cell:m" },
                    { "kind": 2_i32, "document": "cell:b" },
                ] },
            "cellTextDocuments": [
                { "uri": "cell:a", "languageId": "gandr", "version": 3_i32, "text": first },
                { "uri": "cell:m", "languageId": "markdown", "version": 1_i32, "text": "# prose" },
                { "uri": "cell:b", "languageId": "gandr", "version": 5_i32, "text": second },
            ],
        })
    }

    #[test]
    fn a_change_splices_retypes_and_edits_the_cells()
    {
        let mut notebook = opened(&three(&json!("def a = 1 ;"), &json!("def b = a ;")));
        assert_eq!(
            notebook.text(),
            "def a = 1 ;\ndef b = a ;\n",
            "the code cells in order, markup left out"
        );
        let change: NotebookChange = serde_json::from_value(json!({ "cells": {
            "structure": {
                "array": { "start": 2_i32, "deleteCount": 1_i32,
                    "cells": [{ "kind": 2_i32, "document": "cell:c" }] },
                "didOpen": [{ "uri": "cell:c", "languageId": "gandr", "version": 1_i32,
                    "text": "def c = 3 ;" }],
                "didClose": [{ "uri": "cell:b" }],
            },
            "textContent": [{ "document": { "uri": "cell:a", "version": 4_i32 },
                "changes": [{ "range": { "start": { "line": 0_i32, "character": 8_i32 },
                    "end": { "line": 0_i32, "character": 9_i32 } }, "text": "7" }] }],
        } }))
        .expect("the change reads");
        assert_eq!(
            notebook.change(change),
            vec![DocumentUri::from("cell:b")],
            "the code cell the splice removed is answered"
        );
        assert_eq!(
            notebook.text(),
            "def a = 7 ;\ndef c = 3 ;\n",
            "the inserted cell takes the removed one's place, the edit applied"
        );
        let retyped: NotebookChange = serde_json::from_value(json!({ "cells": {
            "data": [{ "kind": 1_i32, "document": "cell:a" }],
        } }))
        .expect("the change reads");
        assert_eq!(
            notebook.change(retyped),
            vec![DocumentUri::from("cell:a")],
            "a code cell made markup is answered"
        );
        assert_eq!(notebook.text(), "def c = 3 ;\n", "and judged no longer");
        assert_eq!(
            notebook.change(NotebookChange::default()),
            Vec::<DocumentUri>::new(),
            "a change of metadata alone changes no cell"
        );
    }

    #[test]
    fn a_publication_splits_into_its_cells_in_their_coordinates()
    {
        let notebook = opened(&three(
            &json!("def a = 1 ;\ndef x = 2 ;"),
            &json!("def b = q ;"),
        ));
        let uri = DocumentUri::from("file:///tmp/n.ipynb");
        let range = |line: u32, start: u32, end_line: u32, end: u32| Range {
            start: Position {
                line: Line::from(line),
                character: Character::from(start),
            },
            end: Position {
                line: Line::from(end_line),
                character: Character::from(end),
            },
        };
        let at = |line: u32, start: u32, end_line: u32, end: u32| {
            serde_json::to_value(range(line, start, end_line, end)).expect("a range encodes")
        };
        let mut related = Diagnostic::new(
            range(2_u32, 8_u32, 2_u32, 9_u32),
            Severity::ERROR,
            String::from("m"),
        );
        related.related_information = vec![RelatedInformation {
            location: Location {
                uri: uri.clone(),
                range: range(1_u32, 4_u32, 1_u32, 5_u32),
            },
            message: String::from("here"),
        }];
        let published: Vec<Value> = notebook
            .split(&uri, &PublishParams {
                uri: uri.clone(),
                version: Some(DocumentVersion::default()),
                diagnostics: vec![
                    related,
                    Diagnostic::new(
                        range(1_u32, 0_u32, 2_u32, 3_u32),
                        Severity::ERROR,
                        String::from("m"),
                    ),
                    Diagnostic::new(
                        range(3_u32, 0_u32, 3_u32, 0_u32),
                        Severity::ERROR,
                        String::from("m"),
                    ),
                ],
            })
            .iter()
            .map(|params| serde_json::to_value(params).expect("a publication encodes"))
            .collect();
        assert_eq!(
            published,
            vec![
                json!({ "uri": "cell:a", "version": 3_i32, "diagnostics": [
                    { "range": at(1_u32, 0_u32, 1_u32, 11_u32), "severity": 1_i32,
                        "source": "gandr", "message": "m" },
                ] }),
                json!({ "uri": "cell:b", "version": 5_i32, "diagnostics": [
                    { "range": at(0_u32, 8_u32, 0_u32, 9_u32), "severity": 1_i32,
                        "source": "gandr", "message": "m", "relatedInformation": [{
                            "location": { "uri": "cell:a", "range": at(1_u32, 4_u32, 1_u32, 5_u32) },
                            "message": "here" }] },
                    { "range": at(0_u32, 11_u32, 0_u32, 11_u32), "severity": 1_i32,
                        "source": "gandr", "message": "m" },
                ] }),
            ],
            "each diagnostic in the cell it starts in, in that cell's coordinates, \
             cut at its end; the document's end is the last cell's"
        );
        assert_eq!(
            notebook
                .cleared()
                .iter()
                .map(|params| params.uri.clone())
                .collect::<Vec<_>>(),
            vec![DocumentUri::from("cell:a"), DocumentUri::from("cell:b")],
            "each code cell is cleared"
        );
    }
}
