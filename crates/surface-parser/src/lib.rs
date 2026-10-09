//! The **gandr surface parser**: source text in, a molded
//! [`SyntaxTree`](gandr_surface_syntax::SyntaxTree) and its completion
//! obligations out.
//!
//! - [`label()`] splits a source into lexemes, losslessly: every byte belongs
//!   to exactly one token, layout included.
//! - [`Molder`] chooses each token's mold from the grammar's candidates, the
//!   one whose completion obligations are least.
//! - [`MeldState`] is the resumable push machine over the checked grammar:
//!   `push` is total, a batch parse is the fold of `push` followed by
//!   [`commit`](MeldState::commit), and [`Checkpoint`] snapshots resume
//!   anywhere.
//! - [`Oblig`], [`ObligationInstance`] and [`Delta`] are the completion
//!   obligations: the material a partial parse is missing, ordered by severity.
//! - [`parse()`] runs the three over one source.
//!
//! The design is stated in this crate's `README.md`: its synopsis, and the
//! decision sections that follow it.

#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

mod label;
mod meld;
mod mold;
mod oblig;
mod parse;
#[cfg(test)]
mod testing;

pub use crate::label::Lexeme;
pub use crate::label::Token;
pub use crate::label::label;
pub use crate::meld::Checkpoint;
pub use crate::meld::CheckpointBytes;
pub use crate::meld::CheckpointBytesRef;
pub use crate::meld::CheckpointError;
pub use crate::meld::Completion;
pub use crate::meld::CompletionStatus;
pub use crate::meld::Expected;
pub use crate::meld::FormContinuation;
pub use crate::meld::Frontier;
pub use crate::meld::HeadOperandPresence;
pub use crate::meld::Mark;
pub use crate::meld::MeldError;
pub use crate::meld::MeldState;
pub use crate::meld::MoldAdmissibility;
pub use crate::meld::MoldedTile;
pub use crate::meld::OpenFormPresence;
pub use crate::meld::OperandContinuation;
pub use crate::meld::SpaceText;
pub use crate::meld::TileText;
pub use crate::mold::CandidateLabel;
pub use crate::mold::Molder;
pub use crate::mold::TokenText;
pub use crate::mold::candidate_labels;
pub use crate::oblig::Delta;
pub use crate::oblig::DeltaEmptyStatus;
pub use crate::oblig::OBLIG_CLASS_COUNT;
pub use crate::oblig::Oblig;
pub use crate::oblig::ObligClassIndex;
pub use crate::oblig::ObligationCount;
pub use crate::oblig::ObligationInstance;
pub use crate::parse::ParseCleanStatus;
pub use crate::parse::ParseResult;
pub use crate::parse::parse;
