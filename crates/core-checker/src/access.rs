//! Temporary access in the judgement: a held value, the access that lends
//! it to a view in a mode, the view's two eliminators, and the refusals that
//! name them.
//!
//! # Temporary access is a yield-once accessor
//!
//! A language without first-class references states with a coroutine what a
//! reference type states with a lifetime: an access lends a held value to
//! its body and takes it back when the body ends. The accessor is a
//! one-shot stack resident in the linear zone `Σ` with exactly two
//! eliminators: `resume`, which runs the write-back, and `abort`, which
//! runs the unwind and never the write-back. Swift ships the shape — a
//! single-yield coroutine's token is ended only by `end_apply` or
//! `abort_apply`, an abort takes the yield's separate unwind edge, and an
//! aborted coroutine may not throw — and one-shot costs no expressiveness.
//!
//! ```text
//! x : A held, not lent exclusively      Σ, w : View^m A ⊢ t ⇓ F B      w ∉ fv(B)
//! ─────────────────────────────────────────────────────────────── (Access)
//! Σ ⊢ access^m x as w { t } ⇓ F B
//!   m = exclusive: x unreadable for t; resume(w, v) writes v back into x;
//!                  abort(w) runs the unwind u : F^∅ 1
//!   m = shared:    x not lent at all to an exclusive access; x readable and
//!                  frozen for t; w ends with t, no eliminator, no unwind
//! ```
//!
//! |form|written|rule|
//! |---|---|---|
//! |hold|`hold x = v; t`|`v` synthesises `A`; `t` runs with `x`, a slot of `Σ` at `A`|
//! |hold at grade one|`hold[1] x = v; t`|as the hold, `v` made in place; `x` is never read, and each view of it is read at most once|
//! |access|`access x as w { t } unwind { u }`|`x` is lent exclusively; `t` runs with `w`, a slot of `Σ` at `A`|
//! |shared access|`access shared x as w { t }`|`x` is lent shared; `t` runs with `w`, a slot of `Σ` at `A`|
//! |access at a place|`access x[i] as w { t } unwind { u }`, `access shared x[i] as w { t }`|`A` is `List E`; `i` checks against the integer type; `x` is lent in the mode; `t` runs with `w`, a slot of `Σ` at `E`|
//! |resume|`resume(w, v)`|`w` is exclusive; `v` checks against `A`; `w` is spent; synthesises `F 1`|
//! |abort|`abort(w)`|`w` is exclusive; `w` is spent; synthesises `F 1`|
//!
//! The rules run as frames of the judgement's one machine:
//!
//! |rule|frame|what it waits on|
//! |---|---|---|
//! |hold|`HoldValue`|the held value's synthesis, then opens the slot|
//! |hold|`HoldBody`|the scope's judgement, then drops the slot|
//! |access|`AccessIndex`|an access at a place's index, checked against the integer type, then lends the place|
//! |access|`AccessBody`|the body's judgement, then requires an exclusive view spent|
//! |access|`AccessUnwind`|an exclusive access's unwind, checked against the pure `F 1`|
//! |resume|`ResumeValue`|the written value's check, then spends the view|
//!
//! # Held is a linear hypothesis, at a grade
//!
//! A held value is a slot of `Σ`, opened by `hold` and by nothing else, at a
//! grade. At grade `ω`, `hold x = v;`, a read of the slot copies the value it
//! holds and spends nothing; the slot is dropped where the hold's scope ends.
//! At grade one, `hold[1] x = v;`, the value has no other holder and is never
//! copied while held, so a write-back through an exclusive view needs no
//! count of other holders. The value enters made in place — a constructor, a
//! literal, a tuple, an injection, a record or a list — and any other is
//! [`AccessDefect::HeldShared`]. A read of the slot, or of a shared view of
//! it, is [`AccessDefect::HeldCopied`]. An exclusive view of it is read at
//! most once: the read moves the value out (the view's slot is left
//! `LinearUse::Moved`), a second read is [`AccessDefect::HeldCopied`], an
//! abort after the move is [`AccessDefect::Moved`], and only `resume`, which
//! writes a value back, ends the view. Exclusivity is the zone's at either
//! grade: the slot is never captured by a thunk, a fixpoint, a branch, a
//! handler, a first-class stack or a shift ([`AccessDefect::HeldCaptured`]),
//! and the hold stands at a pure returner, as a fork does, so no operation a
//! handler could resume twice runs while it holds.
//!
//! # The view is a slot, not a type
//!
//! `View^m A` is the role of the view's slot, not a type former: the slot is
//! declared at `A`, the checker marks it a view of its access, whose mode the
//! access names, and a read of it copies the value it was lent at grade `ω`
//! and moves it out at grade one. A view is never a value, so the rule's side
//! condition `w ∉ fv(B)` is that the view does not escape the body: a view
//! named by a former that may run it other than once, or that outlives the
//! body, is [`AccessDefect::Escaped`], in either mode, unless a region keeps
//! a shared one (§ Regions).
//!
//! # Modes: exclusive, or shared and frozen
//!
//! An access lends its held slot in one of two modes, and the lending is the
//! access law: shared beside shared, nothing beside exclusive. Lent
//! exclusively, `x` is unreadable and cannot be accessed again for the
//! body's extent ([`AccessDefect::Lent`]). Lent shared, `x` stays readable
//! and can be accessed shared again, nested or in turn, but an exclusive
//! access of it is [`AccessDefect::Lent`] until the shared access ends: `x`
//! is frozen for the extent, so every read of `x` and of each shared view
//! answers the one value. A shared view is read-only: it ends with its
//! body, nothing is written back, and an eliminator of it is
//! [`AccessDefect::ReadOnly`]. The machine runs a shared access as no
//! access at all — the view is the held cell itself, and no frame waits on
//! the body.
//!
//! # Places
//!
//! An access lends a place of its held slot: the held value whole, or the
//! element at an index, `x[i]`. The index is a value checked against the
//! integer type where the access stands; a linear index is lent shared with
//! the place for the body and never consumed. A place needs a list
//! ([`AccessDefect::Unindexed`] otherwise), and the view is declared at the
//! list's element type. The lending is the held slot's whatever the index, so
//! an exclusive view of one element excludes a view of any other. A resume
//! writes the element back at its index and the rest of the list stands as it
//! was; an index that names no element stops the machine where the access
//! runs.
//!
//! # Regions: a value kept past its access
//!
//! A capability scope carries a region, and a value checked at `A at c` is
//! kept in the region of the scope binding `c`: it lives until that scope
//! ends and never stands where a type kept in no region is asked. A thunk or
//! a stack kept there may name a shared view whose hold encloses the scope:
//! the view lives as long as the region, and the held value stays frozen, an
//! exclusive access of it [`AccessDefect::Kept`], until the scope ends. An
//! exclusive view is kept nowhere, since its write-back ends it. A scope
//! whose answer names its own region, and a thunk or a stack kept in no
//! region as deep that names a value kept there, are
//! [`AccessDefect::KeptEscaped`].
//!
//! # Two eliminators, one shot
//!
//! The body of an exclusive access ends its view exactly once.
//! `resume(w, v)` spends the view and records `v`; the machine writes `v`
//! back into `x` when it pops the access's frame. `abort(w)` spends the view
//! and records nothing; the machine runs the unwind when it pops the frame,
//! and `x` keeps the value it had. An exclusive view still live when the
//! body ends is [`AccessDefect::Unended`]; a view used after either
//! eliminator — read, resumed again or aborted — is [`AccessDefect::Spent`].
//! The eliminators stand in the body's tail; nothing refuses one elsewhere,
//! because after either the view is spent and `x` is lent until the body
//! ends, so nothing after it can observe the access. The access answers what
//! its body answers, and the write-back runs on `resume` alone.
//!
//! # The unwind runs under the empty row
//!
//! The unwind is checked against the pure returner of the unit: an abort
//! runs it while the access is being torn down, where no handler may be
//! asked for anything. An effect the unwind performs, or a call that needs
//! one, is [`AccessDefect::UnwindEffect`] at the computation whose row
//! exceeded the empty one. An `abandon` written in an unwind is refused the
//! same way, so no cancellation reaches an unwind already running. An unwind
//! may read `x`: the machine restores the value `x` held before it runs.
//!
//! # Spelling
//!
//! `hold x = e;` binds the held value at grade `ω` and `hold[1] x = e;` at
//! grade one; `access x as w { t } unwind {
//! u }` the exclusive view, `access shared x as w { t }` the shared one, and
//! `resume(w, e)` and `abort(w)` end an exclusive view. The mode is a word
//! after `access`: exclusive is the default, unwritten, and
//! `access exclusive x as w { … }` spells it; the unwind clause is an
//! exclusive access's alone, optional, and absent means `unwind { pure unit }`.
//!
//! # What later work may assume
//!
//! - An `io_uring` mock: a held value lives in one machine cell for its hold's
//!   scope; an access pushes one constant frame, `resume` records the new value
//!   and `abort` records nothing, and the frame's pop writes back or runs the
//!   unwind under the empty row. An operation a scope's clause answers inside a
//!   hold hands the clause a continuation holding the cell, which the clause
//!   resumes or abandons exactly once
//!   ([`crate::session::LinearityDefect::ContinuationUsedTwice`]), so the cell
//!   is never duplicated.
//!
//! # References
//!
//! - Without Boats. "References are like jumps." (2024). <https://without.boats/blog/references-are-like-jumps/>
//!   — a language without first-class references needs an effect or coroutine
//!   system for what lifetime-parameterised types represent.
//! - Swift. "SIL instruction set": `begin_apply`, `end_apply`, `abort_apply`. <https://github.com/swiftlang/swift/blob/main/docs/SIL/Instructions.md>
//!   — the yield-once coroutine whose token has exactly two eliminators.
//! - Ana Lúcia de Moura and Roberto Ierusalimschy. "Revisiting
//!   Coroutines." _ACM Transactions on Programming Languages and Systems_
//!   31(2) (2009). <https://doi.org/10.1145/1462166.1462167> — one-shot
//!   continuations and coroutines are equally expressive.

use crate::session::Capture;

/// How a held value or a view broke the access discipline.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AccessDefect
{
    /// An access names a linear slot that holds no value: an endpoint or a
    /// view.
    NotHeld,
    /// A held value was read while an access lends it exclusively, or
    /// accessed again where its lending excludes the access: anything beside
    /// an exclusive lend, or an exclusive access beside a shared one.
    Lent,
    /// A held value was named where its holding may run other than once, or
    /// a hold stands where a handler could resume it twice.
    HeldCaptured
    {
        /// What may run it.
        by: Capture,
    },
    /// A view was named where its use may run other than once: it escapes
    /// the body of its access.
    Escaped
    {
        /// What may run it.
        by: Capture,
    },
    /// An exclusive access's body ended with its view neither resumed nor
    /// aborted.
    Unended,
    /// A view was used after its resume or abort.
    Spent,
    /// A resume or an abort names a linear slot that is no view.
    NotAView,
    /// A resume or an abort names a shared view: a shared view is read-only
    /// and ends with its body.
    ReadOnly,
    /// An access's unwind performs an effect: an unwind runs under the empty
    /// row.
    UnwindEffect,
    /// An access at a place names a held value with no elements an index
    /// reads: its type is no list.
    Unindexed,
    /// A hold at grade one enters a value other than one made in place: a
    /// constructor, a literal, a tuple, an injection, a record or a list.
    /// Any other value may have another holder.
    HeldShared,
    /// A value held at grade one is copied: the held slot read, a shared view
    /// of it read, or an exclusive view of it read a second time.
    HeldCopied,
    /// An abort names a view of a value held at grade one after a read moved
    /// the value out: the held slot would keep the value the read took.
    Moved,
    /// An exclusive access names a held slot a view of which is kept in a
    /// region still live: the kept view would observe the write-back.
    Kept,
    /// A value kept in a region would outlive it: a capability scope's answer
    /// names a value kept in the scope's own region or a deeper one, or a
    /// thunk or a stack kept in no region as deep names one.
    KeptEscaped,
}
