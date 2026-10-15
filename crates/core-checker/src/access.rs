//! Temporary access in the judgement: a value held exclusively, the access
//! that lends it to a view, the view's two eliminators, and the refusals
//! that name them.
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
//! x : A held exclusively      Σ, w : View A ⊢ t ⇓ F B      w ∉ fv(B)
//! ──────────────────────────────────────────────────── (Access)
//! Σ ⊢ access x as w { t } unwind { u } ⇓ F B
//!     resume(w, v) writes v back into x;  abort(w) runs u : F^∅ 1
//! ```
//!
//! |form|written|rule|
//! |---|---|---|
//! |hold|`hold x = v; t`|`v` synthesises `A`; `t` runs with `x`, a slot of `Σ` at `A`|
//! |access|`access x as w { t } unwind { u }`|`x` is lent; `t` runs with `w`, a slot of `Σ` at `A`|
//! |resume|`resume(w, v)`|`v` checks against `A`; `w` is spent; synthesises `F 1`|
//! |abort|`abort(w)`|`w` is spent; synthesises `F 1`|
//!
//! The rules run as frames of the judgement's one machine:
//!
//! |rule|frame|what it waits on|
//! |---|---|---|
//! |hold|`HoldValue`|the held value's synthesis, then opens the slot|
//! |hold|`HoldBody`|the scope's judgement, then drops the slot|
//! |access|`AccessBody`|the body's judgement, then requires the view spent|
//! |access|`AccessUnwind`|the unwind's check against the pure `F 1`|
//! |resume|`ResumeValue`|the written value's check, then spends the view|
//!
//! # Held exclusively is a linear hypothesis
//!
//! The core offers no grades today: the capability's consumable grade is
//! refused and graded hypotheses are not scheduled, so a value held
//! exclusively is a slot of `Σ`, opened by `hold` and by nothing else. A
//! read of the slot copies the value it holds and spends nothing; the slot
//! is dropped where the hold's scope ends. Exclusivity is the zone's: the
//! slot is never captured by a thunk, a fixpoint, a branch, a handler, a
//! first-class stack or a shift ([`AccessDefect::HeldCaptured`]), and the
//! hold stands at a pure returner, as a fork does, so no operation a handler
//! could resume twice runs while it holds. **Alternative.** A graded
//! hypothesis at grade one, which needs the grades the core does not have.
//! **Reversal.** Grades arriving: a held value becomes a grade-one
//! hypothesis and the hold's slot its binder.
//!
//! # The view is a slot, not a type
//!
//! `View^m A` is the role of the view's slot, not a type former: the slot is
//! declared at `A`, the checker marks it a view, and a read of it copies the
//! value it was lent. A view is never a value, so the rule's side condition
//! `w ∉ fv(B)` is that the view does not escape the body: a view named by a
//! former that may run it other than once, or that outlives the body, is
//! [`AccessDefect::Escaped`]. While the access lends `x`, `x` is unreadable
//! and cannot be accessed again ([`AccessDefect::Lent`]): that is the access
//! law, exclusivity for the body's extent. The mode `m` admits one mode
//! today, exclusive; shared views are an open design question, and nothing
//! here reads a mode. **Reversal.** The region index: when it
//! arrives, the view's extent becomes an erased index `ρ`, the view's slot a
//! type `View^m_ρ A`, and the escape refusal the index's own side condition.
//!
//! # Two eliminators, one shot
//!
//! The body ends its view exactly once. `resume(w, v)` spends the view and
//! records `v`; the machine writes `v` back into `x` when it pops the
//! access's frame. `abort(w)` spends the view and records nothing; the
//! machine runs the unwind when it pops the frame, and `x` keeps the value
//! it had. A view still live when the body ends is
//! [`AccessDefect::Unended`]; a view used after either eliminator — read,
//! resumed again or aborted — is [`AccessDefect::Spent`]. The eliminators
//! stand in the body's tail; nothing refuses one elsewhere, because after
//! either the view is spent and `x` is lent until the body ends, so nothing
//! after it can observe the access. The access answers what its body
//! answers.
//!
//! **Choice.** The write-back runs on `resume` only. **Alternative.** The
//! staged register's earlier form, where abandoning an accessor runs the
//! write-back automatically: an abort that writes back is a resume, and the
//! unwind would have no edge of its own. **Alternative.** A plain mutable
//! binding — a `var`, or a `let`-bound mutable view — which has no
//! eliminator to end the access, so neither the write-back's moment nor the
//! unwind exists, and exclusivity is a lint rather than the zone's.
//!
//! # The unwind runs under the empty row
//!
//! The unwind is checked against the pure returner of the unit: an abort
//! runs it while the access is being torn down, where no handler may be
//! asked for anything. An effect the unwind performs, or a call that needs
//! one, is [`AccessDefect::UnwindEffect`] at the computation whose row
//! exceeded the empty one. An unwind may read `x`: the machine restores the
//! value `x` held before it runs.
//!
//! # Spelling
//!
//! `hold x = e;` binds the held value, `access x as w { t } unwind { u }`
//! the view, `resume(w, e)` and `abort(w)` end it; the unwind clause is
//! optional and absent means `unwind { pure unit }`. The mode is unwritten:
//! exclusive is the only one. **Alternatives.** `var x = e;` for the
//! binding, which reads as plain mutability, the declined alternative;
//! member calls `w.resume(e)` and `w.abort()`, which read a view as a value
//! with methods.
//!
//! # What later work may assume
//!
//! - A region index: a view is a slot of `Σ` declared at the held type; its
//!   extent is its access's body, decided by the zone's discipline and refused
//!   by [`AccessDefect::Escaped`]; no type mentions a view. The index replaces
//!   that refusal and nothing else.
//! - An `io_uring` mock: a held value lives in one machine cell for its hold's
//!   scope; an access pushes one constant frame, `resume` records the new value
//!   and `abort` records nothing, and the frame's pop writes back or runs the
//!   unwind under the empty row. A hold stands at a pure returner today: an
//!   operation inside one that a handler resumes twice would duplicate the
//!   cell, so an effectful submission over a held buffer first needs one-shot
//!   resumption of the handler's continuation.
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
    /// A held value was read, or accessed again, while an access lends it.
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
    /// An access's body ended with its view neither resumed nor aborted.
    Unended,
    /// A view was used after its resume or abort.
    Spent,
    /// A resume or an abort names a linear slot that is no view.
    NotAView,
    /// An access's unwind performs an effect: an unwind runs under the empty
    /// row.
    UnwindEffect,
}
