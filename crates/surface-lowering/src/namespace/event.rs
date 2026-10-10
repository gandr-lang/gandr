//! The handler seam: the three namespace events.
//!
//! The engine decides no policy. What it would otherwise decide is performed
//! as one of three events and settled by the [`NamespaceEventHandler`] the
//! caller installs:
//!
//! | event | performed when | the question it asks |
//! | --- | --- | --- |
//! | not-found | an emptiness check found nothing | is a selection that matched nothing a mistake, and is it fatal? |
//! | shadow | a union found two bindings at one path | which survives, and is a collision allowed at all? |
//! | hook | a `hook` constructor was reached | what does this labelled extension point do? |
//!
//! The events are algebraic effects in the design this ports; Rust has no
//! effect handlers, so the surface is a trait of three methods. Warn-and-allow
//! and reject are two handlers, not two engine modes, and a handler carries its
//! own state through `&mut self`, an event log included. [`PermissiveHandler`]
//! is the warn-and-allow default: it records every event, rejects none, lets
//! a later binding shadow an earlier one and runs every hook as the identity.

use alloc::string::String;
use alloc::vec::Vec;
use core::error::Error;
use core::fmt;

use anodized::spec;

use crate::namespace::path::NamePath;
use crate::namespace::trie::Binding;
use crate::namespace::trie::Collision;
use crate::namespace::trie::Trie;

/// Which of the three events a rejection refused.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EventKind
{
    /// An emptiness check found nothing under the reported path.
    NotFound,
    /// A union found two bindings at the reported path.
    Shadow,
    /// A `hook` constructor reached the reported path.
    Hook,
}

impl fmt::Display for EventKind
{
    /// Writes `not-found`, `shadow` or `hook`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let text = match *self {
            | Self::NotFound => "not-found",
            | Self::Shadow => "shadow",
            | Self::Hook => "hook",
        };
        f.write_str(text)
    }
}

/// A handler's explanation for refusing an event.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RejectionReason(String);

impl From<&str> for RejectionReason
{
    /// The reason `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &str) -> Self
    {
        Self(String::from(text))
    }
}

impl From<String> for RejectionReason
{
    /// The reason `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for RejectionReason
{
    /// The reason's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_str()
    }
}

impl fmt::Display for RejectionReason
{
    /// Writes the reason's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.as_str())
    }
}

/// A handler refused an event, aborting the run that performed it.
///
/// The engine has no opinion on whether a collision or an empty selection is
/// fatal, so it propagates the refusal unchanged and stops.
///
/// # Specification
/// - requires: the producer supplies the event it is refusing.
/// - ensures: the kind, whole path and reason travel together; the interpreter
///   returns that refusal rather than replacing it with a different event.
/// - provides: a policy-owned refusal, not proof that an event occurred.
/// - executable: none — correspondence and propagation require the producing
///   handler and interpreter run, neither of which a rejection value holds.
///
/// # Adequacy
/// - hypothesis: L3 — rejecting handlers refuse each event kind at a known
///   path, distinguishing the policy refusal from a structural scope failure.
/// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_missing_selection`
/// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_shadow`
/// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_hook`

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EventRejection
{
    /// The refused event.
    kind: EventKind,
    /// The path the event was performed at.
    path: NamePath,
    /// The handler's explanation.
    reason: RejectionReason,
}

impl EventRejection
{
    /// The refusal of the `kind` event at `path`, for `reason`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        kind: EventKind,
        path: NamePath,
        reason: RejectionReason,
    ) -> Self
    {
        Self { kind, path, reason }
    }

    /// The refused event.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> EventKind
    {
        self.kind
    }

    /// The path the refused event was performed at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn path(&self) -> &NamePath
    {
        &self.path
    }

    /// The handler's explanation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reason(&self) -> &RejectionReason
    {
        &self.reason
    }
}

impl fmt::Display for EventRejection
{
    /// Writes "the {kind} event at `{path}` was rejected: {reason}".
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The formatter's error.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "the {} event at `{}` was rejected: {}",
            self.kind, self.path, self.reason
        )
    }
}

impl Error for EventRejection
{
}

/// One performed event, as a permissive handler records it.
///
/// # Specification
/// - requires: a producer records a performed event at its whole path.
/// - ensures: the variant distinguishes emptiness, collision and hook events;
///   hook records retain the producer's label.
/// - provides: event data without replaying the namespace operation.
/// - executable: none — this record does not hold the interpreter run that
///   establishes its path and label correspondence.
///
/// # Adequacy
/// - hypothesis: L3 — a nested emptiness check, collision and hook expose their
///   accumulated paths, and one mixed run fixes their order.
/// - witness: `namespace::namespace::a_nested_event_reports_the_accumulated_prefix`
/// - witness: `namespace::namespace::a_nested_shadow_reports_the_accumulated_prefix`
/// - witness: `namespace::namespace::a_nested_hook_reports_the_accumulated_prefix`
/// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NamespaceEvent<Label>
{
    /// An emptiness check at `path` found nothing.
    NotFound
    {
        /// The path whose subtree was empty.
        path: NamePath,
    },
    /// A union found two bindings at `path`.
    Shadow
    {
        /// The colliding path.
        path: NamePath,
    },
    /// The hook labelled `label` ran on the namespace at `path`.
    Hook
    {
        /// The prefix the hook ran under.
        path: NamePath,
        /// The hook's label.
        label: Label,
    },
}

/// The policy seam: what the three namespace events mean.
///
/// `Data` and `Tag` are the carrier's binding components, so one handler can
/// serve any payload. `Label` is associated because the handler is what gives
/// hook labels meaning.
///
/// # Specification
/// - requires: the interpreter supplies the current event's path and operands.
/// - ensures: the handler chooses whether execution continues and, for a
///   collision or hook, the value with which it continues.
/// - provides: policy without changing the modifier language.
/// - executable: none — this trait declares callbacks; applying their choices
///   and stopping on refusal belong to the interpreter, not a held trait value.
///
/// # Adequacy
/// - hypothesis: L3 — permissive and rejecting handlers cover all three
///   callback kinds and both successful and refused runs.
/// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
/// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_missing_selection`
/// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_shadow`
/// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_hook`
pub trait NamespaceEventHandler<Data, Tag>
{
    /// The hook vocabulary this handler interprets.
    type Label;

    /// An emptiness check at `path` found nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: success continues the run with the namespace unchanged; the
    ///   event is a signal, not a transformation.
    /// - provides: the place a policy decides whether an empty selection is a
    ///   mistake.
    /// - fails: a rejection aborts the run.
    /// - panics: none.
    /// - executable: none — continuing with the current namespace is an
    ///   interpreter transition; this required callback receives no namespace.
    ///
    /// # Errors
    /// An [`EventRejection`] when the policy treats an empty selection as
    /// fatal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — permissive and rejecting handlers settle one missing
    ///   selection; the caller observes continued or aborted execution.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
    /// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_missing_selection`
    fn not_found(
        &mut self,
        path: &NamePath,
    ) -> Result<(), EventRejection>;

    /// A union found two bindings at `path`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned binding survives at `path`; a handler may return
    ///   either side or a binding of its own.
    /// - provides: the place a policy settles a collision.
    /// - fails: a rejection aborts the run.
    /// - panics: none.
    /// - executable: none — any returned binding is permitted; its installation
    ///   at the path is an interpreter transition outside this callback.
    ///
    /// # Errors
    /// An [`EventRejection`] when the policy forbids the collision.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a later binding survives a permissive collision,
    ///   while the rejecting policy aborts at that collision.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
    /// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_shadow`
    fn shadow(
        &mut self,
        path: &NamePath,
        collision: Collision<Data, Tag>,
    ) -> Result<Binding<Data, Tag>, EventRejection>;

    /// The hook labelled `label` reached the namespace `subject` at `path`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned namespace replaces `subject` in the run; the
    ///   identity is a valid reading of any label.
    /// - provides: the extension point of the modifier language.
    /// - fails: a rejection aborts the run.
    /// - panics: none.
    /// - executable: none — any returned namespace is permitted; replacement
    ///   and abortion are interpreter transitions outside this callback.
    ///
    /// # Errors
    /// An [`EventRejection`] when the policy does not know `label` or refuses
    /// to run it here.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one hook preserves its subject under the permissive
    ///   policy and one is refused by the rejecting policy.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
    /// - witness: `namespace::namespace::a_rejecting_handler_refuses_a_hook`
    fn hook(
        &mut self,
        path: &NamePath,
        label: &Self::Label,
        subject: Trie<Data, Tag>,
    ) -> Result<Trie<Data, Tag>, EventRejection>;
}

/// The warn-and-allow policy: record every event, reject none.
///
/// A later binding shadows an earlier one and hooks are the identity, so a run
/// under this handler always succeeds and its recorded events are what a
/// diagnostic layer reports.
///
/// # Specification
/// - requires: callbacks are invoked in the order the interpreter performs
///   them.
/// - ensures: each callback appends one event; clearing forgets the log without
///   changing the policy, collisions choose the later binding and hooks
///   preserve their subject.
/// - provides: an ordered, reusable warn-and-allow event recorder.
/// - executable: none — this build's specification facade does not expose the
///   type-item runtime; callback predicates check append and clear boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — a three-event run observes order and chosen payloads; a
///   clear followed by another run observes log reuse.
/// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
/// - witness: `namespace::namespace::clearing_a_permissive_handler_forgets_what_it_recorded`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PermissiveHandler<Label>
{
    /// Every event performed since construction or the last clear, in order.
    events: Vec<NamespaceEvent<Label>>,
}

impl<Label> Default for PermissiveHandler<Label>
{
    /// A handler with no recorded events.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl<Label> PermissiveHandler<Label>
{
    /// A handler with no recorded events.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self { events: Vec::new() }
    }

    /// Every event performed so far, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn events(&self) -> &[NamespaceEvent<Label>]
    {
        self.events.as_slice()
    }

    /// Forget the recorded events, keeping the handler usable.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no event is recorded; later events record from empty.
    /// - provides: one handler reused across runs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a handler holding an event, cleared, then recording
    ///   one more, asserted as the exact log both times.
    /// - witness: `namespace::namespace::clearing_a_permissive_handler_forgets_what_it_recorded`
    #[spec(
        ensures: self.events.is_empty(),
    )]
    #[inline]
    pub fn clear(&mut self)
    {
        self.events.clear();
    }
}

impl<Data, Tag, Label> NamespaceEventHandler<Data, Tag> for PermissiveHandler<Label>
where
    Label: Clone,
{
    type Label = Label;

    /// Record the not-found event and continue.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends one not-found record at exactly the supplied path and
    ///   succeeds; earlier events remain in order.
    /// - provides: nonfatal empty-selection diagnostics.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Errors
    /// Never.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run performing all three events, asserted as the
    ///   exact log.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
    #[spec(
        captures: before = self.events.len(),
        ensures: |ret| {
            ret.is_ok()
                && self.events.len() == before.saturating_add(1)
                && matches!(self.events.last(), Some(NamespaceEvent::NotFound { path: recorded }) if recorded == path)
        },
    )]
    #[inline]
    fn not_found(
        &mut self,
        path: &NamePath,
    ) -> Result<(), EventRejection>
    {
        self.events
            .push(NamespaceEvent::NotFound { path: path.clone() });
        Ok(())
    }

    /// Record the shadow event and keep the later binding.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends one shadow record at the supplied path and returns
    ///   the later binding; earlier events remain in order.
    /// - provides: warn-and-allow collision resolution.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Errors
    /// Never.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run performing all three events, asserted as the
    ///   exact log and namespace. Generic payload identity is witnessed here;
    ///   the runtime predicate needs no equality bound on payloads or tags.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
    #[spec(
        captures: before = self.events.len(),
        ensures: |ret| {
            ret.is_ok()
                && self.events.len() == before.saturating_add(1)
                && matches!(self.events.last(), Some(NamespaceEvent::Shadow { path: recorded }) if recorded == path)
        },
    )]
    #[inline]
    fn shadow(
        &mut self,
        path: &NamePath,
        collision: Collision<Data, Tag>,
    ) -> Result<Binding<Data, Tag>, EventRejection>
    {
        self.events
            .push(NamespaceEvent::Shadow { path: path.clone() });
        Ok(collision.latter)
    }

    /// Record the hook event and run the identity.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends one hook record with the supplied path and label and
    ///   returns the unchanged subject; earlier events remain in order.
    /// - provides: diagnostic hooks with no namespace transformation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Errors
    /// Never.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run performing all three events, asserted as the
    ///   exact log and namespace. Labels and payloads need no equality bound;
    ///   the runtime predicate checks the event path and retained binding
    ///   count.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
    #[spec(
        captures: before = (self.events.len(), subject.binding_count()),
        ensures: |ret| {
            self.events.len() == before.0.saturating_add(1)
                && matches!(self.events.last(), Some(NamespaceEvent::Hook { path: recorded, .. }) if recorded == path)
                && ret
                    .as_ref()
                    .is_ok_and(|namespace| namespace.binding_count() == before.1)
        },
    )]
    #[inline]
    fn hook(
        &mut self,
        path: &NamePath,
        label: &Label,
        subject: Trie<Data, Tag>,
    ) -> Result<Trie<Data, Tag>, EventRejection>
    {
        self.events.push(NamespaceEvent::Hook {
            path: path.clone(),
            label: label.clone(),
        });
        Ok(subject)
    }
}
