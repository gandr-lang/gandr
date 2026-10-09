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
    /// - requires: nothing.
    /// - ensures: the text names the event kind, the path — the root as `.` —
    ///   and the handler's reason, because this rendering is what a consumer
    ///   with no other reporting layer shows.
    /// - provides: the message of every namespace refusal.
    /// - fails: propagates the formatter's error.
    /// - panics: none.
    ///
    /// # Errors
    /// The formatter's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one rejection of each kind, one of them at the root,
    ///   each asserted as the exact text.
    /// - witness: `namespace::namespace::a_rejection_renders_its_event_kind_path_and_reason`
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
    ///
    /// # Errors
    /// An [`EventRejection`] when the policy treats an empty selection as
    /// fatal.
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
    ///
    /// # Errors
    /// An [`EventRejection`] when the policy forbids the collision.
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
    ///
    /// # Errors
    /// An [`EventRejection`] when the policy does not know `label` or refuses
    /// to run it here.
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
    /// trivial.
    ///
    /// # Errors
    /// Never.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run performing all three events, asserted as the
    ///   exact log.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
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
    /// trivial.
    ///
    /// # Errors
    /// Never.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run performing all three events, asserted as the
    ///   exact log and namespace.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
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
    /// trivial.
    ///
    /// # Errors
    /// Never.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one run performing all three events, asserted as the
    ///   exact log and namespace.
    /// - witness: `namespace::namespace::the_permissive_handler_records_all_three_events`
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
