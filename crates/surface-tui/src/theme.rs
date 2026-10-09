//! The face's styles: one per highlight role, one per transcript line kind.

use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::OutKind;
use ratatui::style::Color;
use ratatui::style::Modifier;
use ratatui::style::Style;

/// The style a span of `role` is painted in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every role sets a foreground, so no classified span takes the
///   colour of the text around it; [`HlRole::Other`] and the plain variable
///   roles set the terminal's default foreground. Roles the language server
///   sends as one token type share a style — keywords and booleans; defined and
///   called functions; defined and referenced variables; types and built-in
///   types; string, character, escape and path literals; holes and directives —
///   and the theme groups further where colours run short: constructors with
///   functions, members and parameters with numbers, labels with operators,
///   type variables with types, holes with keywords.
/// - provides: the face's theme, total over the roles.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every role is enumerated and its foreground asserted set,
///   the unclassified role asserted at the terminal default, and the keyword
///   grouping asserted; L2 — a painted frame's keyword cells carry the keyword
///   colour.
/// - witness: `theme::tests::every_role_and_kind_sets_a_foreground`
/// - witness: `theme::tests::other_is_the_terminal_default`
/// - witness: `theme::tests::keyword_and_boolean_share_the_keyword_colour`
#[inline]
#[must_use]
pub const fn style_of(role: HlRole) -> Style
{
    let colour = match role {
        | HlRole::Keyword | HlRole::Boolean | HlRole::Hole | HlRole::Directive => Color::Magenta,
        | HlRole::Operator | HlRole::Label => Color::Cyan,
        | HlRole::FunctionDef | HlRole::FunctionCall | HlRole::Constructor => Color::Blue,
        | HlRole::VariableDef | HlRole::Variable | HlRole::Other => Color::Reset,
        | HlRole::VariableParam | HlRole::Member | HlRole::Number => Color::Yellow,
        | HlRole::Type | HlRole::TypeBuiltin | HlRole::TypeVariable => Color::Green,
        | HlRole::StringLit | HlRole::Character | HlRole::Escape | HlRole::Path => Color::Red,
        | HlRole::Comment => Color::DarkGray,
    };
    Style::new().fg(colour)
}

/// The style a transcript line of `kind` is painted in.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every kind sets a foreground. The echo's mark is bold at the
///   terminal default, its text painted by role instead; a type line is green,
///   as types are; a goal magenta, as holes are; a diagnostic red; blame bold
///   red; a stuck evaluation yellow; a value at the terminal default; a note
///   dark grey.
/// - provides: the kind half of the theme, applied at draw time, so a theme
///   change restyles the whole history.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every kind is enumerated and its foreground asserted set;
///   L2 — a fixed session's painted frame carries each line's kind style cell
///   by cell.
/// - witness: `theme::tests::every_role_and_kind_sets_a_foreground`
/// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
#[inline]
#[must_use]
pub const fn style_of_kind(kind: OutKind) -> Style
{
    match kind {
        | OutKind::Source => Style::new().fg(Color::Reset).add_modifier(Modifier::BOLD),
        | OutKind::Type => Style::new().fg(Color::Green),
        | OutKind::Value => Style::new().fg(Color::Reset),
        | OutKind::Goal => Style::new().fg(Color::Magenta),
        | OutKind::Diag => Style::new().fg(Color::Red),
        | OutKind::Blame => Style::new().fg(Color::Red).add_modifier(Modifier::BOLD),
        | OutKind::Stuck => Style::new().fg(Color::Yellow),
        | OutKind::Info => Style::new().fg(Color::DarkGray),
    }
}

/// The style maps' cases.
#[cfg(test)]
mod tests
{
    use gandr_surface_render_remote::HlRole;
    use gandr_surface_render_remote::OutKind;
    use ratatui::style::Color;

    use super::style_of;
    use super::style_of_kind;

    /// Every highlight role.
    const ROLES: [HlRole; 23] = [
        HlRole::Keyword,
        HlRole::Operator,
        HlRole::FunctionDef,
        HlRole::FunctionCall,
        HlRole::VariableDef,
        HlRole::VariableParam,
        HlRole::Member,
        HlRole::Variable,
        HlRole::Constructor,
        HlRole::Type,
        HlRole::TypeBuiltin,
        HlRole::TypeVariable,
        HlRole::Number,
        HlRole::Boolean,
        HlRole::Character,
        HlRole::StringLit,
        HlRole::Escape,
        HlRole::Comment,
        HlRole::Hole,
        HlRole::Label,
        HlRole::Path,
        HlRole::Directive,
        HlRole::Other,
    ];

    /// Every transcript line kind.
    const KINDS: [OutKind; 8] = [
        OutKind::Source,
        OutKind::Type,
        OutKind::Value,
        OutKind::Blame,
        OutKind::Stuck,
        OutKind::Diag,
        OutKind::Goal,
        OutKind::Info,
    ];

    /// Both maps are total: every role and every kind sets a foreground, so
    /// nothing painted inherits the colour around it. The matches below stop
    /// compiling when a role or a kind is added, until it is listed here.
    #[test]
    fn every_role_and_kind_sets_a_foreground()
    {
        for role in ROLES {
            match role {
                | HlRole::Keyword
                | HlRole::Operator
                | HlRole::FunctionDef
                | HlRole::FunctionCall
                | HlRole::VariableDef
                | HlRole::VariableParam
                | HlRole::Member
                | HlRole::Variable
                | HlRole::Constructor
                | HlRole::Type
                | HlRole::TypeBuiltin
                | HlRole::TypeVariable
                | HlRole::Number
                | HlRole::Boolean
                | HlRole::Character
                | HlRole::StringLit
                | HlRole::Escape
                | HlRole::Comment
                | HlRole::Hole
                | HlRole::Label
                | HlRole::Path
                | HlRole::Directive
                | HlRole::Other => {},
            }
            assert!(style_of(role).fg.is_some(), "{role:?} sets a foreground");
        }
        for kind in KINDS {
            match kind {
                | OutKind::Source
                | OutKind::Type
                | OutKind::Value
                | OutKind::Blame
                | OutKind::Stuck
                | OutKind::Diag
                | OutKind::Goal
                | OutKind::Info => {},
            }
            assert!(
                style_of_kind(kind).fg.is_some(),
                "{kind:?} sets a foreground"
            );
        }
    }

    /// An unclassified span is painted at the terminal default, deliberately,
    /// rather than left without a style.
    #[test]
    fn other_is_the_terminal_default()
    {
        assert_eq!(
            style_of(HlRole::Other).fg,
            Some(Color::Reset),
            "the unclassified role is the terminal default"
        );
    }

    /// A boolean is painted as a keyword, as the language server sends both
    /// under one token type.
    #[test]
    fn keyword_and_boolean_share_the_keyword_colour()
    {
        assert_eq!(
            style_of(HlRole::Keyword),
            style_of(HlRole::Boolean),
            "booleans share the keyword style"
        );
    }
}
