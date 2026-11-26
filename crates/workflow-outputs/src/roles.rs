//! The roles of a corpus source: one line for each span that the highlight
//! gives it, its byte range, its role and its text, quoted and escaped.

use core::fmt;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RoleTable;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::HlRole;
use gandr_surface_syntax::SourceText;

/// Why the roles of a source could not be written.
///
/// # Specification
/// - provides: one variant for each refusal; each carries its detail.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RolesError
{
    /// The grammar gives no role table.
    Grammar
    {
        /// The refusal of the grammar.
        detail: String,
    },
    /// The source gives no tree.
    Parse
    {
        /// The refusal of the parser.
        detail: String,
    },
    /// The role table refuses the tree.
    Highlight
    {
        /// The refusal of the table.
        detail: String,
    },
}

impl fmt::Display for RolesError
{
    /// Writes one line that names the refusal and its detail.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Grammar { ref detail } => write!(f, "the grammar gives no role table: {detail}"),
            Self::Parse { ref detail } => write!(f, "the source gives no tree: {detail}"),
            Self::Highlight { ref detail } => {
                write!(f, "the role table refuses the tree: {detail}")
            },
        }
    }
}

/// A refusal is an error value, so a caller can return it.
impl core::error::Error for RolesError
{
}

/// The name of `role`: the name of its variant.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub const fn role_name(role: HlRole) -> &'static str
{
    match role {
        HlRole::Keyword => "Keyword",
        HlRole::Operator => "Operator",
        HlRole::FunctionDef => "FunctionDef",
        HlRole::FunctionCall => "FunctionCall",
        HlRole::VariableDef => "VariableDef",
        HlRole::VariableParam => "VariableParam",
        HlRole::Member => "Member",
        HlRole::Variable => "Variable",
        HlRole::Constructor => "Constructor",
        HlRole::Type => "Type",
        HlRole::TypeBuiltin => "TypeBuiltin",
        HlRole::TypeVariable => "TypeVariable",
        HlRole::Number => "Number",
        HlRole::Boolean => "Boolean",
        HlRole::Character => "Character",
        HlRole::StringLit => "StringLit",
        HlRole::Escape => "Escape",
        HlRole::Comment => "Comment",
        HlRole::Hole => "Hole",
        HlRole::Label => "Label",
        HlRole::Path => "Path",
        HlRole::Directive => "Directive",
        HlRole::Other => "Other",
    }
}

/// The writer of the roles under one grammar.
#[derive(Debug)]
pub struct Roles<'grammar>
{
    /// The grammar that parses each source.
    pbg: &'grammar Pbg,
    /// The role of each mold of the grammar.
    table: RoleTable,
}

impl<'grammar> Roles<'grammar>
{
    /// The writer of the roles of `pbg`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`RolesError::Grammar`] when `pbg` gives no role table.
    #[inline]
    pub fn new(pbg: &'grammar Pbg) -> Result<Self, RolesError>
    {
        let table = RoleTable::build(pbg).map_err(|error| RolesError::Grammar {
            detail: error.to_string(),
        })?;
        Ok(Self { pbg, table })
    }

    /// The roles of the source `text`: `start..end Role "text"` for each
    /// span, in the order of the spans.
    ///
    /// # Specification
    /// - ensures: each line ends with a quote.
    ///
    /// # Errors
    /// [`RolesError`] when `text` gives no tree, or the table refuses it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition gives a keyword, a name and a number,
    ///   each on its line with its range.
    /// - witness: `roles::tests::a_definition_has_a_keyword_a_name_and_a_number`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |lines| lines.lines().all(|line| line.ends_with('"'))))]
    #[inline]
    pub fn value(
        &self,
        text: &str,
    ) -> Result<String, RolesError>
    {
        let parsed =
            parse(self.pbg, SourceText::from(text)).map_err(|error| RolesError::Parse {
                detail: error.to_string(),
            })?;
        let tree = parsed.tree();
        let spans = self
            .table
            .highlight(tree)
            .map_err(|error| RolesError::Highlight {
                detail: error.to_string(),
            })?;
        let mut out = String::new();
        for span in spans {
            let start = usize::from(span.range.start());
            let end = usize::from(span.range.end());
            let written = text.get(start .. end).unwrap_or_default();
            let _written = writeln!(
                out,
                "{start}..{end} {} \"{}\"",
                role_name(span.role),
                written.escape_debug()
            );
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::built_in;

    use super::Roles;

    /// A definition gives a keyword, a name and a number, each on its line
    /// with its range.
    #[test]
    fn a_definition_has_a_keyword_a_name_and_a_number()
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let roles = Roles::new(&pbg).expect("the grammar gives a role table");
        let lines = roles
            .value(include_str!("compute/fixtures/a-definition-of-one.gandr"))
            .expect("the source gives roles");
        assert!(
            lines.starts_with("0..3 Keyword \"def\"\n"),
            "the keyword is first: {lines}"
        );
        assert!(
            lines.contains(" Number \"1\"\n"),
            "the number has its role: {lines}"
        );
    }
}
