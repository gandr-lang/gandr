//! What a source run alone answers its host: a string whole, or another end
//! spelled, and the reasons that a source runs nothing.
//!
//! The workspace runs a source alone (`workspace::ran_alone` and
//! `workspace::answered_alone`). The manifold reads what it answers and reads
//! the placements that a run spells, so these types stay below the run stage.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_surface_lowering::decode_escapes;
use gandr_surface_syntax::SourceFragment;

use crate::manifold::Placed;

/// What a function a source declares answered its host.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Answered
{
    /// A string, whole.
    Text(String),
    /// Any other end, spelled: the evaluation the run ended with, or the kind
    /// of value it answered, never the value.
    Other(String),
}

/// Why [`ran_alone`](crate::workspace::ran_alone) or
/// [`answered_alone`](crate::workspace::answered_alone) ran nothing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unran
{
    /// The source cannot be read.
    Unread
    {
        /// What reading it met.
        message: String,
    },
    /// The source does not compose, or is refused as a whole.
    Refused
    {
        /// Why, spelled.
        why: String,
    },
}

/// A run's value as the machine spells it, read from its start.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Spelling<'text>(&'text str);

impl<'text> From<&'text str> for Spelling<'text>
{
    /// Reads the text as a run's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl Spelling<'_>
{
    /// The strings the spelling lists: `cons "a" (cons "b" nil)` is `a` then
    /// `b`, each decoded as a string literal is; none for any other spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the strings of a spelling `cons s₁ (cons s₂ (… nil))`, each
    ///   `sᵢ` a quoted string read up to its unescaped closing quote and
    ///   decoded, in order; none when anything else stands anywhere in it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a reading of the spelling, which a
    ///   clause would restate whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two members, none, and a string standing alone each
    ///   read as listed or not.
    /// - witness: `entry::answered::tests::a_run_s_spelling_lists_its_strings_2687`
    #[inline]
    pub(crate) fn listed(self) -> Option<Vec<String>>
    {
        self.listed_as(Self::quoted)
    }

    /// The placements the spelling lists: `cons (At "far" *{.key = "<key>",
    /// .secret = "far", .sockets = "127.0.0.1:4733"}) nil` is the world `far`
    /// at the site of that key and socket, once, and `(Instances "far" *{…}
    /// 2)` is it twice; none for any other spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each element of a spelling `cons p₁ (cons p₂ (… nil))` read
    ///   in order, each `pᵢ` written `(At n s)`, read with the count `1`, or
    ///   `(Instances n s c)`, read with the count `c` as spelled, `n` a quoted
    ///   string decoded and `s` a site's model spelled `*{.key = k, .secret =
    ///   e, .sockets = o}`, its labels in the order a run spells them and `k`
    ///   and `o` read as quoted strings decoded; none when anything else stands
    ///   anywhere in it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::listed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a placement of each constructor, none, and one whose
    ///   site lacks its sockets each read as listed or not.
    /// - witness: `entry::answered::tests::a_run_s_spelling_lists_its_placements_3374`
    pub(crate) fn placements(self) -> Option<Vec<Placed>>
    {
        self.listed_as(|spelling| {
            let inner = spelling.0.strip_prefix('(')?;
            let (counted, rest) = match inner.strip_prefix("At ") {
                Some(rest) => (false, rest),
                None => (true, inner.strip_prefix("Instances ")?),
            };
            let (name, Self(rest)) = Self(rest).quoted()?;
            let (key, Self(rest)) = Self(rest.strip_prefix(" *{.key = ")?).quoted()?;
            let (_secret, Self(rest)) = Self(rest.strip_prefix(", .secret = ")?).quoted()?;
            let (sockets, Self(rest)) = Self(rest.strip_prefix(", .sockets = ")?).quoted()?;
            let rest = rest.strip_prefix('}')?;
            let (count, rest) = if counted {
                rest.strip_prefix(' ')?.split_once(')')?
            }
            else {
                ("1", rest.strip_prefix(')')?)
            };
            Some((
                Placed {
                    name,
                    key,
                    sockets,
                    count: String::from(count),
                },
                Self(rest),
            ))
        })
    }

    /// The elements the spelling lists, each read by `element`: `cons e₁
    /// (cons e₂ (… nil))`, every tail but the last `nil` in parentheses.
    ///
    /// # Specification
    /// trivial.
    fn listed_as<T>(
        self,
        element: impl Fn(Self) -> Option<(T, Self)>,
    ) -> Option<Vec<T>>
    {
        let mut rest = self.0;
        let mut elements = Vec::new();
        let mut opened = 0_usize;
        while let Some(after) = rest.strip_prefix("cons ") {
            let (read, Self(after)) = element(Self(after))?;
            elements.push(read);
            let after = after.strip_prefix(' ')?;
            if after.starts_with("nil") {
                rest = after;
                break;
            }
            rest = after.strip_prefix('(')?;
            opened = opened.saturating_add(1);
        }
        let closers = rest.strip_prefix("nil")?;
        (closers.len() == opened && closers.bytes().all(|byte| byte == b')')).then_some(elements)
    }

    /// The string literal the spelling opens with, decoded, and what follows
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn quoted(self) -> Option<(String, Self)>
    {
        let content = self.0.strip_prefix('"')?;
        let mut escaped = false;
        for (at, character) in content.char_indices() {
            match character {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                '"' => {
                    let written = content.get(.. at)?;
                    let after = content.get(at.saturating_add(1) ..)?;
                    return Some((decode_escapes(SourceFragment::from(written)), Self(after)));
                },
                _ => {},
            }
        }
        None
    }
}

#[cfg(test)]
mod tests
{
    use super::Spelling;

    #[test]
    fn a_run_s_spelling_lists_its_strings_2687()
    {
        assert_eq!(
            Spelling("cons \"hello\" (cons \"tools\" nil)").listed(),
            Some(Vec::from([String::from("hello"), String::from("tools")])),
            "two members read in order"
        );
        assert_eq!(
            Spelling("nil").listed(),
            Some(Vec::new()),
            "no member reads as none"
        );
        assert_eq!(
            Spelling("cons \"a \\\"b\\\"\" nil").listed(),
            Some(Vec::from([String::from("a \"b\"")])),
            "a member's escapes are decoded"
        );
        for other in [
            "\"hello\"",
            "cons \"a\" (cons \"b\" nil",
            "cons \"a\" nil)",
            "cons 1 nil",
            "cons(\"a\", nil)",
        ] {
            assert_eq!(Spelling(other).listed(), None, "`{other}` lists no strings");
        }
    }

    #[test]
    fn a_run_s_spelling_lists_its_placements_3374()
    {
        let placed = |name: &str, sockets: &str, count: &str| crate::manifold::Placed {
            name: String::from(name),
            key: String::from("k"),
            sockets: String::from(sockets),
            count: String::from(count),
        };
        let site = |sockets: &str| {
            format!("*{{.key = \"k\", .secret = \"far\", .sockets = \"{sockets}\"}}")
        };
        assert_eq!(
            Spelling(&format!(
                "cons (At \"far\" {}) (cons (Instances \"near\" {} 2) nil)",
                site("127.0.0.1:4733"),
                site("")
            ))
            .placements(),
            Some(Vec::from([
                placed("far", "127.0.0.1:4733", "1"),
                placed("near", "", "2")
            ])),
            "a placement of each constructor reads its site's key and sockets in order, `At` \
             counting one"
        );
        assert_eq!(
            Spelling("nil").placements(),
            Some(Vec::new()),
            "no placement reads as none"
        );
        assert_eq!(
            Spelling("cons (At \"far\" *{.key = \"k\", .secret = \"far\"}) nil").placements(),
            None,
            "a placement whose site lacks its sockets lists nothing"
        );
    }
}
