//! The circuit block form: `sign` blocks, kind-keyword members, the
//! four-glyph arrow grid, two-sided named port lists, and the `node` / `feed`
//! body statements.
//!
//! The form has four shapes:
//!
//! * **Declarations are judgments.** Every member reads `name : signature`, and
//!   a block-bodied member reads `name : sphere { filler }` — the signature
//!   left of the block is the boundary data. The kind keywords `sort` / `data`
//!   / `oper` / `rule` carry the dimension.
//! * **The arrow grid, four glyphs and never more.** The shaft carries the
//!   kind-class and the head carries directedness: `-->` / `<->` are the
//!   circuit 1-cell formers and `==>` / `<=>` the rewrite faces at every
//!   dimension. Dimension is read from the endpoints, never from the arrow, so
//!   the grid scales with no new glyphs; the term language's `->` is untouched
//!   and disjoint.
//! * **Ports are two-sided.** Inputs left of the arrow, outputs right, both as
//!   named lists. The bare-sort and unnamed-port spellings are **sugar** for
//!   the named-port normal form, and both mold through the same shape here.
//! * **Bodies are keyword-led statements with an optional label slot.** `node :
//!   …` is the plain hyperedge and `node w1 : …` names the occurrence; `feed :
//!   (a) --> (b)` is the feedback back-edge.
//!
//! # What the grammar admits and the checker confirms
//!
//! The grammar admits **any** grid glyph at **every** arrow position, and it is
//! deliberate. Every arrow reports the kind of the thing it belongs to, and a
//! disagreement in any one is a localized error with a name — which a parse
//! failure is not. A body line's arrow is moreover confirmed against the
//! **applied head's** kind, an environment fact no grammar can see. So the
//! four glyphs are one alternation here and the confirmation is the
//! checker's.
//!
//! # Why these forms are keyword-led and where they are reserved
//!
//! Every form and member is first-token-discriminated by a keyword, so no new
//! shared-prefix window opens. Only the two **item-position** leads (`sign` and
//! `oper`) are globally reserved in the labeler's keyword table: at a fresh
//! top-level slot a lowercase word is otherwise an expression statement. The
//! member lead `sort` and the body leads `node` / `feed` stay contextual — they
//! are `≐`-successors of an open block, inadmissible at every other
//! lowercase-word slot, so a user program may still bind them as ordinary
//! names.
//!
//! The tree-sitter grammar does not produce these constructs, so their
//! provenances are in [`PBG_ONLY_KINDS`](crate::PBG_ONLY_KINDS).

use alloc::vec::Vec;

use gandr_theory_graphs::Prec;

use crate::Adaptation;
use crate::AdaptationReason;
use crate::PbgError;
use crate::PrecName;
use crate::PrecTable;
use crate::Provenance;
use crate::Regex;
use crate::Rule;
use crate::RuleName;
use crate::Sort;
use crate::SurfaceForm;
use crate::TileLabel;

/// Builds the circuit block form's rules.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the `sign` block declaration, then the top-level `oper` and
///   `rule` declaration, each keyword-led with its members, ports and body
///   statements inlined, over tiles and [`Sort::Type`] and [`Sort::Expression`]
///   holes.
/// - fails: `precs` does not hold `item.singleton`.
/// - panics: none.
/// - intension: members, ports and body statements are inlined rather than
///   declared as rules, so no member opener gains a form-first item mold that
///   would tie at a fresh top-level slot.
///
/// # Errors
/// [`PbgError::MissingPrec`] naming the absent group.
pub(super) fn rules(precs: &PrecTable) -> Result<Vec<Rule>, PbgError>
{
    let item = precs.prec(PrecName("item.singleton"))?;
    let mut out = Vec::new();
    sign_declaration(&mut out, item);
    circuit_declarations(&mut out, item);
    Ok(out)
}

/// Append the `sign` block declaration.
///
/// `sign Nat { sort … ; data … ; oper … ; rule … ; }`. Every member is
/// **terminated** by `;` (the surface's declaration terminator), and the
/// terminator is load-bearing, not admitted:
/// an unseparated member list is a clean parse of the WRONG tree — a member
/// ends in a sort hole (the signature's bare-sort side), the walk's
/// `≐`-relation crosses the hole, and at the fill position the next member's
/// lead can collapse the whole member into one repaired region. The
/// mandatory terminator restores the discrimination: after the hole only `;`
/// is admissible, which never competes with hole content. The declined `,`
/// is not admissible at this slot — unlike the nested `data` / `codata`
/// generator lists (the term forms' `member_list`), where it stays so a stale
/// declaration parses whole and reaches the elaborator's decline. A
/// terminator-free spelling needs a molder key change first: hole-fill must
/// outrank `≐`-continuation. The
/// member family is inlined (never a standalone rule) so `sort` / `data` /
/// `oper` / `rule` never gain a form-first Item mold competing at a top-level
/// slot.
///
/// # Specification
/// trivial.
fn sign_declaration(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let mut sign = r(
        RuleName("sign_declaration"),
        Provenance("sign_declaration"),
        Sort::Item,
        p,
        seq([
            t(TileLabel("sign")),
            t(TileLabel("type_identifier")),
            t(TileLabel("{")),
            repeat(seq([sign_member(), t(TileLabel(";"))])),
            t(TileLabel("}")),
        ]),
    );
    sign.adaptations.push(Adaptation::new(
        RuleName("sign_declaration"),
        SurfaceForm("circuit_member"),
        AdaptationReason("inlined member family: the `sort` / `data` / `oper` / `rule` judgment members are a first-token-discriminated alternation inside the sign block, never standalone rules whose keyword would gain a form-first Item mold at a fresh top-level slot"),
    ));
    sign.adaptations.push(Adaptation::new(
        RuleName("sign_declaration"),
        SurfaceForm("circuit_signature"),
        AdaptationReason("inlined signature: the arrow-separated two-sided port list is kept LOCAL to each member so a named port list `( name : Type, … )` never becomes a standalone `(`-opened form competing with the parenthesized type at every type slot (the `op_result` precedent)"),
    ));
    out.push(sign);
}

/// Append the top-level circuit declaration.
///
/// `oper accumulate : (…) --> (…) { … }` and its `rule` sibling stand outside a
/// `sign` block as well as inside one, so `accumulate` can be declared at the
/// top level.
///
/// The two keywords lead **one** rule rather than two, because the tail they
/// share is the whole form: a second copy would clone the signature, the port
/// lists, and the body statements into a second set of molds, and the
/// `identifier` / `(` / `:` menus a duplicated tail widens are the hottest in
/// the grammar. The `oper` / `rule` alternation still gives each keyword its
/// own form-first mold, so the choice is locally decidable exactly as two rules
/// would make it; only the mold count differs.
///
/// # Specification
/// trivial.
fn circuit_declarations(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let mut declaration = r(
        RuleName("circuit_declaration"),
        Provenance("circuit_declaration"),
        Sort::Item,
        p,
        top_level_judgment(),
    );
    declaration.adaptations.push(Adaptation::new(
        RuleName("circuit_declaration"),
        SurfaceForm("circuit_body"),
        AdaptationReason("inlined body: the `{ node …; feed …; }` filler is kept local to the block-bodied declaration, so `{` never opens a standalone circuit-body form competing with the statement block at every brace"),
    ));
    declaration.adaptations.push(Adaptation::new(
        RuleName("circuit_declaration"),
        SurfaceForm("node_statement"),
        AdaptationReason("inlined statement: the plain hyperedge `node w1? : head(args) <arrow> (ports) ;` rides the body's statement alternation, first-token-discriminated by the contextual `node` keyword"),
    ));
    declaration.adaptations.push(Adaptation::new(
        RuleName("circuit_declaration"),
        SurfaceForm("feed_statement"),
        AdaptationReason("inlined statement: the feedback back-edge `feed w1? : (ports) <arrow> (ports) ;` — the only cycle-forming statement — rides the same alternation, first-token-discriminated by the contextual `feed` keyword"),
    ));
    out.push(declaration);
}

/// Build a `sign` member led by `oper` or `rule`.
///
/// Both genuine judgments use `name : signature { filler }?`. An `oper` also
/// preserves the parenthesis-led data-block spelling as one member so
/// description elaboration can issue the block-aware decline without parser
/// repair consuming a sibling. A `rule` carries the colon-led judgment and —
/// for the same reason, so the decline can name the spelling at the member
/// that wrote it — the data / codata **written face** `rule lhs ==> rhs`,
/// whose arrow rides the shared grid and whose sides are ordinary
/// expressions. The written face elaborates nowhere: description elaboration
/// declines it by name, which is exactly why it must parse whole rather than
/// leave its tail to parser repair, whose blob absorbs every member after it.
///
/// The judgment block body is optional because a declaration may be a
/// **boundary without a filler** — `oper add : (Nat, Nat) --> Nat` declares an
/// interface and nothing else, while `oper accumulate : … { … }` fills one.
///
/// The lead keyword is what arrow-kind confirmation reads: the declared kind
/// fixes the row of the arrow grid the signature's arrow must come from, so a
/// grammar admitting only the matching arrow would trade a nameable error for
/// a parse failure.
///
/// # Specification
/// trivial.
fn circuit_judgment() -> Regex
{
    alt([
        seq([
            t(TileLabel("oper")),
            t(TileLabel("identifier")),
            alt([circuit_judgment_tail(), data_spelled_oper_tail()]),
        ]),
        seq([
            t(TileLabel("rule")),
            t(TileLabel("identifier")),
            alt([rule_judgment_tail(), written_face_tail()]),
        ]),
    ])
}

/// Build the data / codata written-face tail `lhs ==> rhs` a `rule` member
/// may carry in place of its colon-led judgment.
///
/// The two arms past `rule <name>` are first-tile disjoint — `:` versus an
/// expression-start tile — so no shared-prefix window opens between the
/// judgment and the face. The face is deliberately *not* merged into
/// [`rule_judgment_tail`]'s expression alternation: that alternation sits
/// behind a mandatory `:`, and hoisting it would widen the judgment's own
/// menu rather than admit one declined spelling.
///
/// # Specification
/// trivial.
fn written_face_tail() -> Regex
{
    seq([h(Sort::Expression), arrow_grid(), h(Sort::Expression)])
}

/// Build the colon-led tail shared by circuit judgments.
///
/// # Specification
/// trivial.
fn circuit_judgment_tail() -> Regex
{
    seq([t(TileLabel(":")), signature(), opt(body())])
}

/// Build an expression-endpoint rewrite judgment, using the shared
/// parenthesized-expression family for the binder endpoint.
///
/// # Specification
/// trivial.
fn rule_judgment_tail() -> Regex
{
    seq([t(TileLabel(":")), rule_signature(), opt(body())])
}

/// Build a rewrite rule signature from expression endpoints.
///
/// # Specification
/// trivial.
fn rule_signature() -> Regex
{
    alt([
        seq([
            rule_parameter_group(),
            circuit_rule_face_arrow(),
            result_group(),
        ]),
        seq([
            h(Sort::Expression),
            circuit_rule_face_arrow(),
            h(Sort::Expression),
        ]),
    ])
}

/// Build the direct circuit telescope shape for a circuit signature.
///
/// The entry menu is deliberately narrow: a circuit binder is a `rule`/`data`
/// declaration or a typed port. This keeps the direct `(` / `)` tiles consumed
/// by circuit lowering while ordinary call arguments remain recursive
/// expressions.
///
/// # Specification
/// trivial.
fn rule_parameter_group() -> Regex
{
    seq([
        t(TileLabel("(")),
        comma1(alt([
            seq([
                t(TileLabel("rule")),
                t(TileLabel("identifier")),
                t(TileLabel(":")),
                h(Sort::Type),
                arrow_grid(),
                h(Sort::Type),
            ]),
            seq([
                t(TileLabel("data")),
                t(TileLabel("identifier")),
                t(TileLabel(":")),
                h(Sort::Type),
            ]),
            seq([t(TileLabel("identifier")), t(TileLabel(":")), h(Sort::Type)]),
        ])),
        t(TileLabel(")")),
    ])
}

/// Build the circuit rule-face arrow row.
///
/// All four circuit arrows remain admissible here so arrow-kind confirmation
/// can name a rule/oper row disagreement; the reversible `rule` case is a
/// surface-check diagnostic, not a grammar rejection. The `-->` and `<->`
/// forms likewise reach the existing named respell declines; narrowing this
/// row would turn those diagnostics into syntax errors.
///
/// # Specification
/// trivial.
fn circuit_rule_face_arrow() -> Regex
{
    arrow_grid()
}

/// Build the parenthesis-led data-block tail reserved for localized decline.
///
/// # Specification
/// trivial.
fn data_spelled_oper_tail() -> Regex
{
    seq([
        t(TileLabel("(")),
        opt(comma1(seq([
            t(TileLabel("identifier")),
            opt(seq([t(TileLabel(":")), h(Sort::Type)])),
        ]))),
        t(TileLabel(")")),
        opt(seq([t(TileLabel("->")), h(Sort::Type)])),
    ])
}

/// Build the same judgment at **item position**, where its sides must be
/// parenthesized.
///
/// The difference is forced, and it is the one place the sugar ladder does not
/// reach. A top-level form that can end in a **sort hole** does not close: the
/// melder has no following tile of an enclosing form to close it against, so a
/// bare-sort side detaches and the declaration silently keeps only its prefix
/// — a clean parse of the wrong tree, which the zero-obligation gate cannot
/// see. No other Item-sort form in this grammar ends in a sort hole either;
/// every `def` / `module` / `import` / `data` tail ends in `;`, `}`, or `)`.
///
/// Requiring parentheses restores that discipline: every branch here ends in
/// `)` or `}`. Inside a `sign` block the bare-sort spellings stay available,
/// because there the member's sort hole is form-**interior** — the block's own
/// members and its closing brace follow it.
///
/// # Specification
/// trivial.
fn top_level_judgment() -> Regex
{
    seq([
        alt([t(TileLabel("oper")), t(TileLabel("rule"))]),
        t(TileLabel("identifier")),
        t(TileLabel(":")),
        seq([parameter_group(), opt(seq([arrow_grid(), result_group()]))]),
        opt(body()),
    ])
}

/// Build one inlined `sign` member.
///
/// The four kind keywords carry the dimension, and each names what it declares:
/// `sort` a colour, `data` a constructor, `oper` a circuit 1-cell, `rule` a
/// rewrite face. `sort` and `data` are boundary-only; `oper` and `rule` may
/// carry a filler.
///
/// # Specification
/// trivial.
fn sign_member() -> Regex
{
    alt([
        // `sort Nat : Type` — a colour declaration; its right-hand side is an
        // ordinary type (the universe), not a circuit signature. An indexed
        // sort carries its parameter telescope before the colon.
        seq([
            t(TileLabel("sort")),
            t(TileLabel("type_identifier")),
            opt(parameter_group()),
            t(TileLabel(":")),
            h(Sort::Type),
        ]),
        // `data Zero : Nat` / `data Succ : Nat --> Nat` — an uppercase-led
        // constructor, so the member is case-discriminated from `oper` / `rule`
        // as well as keyword-discriminated. A constructor declares a boundary
        // and never fills one, so this branch carries no body.
        seq([
            t(TileLabel("data")),
            t(TileLabel("constructor")),
            t(TileLabel(":")),
            signature(),
        ]),
        circuit_judgment(),
    ])
}

/// Build a circuit signature: `ports <arrow> ports`, or the bare boundary that
/// desugars to one.
///
/// The arrow is optional because the bare-sort spelling is sugar: `data Zero :
/// Nat` is `() --> (_ : Nat)` and `data Succ : Nat --> Nat` is `(_ : Nat) -->
/// (_ : Nat)`. The named-port normal form is what the elaborator sees; the
/// grammar admits every spelling from bare sort to named ports, and the
/// desugaring — including which side a lone boundary lands on — is a later
/// pass's, not the tree's.
///
/// # Specification
/// trivial.
fn signature() -> Regex
{
    seq([parameter_side(), opt(seq([arrow_grid(), result_side()]))])
}

/// Build the **parameter** side of a signature: a bare sort (sugar) or a
/// parenthesized list whose entries may be kind-keyword binders.
///
/// The empty interface `()` is the list's nullary case rather than a second
/// `(`-led branch, so the opener owns exactly one mold and `()` never ties
/// against a one-port list.
///
/// # Specification
/// trivial.
fn parameter_side() -> Regex
{
    alt([h(Sort::Type), parameter_group()])
}

/// Build a parenthesized parameter list `( … )`, binders admitted.
///
/// # Specification
/// trivial.
fn parameter_group() -> Regex
{
    seq([
        t(TileLabel("(")),
        opt(comma1(parameter())),
        t(TileLabel(")")),
    ])
}

/// Build the **result** side of a signature: a bare sort (sugar) or a
/// parenthesized list of plain ports.
///
/// Binders are a parameter-side form only: a `rule` binder may appear in a
/// `rule`'s parameter list (a cell parameterized by rewrites), and confining
/// binders there keeps a second copy of the binder shapes off the
/// `identifier` and `rule` / `data` menus.
///
/// # Specification
/// trivial.
fn result_side() -> Regex
{
    alt([h(Sort::Type), result_group()])
}

/// Build a parenthesized result list `( … )`, plain ports only.
///
/// # Specification
/// trivial.
fn result_group() -> Regex
{
    seq([t(TileLabel("(")), opt(comma1(port())), t(TileLabel(")"))])
}

/// Build one parameter-list entry.
///
/// Two rungs beyond a plain [`port`]: the rewrite-sorted binder
/// `rule p : Nat ==> Nat` — which is also the pinned-endpoint form
/// `rule p : x ==> x′`, since an endpoint spelled by a variable molds through
/// the same type hole — and the data binder `data x : Nat` that a congruence
/// cell's telescope binds beside it.
///
/// # Specification
/// trivial.
fn parameter() -> Regex
{
    alt([
        port(),
        seq([
            t(TileLabel("rule")),
            t(TileLabel("identifier")),
            t(TileLabel(":")),
            h(Sort::Type),
            arrow_grid(),
            h(Sort::Type),
        ]),
        seq([
            t(TileLabel("data")),
            t(TileLabel("identifier")),
            t(TileLabel(":")),
            h(Sort::Type),
        ]),
    ])
}

/// Build one plain port: the named form `x : Nat`, or the unnamed sort that is
/// sugar for it (minting a fresh name in order).
///
/// # Specification
/// trivial.
fn port() -> Regex
{
    alt([
        seq([port_name(), t(TileLabel(":")), h(Sort::Type)]),
        h(Sort::Type),
    ])
}

/// Build a port name: an identifier, or `_` for the port the sugar ladder's
/// fresh-name minting writes out.
///
/// # Specification
/// trivial.
fn port_name() -> Regex
{
    alt([t(TileLabel("identifier")), t(TileLabel("_"))])
}

/// Build the four-glyph arrow grid.
///
/// The shaft carries the kind-class and the head carries directedness. All four
/// are admissible at every arrow position: which one *belongs* there is the
/// arrow-kind confirmation's question, and `<->` is reserved — it parses and is
/// declined until the reversible lane lands its checking story.
///
/// # Specification
/// trivial.
fn arrow_grid() -> Regex
{
    alt([
        t(TileLabel("-->")),
        t(TileLabel("<->")),
        t(TileLabel("==>")),
        t(TileLabel("<=>")),
    ])
}

/// Build a circuit body `{ node …; feed …; }`.
///
/// # Specification
/// trivial.
fn body() -> Regex
{
    seq([
        t(TileLabel("{")),
        repeat(body_statement()),
        t(TileLabel("}")),
    ])
}

/// Build one body statement.
///
/// Both statements carry an optional occurrence label between the keyword and
/// the `:` — the named-face slot the attachment discipline wants, kept open for
/// diagnostics. A `node` line applies a head to its input ports; a `feed` line
/// wires ports directly, and is the only statement that may close a cycle.
///
/// # Specification
/// trivial.
fn body_statement() -> Regex
{
    alt([
        seq([
            t(TileLabel("node")),
            opt(t(TileLabel("identifier"))),
            t(TileLabel(":")),
            application(),
            arrow_grid(),
            port_tuple(),
            t(TileLabel(";")),
        ]),
        seq([
            t(TileLabel("feed")),
            opt(t(TileLabel("identifier"))),
            t(TileLabel(":")),
            port_tuple(),
            arrow_grid(),
            port_tuple(),
            t(TileLabel(";")),
        ]),
    ])
}

/// Build a node line's head application `head(a, b)`.
///
/// # Specification
/// trivial.
fn application() -> Regex
{
    seq([
        t(TileLabel("identifier")),
        t(TileLabel("(")),
        opt(comma1(port_name())),
        t(TileLabel(")")),
    ])
}

/// Build a parenthesized tuple of port names `(a, b)` — a body line's wire
/// list, where every entry is already bound or being bound by name.
///
/// # Specification
/// trivial.
fn port_tuple() -> Regex
{
    seq([
        t(TileLabel("(")),
        opt(comma1(port_name())),
        t(TileLabel(")")),
    ])
}

/// Build a rule preserving its PBG-only provenance.
///
/// # Specification
/// trivial.
fn r(
    name: RuleName,
    provenance: Provenance,
    sort: Sort,
    prec: Prec,
    regex: Regex,
) -> Rule
{
    Rule::with_provenance(name, provenance, sort, prec, regex)
}

/// Build a terminal tile by label; mold identity is assigned at `Pbg` build.
///
/// # Specification
/// trivial.
fn t(label: TileLabel) -> Regex
{
    Regex::tile(label)
}

/// Build a sort hole.
///
/// # Specification
/// trivial.
fn h(sort: Sort) -> Regex
{
    Regex::sort(sort)
}

/// Build a sequence regex.
///
/// # Specification
/// trivial.
fn seq<const N: usize>(parts: [Regex; N]) -> Regex
{
    Regex::seq(parts)
}

/// Build an alternation regex.
///
/// # Specification
/// trivial.
fn alt<const N: usize>(parts: [Regex; N]) -> Regex
{
    Regex::alt(parts)
}

/// Build an optional regex.
///
/// # Specification
/// trivial.
fn opt(part: Regex) -> Regex
{
    Regex::optional(part)
}

/// Build a repeat regex.
///
/// # Specification
/// trivial.
fn repeat(part: Regex) -> Regex
{
    Regex::repeat(part)
}

/// Build a comma-separated nonempty regex list.
///
/// # Specification
/// trivial.
fn comma1(element: Regex) -> Regex
{
    seq([element.clone(), repeat(seq([t(TileLabel(",")), element]))])
}
