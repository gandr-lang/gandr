//! The term surface: item, declaration, statement, pattern, instantiation,
//! expression and lexical forms.

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

/// Builds every surface rule except the type, shell and circuit forms.
///
/// # Specification
/// - requires: nothing.
/// - ensures: item, declaration, attribute, extern, statement, module member,
///   pattern, instantiation, expression and lexical forms, in that order, over
///   [`Sort::Item`], [`Sort::ModuleMember`], [`Sort::Pattern`],
///   [`Sort::Expression`], [`Sort::Type`] and [`Sort::Instantiation`] holes.
/// - fails: a group `precs` does not hold.
/// - panics: none.
///
/// # Errors
/// [`PbgError::MissingPrec`] naming the absent group.
pub(super) fn rules(precs: &PrecTable) -> Result<Vec<Rule>, PbgError>
{
    let item = precs.prec(PrecName("item.singleton"))?;
    let pat_or = precs.prec(PrecName("pattern.or"))?;
    let pat_as = precs.prec(PrecName("pattern.as"))?;
    let pat_atom = precs.prec(PrecName("pattern.atom"))?;
    let ret = precs.prec(PrecName("expression.ret"))?;
    let or = precs.prec(PrecName("expression.or"))?;
    let and = precs.prec(PrecName("expression.and"))?;
    let cmp = precs.prec(PrecName("expression.cmp"))?;
    let add = precs.prec(PrecName("expression.add"))?;
    let mul = precs.prec(PrecName("expression.mul"))?;
    let unary = precs.prec(PrecName("expression.unary"))?;
    let postfix = precs.prec(PrecName("expression.postfix"))?;
    let atom = precs.prec(PrecName("expression.atom"))?;

    let mut out = Vec::new();
    items(&mut out, item);
    declarations(&mut out, item);
    attributes_parameters_externs(&mut out, item);
    statements(&mut out, item);
    module_members(&mut out, item);
    patterns(&mut out, pat_or, pat_as, pat_atom);
    instantiations(&mut out, atom);
    expressions(&mut out, ExprPrecs {
        ret,
        or,
        and,
        cmp,
        add,
        mul,
        unary,
        postfix,
        atom,
    });
    lexical(&mut out, pat_atom, atom);
    Ok(out)
}

/// Append top-level item declarations.
///
/// The three `def` variants — a signature (`def id : T ;`), a value
/// (`def id = E ;`), and a function (`def id (params) -> T { … }`) — share the
/// `@[…]* def id` prefix and diverge only at the tile after the name (`:` vs
/// `=` vs `(`). Declaring them as three rules gives the tile `def` three molds
/// with identical local shape, so an obligation-minimizing molder cannot pick
/// the right one at `def`: the discriminating tile can sit arbitrarily far past
/// the name (behind any number of `@[…]` attribute blocks), out of reach of a
/// bounded lookahead. They are therefore **factored** into one form whose tail
/// alternates on the discriminating tile, so the shared prefix owns one `def`
/// and one `identifier` mold and the choice becomes locally decidable: the
/// discriminating tile `≐`-continues exactly one of the three tails, an LL(1)
/// choice at the level of the form. The concrete language is unchanged —
/// every program that parsed as a signature, value, or function still parses,
/// tile for tile — and the folded-away kinds `def_signature` and
/// `def_function` are recorded as adaptations so the named-kind inventory
/// still covers them.
///
/// # Specification
/// trivial.
fn items(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::Item;
    let mut def = r(
        RuleName("def_value"),
        Provenance("def_value"),
        s,
        p,
        def_family(),
    );
    def.adaptations.push(Adaptation::new(
        RuleName("def_value"),
        SurfaceForm("def_signature"),
        AdaptationReason("factored into the def family: the signature tail `: T ;` shares the `@[…]* def id` prefix and discriminates on the leading `:` tile"),
    ));
    def.adaptations.push(Adaptation::new(
        RuleName("def_value"),
        SurfaceForm("def_function"),
        AdaptationReason("factored into the def family: the function tail `(params) -> T? { … }` shares the `@[…]* def id` prefix and discriminates on the leading `(` tile"),
    ));
    def.adaptations.push(Adaptation::new(
        RuleName("def_value"),
        SurfaceForm("def_rec"),
        AdaptationReason("`def rec` is folded into the def family as a fourth tail discriminating on the `rec` keyword after `def`, rather than a standalone `def_rec` item rule, so `def` keeps one form-first mold and the rec-or-name choice is locally decidable (a second `def` form-start would tie every top-level `def`). The reserved copattern default arm `_ =>` rides the same clause list."),
    ));
    out.push(def);
}

/// Append the declaration forms: `data` and `codata` datatypes and their
/// members, `import`, the reserved operator-fixity declaration, and the
/// reserved mutual-recursion `rec` block.
///
/// All land at `item.singleton` beside the def and val families. Every form
/// is keyword-led (a fresh first-token discriminator with no lookahead against
/// `def`, `val`, `import`, …), so no new shared-prefix window opens. The
/// tree-sitter grammar does not produce these constructs, so their provenance
/// names are in [`PBG_ONLY_KINDS`](crate::PBG_ONLY_KINDS) and the named-kind
/// inventory never lists them.
///
/// # Specification
/// trivial.
fn declarations(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::Item;

    // --- `data` datatype declaration ---------
    // THE one data-declaration form is the nested generator block: the family
    // head binds its parameters once — each a typed binder `a : Type` — and
    // declares its index arity as the head annotation `: Idx -> Type` (`:
    // Type` when unindexed); every generator member is a judgment `Ctor :
    // (binders) --> Result` whose result head is the family applied to the
    // parameter variables. Members are first-token-discriminated by case
    // (uppercase-led constructors versus the lowercase-led reserved `oper` /
    // `rule` members) and are terminated by `;`, with a comma separator
    // admissible between members so the declined shapes still parse whole:
    // the Haskell-style head `data Maybe(a)` (bare parameters, no head
    // annotation) and the field-tuple member `Ctor(x: A)` reach the
    // elaborator, which declines them with the respelling hint (as it does
    // the `~>` face arrow) rather than the parser repairing a token. An
    // unseparated member list is deliberately not admitted; the mis-parse
    // mechanism is documented on `member_list`.
    let mut data = r(
        RuleName("data_declaration"),
        Provenance("data_declaration"),
        s,
        p,
        seq([
            t(TileLabel("data")),
            t(TileLabel("type_identifier")),
            opt(head_params()),
            opt(seq([t(TileLabel(":")), h(Sort::Type)])),
            t(TileLabel("{")),
            opt(member_list(data_member())),
            t(TileLabel("}")),
        ]),
    );
    data.adaptations.push(Adaptation::new(
        RuleName("data_declaration"),
        SurfaceForm("data_generator"),
        AdaptationReason("the generator member `Ctor : (binders) --> Result` is inlined in the data block: its telescope `( name : Type, … )` is kept LOCAL to the member so a named binder list never becomes a standalone `(`-opened form competing with the parenthesized type at every type slot (the `op_result` precedent), and its `:` lead discriminates against the declined field-tuple tail one tile after the constructor name"),
    ));
    data.adaptations.push(Adaptation::new(
        RuleName("data_declaration"),
        SurfaceForm("constructor_block_member"),
        AdaptationReason("parse-and-decline: the Haskell-style constructor member `Ctor(fields?) (: Result)?` stays admissible as the constructor-led member's second tail so a stale declaration reaches the elaborator's decline with the respelling hint instead of a parse repair; the tail discriminates on `(` vs `:` immediately after the constructor name"),
    ));
    data.adaptations.push(Adaptation::new(
        RuleName("data_declaration"),
        SurfaceForm("bare_type_params"),
        AdaptationReason("parse-and-decline: the bare head parameter `(a)` — no `: Type` binder annotation — stays admissible in the head's parameter list so a stale head reaches the elaborator's decline; the typed binder and the bare spelling share the `type_variable` lead and discriminate on the following `:`"),
    ));
    data.adaptations.push(Adaptation::new(
        RuleName("data_declaration"),
        SurfaceForm("op_member"),
        AdaptationReason("reserved parse-and-decline: an `op name(params) -> R` operation member is inlined in the data block, first-token-discriminated by the `op` keyword"),
    ));
    data.adaptations.push(Adaptation::new(
        RuleName("data_declaration"),
        SurfaceForm("rule_member"),
        AdaptationReason("reserved parse-and-decline: a `rule lhs ==> rhs` 2-cell member is inlined in the data block, first-token-discriminated by the `rule` keyword; the declined `~>` face arrow stays admissible so a stale spelling reaches the elaborator's decline instead of a parse repair"),
    ));
    data.adaptations.push(Adaptation::new(
        RuleName("data_declaration"),
        SurfaceForm("grade_prefix"),
        AdaptationReason("the reserved grade prefix on a constructor field is restricted to `{ number, ω }`, without the bare identifier spelling, so a graded field `Cons(1 x: a)` stays first-token-distinct from an ungraded field `Some(x: a)`: an identifier grade would be indistinguishable from a field name"),
    ));
    out.push(data);

    // --- `codata` datatype declaration -------
    // The other polarity's block over the SAME head discipline: parameters
    // are typed binders bound once at the head and the head carries the
    // annotation (`codata Stream(a : Type) : Type`). The members are
    // lowercase-led observations (`head: a`) plus the reserved `rule` 2-cell —
    // observations are not generators, so no result-head discipline applies to
    // them. `codata` reserves as one whole keyword so it never lexes as `co` +
    // `data`. Observations are inline (the `ident : Type` shape, like the
    // constructor field, never a standalone rule). The bare-parameter head
    // stays admissible for the elaborator's decline, as on `data`.
    let mut codata = r(
        RuleName("codata_declaration"),
        Provenance("codata_declaration"),
        s,
        p,
        seq([
            t(TileLabel("codata")),
            t(TileLabel("type_identifier")),
            opt(head_params()),
            opt(seq([t(TileLabel(":")), h(Sort::Type)])),
            t(TileLabel("{")),
            opt(member_list(codata_member())),
            t(TileLabel("}")),
        ]),
    );
    codata.adaptations.push(Adaptation::new(
        RuleName("codata_declaration"),
        SurfaceForm("bare_type_params"),
        AdaptationReason("parse-and-decline: the bare head parameter `(a)` — no `: Type` binder annotation — stays admissible in the head's parameter list so a stale head reaches the elaborator's decline, exactly as on the `data` block"),
    ));
    codata.adaptations.push(Adaptation::new(
        RuleName("codata_declaration"),
        SurfaceForm("codata_observation"),
        AdaptationReason("inline observation member `[grade?] name (params?) : Type`, kept inside the codata block — the `ident : Type` shape is never a standalone rule that would collide-by-menu with `record_type_field` / `session_field`"),
    ));
    codata.adaptations.push(Adaptation::new(
        RuleName("codata_declaration"),
        SurfaceForm("parameterized_observation"),
        AdaptationReason("reserved parse-and-decline: a parameterized observation `ap(x: a): b` rides the observation member's optional parameter list"),
    ));
    codata.adaptations.push(Adaptation::new(
        RuleName("codata_declaration"),
        SurfaceForm("rule_member"),
        AdaptationReason("reserved parse-and-decline: a `rule lhs ==> rhs` 2-cell member is inlined in the codata block, first-token-discriminated by the `rule` keyword; the declined `~>` face arrow stays admissible so a stale spelling reaches the elaborator's decline instead of a parse repair"),
    ));
    out.push(codata);

    // --- module declaration ----------------------------------------------------
    // `module M { … }`, optionally ascribed against a `#{ … }` signature, `:`
    // transparently or `:>` opaquely (`module_ascription_tail`). The shared
    // `module type_identifier` opener owns one mold. The body is a repetition
    // of `Sort::ModuleMember` holes: a definition, an attributed definition, or
    // a nested module of either name case with its own optional ascription,
    // whose body is the same repetition, so nesting depth is unbounded.
    out.push(r(
        RuleName("module_declaration"),
        Provenance("module_declaration"),
        s,
        p,
        seq([
            t(TileLabel("module")),
            t(TileLabel("type_identifier")),
            opt(module_ascription_tail()),
            t(TileLabel("{")),
            repeat(h(Sort::ModuleMember)),
            t(TileLabel("}")),
        ]),
    ));

    // --- module `import` -------------------------------
    // `import "URI" as name ;`. The URI is a plain string literal, so a new
    // scheme needs no grammar change.
    out.push(r(
        RuleName("import_declaration"),
        Provenance("import_declaration"),
        s,
        p,
        seq([
            t(TileLabel("import")),
            dq_string(),
            t(TileLabel("as")),
            t(TileLabel("identifier")),
            t(TileLabel(";")),
        ]),
    ));

    // --- operator-fixity declaration (reserved) -------
    // `op <fixity> <level> "spelling" ;` — reserved parse-and-decline. Reusing
    // the `op` keyword (already reserved for data operation members) keeps the
    // keyword table tight: at a fresh item slot only THIS `op` mold is
    // admissible, while the data-member `op` is a `≐`-successor reachable only
    // inside an open `data` / `codata` block. The fixity classes are contextual
    // tiles (not reserved keywords), and the operator spelling is a STRING
    // literal so the labeler need not tokenise a user operator; folding a
    // declared operator into the grammar is not part of this surface.
    let mut operator = r(
        RuleName("operator_declaration"),
        Provenance("operator_declaration"),
        s,
        p,
        seq([
            t(TileLabel("op")),
            fixity_class(),
            t(TileLabel("number")),
            dq_string(),
            t(TileLabel(";")),
        ]),
    );
    operator.adaptations.push(Adaptation::new(
        RuleName("operator_declaration"),
        SurfaceForm("operator_declaration"),
        AdaptationReason("the operator declaration reads `op <infixl|infixr|infix|prefix|postfix> <level> \"spelling\" ;`, reusing the reserved `op` lead and a string-literal spelling so the labeler needs no user-operator token; the declaration parses and is declined, since no declared operator is folded into the grammar"),
    ));
    out.push(operator);

    // --- mutual-recursion `rec { … }` block (reserved) -
    // Cheap once `rec` is a keyword. Form-first `rec {` is distinct from
    // the `def rec` tail (where `rec` is a `≐`-successor of `def`), so the two
    // `rec` uses never tie at a fresh item slot.
    let mut rec_block = r(
        RuleName("rec_block"),
        Provenance("rec_block"),
        s,
        p,
        seq([
            t(TileLabel("rec")),
            t(TileLabel("{")),
            repeat(rec_member()),
            t(TileLabel("}")),
        ]),
    );
    rec_block.adaptations.push(Adaptation::new(
        RuleName("rec_block"),
        SurfaceForm("rec_block"),
        AdaptationReason("reserved parse-and-decline: a `rec { def … ; def … }` mutual-recursion block; members are inline value / function defs, distinct-rctx from the top-level `def` family"),
    ));
    out.push(rec_block);
}

/// Build the top-level definition family: attributes, `def`, and a factored
/// value/signature/function/recursive tail.
///
/// # Specification
/// trivial.
fn def_family() -> Regex
{
    seq([
        repeat(attr_block_inline()),
        t(TileLabel("def")),
        alt([def_rec_tail(), regular_def_tail()]),
    ])
}

/// Build a module declaration's optional ascription tail, transparent or
/// opaque.
///
/// The two forms share their signature and differ **only on the tile that opens
/// the tail** — `:` for transparent ascription, `:>` for opaque — so the choice
/// is made at one token with no lookahead, which is the constraint the
/// signature surface is under. The body is one signature either way: sealing
/// changes what the ascription *does*, never what it is written against.
///
/// # Specification
/// trivial.
fn module_ascription_tail() -> Regex
{
    alt([
        seq([t(TileLabel(":")), module_signature()]),
        seq([t(TileLabel(":>")), module_signature()]),
    ])
}

/// Build a module signature: the record-shaped ascription body, whose fields
/// are value components and abstract type components.
///
/// # Specification
/// trivial.
fn module_signature() -> Regex
{
    seq([
        t(TileLabel("#{")),
        opt(comma1(module_signature_field())),
        t(TileLabel("}")),
    ])
}

/// A value component `ℓ : T` or a parameterized value component
/// `ℓ : (a : T) -> U`, or a **type component** — `type T = τ` when the
/// component is *manifest*, `type T` when it is abstract. The value and type
/// forms are first-token-discriminated by the `type` keyword — already a tile
/// in this grammar, from the `extern` block's inline type members — so
/// admitting them in one semicolon- or comma-separated list costs no lookahead,
/// and the manifest tail is one optional `=`.
///
/// **All three type forms parse and they mean different things.** A manifest
/// component `type T = τ` names the type it equals, so it introduces no
/// abstraction and its occurrences expand to that type. A bare `type T` is what
/// opaque ascription mints an atom for, so its meaning is sealing's. A
/// **kinded** component `type T : κ` declares a type *family* — `type Home : Ob
/// → Ob → Type` is the indexed sort the higher-cells weak category needs, and
/// its occurrences are applications `Home(a, b)` rather than expansions.
///
/// Parsing a form the elaborator cannot yet hold, and refusing it there, is
/// what makes the gap visible. Not parsing it is worse than useless: the
/// recovery reads as a syntax error about the wrong thing, and — as the kinded
/// form demonstrated before it was admitted here — a member whose tail does not
/// match any alternative lets the field consume the rest of the source and
/// still bind, which reports nothing at all.
///
/// The kind is an ordinary type, because that is what a kind looks like in this
/// grammar: an arrow spine ending in `Type`. Reusing `Sort::Type` for it costs
/// no new production and keeps one parser for one syntax.
///
/// **A type component may bind parameters**, reusing [`head_params`] verbatim
/// so a family's binder list is spelled exactly as a `data` head spells one:
/// `type Home(a : Ob, b : Ob) = U[ω] (a -> F b)`. That is the *manifest* family
/// — the form an instance supplies a kinded component with — and it is a
/// declaration rather than a type-level lambda, which is why it needs no
/// expression-level binder and no new sort. Without it the kinded component
/// declares a family nothing can satisfy: a signature could state `type Home :
/// Ob → Ob → Type` and no module could ever match it, because every way of
/// writing the answer down is a type-level function the grammar has no term
/// for.
///
/// The parameter list is where the comma matters. A member list is split on
/// commas, so a parameter list carrying its own commas must be respected by
/// whatever does the splitting; `type Home(a : Ob, b : Ob) = τ` parses here and
/// is the case a depth-blind splitter silently cuts in half.
///
/// # Specification
/// trivial.
fn module_signature_field() -> Regex
{
    alt([
        seq([t(TileLabel("identifier")), t(TileLabel(":")), h(Sort::Type)]),
        seq([
            t(TileLabel("type")),
            t(TileLabel("type_identifier")),
            opt(head_params()),
            opt(alt([
                seq([t(TileLabel("=")), h(Sort::Type)]),
                seq([t(TileLabel(":")), h(Sort::Type)]),
            ])),
        ]),
    ])
}

/// Build the `def rec` recursive tail: `rec id (params) -> T? { body }`.
///
/// A single `{ … }` with an interior alternative separates the corecursive
/// copattern-clause body from the ordinary statement body, so the two never
/// expose two `{`-led branches sharing one context (the
/// [`PbgError::DuplicateTile`] hazard). The
/// copattern `.head => e` clause's `.` is a `≐`-successor of `{` / `,`,
/// distinct from the postfix projection `.` (which requires a left operand), so
/// the same `.` label molds by context.
///
/// # Specification
/// trivial.
fn def_rec_tail() -> Regex
{
    seq([
        t(TileLabel("rec")),
        t(TileLabel("identifier")),
        params(),
        opt(seq([t(TileLabel("->")), h(Sort::Type)])),
        t(TileLabel("{")),
        alt([
            // corecursive body: copattern clauses `.head => e` (+ reserved `_ =>`).
            comma1(copattern_clause()),
            // ordinary statement body (the block interior, flat).
            seq([repeat(statement_alt()), opt(h(Sort::Expression))]),
        ]),
        t(TileLabel("}")),
    ])
}

/// Build a copattern clause: `.observation => e`, or the reserved `_ => e`
/// default arm.
///
/// # Specification
/// trivial.
fn copattern_clause() -> Regex
{
    alt([
        seq([
            t(TileLabel(".")),
            t(TileLabel("identifier")),
            t(TileLabel("=>")),
            h(Sort::Expression),
        ]),
        seq([t(TileLabel("_")), t(TileLabel("=>")), h(Sort::Expression)]),
    ])
}

/// Build an inline datatype head parameter list `( a : Type, b : Type, … )`.
///
/// Parameters are bound **once** at the family head, each as a typed binder.
/// The binder's `: Type` annotation is optional in the grammar so the
/// bare-parameter head `data Maybe(a)` still parses whole and reaches the
/// elaborator's decline with the respelling hint (as the `~>` face arrow
/// does); the elaborator requires every entry typed.
///
/// # Specification
/// trivial.
fn head_params() -> Regex
{
    seq([
        t(TileLabel("(")),
        comma1(seq([
            t(TileLabel("type_variable")),
            opt(seq([t(TileLabel(":")), h(Sort::Type)])),
        ])),
        t(TileLabel(")")),
    ])
}

/// Build an inline `data` member: a **generator** judgment (the one form), the
/// declined field-tuple constructor (admissible for the elaborator's decline),
/// a reserved `op` operation, or a reserved `rule` 2-cell.
///
/// The constructor-led tails share the `constructor` tile and discriminate one
/// tile later: `:` leads the generator judgment, anything else the declined
/// field-tuple tail — so the choice is locally decidable exactly as the `def`
/// family's factored tails are.
///
/// # Specification
/// trivial.
fn data_member() -> Regex
{
    alt([
        seq([
            t(TileLabel("constructor")),
            alt([
                // generator judgment `Ctor : Side (--> Result)? [attrs]?` —
                // THE one constructor-declaration form.
                seq([t(TileLabel(":")), generator_signature(), opt(attr_slot())]),
                // declined `Ctor(fields?) (: Result)? [attrs]?`, kept admissible
                // so the elaborator's decline names the respelling.
                seq([
                    opt(seq([
                        t(TileLabel("(")),
                        comma1(ctor_field()),
                        t(TileLabel(")")),
                    ])),
                    opt(seq([t(TileLabel(":")), h(Sort::Type)])),
                    opt(attr_slot()),
                ]),
            ]),
        ]),
        // reserved `oper name(params) -> R?` operation member. The `op` lead
        // still parses so the elaborator can decline it with the respelling
        // (as it does the `~>` face arrow); `op` otherwise leads only the
        // operator-fixity declaration.
        data_oper_member(alt([t(TileLabel("oper")), t(TileLabel("op"))])),
        // reserved `rule lhs ==> rhs` 2-cell member.
        seq([
            t(TileLabel("rule")),
            h(Sort::Expression),
            rule_face_arrow(),
            h(Sort::Expression),
        ]),
    ])
}

/// Build the data-style operation member after its context-specific lead menu.
///
/// # Specification
/// trivial.
fn data_oper_member(lead: Regex) -> Regex
{
    seq([
        lead,
        t(TileLabel("identifier")),
        params(),
        opt(seq([t(TileLabel("->")), op_result()])),
    ])
}

/// Build a generator's signature: a **side** — the bare result sort, a bare
/// single-field sort, or a parenthesized binder telescope — optionally
/// followed by `-->` and the result head.
///
/// The ladder mirrors the circuit signature's: no arrow means the side IS the
/// result (`Nil : Vec(a, 0)` declares no fields); an arrow makes the side the
/// telescope and the post-arrow type the result (`Cons : (n : Nat, x : a) -->
/// Vec(a, n)`). Every generator's result head is checked against the family by
/// the elaborator — head uniformity is a structural property of this form, not
/// a grammar fact, because the result is an ordinary type hole.
///
/// # Specification
/// trivial.
fn generator_signature() -> Regex
{
    seq([
        alt([h(Sort::Type), generator_telescope()]),
        opt(seq([t(TileLabel("-->")), h(Sort::Type)])),
    ])
}

/// Build a generator's parenthesized telescope `( entry, … )`: named binders
/// (with the reserved grade prefix) or bare-sort ports, the same sugar ladder
/// the circuit parameter side climbs.
///
/// # Specification
/// trivial.
fn generator_telescope() -> Regex
{
    seq([
        t(TileLabel("(")),
        comma1(alt([ctor_field(), h(Sort::Type)])),
        t(TileLabel(")")),
    ])
}

/// Build the rewrite-face arrow of a `rule` member: `==>`, or the declined
/// `~>` kept admissible so it can be declined by name.
///
/// `==>` is the rewrite-face former at every position. Removing `~>` from the
/// grammar outright would turn a stale face into a parse repair, which names
/// a token rather than the respelling; admitting it here keeps the member's
/// shape whole so the elaborator declines it by name and points at `==>`.
///
/// # Specification
/// trivial.
pub(super) fn rule_face_arrow() -> Regex
{
    alt([t(TileLabel("==>")), t(TileLabel("~>"))])
}

/// Build the reserved grade prefix, narrowed to `{ number, ω }`.
///
/// # Specification
/// trivial.
fn grade_prefix() -> Regex
{
    alt([t(TileLabel("number")), t(TileLabel("ω"))])
}

/// Build a reserved per-symbol attribute slot `[name, …]` inside a data block.
///
/// Distinct from a list literal / instantiation `[` by its declaration-position
/// rctx; no `@` sigil inside the block. The attribute
/// entries reuse the `attribute` shape (`name (payload)?`).
///
/// # Specification
/// trivial.
fn attr_slot() -> Regex
{
    seq([t(TileLabel("[")), comma1(attr_inline()), t(TileLabel("]"))])
}

/// Build the reserved `op` result: a single type or a named multi-out tuple,
/// kept LOCAL to the op member so `( ident : Type, … )` never collides with
/// `parenthesized_type`.
///
/// # Specification
/// trivial.
fn op_result() -> Regex
{
    alt([
        h(Sort::Type),
        seq([
            t(TileLabel("(")),
            comma1(seq([
                t(TileLabel("identifier")),
                t(TileLabel(":")),
                h(Sort::Type),
            ])),
            t(TileLabel(")")),
        ]),
    ])
}

/// Build an inline `codata` member: an observation `[grade?] name (params?) :
/// Type`, a data-style `oper` preserved whole for block-kind-aware decline, or
/// the reserved `rule` 2-cell.
///
/// # Specification
/// trivial.
fn codata_member() -> Regex
{
    alt([
        seq([
            opt(grade_prefix()),
            t(TileLabel("identifier")),
            opt(seq([
                t(TileLabel("(")),
                comma1(ctor_field()),
                t(TileLabel(")")),
            ])),
            t(TileLabel(":")),
            h(Sort::Type),
        ]),
        data_oper_member(t(TileLabel("oper"))),
        seq([
            t(TileLabel("rule")),
            h(Sort::Expression),
            rule_face_arrow(),
            h(Sort::Expression),
        ]),
    ])
}

/// Build a constructor field `[grade?] name : Type`, the grade reserved and
/// narrowed.
///
/// # Specification
/// trivial.
fn ctor_field() -> Regex
{
    seq([
        opt(grade_prefix()),
        t(TileLabel("identifier")),
        t(TileLabel(":")),
        h(Sort::Type),
    ])
}

/// Build the reserved operator-declaration fixity class menu.
///
/// # Specification
/// trivial.
fn fixity_class() -> Regex
{
    alt([
        t(TileLabel("infixl")),
        t(TileLabel("infixr")),
        t(TileLabel("infix")),
        t(TileLabel("prefix")),
        t(TileLabel("postfix")),
    ])
}

/// Build one inline `rec { … }` member: a value or function definition.
///
/// # Specification
/// trivial.
fn rec_member() -> Regex
{
    seq([
        t(TileLabel("def")),
        t(TileLabel("identifier")),
        alt([
            seq([t(TileLabel("=")), h(Sort::Expression), t(TileLabel(";"))]),
            seq([
                params(),
                opt(seq([t(TileLabel("->")), h(Sort::Type)])),
                block(),
            ]),
        ]),
    ])
}

/// Append attribute, parameter, and extern helper forms.
///
/// # Specification
/// trivial.
fn attributes_parameters_externs(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::Item;
    // The `attribute` (`id (E)?`), `parameters` (`( id, … )`), and `parameter`
    // (`id : T?`) helpers are inline-only: each appears solely inside an
    // enclosing form (`attribute` in `attribute_block`, `parameters` /
    // `parameter` in the def-function tail, lambda, and extern members). A
    // standalone rule additionally gives their opener a form-first Item-sort mold
    // — `attribute` / `parameter` a bare `identifier`, `parameters` a `(` — that
    // ties with every operand at a fresh slot, a spurious competitor the molder
    // must break by lookahead (the helper-rule class the fold-in audit found;
    // folding it fixes correctness and cost together). They are folded into
    // `attribute_block` (recorded as adaptations for the parity inventory); their
    // inlined occurrences still realise each helper's shape.
    let mut attribute_block = r(
        RuleName("attribute_block"),
        Provenance("attribute_block"),
        s,
        p,
        attr_block_inline(),
    );
    attribute_block.adaptations.push(Adaptation::new(
        RuleName("attribute_block"),
        SurfaceForm("attribute"),
        AdaptationReason("folded into attribute_block: the `id (E)?` attribute is inlined in the block body, not a standalone form-first identifier competing with a bare variable"),
    ));
    attribute_block.adaptations.push(Adaptation::new(
        RuleName("attribute_block"),
        SurfaceForm("parameters"),
        AdaptationReason("folded away: the `( id, … )` parameter list is inlined in the def-function tail and lambda, not a standalone `(`-opened Item form competing with the parenthesized expression"),
    ));
    attribute_block.adaptations.push(Adaptation::new(
        RuleName("attribute_block"),
        SurfaceForm("parameter"),
        AdaptationReason("folded away: the `id : T?` parameter is inlined in the parameter list, not a standalone form-first identifier competing with a bare variable"),
    ));
    out.push(attribute_block);
    // The extern members `extern_type` (`type T ;`) and `extern_function`
    // (`def id (params) -> T? ;`) live only inside an `extern { … }` block, where
    // they are inlined below. Declaring them as standalone top-level Item rules
    // additionally gives their opener tiles (`type`, `def`) a form-first mold at
    // the top level, where an `extern_function`'s `def` then competes with a real
    // top-level `def` — an ambiguity no lookahead can settle since the two only
    // diverge deep in the body. They are folded into `extern_block` (recorded as
    // adaptations for the parity inventory); the block's inlined members still
    // realise the members' shape, and their `def` / `type` carry a required
    // `≐`-predecessor so they are never top-level form-starts.
    let mut extern_block = r(
        RuleName("extern_block"),
        Provenance("extern_block"),
        s,
        p,
        seq([
            t(TileLabel("extern")),
            dq_string(),
            t(TileLabel("from")),
            dq_string(),
            opt(seq([t(TileLabel("as")), t(TileLabel("identifier"))])),
            t(TileLabel("{")),
            repeat(alt([extern_type_inline(), extern_function_inline()])),
            t(TileLabel("}")),
        ]),
    );
    extern_block.adaptations.push(Adaptation::new(
        RuleName("extern_block"),
        SurfaceForm("extern_type"),
        AdaptationReason("folded into extern_block: the `type T ;` member is inlined in the block body, not a top-level form"),
    ));
    extern_block.adaptations.push(Adaptation::new(
        RuleName("extern_block"),
        SurfaceForm("extern_function"),
        AdaptationReason("folded into extern_block: the `def id (params) -> T? ;` member is inlined in the block body, not a top-level form whose `def` competes with a real definition"),
    ));
    out.push(extern_block);
}

/// Append block statement forms.
///
/// # Specification
/// trivial.
fn statements(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::Item;
    out.push(r(
        RuleName("let_statement"),
        Provenance("let_statement"),
        s,
        p,
        val_statement(),
    ));
    out.push(r(
        RuleName("bind_statement"),
        Provenance("bind_statement"),
        s,
        p,
        bind_statement(),
    ));
    out.push(r(
        RuleName("unpack_statement"),
        Provenance("unpack_statement"),
        s,
        p,
        unpack_statement(),
    ));
    out.push(r(
        RuleName("leta_statement"),
        Provenance("leta_statement"),
        s,
        p,
        seq([
            t(TileLabel("leta")),
            t(TileLabel("identifier")),
            t(TileLabel("=")),
            h(Sort::Expression),
            t(TileLabel(";")),
        ]),
    ));
    out.push(r(
        RuleName("recv_statement"),
        Provenance("recv_statement"),
        s,
        p,
        session_stmt(TileLabel("recv")),
    ));
    out.push(r(
        RuleName("acquire_statement"),
        Provenance("acquire_statement"),
        s,
        p,
        session_stmt(TileLabel("acquire")),
    ));
    out.push(r(
        RuleName("release_statement"),
        Provenance("release_statement"),
        s,
        p,
        session_stmt(TileLabel("release")),
    ));
    out.push(r(
        RuleName("fork_statement"),
        Provenance("fork_statement"),
        s,
        p,
        seq([
            t(TileLabel("fork")),
            t(TileLabel("(")),
            t(TileLabel("identifier")),
            t(TileLabel(":")),
            h(Sort::Type),
            t(TileLabel(")")),
            block(),
            t(TileLabel("as")),
            t(TileLabel("identifier")),
            t(TileLabel(";")),
        ]),
    ));
    out.push(r(
        RuleName("fork_shared_statement"),
        Provenance("fork_shared_statement"),
        s,
        p,
        seq([
            t(TileLabel("fork")),
            t(TileLabel("!")),
            t(TileLabel("(")),
            t(TileLabel("identifier")),
            t(TileLabel(":")),
            h(Sort::Type),
            t(TileLabel(")")),
            block(),
            t(TileLabel(";")),
        ]),
    ));
    out.push(r(
        RuleName("expression_statement"),
        Provenance("expression_statement"),
        s,
        p,
        seq([h(Sort::Expression), t(TileLabel(";"))]),
    ));
}

/// Append pattern forms.
///
/// # Specification
/// trivial.
fn patterns(
    out: &mut Vec<Rule>,
    or: Prec,
    as_p: Prec,
    atom: Prec,
)
{
    let s = Sort::Pattern;
    out.push(r(
        RuleName("wildcard"),
        Provenance("wildcard"),
        s,
        atom,
        t(TileLabel("_")),
    ));
    out.push(r(
        RuleName("constructor_pattern"),
        Provenance("constructor_pattern"),
        s,
        atom,
        seq([
            t(TileLabel("constructor")),
            opt(seq([t(TileLabel("(")), comma1(h(s)), t(TileLabel(")"))])),
        ]),
    ));
    out.push(r(
        RuleName("tuple_pattern"),
        Provenance("tuple_pattern"),
        s,
        atom,
        seq([
            t(TileLabel("(")),
            h(s),
            repeat1(seq([t(TileLabel(",")), h(s)])),
            t(TileLabel(")")),
        ]),
    ));
    // The `record_pattern_field` (`id = PAT`) helper is inline-only — it appears
    // solely inside `record_pattern`. A standalone rule additionally gives its
    // `identifier` opener a form-first Pattern-sort mold that ties with every
    // bare pattern variable, a spurious competitor the molder must break by
    // lookahead (the pattern analogue of the folded `record_field`). It is folded
    // into `record_pattern` (recorded as an adaptation); the inlined fields still
    // realise its shape.
    let mut record_pattern = r(
        RuleName("record_pattern"),
        Provenance("record_pattern"),
        s,
        atom,
        seq([
            t(TileLabel("#{")),
            opt(comma1(record_pat_field())),
            t(TileLabel("}")),
        ]),
    );
    record_pattern.adaptations.push(Adaptation::new(
        RuleName("record_pattern"),
        SurfaceForm("record_pattern_field"),
        AdaptationReason("folded into record_pattern: the `id = PAT` field is inlined, not a standalone form-first identifier competing with a bare pattern variable"),
    ));
    out.push(record_pattern);
    out.push(r(
        RuleName("list_pattern"),
        Provenance("list_pattern"),
        s,
        atom,
        seq([t(TileLabel("[")), opt(list_pat_elems()), t(TileLabel("]"))]),
    ));
    out.push(r(
        RuleName("rest_pattern"),
        Provenance("rest_pattern"),
        s,
        atom,
        seq([t(TileLabel("..")), h(s)]),
    ));
    out.push(r(
        RuleName("literal_pattern"),
        Provenance("literal_pattern"),
        s,
        atom,
        alt([
            t(TileLabel("number")),
            t(TileLabel("typed_number")),
            dq_string(),
            t(TileLabel("true")),
            t(TileLabel("false")),
        ]),
    ));
    // The pattern-position typed hole `?` / `?name`, the SAME tile pair the
    // expression hole is built from ([`primary_expressions`]), molded at
    // `pattern.atom`. It is a distinct mold rather than a shared one because a
    // mold carries its sort: without this rule the melder still admits `?` in a
    // pattern slot, but it admits the *Expression* mold, so the committed tile
    // records `Sort::Expression` and every sort-directed consumer reads a
    // pattern hole as an expression that wandered into pattern position. The
    // rule makes the hole a pattern atom in the tree as well as on the page.
    //
    // The `hole_name` tail rides along for the same reason it does in
    // expression position — a named hole is how the goal stream addresses one —
    // and it stays folded (an inline `opt` occurrence, never a standalone
    // Pattern atom), so it remains reachable only while a `?` frontier is open
    // and never competes with the bare pattern-variable menu.
    let mut hole = r(
        RuleName("hole.pattern"),
        Provenance("hole"),
        s,
        atom,
        seq([t(TileLabel("?")), opt(t(TileLabel("hole_name")))]),
    );
    hole.adaptations.push(Adaptation::new(
        RuleName("hole.pattern"),
        SurfaceForm("hole_name"),
        AdaptationReason("folded into the pattern hole, exactly as into the expression hole: the `hole_name` tile is the `?` hole's optional name tail, realised as an inline `opt(hole_name)` occurrence rather than a standalone Pattern atom that would tie with every bare pattern variable"),
    ));
    out.push(hole);
    out.push(r(
        RuleName("or_pattern"),
        Provenance("or_pattern"),
        s,
        or,
        seq([h(s), t(TileLabel("|")), h(s)]),
    ));
    out.push(r(
        RuleName("as_pattern"),
        Provenance("as_pattern"),
        s,
        as_p,
        seq([h(s), t(TileLabel("as")), t(TileLabel("identifier"))]),
    ));
}

/// Append instantiation-slot resident forms.
///
/// The dedicated sort is the syntax boundary at which name resolution and
/// checking interpret or decline each resident: type arguments, direction
/// sigils, named measures, explicit residents (the reserved `size = e` and
/// `cost = e` forms included), and `tail` inhabit only
/// [`Sort::Instantiation`], an atom-only context for `<` and `>` distinct from
/// their binary-expression molds.
///
/// # Specification
/// trivial.
fn instantiations(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::Instantiation;
    out.push(r(
        RuleName("instantiation.type"),
        Provenance("instantiation_expression"),
        s,
        p,
        h(Sort::Type),
    ));
    out.push(r(
        RuleName("instantiation.direction.descent"),
        Provenance("instantiation_expression"),
        s,
        p,
        t(TileLabel("<")),
    ));
    out.push(r(
        RuleName("instantiation.direction.productivity"),
        Provenance("instantiation_expression"),
        s,
        p,
        t(TileLabel(">")),
    ));
    out.push(r(
        RuleName("instantiation.named_measure"),
        Provenance("instantiation_expression"),
        s,
        p,
        seq([t(TileLabel("identifier")), t(TileLabel("<"))]),
    ));
    out.push(r(
        RuleName("instantiation.explicit"),
        Provenance("instantiation_expression"),
        s,
        p,
        seq([
            t(TileLabel("identifier")),
            t(TileLabel("=")),
            h(Sort::Expression),
        ]),
    ));
    out.push(r(
        RuleName("instantiation.tail"),
        Provenance("instantiation_expression"),
        s,
        p,
        t(TileLabel("tail")),
    ));
}

/// Append expression forms.
///
/// # Specification
/// trivial.
fn expressions(
    out: &mut Vec<Rule>,
    p: ExprPrecs,
)
{
    let s = Sort::Expression;
    out.push(r(
        RuleName("ret_expression"),
        Provenance("ret_expression"),
        s,
        p.ret,
        seq([t(TileLabel("ret")), h(s)]),
    ));
    binary(
        out,
        RuleName("binary_expression.or"),
        TileLabel("||"),
        s,
        p.or,
    );
    binary(
        out,
        RuleName("binary_expression.and"),
        TileLabel("&&"),
        s,
        p.and,
    );
    binary(
        out,
        RuleName("binary_expression.cmp.eq"),
        TileLabel("=="),
        s,
        p.cmp,
    );
    binary(
        out,
        RuleName("binary_expression.cmp.ne"),
        TileLabel("!="),
        s,
        p.cmp,
    );
    binary(
        out,
        RuleName("binary_expression.cmp.lt"),
        TileLabel("<"),
        s,
        p.cmp,
    );
    binary(
        out,
        RuleName("binary_expression.cmp.le"),
        TileLabel("<="),
        s,
        p.cmp,
    );
    binary(
        out,
        RuleName("binary_expression.cmp.gt"),
        TileLabel(">"),
        s,
        p.cmp,
    );
    binary(
        out,
        RuleName("binary_expression.cmp.ge"),
        TileLabel(">="),
        s,
        p.cmp,
    );
    binary(
        out,
        RuleName("binary_expression.then"),
        TileLabel("then"),
        s,
        p.cmp,
    );
    binary(
        out,
        RuleName("binary_expression.add.concat"),
        TileLabel("++"),
        s,
        p.add,
    );
    binary(
        out,
        RuleName("binary_expression.add.plus"),
        TileLabel("+"),
        s,
        p.add,
    );
    binary(
        out,
        RuleName("binary_expression.add.minus"),
        TileLabel("-"),
        s,
        p.add,
    );
    binary(
        out,
        RuleName("binary_expression.mul.times"),
        TileLabel("*"),
        s,
        p.mul,
    );
    out.push(r(
        RuleName("unary_expression"),
        Provenance("unary_expression"),
        s,
        p.unary,
        seq([t(TileLabel("-")), h(s)]),
    ));
    out.push(r(
        RuleName("force_expression"),
        Provenance("force_expression"),
        s,
        p.unary,
        seq([t(TileLabel("force")), h(s)]),
    ));
    out.push(r(
        RuleName("hold_expression"),
        Provenance("hold_expression"),
        s,
        p.unary,
        seq([t(TileLabel("hold")), h(s)]),
    ));
    // `pack [ T , U ] E` — the package introduction. The bracketed types are
    // the **witnesses**, one per abstract type component of the signature this
    // is checked against, and they are written rather than inferred: the
    // components exist only in the signature, so recovering them from the
    // payload would mean guessing which of its types were meant to be
    // abstract.
    out.push(r(
        RuleName("pack_expression"),
        Provenance("pack_expression"),
        s,
        // `ret`'s precedence, not `force`'s: a pack takes a whole expression,
        // and the payload a module is packed from is normally a `thunk { … }`
        // — itself a unary form, which a non-associative unary `pack` could
        // not take as an operand without parentheses.
        p.ret,
        seq([
            t(TileLabel("pack")),
            t(TileLabel("[")),
            comma1(h(Sort::Type)),
            t(TileLabel("]")),
            h(s),
        ]),
    ));
    // The `arguments` list `( E, … )` is inlined in `call_expression` below. A
    // standalone `arguments` rule additionally gives `(` a form-first
    // Expression-sort mold that competes with the parenthesized-expression atom
    // at a fresh slot — a tie a bounded lookahead cannot settle when the
    // parenthesized expression is long. It is folded into `call_expression`
    // (recorded as an adaptation for the parity inventory); the inlined argument
    // list still realises the arguments' shape in the only place it occurs.
    let mut call = r(
        RuleName("call_expression"),
        Provenance("call_expression"),
        s,
        p.postfix,
        seq([h(s), args()]),
    );
    call.adaptations.push(Adaptation::new(
        RuleName("call_expression"),
        SurfaceForm("arguments"),
        AdaptationReason("folded into call_expression: the argument list `( E, … )` is inlined as the call's tail, not a standalone atom competing with the parenthesized expression"),
    ));
    out.push(call);
    out.push(r(
        RuleName("instantiation_expression"),
        Provenance("instantiation_expression"),
        s,
        p.postfix,
        seq([
            h(s),
            t(TileLabel("[")),
            comma1(h(Sort::Instantiation)),
            t(TileLabel("]")),
        ]),
    ));
    out.push(r(
        RuleName("projection_expression"),
        Provenance("projection_expression"),
        s,
        p.postfix,
        seq([h(s), t(TileLabel(".")), t(TileLabel("identifier"))]),
    ));
    primary_expressions(out, p.atom);
}

/// Append shared lexical named-token forms used by term and pattern rules.
///
/// # Specification
/// trivial.
fn lexical(
    out: &mut Vec<Rule>,
    pat: Prec,
    expr: Prec,
)
{
    let p = Sort::Pattern;
    out.push(r(
        RuleName("identifier.pattern"),
        Provenance("identifier"),
        p,
        pat,
        t(TileLabel("identifier")),
    ));
    out.push(r(
        RuleName("constructor.pattern"),
        Provenance("constructor"),
        p,
        pat,
        t(TileLabel("constructor")),
    ));
    out.push(r(
        RuleName("boolean.pattern"),
        Provenance("boolean"),
        p,
        pat,
        alt([t(TileLabel("true")), t(TileLabel("false"))]),
    ));
    out.push(r(
        RuleName("number.pattern"),
        Provenance("number"),
        p,
        pat,
        t(TileLabel("number")),
    ));
    out.push(r(
        RuleName("typed_number.pattern"),
        Provenance("typed_number"),
        p,
        pat,
        t(TileLabel("typed_number")),
    ));
    out.push(r(
        RuleName("string.pattern"),
        Provenance("string"),
        p,
        pat,
        seq([
            t(TileLabel("\"")),
            repeat(alt([
                t(TileLabel("escape_sequence")),
                t(TileLabel("string_fragment")),
            ])),
            t(TileLabel("\"")),
        ]),
    ));

    let e = Sort::Expression;
    out.push(r(
        RuleName("identifier.expression"),
        Provenance("identifier"),
        e,
        expr,
        t(TileLabel("identifier")),
    ));
    out.push(r(
        RuleName("constructor.expression"),
        Provenance("constructor"),
        e,
        expr,
        t(TileLabel("constructor")),
    ));
    out.push(r(
        RuleName("boolean.expression"),
        Provenance("boolean"),
        e,
        expr,
        alt([t(TileLabel("true")), t(TileLabel("false"))]),
    ));
    out.push(r(
        RuleName("number.expression"),
        Provenance("number"),
        e,
        expr,
        t(TileLabel("number")),
    ));
    out.push(r(
        RuleName("typed_number.expression"),
        Provenance("typed_number"),
        e,
        expr,
        t(TileLabel("typed_number")),
    ));
    out.push(r(
        RuleName("character"),
        Provenance("character"),
        e,
        expr,
        t(TileLabel("character")),
    ));
    // The expression-position string additionally admits interpolation
    // segments `${ E }` — a multi-tile
    // bracket-family member (open `${`, a host-Expression hole, close `}`)
    // interleaved with the fragment / escape runs, no format specs. The
    // labeler's string-segment mode emits the `${` opener and re-enters
    // string mode at the matching `}`; escapes ride the existing
    // `escape_sequence`. The pattern-position and extern-header strings stay
    // plain (interpolation is meaningless there).
    let mut string_expr = r(
        RuleName("string.expression"),
        Provenance("string"),
        e,
        expr,
        seq([
            t(TileLabel("\"")),
            repeat(alt([
                t(TileLabel("escape_sequence")),
                t(TileLabel("string_fragment")),
                seq([t(TileLabel("${")), h(Sort::Expression), t(TileLabel("}"))]),
            ])),
            t(TileLabel("\"")),
        ]),
    );
    string_expr.adaptations.push(Adaptation::new(
        RuleName("string.expression"),
        SurfaceForm("string_interpolation"),
        AdaptationReason("an expression string carries `${ E }` interpolation segments as a bracket-family member of the fragment and escape repeat; the `${` opener and `}` closer are the labeler's string-segment boundaries. No format specifiers."),
    ));
    out.push(string_expr);
    out.push(r(
        RuleName("escape_sequence"),
        Provenance("escape_sequence"),
        e,
        expr,
        t(TileLabel("escape_sequence")),
    ));
}

/// Expression precedence bundle.
#[derive(Clone, Copy)]
struct ExprPrecs
{
    /// Return-expression precedence.
    ret: Prec,
    /// Logical-or precedence.
    or: Prec,
    /// Logical-and precedence.
    and: Prec,
    /// Comparison precedence.
    cmp: Prec,
    /// Additive precedence.
    add: Prec,
    /// Multiplicative precedence.
    mul: Prec,
    /// Unary precedence.
    unary: Prec,
    /// Postfix precedence.
    postfix: Prec,
    /// Atomic-expression precedence.
    atom: Prec,
}

/// Append one binary expression rule.
///
/// # Specification
/// trivial.
fn binary(
    out: &mut Vec<Rule>,
    name: RuleName,
    op: TileLabel,
    s: Sort,
    p: Prec,
)
{
    out.push(r(
        name,
        Provenance("binary_expression"),
        s,
        p,
        seq([h(s), t(op), h(s)]),
    ));
}

/// Build an inline attribute block.
///
/// # Specification
/// trivial.
fn attr_block_inline() -> Regex
{
    seq([t(TileLabel("@[")), comma1(attr_inline()), t(TileLabel("]"))])
}

/// Build an inline attribute.
///
/// # Specification
/// trivial.
fn attr_inline() -> Regex
{
    seq([
        t(TileLabel("identifier")),
        opt(seq([
            t(TileLabel("(")),
            h(Sort::Expression),
            t(TileLabel(")")),
        ])),
    ])
}

/// Build an inline parameter, including uppercase type-variable binders.
///
/// # Specification
/// trivial.
fn param() -> Regex
{
    seq([
        alt([
            t(TileLabel("identifier")),
            t(TileLabel("type_variable")),
            t(TileLabel("type_identifier")),
        ]),
        opt(seq([t(TileLabel(":")), h(Sort::Type)])),
    ])
}

/// Build an inline receive/acquire/release statement.
///
/// # Specification
/// trivial.
fn session_stmt(keyword: TileLabel) -> Regex
{
    seq([
        t(keyword),
        t(TileLabel("(")),
        h(Sort::Expression),
        t(TileLabel(")")),
        t(TileLabel("as")),
        t(TileLabel("identifier")),
        t(TileLabel(";")),
    ])
}

/// Build the inline statement alternatives used inside a block.
///
/// # Specification
/// trivial.
fn statement_alt() -> Regex
{
    alt([
        val_statement(),
        bind_statement(),
        unpack_statement(),
        seq([
            t(TileLabel("leta")),
            t(TileLabel("identifier")),
            t(TileLabel("=")),
            h(Sort::Expression),
            t(TileLabel(";")),
        ]),
        session_stmt(TileLabel("recv")),
        session_stmt(TileLabel("acquire")),
        session_stmt(TileLabel("release")),
        seq([
            t(TileLabel("fork")),
            t(TileLabel("(")),
            t(TileLabel("identifier")),
            t(TileLabel(":")),
            h(Sort::Type),
            t(TileLabel(")")),
            h(Sort::Expression),
            t(TileLabel("as")),
            t(TileLabel("identifier")),
            t(TileLabel(";")),
        ]),
        seq([
            t(TileLabel("fork")),
            t(TileLabel("!")),
            t(TileLabel("(")),
            t(TileLabel("identifier")),
            t(TileLabel(":")),
            h(Sort::Type),
            t(TileLabel(")")),
            h(Sort::Expression),
            t(TileLabel(";")),
        ]),
        seq([h(Sort::Expression), t(TileLabel(";"))]),
    ])
}

/// Build a variable-binding statement: `val PAT = E ;`.
///
/// # Specification
/// trivial.
fn val_statement() -> Regex
{
    seq([
        t(TileLabel("val")),
        h(Sort::Pattern),
        t(TileLabel("=")),
        h(Sort::Expression),
        t(TileLabel(";")),
    ])
}

/// Build a package-eliminating statement: `unpack m : Sig = E ;`.
///
/// The module variable binds over the **rest of its block**, which is what
/// makes the elimination check-only and the avoidance fence structural: the
/// block's answer is fixed from outside, so an atom minted here can never reach
/// it. The ascribed signature is the elimination's own half of the
/// both-directions annotation, and it names the abstract type components the
/// lowerer mints atoms for — so no separate binder list is needed or admitted.
///
/// # Specification
/// trivial.
fn unpack_statement() -> Regex
{
    seq([
        t(TileLabel("unpack")),
        t(TileLabel("identifier")),
        t(TileLabel(":")),
        h(Sort::Type),
        t(TileLabel("=")),
        h(Sort::Expression),
        t(TileLabel(";")),
    ])
}

/// Build a computation-binding statement: `run PAT : B <- E ;`.
///
/// The optional `: B` names the **bound computation's** type, so it is a
/// computation type (`F A`, and the other negative formers) rather than the
/// type of the name the pattern binds. The binder keyword already says which
/// category is bound; the annotation says which computation type the source is
/// checked against, and the lowerer spends it through the existing computation
/// ascription.
///
/// No pattern form carries a top-level `:`, so the tile after the pattern
/// discriminates the annotated and bare spellings with no lookahead.
///
/// # Specification
/// trivial.
fn bind_statement() -> Regex
{
    seq([
        t(TileLabel("run")),
        h(Sort::Pattern),
        opt(seq([t(TileLabel(":")), h(Sort::Type)])),
        t(TileLabel("<-")),
        h(Sort::Expression),
        t(TileLabel(";")),
    ])
}

/// Build a repeat-one regex.
///
/// # Specification
/// trivial.
fn repeat1(element: Regex) -> Regex
{
    seq([element.clone(), repeat(element)])
}

/// Build an inline block with semicolon-bearing statement alternatives.
///
/// # Specification
/// trivial.
fn block() -> Regex
{
    seq([
        t(TileLabel("{")),
        repeat(statement_alt()),
        opt(h(Sort::Expression)),
        t(TileLabel("}")),
    ])
}

/// Build a record pattern field.
///
/// # Specification
/// trivial.
fn record_pat_field() -> Regex
{
    seq([
        t(TileLabel("identifier")),
        t(TileLabel("=")),
        h(Sort::Pattern),
    ])
}

/// Build list pattern elements.
///
/// # Specification
/// trivial.
fn list_pat_elems() -> Regex
{
    alt([
        seq([
            comma1(h(Sort::Pattern)),
            opt(seq([t(TileLabel(",")), rest_pat()])),
        ]),
        rest_pat(),
    ])
}

/// Build an inline double-quoted string form (`" … "`).
///
/// The label `string` is a tree-sitter placeholder that no labeler token
/// carries: a string literal lexes as a `"` open quote, interior
/// `string_fragment` / `escape_sequence` tiles, and a `"` close quote — the
/// same shape the `string.expression` / `string.pattern` lexical forms declare.
/// The `extern` header and `literal_pattern` inline this shape directly so a
/// real string literal parses in those positions rather than an unmatchable
/// `string` tile.
///
/// # Specification
/// trivial.
fn dq_string() -> Regex
{
    seq([
        t(TileLabel("\"")),
        repeat(alt([
            t(TileLabel("escape_sequence")),
            t(TileLabel("string_fragment")),
        ])),
        t(TileLabel("\"")),
    ])
}

/// Build an inline extern type member.
///
/// # Specification
/// trivial.
fn extern_type_inline() -> Regex
{
    seq([
        t(TileLabel("type")),
        t(TileLabel("type_identifier")),
        t(TileLabel(";")),
    ])
}

/// Build a rest pattern.
///
/// # Specification
/// trivial.
fn rest_pat() -> Regex
{
    seq([t(TileLabel("..")), h(Sort::Pattern)])
}

/// Build expression arguments.
///
/// # Specification
/// trivial.
fn args() -> Regex
{
    seq([
        t(TileLabel("(")),
        opt(comma1(h(Sort::Expression))),
        t(TileLabel(")")),
    ])
}

/// Build a grade fragment.
///
/// # Specification
/// trivial.
fn grade() -> Regex
{
    alt([
        t(TileLabel("number")),
        t(TileLabel("identifier")),
        t(TileLabel("ω")),
    ])
}

/// Build a single nested `else if` shape.
///
/// # Specification
/// trivial.
fn if_tail() -> Regex
{
    seq([
        t(TileLabel("if")),
        h(Sort::Expression),
        opt(answer_type()),
        block(),
        t(TileLabel("else")),
        block(),
    ])
}

/// Build the eliminator answer-type slot: `-> T` after the scrutinee.
///
/// The slot is the **constant motive** of a check-only eliminator — `-> T` is
/// the motive `[_. T]`, the degenerate case of the motive slot a dependent
/// split will later widen. Placing it between the scrutinee and the body is
/// what makes the widening additive: a dependent motive replaces this slot's
/// contents, never its position.
///
/// It is locally decidable wherever it appears: the tile after the scrutinee is
/// `->` or the body's opener, so the optional tail `≐`-continues on one tile
/// and needs no lookahead.
///
/// # Specification
/// trivial.
fn answer_type() -> Regex
{
    seq([t(TileLabel("->")), h(Sort::Type)])
}

/// Build a `co` field.
///
/// # Specification
/// trivial.
fn co_field() -> Regex
{
    seq([
        t(TileLabel("identifier")),
        t(TileLabel("=")),
        h(Sort::Expression),
    ])
}

/// Build a record expression field.
///
/// # Specification
/// trivial.
fn record_field() -> Regex
{
    seq([
        t(TileLabel("identifier")),
        t(TileLabel("=")),
        h(Sort::Expression),
    ])
}

/// Build a rule preserving tree-sitter provenance.
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

/// Build a case/offer arm.
///
/// # Specification
/// trivial.
fn arm() -> Regex
{
    seq([h(Sort::Pattern), t(TileLabel("=>")), h(Sort::Expression)])
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

/// Build an inline extern function member.
///
/// # Specification
/// trivial.
fn extern_function_inline() -> Regex
{
    seq([
        t(TileLabel("def")),
        t(TileLabel("identifier")),
        params(),
        opt(seq([t(TileLabel("->")), h(Sort::Type)])),
        t(TileLabel(";")),
    ])
}

/// Build an inline parameter list.
///
/// # Specification
/// trivial.
fn params() -> Regex
{
    seq([t(TileLabel("(")), opt(comma1(param())), t(TileLabel(")"))])
}

/// Append session-operation expression forms.
///
/// # Specification
/// trivial.
fn session_expressions(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::Expression;
    out.push(r(
        RuleName("offer_expression"),
        Provenance("offer_expression"),
        s,
        p,
        seq([
            t(TileLabel("offer")),
            t(TileLabel("(")),
            h(s),
            t(TileLabel(")")),
            t(TileLabel("{")),
            comma1(arm()),
            t(TileLabel("}")),
        ]),
    ));
    out.push(r(
        RuleName("migrate_expression"),
        Provenance("migrate_expression"),
        s,
        p,
        seq([
            t(TileLabel("migrate")),
            t(TileLabel("[")),
            t(TileLabel("identifier")),
            t(TileLabel("]")),
            block(),
        ]),
    ));
    out.push(r(
        RuleName("send_expression"),
        Provenance("send_expression"),
        s,
        p,
        seq([
            t(TileLabel("send")),
            t(TileLabel("(")),
            h(s),
            t(TileLabel(",")),
            h(s),
            t(TileLabel(")")),
        ]),
    ));
    out.push(r(
        RuleName("close_expression"),
        Provenance("close_expression"),
        s,
        p,
        seq([
            t(TileLabel("close")),
            t(TileLabel("(")),
            h(s),
            t(TileLabel(")")),
        ]),
    ));
    out.push(r(
        RuleName("select_expression"),
        Provenance("select_expression"),
        s,
        p,
        seq([
            t(TileLabel("select")),
            t(TileLabel("(")),
            h(s),
            t(TileLabel(",")),
            t(TileLabel("identifier")),
            t(TileLabel(")")),
        ]),
    ));
    out.push(r(
        RuleName("dup_expression"),
        Provenance("dup_expression"),
        s,
        p,
        seq([
            t(TileLabel("dup")),
            t(TileLabel("(")),
            h(s),
            t(TileLabel(")")),
        ]),
    ));
    out.push(r(
        RuleName("drop_expression"),
        Provenance("drop_expression"),
        s,
        p,
        seq([
            t(TileLabel("drop")),
            t(TileLabel("(")),
            h(s),
            t(TileLabel(")")),
        ]),
    ));
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

/// Build a terminal tile by label; mold identity is assigned at `Pbg` build.
///
/// # Specification
/// trivial.
fn t(label: TileLabel) -> Regex
{
    Regex::tile(label)
}

/// Build a comma-separated nonempty regex list.
///
/// # Specification
/// trivial.
fn comma1(element: Regex) -> Regex
{
    seq([element.clone(), repeat(seq([t(TileLabel(",")), element]))])
}

/// Build a block member list: every member is **terminated** by `;` (the
/// surface's declaration terminator) or followed by `,` (the declined
/// constructor-block separator, kept admissible so a stale declaration parses
/// whole and reaches the elaborator's decline).
///
/// An unseparated list is NOT admitted, and the reason is a fact about the
/// machinery: a member ends in a sort hole (the generator's signature, the
/// observation's payload), the walk's `≐`-relation crosses a hole to whatever
/// may follow the member, and at the hole's fill position the next member's
/// lead mold (`constructor`, `identifier`) then outranks the hole's own
/// content in the molder's local key — `Nil : Vec` reads as a member `Nil`
/// whose signature is missing plus a nullary member `Vec`, a clean parse of
/// the wrong tree. The `sign` block's leads are reserved words, never
/// hole-content candidates, but its members collapse the same way, so it takes
/// the same mandatory `;` terminator (see the circuit forms).
/// A mandatory separator restores the discrimination: after the hole only
/// `;`, `,`, or `}` is admissible, none of which competes with hole content.
///
/// # Specification
/// trivial.
fn member_list(element: Regex) -> Regex
{
    let first = element.clone();
    seq([
        first,
        repeat(seq([member_sep(), element])),
        opt(member_sep()),
    ])
}

/// Build one member separator: the `;` terminator, or the declined `,`
/// separator admitted so it can be declined.
///
/// # Specification
/// trivial.
fn member_sep() -> Regex
{
    alt([t(TileLabel(";")), t(TileLabel(","))])
}

/// Append the module-body member forms, at their own sort.
///
/// **This is where module nesting becomes unbounded.** A precedence-bounded
/// grammar has no rule self-reference — a rule's regex names tiles and *sorts*
/// — so the only way one form can contain itself is for the containing position
/// to be a sort hole whose sort the form inhabits. Giving members a sort of
/// their own is exactly that: a module body is a repetition of
/// [`Sort::ModuleMember`] holes, and one of the forms at that sort is a nested
/// module whose body is the same repetition. Depth is therefore a property of
/// the input rather than of the grammar, and it costs two rules instead of one
/// copy of the member family per admitted level.
///
/// Repeating a bare sort hole is safe here because **every member carries its
/// own terminator**: a definition ends at `;` or at its body's closing brace,
/// and a nested module ends at its closing brace. After a member the only
/// admissible tiles are the next member's lead (`@[`, `def`, `module`) or the
/// body's `}`, none of which competes with the hole's own content — the
/// discrimination the member-list separator rule exists to protect.
///
/// # Specification
/// trivial.
fn module_members(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::ModuleMember;
    // The plain and attributed definition members are **two rules, not one
    // with an optional prefix**. A form whose first symbol is a repetition has
    // no definite lead tile, and at a sort-hole position the melder then starts
    // the member at `def` and leaves the preceding `@[ … ]` block outside it —
    // an attribute silently detached from the definition it decorates. Splitting
    // on the one token that distinguishes them gives each form a definite lead
    // and puts the block back inside the member.
    out.push(r(
        RuleName("module_definition_member"),
        Provenance("module_declaration"),
        s,
        p,
        seq([t(TileLabel("def")), regular_def_tail()]),
    ));
    out.push(r(
        RuleName("attributed_module_definition_member"),
        Provenance("module_declaration"),
        s,
        p,
        module_definition_member(),
    ));
    out.push(r(
        RuleName("nested_module_member"),
        Provenance("module_declaration"),
        s,
        p,
        nested_module_member(),
    ));
}

/// Build one **attributed** definition/signature module member: at least one
/// `@[ … ]` block, then the ordinary definition tail.
///
/// # Specification
/// trivial.
fn module_definition_member() -> Regex
{
    seq([
        attr_block_inline(),
        repeat(attr_block_inline()),
        t(TileLabel("def")),
        regular_def_tail(),
    ])
}

/// Build the declaration-level implicit telescope `@[binder, …]`.
///
/// This prefix follows the declaration name and precedes its explicit
/// parameter list. Binders are kept in source order and their type holes are
/// ordinary type syntax, so a binder may mention a later explicit parameter;
/// dependency ordering is a later lowering concern. The optional body admits
/// the empty `@[]` spelling without conflating this form with the ordinary
/// attribute block, which remains before `def`.
///
/// # Specification
/// trivial.
fn implicit_telescope() -> Regex
{
    seq([
        t(TileLabel("@[")),
        opt(comma1(implicit_param())),
        t(TileLabel("]")),
    ])
}

/// Build one typed declaration-level implicit binder.
///
/// Lowercase binders use the ordinary name classes; uppercase binders such as
/// `A` are lexically offered as type identifiers by the labeler and remain
/// valid binder names at this parse-only stage.
///
/// # Specification
/// trivial.
fn implicit_param() -> Regex
{
    seq([
        alt([
            t(TileLabel("identifier")),
            t(TileLabel("type_variable")),
            t(TileLabel("type_identifier")),
        ]),
        t(TileLabel(":")),
        h(Sort::Type),
    ])
}

/// Build the non-recursive definition/signature tail after `def`.
///
/// # Specification
/// trivial.
fn regular_def_tail() -> Regex
{
    seq([
        t(TileLabel("identifier")),
        opt(implicit_telescope()),
        alt([
            // signature tail: `: T ;`
            seq([t(TileLabel(":")), h(Sort::Type), t(TileLabel(";"))]),
            // value tail: `= E ;`
            seq([t(TileLabel("=")), h(Sort::Expression), t(TileLabel(";"))]),
            // function tail: `(params) -> T? { … }`
            seq([
                params(),
                opt(seq([t(TileLabel("->")), h(Sort::Type)])),
                block(),
            ]),
        ]),
    ])
}

// The prefix telescope is intentionally absent from ordinary attribute blocks:
// `@[doc("…")] def …` remains the declaration-level attribute spelling, while
// `def name @[A : Type] …` is the typed implicit-parameter spelling.

/// Build one nested module component.
///
/// Its body is the same [`Sort::ModuleMember`] repetition the outer declaration
/// takes, which is what makes nesting recursive rather than unrolled: this form
/// inhabits the sort its own body is a repetition of.
///
/// The name admits both case spellings. A nested declaration is a component of
/// its enclosing module's record, and nothing downstream keys on its case, so
/// refusing the uppercase spelling here would only turn `module Limits` into
/// a repair region the reader experiences as malformed input. The outer
/// form's uppercase-only tile keeps its named lowercase-name decline at the
/// top level, and this slot carries no such ruling to preserve.
///
/// # Specification
/// trivial.
fn nested_module_member() -> Regex
{
    seq([
        t(TileLabel("module")),
        alt([t(TileLabel("identifier")), t(TileLabel("type_identifier"))]),
        opt(module_ascription_tail()),
        t(TileLabel("{")),
        repeat(h(Sort::ModuleMember)),
        t(TileLabel("}")),
    ])
}

/// Build a sort hole.
///
/// # Specification
/// trivial.
fn h(sort: Sort) -> Regex
{
    Regex::sort(sort)
}

/// Append atom-level expression forms.
///
/// # Specification
/// trivial.
fn primary_expressions(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::Expression;
    // A user-written typed hole `?` (anonymous) or `?name` (the optional Hazelnut
    // hole *name*, addressing the hole in the goal stream). The `hole_name` tile
    // occurs ONLY here, as the hole's optional tail; it is deliberately NOT also a
    // standalone Expression atom. A standalone `hole_name` rule gave
    // the tile a second, fresh-slot mold that ties with every bare `identifier` on
    // the molder's local key and — sitting at a smaller `MoldId` — would win,
    // reading every lowercase word as a hole name. Folding it away leaves one
    // `hole_name` mold, a form-end reachable only while a `?` frontier is open, so
    // `?name`'s name attaches without shadowing the identifier menu. The `?` hole
    // is in the grammar LAST set (its tail is nullable), so the melder closes a
    // bare `?` cleanly instead of demanding the name.
    let mut hole = r(
        RuleName("hole"),
        Provenance("hole"),
        s,
        p,
        seq([t(TileLabel("?")), opt(t(TileLabel("hole_name")))]),
    );
    hole.adaptations.push(Adaptation::new(
        RuleName("hole"),
        SurfaceForm("hole_name"),
        AdaptationReason("folded into the hole family: the tree-sitter `hole_name` node is the `?` hole's optional name tail (`imm(/[a-z_]\\w*/)`), realised inline as the `opt(hole_name)` tile occurrence, dropping the redundant standalone `hole_name` Expression atom — a second, fresh-slot mold that tied with every bare `identifier` on the molder's local key and, at a smaller `MoldId`, would have won, reading every lowercase word as a hole name — so `hole_name` keeps ONE mold, reachable only while a `?` frontier is open."),
    ));
    out.push(hole);
    // The `(`-opened expression atoms — unit `( )`, parenthesized `( E )`, tuple
    // `( E , E+ )`, and annotation `( E : T )` — share the `( E` prefix and
    // diverge only at the tile after the expression (`)` versus `,` versus `:`),
    // which for a long `E` sits arbitrarily far past the `(`, out of reach of a
    // bounded lookahead. They are factored into one form whose tail alternates on
    // that discriminating tile, so the `(` owns one mold and the choice is
    // locally decidable — the discriminator `≐`-continues exactly one tail.
    // The concrete language is unchanged; the folded kinds are recorded as
    // adaptations for the parity inventory.
    let mut paren = r(
        RuleName("parenthesized_expression"),
        Provenance("parenthesized_expression"),
        s,
        p,
        seq([
            t(TileLabel("(")),
            alt([
                // unit: `( )`
                t(TileLabel(")")),
                seq([
                    h(s),
                    alt([
                        // parenthesized: `( E )`
                        t(TileLabel(")")),
                        // tuple: `( E , E+ )`
                        seq([repeat1(seq([t(TileLabel(",")), h(s)])), t(TileLabel(")"))]),
                        // annotation: `( E : T )`
                        seq([t(TileLabel(":")), h(Sort::Type), t(TileLabel(")"))]),
                    ]),
                ]),
            ]),
        ]),
    );
    paren.adaptations.push(Adaptation::new(
        RuleName("parenthesized_expression"),
        SurfaceForm("unit"),
        AdaptationReason("factored into the `(` expression-atom family: the empty tail `)` shares the `(` prefix"),
    ));
    paren.adaptations.push(Adaptation::new(
        RuleName("parenthesized_expression"),
        SurfaceForm("tuple_expression"),
        AdaptationReason("factored into the `(` expression-atom family: the tuple tail `, E+ )` shares the `( E` prefix and discriminates on the leading `,` tile"),
    ));
    paren.adaptations.push(Adaptation::new(
        RuleName("parenthesized_expression"),
        SurfaceForm("annotation_expression"),
        AdaptationReason("factored into the `(` expression-atom family: the annotation tail `: T )` shares the `( E` prefix and discriminates on the leading `:` tile"),
    ));
    out.push(paren);
    out.push(r(
        RuleName("list_expression"),
        Provenance("list_expression"),
        s,
        p,
        seq([t(TileLabel("[")), opt(comma1(h(s))), t(TileLabel("]"))]),
    ));
    out.push(r(RuleName("block"), Provenance("block"), s, p, block()));
    // The value lambda `fn (params) { … }` and the type abstraction
    // `fn [ tyvars ] { … }` share the `fn` prefix and diverge only at the tile
    // after it — `(` versus `[`. Declaring them as two rules gives `fn` two molds
    // that tie on the molder's local key and fire a lookahead window per `fn`;
    // they are factored into one form whose tail alternates on that discriminating
    // tile (the `def` / `val` idiom), so `fn` owns one mold and the choice is
    // locally decidable. The folded kind is an adaptation for the parity inventory.
    let mut lambda = r(
        RuleName("lambda_expression"),
        Provenance("lambda_expression"),
        s,
        p,
        seq([
            t(TileLabel("fn")),
            alt([
                seq([params(), block()]),
                seq([
                    t(TileLabel("[")),
                    comma1(t(TileLabel("type_variable"))),
                    t(TileLabel("]")),
                    block(),
                ]),
            ]),
        ]),
    );
    lambda.adaptations.push(Adaptation::new(
        RuleName("lambda_expression"),
        SurfaceForm("type_abstraction"),
        AdaptationReason("factored into the fn family: the type-abstraction tail `[ tyvars ] { … }` shares the `fn` prefix and discriminates on the leading `[` tile"),
    ));
    out.push(lambda);
    out.push(r(
        RuleName("thunk_expression"),
        Provenance("thunk_expression"),
        s,
        p,
        seq([
            t(TileLabel("thunk")),
            opt(seq([t(TileLabel("[")), grade(), t(TileLabel("]"))])),
            block(),
        ]),
    ));
    // The `arm` (`PAT => E`) helper is inline-only — it appears solely inside a
    // `case` / `offer` body. A standalone rule additionally gives its first tile
    // (a pattern atom: `identifier`, `constructor`, …) a form-first
    // Expression-sort mold that ties with every operand, a spurious competitor
    // the molder must break by lookahead. It is folded into `case_expression`
    // (recorded as an adaptation); the inlined arms still realise its shape.
    // The case body's arms are `opt`-wrapped so an empty/absurd match `case x
    // {}` over an uninhabited type parses; the reserved
    // with-view `case e with e { … }` adds an optional `with`
    // scrutinee, the `with` tile separating the two Expression holes.
    // The answer type `-> T` sits after everything being eliminated — past the
    // `with` view rather than between it and the scrutinee — because a motive
    // quantifies over the whole target, so a later dependent motive occupies
    // this same position without moving the view.
    let mut case = r(
        RuleName("case_expression"),
        Provenance("case_expression"),
        s,
        p,
        seq([
            t(TileLabel("case")),
            h(s),
            opt(seq([t(TileLabel("with")), h(s)])),
            opt(answer_type()),
            t(TileLabel("{")),
            opt(comma1(arm())),
            t(TileLabel("}")),
        ]),
    );
    case.adaptations.push(Adaptation::new(
        RuleName("case_expression"),
        SurfaceForm("arm"),
        AdaptationReason("folded into case_expression / offer_expression: the `PAT => E` arm is inlined in the body, not a standalone form-first pattern atom competing with a bare operand"),
    ));
    case.adaptations.push(Adaptation::new(
        RuleName("case_expression"),
        SurfaceForm("case_with_view"),
        AdaptationReason("reserved parse-and-decline: the optional `with e` scrutinee view; the empty-arm option additionally admits the absurd match `case x {}`"),
    ));
    case.adaptations.push(Adaptation::new(
        RuleName("case_expression"),
        SurfaceForm("case_answer_type"),
        AdaptationReason("folded into case_expression: the optional `-> T` answer type is an inline slot after the scrutinee and the reserved `with` view, not a standalone form; it is the constant motive `[_. T]`, and the later dependent motive replaces its contents rather than its position"),
    ));
    out.push(case);
    let mut if_expression = r(
        RuleName("if_expression"),
        Provenance("if_expression"),
        s,
        p,
        seq([
            t(TileLabel("if")),
            h(s),
            opt(answer_type()),
            block(),
            t(TileLabel("else")),
            alt([block(), if_tail()]),
        ]),
    );
    if_expression.adaptations.push(Adaptation::new(
        RuleName("if_expression"),
        SurfaceForm("if_answer_type"),
        AdaptationReason("folded into if_expression: the optional `-> T` answer type is an inline slot after the condition, carried by the nested `else if` tail as well as the head, not a standalone form; it is the constant motive `[_. T]`"),
    ));
    out.push(if_expression);
    // Control-flow atoms.
    // Each is keyword-led — a fresh first-token discriminator, siblings of
    // `if` / `case` at `expression.atom`, flowing into `expression_statement`
    // for `;`-terminated statement position. `for` binds a single identifier
    // (the MVP; a full pattern binder is a later widening); `break` / `continue`
    // are bare single-tile atoms (unlabeled, unit payload). These are PBG-only,
    // parity-exempt.
    out.push(r(
        RuleName("for_expression"),
        Provenance("for_expression"),
        s,
        p,
        seq([
            t(TileLabel("for")),
            t(TileLabel("identifier")),
            t(TileLabel("in")),
            h(s),
            block(),
        ]),
    ));
    out.push(r(
        RuleName("while_expression"),
        Provenance("while_expression"),
        s,
        p,
        seq([t(TileLabel("while")), h(s), block()]),
    ));
    out.push(r(
        RuleName("loop_expression"),
        Provenance("loop_expression"),
        s,
        p,
        seq([t(TileLabel("loop")), block()]),
    ));
    out.push(r(
        RuleName("break_expression"),
        Provenance("break_expression"),
        s,
        p,
        t(TileLabel("break")),
    ));
    out.push(r(
        RuleName("continue_expression"),
        Provenance("continue_expression"),
        s,
        p,
        t(TileLabel("continue")),
    ));
    // The `co_field` / `record_field` members are inlined in their enclosing
    // forms. A standalone rule would additionally give their `identifier`
    // opener a form-first Expression-sort mold that ties with every bare
    // identifier at an operand slot — a tie the molder must break by lookahead
    // on EVERY identifier, which dominates parse cost. They are folded into
    // their enclosing forms (recorded as adaptations for the parity
    // inventory); the inlined members still realise the fields' shape.
    let mut co = r(
        RuleName("co_expression"),
        Provenance("co_expression"),
        s,
        p,
        seq([
            t(TileLabel("co")),
            t(TileLabel("{")),
            comma1(co_field()),
            t(TileLabel("}")),
        ]),
    );
    co.adaptations.push(Adaptation::new(
        RuleName("co_expression"),
        SurfaceForm("co_field"),
        AdaptationReason("folded into co_expression: the `id = E` field is inlined, not a standalone form-first identifier competing with a bare variable"),
    ));
    out.push(co);
    // A glob copattern block is an expression-level consumer form. Its
    // semicolon-terminated fields are deliberately separate from the comma
    // record family: `glob { cells = A; home(x, y) = e; }` is a sequence of
    // observations whose names and values remain ordinary expression slots.
    out.push(r(
        RuleName("glob_expression"),
        Provenance("glob_expression"),
        s,
        p,
        seq([
            t(TileLabel("glob")),
            t(TileLabel("{")),
            repeat(seq([co_field(), t(TileLabel(";"))])),
            t(TileLabel("}")),
        ]),
    ));
    // The `#{`-opened expression forms — the empty/populated record literal
    // `#{ }` / `#{ id = E, … }` and the record update `#{ E | id = E, … }` —
    // share the `#{` prefix and diverge only at the tile after the first
    // expression: an update's `|` versus a literal field's `=`. Declaring them as
    // two rules gives `#{` two Expression-sort molds, so the molder must decide
    // record-versus-update at the `#{` — a choice whose discriminating `|` sits
    // arbitrarily deep past nested `#{ … }` values (each carrying its own `|`),
    // out of a bounded lookahead's reach (`deep-record-update-cost`). They are
    // factored into one form whose tail alternates on the discriminating tile:
    // `#{` owns one mold, the first expression fills one hole, and the following
    // `|` / `=` `≐`-continues exactly one tail — locally decidable with no window
    // — and the `|` reads as the form's own continuation (continuation-rank 0),
    // never the pipeline operator. The
    // concrete language is unchanged; the folded kinds are adaptations for the
    // parity inventory.
    let mut record = r(
        RuleName("record_expression"),
        Provenance("record_expression"),
        s,
        p,
        seq([
            t(TileLabel("#{")),
            alt([
                // empty record: `#{ }`
                t(TileLabel("}")),
                seq([
                    // the first expression: the update source, or a literal
                    // field's key (a bare identifier molds as an atom here).
                    h(s),
                    alt([
                        // update tail: `| id = E, … }`
                        seq([t(TileLabel("|")), comma1(record_field()), t(TileLabel("}"))]),
                        // literal tail: the first field's `= E`, then `, id = E`*.
                        seq([
                            t(TileLabel("=")),
                            h(s),
                            repeat(seq([t(TileLabel(",")), record_field()])),
                            t(TileLabel("}")),
                        ]),
                    ]),
                ]),
            ]),
        ]),
    );
    record.adaptations.push(Adaptation::new(
        RuleName("record_expression"),
        SurfaceForm("record_field"),
        AdaptationReason("folded into the factored #{ family: the `id = E` field is inlined (the first field's key is the leading expression hole), not a standalone form-first identifier competing with a bare variable"),
    ));
    record.adaptations.push(Adaptation::new(
        RuleName("record_expression"),
        SurfaceForm("record_update_expression"),
        AdaptationReason("factored into the #{ expression family: the update tail `| id = E, … }` shares the `#{ E` prefix and discriminates on the `|` tile after the source expression"),
    ));
    out.push(record);
    session_expressions(out, p);
    // The shell block's interior is a generic Expression hole: its commands mold
    // as juxtaposed command atoms (`command_name`, `single_quoted_string`, …)
    // joined by the separator / operator forms (`;`, `&&`, the `|` pipeline), the
    // way a POSIX shell reads them. The `[ … ]` subshell is an
    // Expression-atom form of its own (`type_shell::add_shell_rules`), molded
    // on distinct shell-context bracket tiles, so this block does not fold it.
    out.push(r(
        RuleName("shell_block"),
        Provenance("shell_block"),
        s,
        p,
        seq([
            t(TileLabel("#!{")),
            opt(h(Sort::Expression)),
            t(TileLabel("}")),
        ]),
    ));
}
