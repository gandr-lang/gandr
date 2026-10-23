//! The term surface: item, declaration, statement, pattern, instantiation,
//! expression and lexical forms.
//!
//! # Type operators: the static abstraction and the value function space
//!
//! A type operator is written `\A. T`: the backslash, one binder — a type name
//! or a type variable — a dot and the body, which runs as far right as a
//! `forall`'s does, so `\T. \A. \B. T(A) * B` nests three binders. The labeler
//! reads a backslash in code as one tile; escape sequences stay inside strings
//! and characters, where their scanners read them. Applying an operator reuses
//! `type_application`, `T(A, B)`, whose head is a type name or a type variable:
//! a declaration is named by a lowercase identifier, which molds as a type
//! variable in type position, so an operator declared by `def` applies as
//! `raw_rel_monad(T, A, B)`. Admitting the variable head added one mold and
//! moved the fingerprint from `0x8feb_efc4_2bd0_36d1`.
//!
//! - Alternatives: a keyword lead such as `fn` at the type sort, which ties
//!   with the term lambda wherever a definition's body stands, where a
//!   type-only lead molds unopposed; a binder list `\A B. T`, which saves a few
//!   backslashes and adds a repetition the lowering would curry anyway.
//! - Reversal: a binder that needs its classifier written beside it (`\(T :
//!   Type -> Type[-]). …`) would take the parenthesized binder as a second
//!   alternative of the same rule.
//!
//! The value function space `A => B` is the alias of the thunked arrow `+U (A
//! -> -F B)`, and `(A, B) => C` its n-ary form, `+U (A -> B -> -F C)`. It is an
//! infix rule in the arrow's group, so the two arrows nest to the right of one
//! another; its n-ary domain is a parenthesized type list, which is why
//! `parenthesized_type` holds one type or several. One rule keeps `(` at a
//! single type-sort mold, so the molder never opens a lookahead window to tell
//! a parenthesized type from a domain list, and the lowering refuses a list
//! anywhere but before `=>`. A case arm's `=>` follows a pattern and this one a
//! type; the two never compete for one slot. Nothing distinguishes the alias
//! from its unfolding after lowering except the printer, which may choose
//! either spelling.
//!
//! The empty list `() => B` is the nullary form, `+U (-F B)`: the lowering
//! reads an empty domain list as no domain, so it is a different type from
//! `Unit => B`, the function of one argument of the unit type.
//!
//! - Alternatives: a separate rule for the n-ary domain, `( T , T+ ) => T`,
//!   which gives `(` two type-sort molds tied on the molder's local key.
//! - Reversal: if a tuple type ever takes the parenthesized list, the domain
//!   list moves into the alias rule and the tie is settled there.
//!
//! # The unit value is a keyword
//!
//! The unit value is the keyword `unit`, one tile at the expression sort and
//! one at the pattern sort, beside `true` and `false`; its type is the type
//! name `Unit`. The empty parentheses `()` stay a parenthesised list with no
//! member, so the lowering refuses them as a value or a type and reads them as
//! the empty domain list before `=>`. Adding the two rules moved the pinned
//! shape from 2487 molds, 77 labels and the fingerprint
//! `0x4116_5b5c_93e2_0732`.
//!
//! - Choice: `unit` is reserved, and `()` is always an empty list. The unit is
//!   the nullary product, and with an n-ary product the empty list is its
//!   nullary case, so one spelling stands for one thing.
//! - Alternatives: `()` as the unit, which makes `() => B` and `Unit => B` the
//!   same type and reads one token sequence two ways by position; leaving
//!   `unit` an ordinary name the prelude declares, which a local binding could
//!   shadow.
//! - Reversal: if the n-ary product is never admitted and no source writes `()
//!   => B`, `()` may return as a second spelling of `unit` and the keyword
//!   stays.

use alloc::vec::Vec;

use anodized::spec;
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
use crate::model::RegexShape;
use crate::model::Sym;

/// Builds every surface rule except the type, shell and circuit forms.
///
/// # Specification
/// - requires: nothing.
/// - ensures: item, declaration, attribute, extern, module member, pattern,
///   instantiation, expression and lexical forms, in that order, over
///   [`Sort::Item`], [`Sort::ModuleMember`], [`Sort::Pattern`],
///   [`Sort::Expression`], [`Sort::Type`] and [`Sort::Instantiation`] holes.
/// - fails: a group `precs` does not hold.
/// - panics: none.
///
/// # Errors
/// [`PbgError::MissingPrec`] naming the absent group.
///
/// # Adequacy
/// - hypothesis: For complete and missing-band tables, L2 error-order
///   observations and L3 grammar identity catch silent omission, reordered
///   families and incorrect missing-group provenance. The predicate observes
///   the first missing band or the ordered resident-sort ranges; arbitrary
///   aliases and source programs beyond the corpus are not exhausted.
/// - witness: `surface::term::tests::assembly_reports_the_first_missing_band`
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error, &PbgError::MissingPrec { name } if ["item.singleton", "pattern.or", "pattern.as", "pattern.cons", "pattern.atom", "expression.pure", "expression.or", "expression.and", "expression.cmp", "expression.cons", "expression.add", "expression.mul", "expression.unary", "expression.postfix", "expression.atom"].into_iter().find(|&group| precs.get(PrecName(group)).is_none()) == Some(name)), |rules| rules.len() == 104 && rules.iter().enumerate().all(|(index, rule)| rule.sort() == match index { 0..=9 => Sort::Item, 10..=13 => Sort::ModuleMember, 14..=25 | 94..=95 => Sort::Pattern, 26..=31 => Sort::Instantiation, _ => Sort::Expression }) && rules.first().is_some_and(|rule| rule.name().0 == "def_value") && rules.last().is_some_and(|rule| rule.name().0 == "string.expression")))]
pub(super) fn rules(precs: &PrecTable) -> Result<Vec<Rule>, PbgError>
{
    let item = precs.prec(PrecName("item.singleton"))?;
    let pat_or = precs.prec(PrecName("pattern.or"))?;
    let pat_as = precs.prec(PrecName("pattern.as"))?;
    let pat_cons = precs.prec(PrecName("pattern.cons"))?;
    let pat_atom = precs.prec(PrecName("pattern.atom"))?;
    let pure = precs.prec(PrecName("expression.pure"))?;
    let or = precs.prec(PrecName("expression.or"))?;
    let and = precs.prec(PrecName("expression.and"))?;
    let cmp = precs.prec(PrecName("expression.cmp"))?;
    let cons = precs.prec(PrecName("expression.cons"))?;
    let add = precs.prec(PrecName("expression.add"))?;
    let mul = precs.prec(PrecName("expression.mul"))?;
    let unary = precs.prec(PrecName("expression.unary"))?;
    let postfix = precs.prec(PrecName("expression.postfix"))?;
    let atom = precs.prec(PrecName("expression.atom"))?;

    let mut out = Vec::new();
    items(&mut out, item);
    declarations(&mut out, item);
    attributes_parameters_externs(&mut out, item);
    module_members(&mut out, item);
    patterns(&mut out, PatternPrecs {
        or: pat_or,
        as_p: pat_as,
        cons: pat_cons,
        atom: pat_atom,
    });
    instantiations(&mut out, atom, pure);
    expressions(&mut out, ExprPrecs {
        pure,
        or,
        and,
        cmp,
        cons,
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
/// - requires: nothing.
/// - ensures: appends one factored definition rule at the item sort and
///   supplied band.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 1 && added.first().is_some_and(|rule| rule.name().0 == "def_value" && rule.provenance().0 == "def_value" && rule.sort() == Sort::Item && rule.prec() == p && rule.adaptations().iter().map(|adaptation| adaptation.surface).eq(["def_signature", "def_function", "def_rec"]))))]
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
        AdaptationReason("factored into the def family: the signature tail `: T ;` shares the `def id` prefix and discriminates on the leading `:` tile"),
    ));
    def.adaptations.push(Adaptation::new(
        RuleName("def_value"),
        SurfaceForm("def_function"),
        AdaptationReason("factored into the def family: the function tail `(params) -> T? { … }` shares the `def id` prefix and discriminates on the leading `(` tile"),
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
/// All land at `item.singleton` beside the def family. Every form is
/// keyword-led (a fresh first-token discriminator with no lookahead against
/// `def`, `import`, …), so no new shared-prefix window opens. The
/// tree-sitter grammar does not produce these constructs, so their provenance
/// names are in [`PBG_ONLY_KINDS`](crate::PBG_ONLY_KINDS) and the named-kind
/// inventory never lists them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the six ordered declaration families at the item sort and
///   supplied band.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 7 && added.iter().zip(["data_declaration", "codata_declaration", "module_declaration", "import_declaration", "world_declaration", "operator_declaration", "rec_block"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::Item && rule.prec() == p && rule.provenance().0 == name)))]
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
        AdaptationReason("parse-and-decline: the Haskell-style constructor member `Ctor(fields) (: Result)?`, or a bare `Ctor`, stays admissible as the constructor-led member's second tail so a stale declaration reaches the elaborator's decline with the respelling hint instead of a parse repair; the tail discriminates on `(` vs `:` immediately after the constructor name, and its result annotation follows the field tuple only, since a fieldless `Ctor : Result` is the generator"),
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
        AdaptationReason("a `rule lhs <=> rhs` equation, or `rule lhs ==> rhs` pinning its direction, is inlined in the data block, first-token-discriminated by the `rule` keyword; the declined `~>` face arrow stays admissible so a stale spelling reaches the elaborator's decline instead of a parse repair"),
    ));
    data.adaptations.push(Adaptation::new(
        RuleName("data_declaration"),
        SurfaceForm("grade_prefix"),
        AdaptationReason("the reserved grade prefix on a constructor field is restricted to `{ number, ω }`, without the bare identifier spelling, so a graded field `Cons(1 x: a)` stays first-token-distinct from an ungraded field `Some(x: a)`: an identifier grade would be indistinguishable from a field name"),
    ));
    data.adaptations.push(Adaptation::new(
        RuleName("data_declaration"),
        SurfaceForm("cell_member"),
        AdaptationReason("the cell member `name : a <-> b` is inlined in the data block, first-token-discriminated by its lowercase name, which no other member opens on; every glyph of the arrow grid parses between its two terms so the elaborator refuses each one the fragment does not lower by its own name"),
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
        AdaptationReason("a `rule lhs <=> rhs` equation, or `rule lhs ==> rhs` pinning its direction, is inlined in the codata block, first-token-discriminated by the `rule` keyword; the declined `~>` face arrow stays admissible so a stale spelling reaches the elaborator's decline instead of a parse repair"),
    ));
    out.push(codata);

    // --- module declaration ----------------------------------------------------
    // `module M { … }`, optionally ascribed against a `#{ … }` signature, `:`
    // transparently or `:>` opaquely (`module_ascription_tail`). The shared
    // `module` opener and its name own one mold. The body is a repetition of
    // `Sort::ModuleMember` holes: a definition, an attributed definition, a
    // type member, or a nested module of either name case with its own
    // optional ascription, whose body is the same repetition, so nesting depth
    // is unbounded.
    //
    // After the name, a functor declares its parameter in parentheses,
    // `module MkSet(Elt : #{ … }) :> #{ … } { … }` (`functor_parameter`), and a
    // functor application binds its instance, `module IntSet = MkSet(IntOrd) ;`
    // (`functor_application_tail`). The application's tail opens at `=`, the
    // parameter at `(`, the ascription at `:` or `:>` and the body at `{`, so
    // the choice stays one token deep. The application is a module binding and
    // nothing else: no rule projects from it, so `MkSet(IntOrd).T` has no
    // reading but the one the lowering refuses by name.
    let mut module = r(
        RuleName("module_declaration"),
        Provenance("module_declaration"),
        s,
        p,
        seq([
            t(TileLabel("module")),
            alt([t(TileLabel("type_identifier")), t(TileLabel("identifier"))]),
            alt([
                functor_application_tail(),
                seq([
                    opt(functor_parameter()),
                    opt(module_ascription_tail()),
                    t(TileLabel("{")),
                    repeat(h(Sort::ModuleMember)),
                    t(TileLabel("}")),
                ]),
            ]),
        ]),
    );
    module.adaptations.push(Adaptation::new(
        RuleName("module_declaration"),
        SurfaceForm("lowercase_module_name"),
        AdaptationReason("parse-and-decline: a top-level module named with a lowercase initial stays admissible, so the declaration reaches the lowering's named decline instead of a parse repair whose recovery depends on what the module's signature and body hold"),
    ));
    out.push(module);

    // --- module `import` -------------------------------
    // `import "URI" ;` and `import "URI" as name ;`. The URI is a plain string
    // literal, so a new scheme needs no grammar change.
    out.push(r(
        RuleName("import_declaration"),
        Provenance("import_declaration"),
        s,
        p,
        seq([
            t(TileLabel("import")),
            dq_string(),
            opt(seq([t(TileLabel("as")), t(TileLabel("identifier"))])),
            t(TileLabel(";")),
        ]),
    ));

    // --- world declaration ------------------------------
    // `world w ;` declares a world a located judgement names: where a handle
    // `A at w` lives, where `migrate [w] { … }` runs its body, and where an
    // entry the host grants is homed. A world has no body and no type; its
    // name is all it brings into scope, and only the world positions read it.
    out.push(r(
        RuleName("world_declaration"),
        Provenance("world_declaration"),
        s,
        p,
        seq([
            t(TileLabel("world")),
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

    // --- mutual-recursion `rec { … }` block -
    // Form-first `rec {` is distinct from the `def` tail's `rec` (where `rec`
    // is a `≐`-successor of `def`), so the two `rec` uses never tie at a fresh
    // item slot. Each member is an item hole: a data declaration, a
    // definition or an attribute block, read by the module as it reads one at
    // the root.
    let mut rec_block = r(
        RuleName("rec_block"),
        Provenance("rec_block"),
        s,
        p,
        seq([
            t(TileLabel("rec")),
            t(TileLabel("{")),
            repeat(h(Sort::Item)),
            t(TileLabel("}")),
        ]),
    );
    rec_block.adaptations.push(Adaptation::new(
        RuleName("rec_block"),
        SurfaceForm("rec_block"),
        AdaptationReason("a `rec { … }` mutual block: its members are items — data declarations, definitions and their attribute blocks — admitted as one block"),
    ));
    out.push(rec_block);
}

/// Build the top-level definition family: `def` and a factored
/// value/signature/function/recursive tail.
///
/// The attribute blocks decorating a definition stand before it as
/// `attribute_block` forms of their own, as they do before a data
/// declaration, so the definition's identity excludes them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one def tile and the recursive-or-regular tail menu.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "def")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Alt(_)))))]
fn def_family() -> Regex
{
    seq([
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
/// The signature is written inline, `#{ … }`, or computed by a signature
/// former applied to a declaration, `Model(CatShape)`: the signature of the
/// models of a `theory` block, which the lowering derives from the block rather
/// than reading it off a written list. The two are first-token-discriminated —
/// `#{` against a type name — so the choice stays one token deep. The former is
/// a type name rather than a reserved word, so the lowering names an unknown
/// former instead of the lexer refusing an ordinary identifier.
///
/// # Specification
/// - requires: nothing.
/// - ensures: transparent and opaque ascription branches whose signature shapes
///   agree and whose opening tiles differ, each offering the inline signature
///   and the applied signature former.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 2 && parts.iter().zip([":", ":>"]).all(|(part, lead)| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.first().is_some_and(|item| matches!(item.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == lead)) && sequence.get(1).is_some_and(|item| matches!(item.shape(), RegexShape::Alt(ref signatures) if signatures.len() == 2))))))]
fn module_ascription_tail() -> Regex
{
    alt([
        seq([
            t(TileLabel(":")),
            alt([module_signature(), signature_former()]),
        ]),
        seq([
            t(TileLabel(":>")),
            alt([module_signature(), signature_former()]),
        ]),
    ])
}

/// Build a functor's parameter, `(Elt : #{ … })` or `(S : Model(Mag))`: the
/// parameter's module name and the signature it is matched against, in
/// parentheses.
///
/// Matching an argument against the parameter is transparent ascription, so
/// the signature is spelled as an ascription spells one: inline, or computed
/// by a signature former applied to a declaration, first-token-discriminated
/// as there. One parameter: a functor of several is spelled as a functor
/// whose body applies another.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an opening parenthesis, one type name, a colon, the inline
///   signature or the applied signature former, and the closer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 5 && parts.iter().zip(["(", "type_identifier", ":"]).all(|(part, label)| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label)) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Alt(ref signatures) if signatures.len() == 2)) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ")"))))]
fn functor_parameter() -> Regex
{
    seq([
        t(TileLabel("(")),
        t(TileLabel("type_identifier")),
        t(TileLabel(":")),
        alt([module_signature(), signature_former()]),
        t(TileLabel(")")),
    ])
}

/// Build a functor application's binding tail, `= MkSet(IntOrd) ;`: the
/// functor's name and the module path it is applied to, in parentheses.
///
/// The argument is a path, `IntOrd` or `Outer.Inner`, never a structure
/// literal: an application names modules that exist, and an inline structure
/// is a module binding written first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an equals sign, the functor's type name, an opening parenthesis,
///   a type name followed by any number of dotted segments of either name case,
///   the closer and a semicolon.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 7 && ["=", "type_identifier", "(", "type_identifier"].iter().zip(parts.iter()).chain([")", ";"].iter().zip(parts.iter().skip(5))).all(|(label, part)| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == *label)) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(_)))))]
fn functor_application_tail() -> Regex
{
    seq([
        t(TileLabel("=")),
        t(TileLabel("type_identifier")),
        t(TileLabel("(")),
        t(TileLabel("type_identifier")),
        repeat(seq([
            t(TileLabel(".")),
            alt([t(TileLabel("type_identifier")), t(TileLabel("identifier"))]),
        ])),
        t(TileLabel(")")),
        t(TileLabel(";")),
    ])
}

/// Build an applied signature former, `Model(CatShape)`, and the manifest
/// sorts it fixes, `Model(Metering) with sort Ratio = Integer`: a former's
/// name, the declaration it is applied to in parentheses, then any number of
/// `with sort` clauses, each a sort's name and the type it is.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a type name, an opening parenthesis, one type name and its
///   closer, then a repetition of `with`, `sort`, a type name, `=` and a type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 5 && parts.iter().zip(["type_identifier", "(", "type_identifier", ")"]).all(|(part, label)| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label)) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(_)))))]
fn signature_former() -> Regex
{
    seq([
        t(TileLabel("type_identifier")),
        t(TileLabel("(")),
        t(TileLabel("type_identifier")),
        t(TileLabel(")")),
        repeat(seq([
            t(TileLabel("with")),
            t(TileLabel("sort")),
            t(TileLabel("type_identifier")),
            t(TileLabel("=")),
            h(Sort::Type),
        ])),
    ])
}

/// Build a module signature: the record-shaped ascription body, whose fields
/// are value components and abstract type components.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a record-signature opener, optional field list and closing brace.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "#{")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "}"))))]
fn module_signature() -> Regex
{
    seq([
        t(TileLabel("#{")),
        opt(comma1(module_signature_field())),
        t(TileLabel("}")),
    ])
}

/// A value component `ℓ : T` or a parameterized value component
/// `ℓ : (a : T) -> U`, a **type component** — `type T = τ` when the
/// component is *manifest*, `type T` when it is abstract — or a **mobile**
/// abstract component, `mobile type T`. The value and type forms are
/// first-token-discriminated by the `type` keyword — already a tile in this
/// grammar, from the `extern` block's inline type members — and the mobile one
/// by its own `mobile` keyword, so admitting them in one semicolon- or
/// comma-separated list costs no lookahead, and the manifest tail is one
/// optional `=`.
///
/// The `mobile` mark is the signature's promise that the atom sealing mints
/// may cross between worlds; the checker holds the representation to it when
/// it seals. Only an abstract component carries it: a manifest component
/// expands to its type, whose mobility is decided on the type itself, and a
/// kinded one declares a family no single representation answers for.
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
/// `type Home(a : Ob, b : Ob) = +U[ω] (a -> -F b)`. That is the *manifest*
/// family — the form an instance supplies a kinded component with — and it is a
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
/// - requires: nothing.
/// - ensures: a value-field branch, a type-component branch and a mobile
///   abstract-component branch, discriminated by their initial name classes.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 3 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ":")) && sequence.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Type)))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 4 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "type")) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "type_identifier")) && sequence.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && sequence.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 3 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "mobile")) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "type")) && sequence.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "type_identifier"))))))]
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
        seq([
            t(TileLabel("mobile")),
            t(TileLabel("type")),
            t(TileLabel("type_identifier")),
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
/// - requires: nothing.
/// - ensures: a rec keyword, name and parameters followed by an optional result
///   and one brace-delimited alternative body.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 7 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "rec")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "{")) && parts.get(5).is_some_and(|part| matches!(part.shape(), RegexShape::Alt(_))) && parts.get(6).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "}"))))]
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
/// - requires: nothing.
/// - ensures: an observation arm and a default arm, each ending in an
///   expression hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 4 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ".")) && sequence.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "=>")) && sequence.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 3 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "_")) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "=>")) && sequence.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression))))))]
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
/// - requires: nothing.
/// - ensures: a non-optional binder list between parentheses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "(")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ")"))))]
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
/// a reserved `op` operation, a reserved `rule` 2-cell, or a **cell** between
/// two terms of the block's sort.
///
/// The constructor-led tails share the `constructor` tile and discriminate one
/// tile later: `:` leads the generator judgment, anything else the declined
/// field-tuple tail — so the choice is locally decidable exactly as the `def`
/// family's factored tails are. The declined tail annotates a result only after
/// its field tuple, so no fieldless member reads its `:` a second way.
///
/// A cell is named by a lowercase identifier, which no other member opens on:
/// `loop : Base <-> Base` relates two terms by one glyph of the arrow grid.
/// The grammar admits the whole grid between terms so the elaborator refuses
/// each glyph the fragment does not lower by its own name, as the circuit
/// grid's rows are refused, rather than the parser by repair.
///
/// # Specification
/// - requires: nothing.
/// - ensures: constructor, operation, rewrite-member and cell branches; the
///   constructor owns one shared leading tile.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts,
///   and a second `:` successor of the constructor name is refused. The
///   predicate observes the stated shape; source programs outside the finite
///   corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::walk::a_data_member_colon_after_a_constructor_name_reads_one_way`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 4 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "constructor")) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Alt(_))))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 4)) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 4 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "rule")) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)) && sequence.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)))) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 5 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && sequence.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)) && sequence.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression))))))]
fn data_member() -> Regex
{
    alt([
        seq([
            t(TileLabel("constructor")),
            alt([
                // generator judgment `Ctor : Side (--> Result)? [attrs]?` —
                // THE one constructor-declaration form.
                seq([t(TileLabel(":")), generator_signature(), opt(attr_slot())]),
                // declined `Ctor(fields) (: Result)? [attrs]?` and bare `Ctor`,
                // kept admissible so the elaborator's decline names the
                // respelling. The result annotation follows the field tuple
                // only: `Ctor : Result` is the generator without a telescope,
                // and a fieldless declined tail led by `:` would read the same
                // tiles a second way.
                seq([
                    opt(seq([
                        t(TileLabel("(")),
                        comma1(ctor_field()),
                        t(TileLabel(")")),
                        opt(seq([t(TileLabel(":")), h(Sort::Type)])),
                    ])),
                    opt(attr_slot()),
                ]),
            ]),
        ]),
        // reserved `oper name(params) -> R?` operation member. The `op` lead
        // still parses so the elaborator can decline it with the respelling
        // (as it does the `~>` face arrow); `op` otherwise leads only the
        // operator-fixity declaration.
        data_oper_member(alt([t(TileLabel("oper")), t(TileLabel("op"))])),
        // `rule lhs <=> rhs`, or `rule lhs ==> rhs` pinning the direction.
        seq([
            t(TileLabel("rule")),
            h(Sort::Expression),
            rule_face_arrow(),
            h(Sort::Expression),
        ]),
        // a cell `name : a <-> b` between two terms of the block's sort, its
        // glyph any of the arrow grid's.
        seq([
            t(TileLabel("identifier")),
            t(TileLabel(":")),
            h(Sort::Expression),
            alt([
                t(TileLabel("-->")),
                t(TileLabel("<->")),
                t(TileLabel("==>")),
                t(TileLabel("<=>")),
            ]),
            h(Sort::Expression),
        ]),
    ])
}

/// Build the data-style operation member after its context-specific lead menu.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the supplied lead, a name, parameters and an optional
///   arrow/result tail.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 4 && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_)))))]
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
/// - requires: nothing.
/// - ensures: a type-or-telescope side followed by an optional result-arrow
///   tail.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Alt(_))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_)))))]
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
/// - requires: nothing.
/// - ensures: a non-optional port/binder list inside parentheses.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "(")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ")"))))]
fn generator_telescope() -> Regex
{
    seq([
        t(TileLabel("(")),
        comma1(alt([ctor_field(), h(Sort::Type)])),
        t(TileLabel(")")),
    ])
}

/// Build the rewrite-face arrow of a `rule` member: `==>` pinning the
/// direction, `<=>` leaving it to the order, or the declined `~>` kept
/// admissible so it can be declined by name.
///
/// `<=>` is the equation. The order over the block's faces chooses its
/// direction; `==>` states the direction the order must admit. Removing `~>`
/// from the grammar outright would turn a stale face into a parse repair,
/// which names a token rather than the respelling; admitting it here keeps
/// the member's shape whole so the elaborator declines it by name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the pinned arrow, the equation, and the admitted obsolete
///   spelling, in that order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 3 && parts.iter().zip(["==>","<=>","~>"]).all(|(part, label)| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label))))]
pub(super) fn rule_face_arrow() -> Regex
{
    alt([t(TileLabel("==>")), t(TileLabel("<=>")), t(TileLabel("~>"))])
}

/// Build the reserved grade prefix, narrowed to `{ number, ω }`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: only numeric and omega grade-prefix alternatives, excluding
///   identifier grades.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 2 && parts.iter().zip(["number","ω"]).all(|(part, label)| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label))))]
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
/// - requires: nothing.
/// - ensures: a non-optional attribute list inside square brackets.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "[")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "]"))))]
fn attr_slot() -> Regex
{
    seq([t(TileLabel("[")), comma1(attr_inline()), t(TileLabel("]"))])
}

/// Build the reserved `op` result: a single type or a named multi-out tuple,
/// kept LOCAL to the op member so `( ident : Type, … )` never collides with
/// `parenthesized_type`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: either a type hole or a parenthesized named-result group.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Type)) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 3 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "(")) && sequence.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ")"))))))]
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
/// - requires: nothing.
/// - ensures: observation, operation and rewrite-member branches, with the
///   observation ending in a type hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 5 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && sequence.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ":")) && sequence.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Type)))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 4 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "oper")))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 4 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "rule"))))))]
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
/// - requires: nothing.
/// - ensures: an optional restricted grade, a name, colon and type hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 4 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ":")) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Type))))]
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
/// - requires: nothing.
/// - ensures: the five declared fixity spellings in their grammar order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 5 && parts.iter().zip(["infixl","infixr","infix","prefix","postfix"]).all(|(part, label)| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label))))]
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

/// Append attribute, parameter, and extern helper forms.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the attribute and extern blocks, in order, at the item
///   sort and supplied band.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 2 && added.iter().zip(["attribute_block", "extern_block"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::Item && rule.prec() == p && rule.provenance().0 == name)))]
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

/// Append pattern forms.
///
/// The word cons `g ∷ p` matches a word of a path type a `data` block's cells
/// present, its first letter `g` — a cell's name, or `back(g)` its inverse —
/// and the rest `p`. The letter is read by its shape, never as a pattern of
/// its own: `back(g)` is spelled as a call and stands nowhere else in a
/// pattern, so the form opens on the name and discriminates on the tile after
/// it, `∷` or `(`, where the bare pattern variable takes neither.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the ordered pattern forms, assigning the cons, or and as
///   forms their own bands and every other form the atom band.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 12 && added.iter().zip(["wildcard", "constructor_pattern", "tuple_pattern", "telescope_pattern", "labelled_sum_pattern", "list_pattern", "rest_pattern", "literal_pattern", "hole.pattern", "cons_pattern", "or_pattern", "as_pattern"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::Pattern && rule.prec() == match name { "or_pattern" => precs.or, "as_pattern" => precs.as_p, "cons_pattern" => precs.cons, _ => precs.atom } && rule.provenance().0 == if name == "hole.pattern" { "hole" } else { name })))]
fn patterns(
    out: &mut Vec<Rule>,
    precs: PatternPrecs,
)
{
    let PatternPrecs {
        or,
        as_p,
        cons,
        atom,
    } = precs;
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
            opt(t(TileLabel(","))),
            t(TileLabel(")")),
        ]),
    ));
    // The telescope pattern `#{ x, y }`, `#{ .n, .v }` punning its labels and
    // `#{ .n = m }` renaming one. An entry's shape is inlined, since a
    // standalone `record_pattern_field` rule would give its `identifier`
    // opener a form-first Pattern-sort mold that ties with every bare pattern
    // variable. A bare `n = m` molds too, its key a pattern hole, so the
    // lowering refuses the undotted label by name rather than the parser by
    // repair; the record pattern this renames and the folded field are
    // adaptations.
    let mut telescope_pattern = r(
        RuleName("telescope_pattern"),
        Provenance("telescope_pattern"),
        s,
        atom,
        seq([
            t(TileLabel("#{")),
            opt(comma1(telescope_pattern_entry())),
            t(TileLabel("}")),
        ]),
    );
    telescope_pattern.adaptations.push(Adaptation::new(
        RuleName("telescope_pattern"),
        SurfaceForm("record_pattern"),
        AdaptationReason("renamed into telescope_pattern: the record pattern is the telescope pattern `#{ … }` with labelled entries, the same former as the tuple pattern"),
    ));
    telescope_pattern.adaptations.push(Adaptation::new(
        RuleName("telescope_pattern"),
        SurfaceForm("record_pattern_field"),
        AdaptationReason("folded into telescope_pattern: the `.id = PAT` entry is inlined, not a standalone form-first identifier competing with a bare pattern variable"),
    ));
    out.push(telescope_pattern);
    // The injection pattern `+{ .ok = PAT }`, positional as `+{ .1 = PAT }`.
    out.push(r(
        RuleName("labelled_sum_pattern"),
        Provenance("labelled_sum_pattern"),
        s,
        atom,
        seq([
            t(TileLabel("+")),
            t(TileLabel("{")),
            dotted_label(),
            t(TileLabel("=")),
            h(s),
            t(TileLabel("}")),
        ]),
    ));
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
        RuleName("cons_pattern"),
        Provenance("cons_pattern"),
        s,
        cons,
        seq([
            t(TileLabel("identifier")),
            opt(seq([
                t(TileLabel("(")),
                t(TileLabel("identifier")),
                t(TileLabel(")")),
            ])),
            t(TileLabel("∷")),
            h(s),
        ]),
    ));
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
/// their binary-expression molds. An explicit resident's value is a whole
/// expression up to the slot's next `,` or its `]`, `f[g = M.h]` and `f[n =
/// a + 1]` alike: the resident stands at the loosest band, `explicit`, so no
/// operator or projection after its `=` takes the resident as its operand.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends six ordered instantiation residents, all at the dedicated
///   sort with shared instantiation provenance, the explicit resident at
///   `explicit` and the rest at `p`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 6 && added.iter().zip(["instantiation.type", "instantiation.direction.descent", "instantiation.direction.productivity", "instantiation.named_measure", "instantiation.explicit", "instantiation.tail"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::Instantiation && rule.prec() == if name == "instantiation.explicit" { explicit } else { p } && rule.provenance().0 == "instantiation_expression")))]
fn instantiations(
    out: &mut Vec<Rule>,
    p: Prec,
    explicit: Prec,
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
        explicit,
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
/// - requires: nothing.
/// - ensures: appends the ordered operator and primary expression families at
///   their selected precedence bands.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 62 && added.iter().zip(["pure_expression", "return_expression", "become_expression", "bind_expression", "binary_expression.or", "binary_expression.and", "binary_expression.cmp.eq", "binary_expression.cmp.ne", "binary_expression.cmp.lt", "binary_expression.cmp.le", "binary_expression.cmp.gt", "binary_expression.cmp.ge", "binary_expression.then", "binary_expression.cons", "binary_expression.add.concat", "binary_expression.add.plus", "binary_expression.add.minus", "binary_expression.mul.times", "unary_expression", "force_expression", "run_expression", "hold_expression", "pack_expression", "pack_model_expression", "call_expression", "instantiation_expression", "projection_expression", "view_expression", "index_expression", "hole", "wildcard.expression", "parenthesized_expression", "type_quote_expression", "list_expression", "block", "lambda_expression", "thunk_expression", "case_expression", "handle_expression", "if_expression", "for_expression", "while_expression", "loop_expression", "break_expression", "break_value_expression", "continue_expression", "co_expression", "glob_expression", "telescope_expression", "labelled_sum_expression", "lazy_record_expression", "offer_expression", "migrate_expression", "send_expression", "close_expression", "select_expression", "dup_expression", "drop_expression", "access_expression", "resume_expression", "abort_expression", "shell_block"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::Expression && rule.prec() == match name { "pure_expression" | "return_expression" | "become_expression" | "bind_expression" | "pack_expression" | "pack_model_expression" => p.pure, "binary_expression.or" => p.or, "binary_expression.and" => p.and, "binary_expression.cmp.eq" | "binary_expression.cmp.ne" | "binary_expression.cmp.lt" | "binary_expression.cmp.le" | "binary_expression.cmp.gt" | "binary_expression.cmp.ge" | "binary_expression.then" => p.cmp, "binary_expression.cons" => p.cons, "binary_expression.add.concat" | "binary_expression.add.plus" | "binary_expression.add.minus" => p.add, "binary_expression.mul.times" => p.mul, "unary_expression" | "force_expression" | "run_expression" | "hold_expression" => p.unary, "call_expression" | "instantiation_expression" | "projection_expression" | "view_expression" | "index_expression" => p.postfix, _ => p.atom } && rule.provenance().0 == name.split_once('.').map_or(name, |(stem, _)| stem))))]
fn expressions(
    out: &mut Vec<Rule>,
    p: ExprPrecs,
)
{
    let s = Sort::Expression;
    out.push(r(
        RuleName("pure_expression"),
        Provenance("pure_expression"),
        s,
        p.pure,
        seq([t(TileLabel("pure")), h(s)]),
    ));
    // The function exits: `return v` leaves the enclosing function with a
    // value, `become c` by running a computation in tail position. Keyword-led
    // like `pure`, at its precedence, so the first token decides the form.
    // PBG-only, parity-exempt.
    out.push(r(
        RuleName("return_expression"),
        Provenance("return_expression"),
        s,
        p.pure,
        seq([t(TileLabel("return")), h(s)]),
    ));
    out.push(r(
        RuleName("become_expression"),
        Provenance("become_expression"),
        s,
        p.pure,
        seq([t(TileLabel("become")), h(s)]),
    ));
    // `bind a . t` abstracts the atom `a` over the term `t`: a theory rule's
    // argument at a port written `bind (a : N) . T`. Keyword-led at `pure`'s
    // precedence, so the abstraction's body runs as far right as it can.
    out.push(r(
        RuleName("bind_expression"),
        Provenance("bind_expression"),
        s,
        p.pure,
        seq([
            t(TileLabel("bind")),
            t(TileLabel("identifier")),
            t(TileLabel(".")),
            h(s),
        ]),
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
        RuleName("binary_expression.cons"),
        TileLabel("∷"),
        s,
        p.cons,
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
    // `run c` — the explicit spelling of the fourth bridge: the computation
    // runs before the computation around it and stands for the value it
    // returns. `run` also opens a bind statement: at a statement's start
    // inside a body the statement is the reading, so an inline run standing
    // first in a statement is parenthesised; at the top level the token after
    // the pattern, `<-` or not, tells the two apart.
    out.push(r(
        RuleName("run_expression"),
        Provenance("run_expression"),
        s,
        p.unary,
        seq([t(TileLabel("run")), h(s)]),
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
        // `pure`'s precedence, not `force`'s: a pack takes a whole expression,
        // and the payload a module is packed from is normally a `thunk { … }`
        // — itself a unary form, which a non-associative unary `pack` could
        // not take as an operand without parentheses.
        p.pure,
        seq([
            t(TileLabel("pack")),
            t(TileLabel("[")),
            comma1(h(Sort::Type)),
            t(TileLabel("]")),
            h(s),
        ]),
    ));
    // `pack M at Model(T)` — a module packed at the model type its signature
    // states: the bundled record of its members, read off the module. Every
    // sort the module gives is manifest, so nothing is hidden and no witness
    // is written; a module that keeps a sort abstract is the package former's,
    // `pack [ τ ] M`. At `pure`'s precedence for the reason the package
    // introduction is. PBG-only, parity-exempt.
    out.push(r(
        RuleName("pack_model_expression"),
        Provenance("pack_model_expression"),
        s,
        p.pure,
        seq([
            t(TileLabel("pack")),
            h(s),
            t(TileLabel("at")),
            h(Sort::Type),
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
    // A selection names its entry by label, `p.n`, or by position, `p.0`: the
    // printer writes a projection off a pair whose labels the core does not
    // keep by its position, and that spelling reads back.
    out.push(r(
        RuleName("projection_expression"),
        Provenance("projection_expression"),
        s,
        p.postfix,
        seq([
            h(s),
            t(TileLabel(".")),
            Regex::alt([
                t(TileLabel("identifier")),
                t(TileLabel("constructor")),
                t(TileLabel("number")),
            ]),
        ]),
    ));
    // A view-answering method's call lends its view over a block, `s.first()
    // as w { … }`: postfix, so the block takes the whole call. The lowering
    // refuses an operand that is not such a call. The tree-sitter grammar has
    // no temporary access, so the kind is in `PBG_ONLY_KINDS`.
    out.push(r(
        RuleName("view_expression"),
        Provenance("view_expression"),
        s,
        p.postfix,
        seq([
            h(s),
            t(TileLabel("as")),
            t(TileLabel("identifier")),
            block(),
        ]),
    ));
    // A place of a value, `s[e]`, its index a whole expression: the body a
    // view-answering method ends in, `{ self[i] }`. It follows the
    // instantiation, so a bracket an instantiation resident reads as well,
    // `f[<]`, `f[tail]` or `f[T]`, keeps the instantiation's mold. The
    // tree-sitter grammar has no places, so the kind is in `PBG_ONLY_KINDS`.
    out.push(r(
        RuleName("index_expression"),
        Provenance("index_expression"),
        s,
        p.postfix,
        seq([h(s), t(TileLabel("[")), h(s), t(TileLabel("]"))]),
    ));
    primary_expressions(out, p.atom);
}

/// Append shared lexical named-token forms used by term and pattern rules.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends two pattern lexical forms followed by eight expression
///   lexical forms, preserving the shared source kinds and distinct bands. A
///   constructor, boolean, number or string pattern is read by
///   `constructor_pattern` and `literal_pattern`, so the pattern sort has no
///   lexical rule of its own for them.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 10 && added.iter().zip([("identifier.pattern", "identifier", Sort::Pattern, pat), ("unit.pattern", "unit", Sort::Pattern, pat), ("identifier.expression", "identifier", Sort::Expression, expr), ("constructor.expression", "constructor", Sort::Expression, expr), ("boolean.expression", "boolean", Sort::Expression, expr), ("unit.expression", "unit", Sort::Expression, expr), ("number.expression", "number", Sort::Expression, expr), ("typed_number.expression", "typed_number", Sort::Expression, expr), ("character", "character", Sort::Expression, expr), ("string.expression", "string", Sort::Expression, expr)]).all(|(rule, (name, provenance, sort, prec))| rule.name().0 == name && rule.provenance().0 == provenance && rule.sort() == sort && rule.prec() == prec)))]
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
        RuleName("unit.pattern"),
        Provenance("unit"),
        p,
        pat,
        t(TileLabel("unit")),
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
        RuleName("unit.expression"),
        Provenance("unit"),
        e,
        expr,
        t(TileLabel("unit")),
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
    string_expr.adaptations.push(Adaptation::new(
        RuleName("string.expression"),
        SurfaceForm("escape_sequence"),
        AdaptationReason("an escape is a tile of the string forms, lexed only between a string's quotes, so it has no form of its own: the `escape_sequence` named kind is realised by the tile inside `string.expression`, the pattern-position string of `literal_pattern` and the shell `double_quoted_string`"),
    ));
    out.push(string_expr);
}

/// Expression precedence bundle.
#[derive(Clone, Copy)]
struct ExprPrecs
{
    /// The precedence of `pure` and of the exits `return` and `become`.
    pure: Prec,
    /// Logical-or precedence.
    or: Prec,
    /// Logical-and precedence.
    and: Prec,
    /// Comparison precedence.
    cmp: Prec,
    /// The word cons `∷`, right-associative, between comparison and addition.
    cons: Prec,
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

/// Pattern precedence bundle.
#[derive(Clone, Copy)]
struct PatternPrecs
{
    /// The alternation `p | q`.
    or: Prec,
    /// The binding `p as x`.
    as_p: Prec,
    /// The word cons `g ∷ p`, right-associative, between `as` and the atoms.
    cons: Prec,
    /// Every atomic pattern.
    atom: Prec,
}

/// Append one binary expression rule.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends one binary-expression rule with the supplied header and a
///   single operator separating recursive holes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 1 && added.first().is_some_and(|rule| rule.name() == name && rule.provenance().0 == "binary_expression" && rule.sort() == s && rule.prec() == p && matches!(rule.regex().view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == s)) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == op.0)) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == s))))))]
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
/// - requires: nothing.
/// - ensures: a non-optional attribute list between the attribute opener and
///   its closer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "@[")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "]"))))]
fn attr_block_inline() -> Regex
{
    seq([t(TileLabel("@[")), comma1(attr_inline()), t(TileLabel("]"))])
}

/// Build an inline attribute.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a name followed by an optional parenthesized expression payload.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_)))))]
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
/// The annotation may open on a receiver's mode, `self : shared Str` or `self :
/// consumed Str`: the words of the access form's mode, the written-through
/// mode unwritten as there. The lowering reads the word on a method's `self`
/// and refuses it anywhere else.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a binder-name menu followed by an optional type annotation,
///   itself opening on an optional `shared` or `consumed`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Alt(_))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_)))))]
fn param() -> Regex
{
    seq([
        alt([
            t(TileLabel("identifier")),
            t(TileLabel("type_variable")),
            t(TileLabel("type_identifier")),
        ]),
        opt(seq([
            t(TileLabel(":")),
            opt(alt([t(TileLabel("shared")), t(TileLabel("consumed"))])),
            h(Sort::Type),
        ])),
    ])
}

/// Build an inline receive/acquire/release statement.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the supplied keyword and parenthesized expression, then an
///   as-binding terminated by a semicolon.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 7 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == keyword.0)) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "(")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ")")) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "as")) && parts.get(5).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(6).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))]
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
/// - requires: nothing.
/// - ensures: the eleven statement alternatives, each carrying its own
///   terminating semicolon.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 11 && parts.iter().all(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.last().is_some_and(|last| matches!(last.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))))]
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
        hold_statement(),
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

/// Build the statement that holds a value: `hold x = E ;`, or `hold[1] x = E
/// ;` at a grade.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the `hold` keyword, an optional bracketed numeral grade, the held
///   name, then an equals-delimited expression and a semicolon.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 6 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "hold")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "=")) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)) && parts.get(5).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))]
fn hold_statement() -> Regex
{
    seq([
        t(TileLabel("hold")),
        opt(seq([
            t(TileLabel("[")),
            t(TileLabel("number")),
            t(TileLabel("]")),
        ])),
        t(TileLabel("identifier")),
        t(TileLabel("=")),
        h(Sort::Expression),
        t(TileLabel(";")),
    ])
}

/// Build a variable-binding statement: `val PAT = E ;`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a val keyword and pattern hole, then an equals-delimited
///   expression and semicolon.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 5 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "val")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Pattern)) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "=")) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))]
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
/// - requires: nothing.
/// - ensures: an unpack binding with a mandatory signature before its source
///   expression.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 7 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "unpack")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ":")) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Type)) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "=")) && parts.get(5).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)) && parts.get(6).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))]
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
/// computation type (`-F A`, and the other negative formers) rather than the
/// type of the name the pattern binds. The binder keyword already says which
/// category is bound; the annotation says which computation type the source is
/// checked against, and the lowerer spends it through the existing computation
/// ascription.
///
/// No pattern form carries a top-level `:`, so the tile after the pattern
/// discriminates the annotated and bare spellings with no lookahead.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a run keyword and pattern, optional bound-type annotation and
///   left-arrow source expression, terminated by a semicolon.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 6 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "run")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Pattern)) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "<-")) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)) && parts.get(5).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))]
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
/// - requires: nothing.
/// - ensures: one explicit element followed by a repetition of the same
///   element.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted. Arbitrary nullable elements are not
///   exhausted.
/// - witness: `surface::term::tests::list_separators_are_not_optional_between_members`
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 2 && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(inner) if parts.first() == Some(&inner)))))]
fn repeat1(element: Regex) -> Regex
{
    seq([element.clone(), repeat(element)])
}

/// Build an inline block with semicolon-bearing statement alternatives.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a brace-delimited block with repeated terminated statements and
///   an optional final expression.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 4 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "{")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "}"))))]
fn block() -> Regex
{
    seq([
        t(TileLabel("{")),
        repeat(statement_alt()),
        opt(h(Sort::Expression)),
        t(TileLabel("}")),
    ])
}

/// Build a leading-dot label: `.` then a name, or `.` then an index for a
/// positional entry.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a `.` tile followed by an identifier or a number tile.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ".")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Alt(ref labels) if labels.len() == 2 && labels.iter().zip(["identifier", "number"]).all(|(label, expected)| matches!(label.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == expected))))))]
fn dotted_label() -> Regex
{
    seq([
        t(TileLabel(".")),
        alt([t(TileLabel("identifier")), t(TileLabel("number"))]),
    ])
}

/// Build one hole-led entry of a telescope value: a positional `E`, or the
/// shorthand `E = E` whose key the lowering reads as a bare label.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an expression hole optionally followed by `=` and a second
///   expression hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.first().is_some_and(|hole| matches!(hole.shape(), RegexShape::Sym(Sym::Sort(Sort::Expression)))) && sequence.get(1).is_some_and(|key| matches!(key.shape(), RegexShape::Optional(_)))))]
fn positional_entry() -> Regex
{
    let s = Sort::Expression;
    seq([h(s), opt(seq([t(TileLabel("=")), h(s)]))])
}

/// Build one entry of a telescope pattern: a labelled `.l`, punning its
/// label, or `.l = PAT`; a positional `PAT`; or `PAT = PAT`, whose undotted
/// key the lowering refuses by name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the labelled entry with an optional `= PAT`, then a pattern hole
///   optionally followed by `=` and a second pattern hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.get(1).is_some_and(|rename| matches!(rename.shape(), RegexShape::Optional(_))))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.first().is_some_and(|hole| matches!(hole.shape(), RegexShape::Sym(Sym::Sort(Sort::Pattern))))))))]
fn telescope_pattern_entry() -> Regex
{
    let s = Sort::Pattern;
    alt([
        seq([dotted_label(), opt(seq([t(TileLabel("=")), h(s)]))]),
        seq([h(s), opt(seq([t(TileLabel("=")), h(s)]))]),
    ])
}

/// Build list pattern elements.
///
/// The element list cannot reuse [`comma1`]: its optional trailing comma
/// followed by the `, ..rest` tail would admit `[a,, ..rest]`. The comma after
/// the last element instead opens an optional rest, so `[a, b,]` and
/// `[a, ..rest]` both read with one comma before what follows.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an element-list branch whose optional tail is a comma and an
///   optional rest, and a separate rest-only branch.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "..")) && sequence.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Pattern))))))]
fn list_pat_elems() -> Regex
{
    alt([
        seq([
            seq([
                h(Sort::Pattern),
                repeat(seq([t(TileLabel(",")), h(Sort::Pattern)])),
            ]),
            opt(seq([t(TileLabel(",")), opt(rest_pat())])),
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
/// - requires: nothing.
/// - ensures: quotes surrounding only a repetition of escapes and plain string
///   fragments.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "\"")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(inner) if matches!(inner.shape(), RegexShape::Alt(ref fragments) if fragments.len() == 2 && fragments.iter().zip(["escape_sequence", "string_fragment"]).all(|(fragment,label)| matches!(fragment.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label))))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "\""))))]
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
/// - requires: nothing.
/// - ensures: a type keyword, type name and semicolon.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "type")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "type_identifier")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))]
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
/// - requires: nothing.
/// - ensures: a rest marker followed by a pattern hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "..")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Pattern))))]
fn rest_pat() -> Regex
{
    seq([t(TileLabel("..")), h(Sort::Pattern)])
}

/// Build expression arguments.
///
/// # Specification
/// - requires: nothing.
/// - ensures: parentheses around an optional expression-argument list.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "(")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ")"))))]
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
/// - requires: nothing.
/// - ensures: the ordered numeric, identifier and omega grade alternatives.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 3 && parts.iter().zip(["number","identifier","ω"]).all(|(part, label)| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label))))]
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
/// - requires: nothing.
/// - ensures: an if condition, optional answer-type slot and two blocks
///   separated by else.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 6 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "if")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression)) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "else")) && parts.get(5).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_)))))]
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
/// - requires: nothing.
/// - ensures: a result arrow followed by a type hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 2 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "->")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Type))))]
fn answer_type() -> Regex
{
    seq([t(TileLabel("->")), h(Sort::Type)])
}

/// Build a `co` field.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a named observation assigned an expression hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "=")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression))))]
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
/// - requires: nothing.
/// - ensures: a named record field assigned an expression hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "=")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression))))]
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
/// - requires: nothing.
/// - ensures: a pattern and expression separated by the arm arrow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Pattern)) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "=>")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Expression))))]
fn arm() -> Regex
{
    seq([h(Sort::Pattern), t(TileLabel("=>")), h(Sort::Expression)])
}

/// Build one clause of a capability scope: the return clause `pure(x) => e`,
/// or an operation clause `oper op(p, k) => e` binding the payload and the
/// resumption, or `oper op(p, b, k) => e` binding as well the buffer the
/// scope mints for an operation that replies one.
///
/// Both clauses open on a keyword: `pure`, the returner's, and `oper`, the
/// one a signature declares an operation with. A clause opening on the
/// operation's name gave every damaged call `f(a, b)` a stray clause to read,
/// and its recovery worsened.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two alternatives, `pure ( identifier ) => E` and `oper identifier
///   ( identifier , identifier [, identifier] ) => E`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref branches) if branches.len() == 2 && branches.iter().all(|branch| matches!(branch.shape(), RegexShape::Seq(ref parts) if parts.last().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(Sort::Expression))))))))]
fn handler_clause() -> Regex
{
    alt([
        seq([
            t(TileLabel("pure")),
            t(TileLabel("(")),
            t(TileLabel("identifier")),
            t(TileLabel(")")),
            t(TileLabel("=>")),
            h(Sort::Expression),
        ]),
        seq([
            t(TileLabel("oper")),
            t(TileLabel("identifier")),
            t(TileLabel("(")),
            t(TileLabel("identifier")),
            t(TileLabel(",")),
            t(TileLabel("identifier")),
            opt(seq([t(TileLabel(",")), t(TileLabel("identifier"))])),
            t(TileLabel(")")),
            t(TileLabel("=>")),
            h(Sort::Expression),
        ]),
    ])
}

/// Build a braced, comma-separated, nonempty arm list whose every arm may open
/// with `|`.
///
/// A leading `|` lets an or-pattern spread over lines open with its
/// separator. A mold is one tile occurrence, and an occurrence a hole can
/// follow admits an operand before any successor: an optional `|` after a
/// single `{` would admit `{ A | B => …` as `A` before the arm's bar, a
/// reading that ties with the or-pattern's. So the bar is never optional
/// after a shared tile: the opener and every separator come in two
/// occurrences, one a hole follows and one the bar follows, and the token
/// after the tile tells them apart.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two alternatives, `{` then an arm and `{ |` then an arm, each
///   followed by repetitions of `,` or `, |` before an arm, an optional
///   trailing `,`, and `}`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   An or-pattern arm must lower with each alternative intact, which a bar
///   reachable after a hole breaks.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref branches) if branches.len() == 2 && branches.iter().all(|branch| matches!(branch.shape(), RegexShape::Seq(ref parts) if parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "{")) && parts.last().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "}"))))))]
fn arm_block() -> Regex
{
    let bar = || t(TileLabel("|"));
    let tail = || {
        seq([
            repeat(alt([
                seq([t(TileLabel(",")), arm()]),
                seq([t(TileLabel(",")), bar(), arm()]),
            ])),
            opt(t(TileLabel(","))),
        ])
    };
    alt([
        seq([t(TileLabel("{")), arm(), tail(), t(TileLabel("}"))]),
        seq([t(TileLabel("{")), bar(), arm(), tail(), t(TileLabel("}"))]),
    ])
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
/// - requires: nothing.
/// - ensures: a def/name prefix, parameters, optional result annotation and
///   mandatory semicolon.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 5 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "def")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))]
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
/// - requires: nothing.
/// - ensures: parentheses around an optional parameter list.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "(")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ")"))))]
fn params() -> Regex
{
    seq([t(TileLabel("(")), opt(comma1(param())), t(TileLabel(")"))])
}

/// Append session-operation expression forms.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the seven ordered session-expression forms at the
///   supplied band.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 7 && added.iter().zip(["offer_expression", "migrate_expression", "send_expression", "close_expression", "select_expression", "dup_expression", "drop_expression"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::Expression && rule.prec() == p && rule.provenance().0 == name)))]
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
            arm_block(),
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

/// Append the temporary-access expression forms: the access that lends a
/// held value, or a place of it, to a view, and the two eliminators that end
/// the view.
///
/// `access x as v { t } unwind { u }` names the held slot `x` and binds the
/// view `v` over the body `t`; the optional `unwind` block runs when an
/// `abort` ends the view and defaults to nothing. A mode word after `access`,
/// `shared` or `exclusive`, names the mode; the grammar admits an `unwind`
/// after either, and lowering refuses one after `shared`. An index after the
/// held name, `x[e]`, lends the place of `x` at `e`. `resume(v, e)` ends
/// the view writing `e` back and `abort(v)` ends it with nothing written. Each
/// opens on its own reserved lead and names its view by an identifier tile,
/// so no expression hole competes with the name. The tree-sitter grammar has
/// no temporary access, so the kinds are in `PBG_ONLY_KINDS`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the three ordered access forms at the supplied band.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 3 && added.iter().zip(["access_expression", "resume_expression", "abort_expression"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::Expression && rule.prec() == p && rule.provenance().0 == name)))]
fn access_expressions(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::Expression;
    out.push(r(
        RuleName("access_expression"),
        Provenance("access_expression"),
        s,
        p,
        seq([
            t(TileLabel("access")),
            opt(alt([t(TileLabel("shared")), t(TileLabel("exclusive"))])),
            t(TileLabel("identifier")),
            opt(seq([t(TileLabel("[")), h(s), t(TileLabel("]"))])),
            t(TileLabel("as")),
            t(TileLabel("identifier")),
            block(),
            opt(seq([t(TileLabel("unwind")), block()])),
        ]),
    ));
    out.push(r(
        RuleName("resume_expression"),
        Provenance("resume_expression"),
        s,
        p,
        seq([
            t(TileLabel("resume")),
            t(TileLabel("(")),
            t(TileLabel("identifier")),
            t(TileLabel(",")),
            h(s),
            t(TileLabel(")")),
        ]),
    ));
    out.push(r(
        RuleName("abort_expression"),
        Provenance("abort_expression"),
        s,
        p,
        seq([
            t(TileLabel("abort")),
            t(TileLabel("(")),
            t(TileLabel("identifier")),
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

/// Build a comma-separated nonempty regex list, closed by its caller.
///
/// A trailing comma is admitted: every caller puts a closer after the list,
/// and a closer never competes with an element's hole content, so the comma
/// before it keeps the discrimination [`member_list`] describes.
///
/// # Specification
/// - requires: the caller follows the list with a closing tile.
/// - ensures: one explicit element, a repetition of comma followed by the same
///   element, and an optional trailing comma.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted. Arbitrary nullable elements are not
///   exhausted.
/// - witness: `surface::term::tests::list_separators_are_not_optional_between_members`
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(tail) if matches!(tail.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ",")) && sequence.get(1) == parts.first()))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(inner) if matches!(inner.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ",")))))]
fn comma1(element: Regex) -> Regex
{
    seq([
        element.clone(),
        repeat(seq([t(TileLabel(",")), element])),
        opt(t(TileLabel(","))),
    ])
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
/// the wrong tree. The `theory` block's leads are reserved words, never
/// hole-content candidates, but its members collapse the same way, so it takes
/// the same mandatory `;` terminator (see the circuit forms).
/// A mandatory separator restores the discrimination: after the hole only
/// `;`, `,`, or `}` is admissible, none of which competes with hole content.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one explicit member, repeated separator/member pairs and an
///   optional trailing separator.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted. Arbitrary nullable elements are not
///   exhausted.
/// - witness: `surface::term::tests::list_separators_are_not_optional_between_members`
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(tail) if matches!(tail.shape(), RegexShape::Seq(ref sequence) if sequence.len() == 2 && sequence.get(1) == parts.first() && sequence.first().is_some_and(|separator| matches!(separator.shape(), RegexShape::Alt(ref alternatives) if alternatives.len() == 2 && alternatives.iter().zip([";", ","]).all(|(alternative,label)| matches!(alternative.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label))))))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(inner) if matches!(inner.shape(), RegexShape::Alt(ref alternatives) if alternatives.len() == 2 && alternatives.iter().zip([";", ","]).all(|(alternative,label)| matches!(alternative.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label)))))))]
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
/// - requires: nothing.
/// - ensures: the semicolon and admitted comma separators in that order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted. Arbitrary nullable elements are not
///   exhausted.
/// - witness: `surface::term::tests::list_separators_are_not_optional_between_members`
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref parts) if parts.len() == 2 && parts.iter().zip([";",","]).all(|(part, label)| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == label))))]
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
/// a type member at its `;`, and a nested module ends at its closing brace.
/// After a member the only admissible tiles are the next member's lead (`@[`,
/// `def`, `type`, `module`) or the body's `}`, none of which competes with the
/// hole's own content — the discrimination the member-list separator rule
/// exists to protect.
///
/// A type member `type T = τ ;` names a type inside the body: the
/// representation a signature's abstract component `type T` seals. It leads
/// with `type`, as a signature's type component does, and closes on `;`, so
/// its type runs to the terminator however far it reaches.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends plain definitions, attributed definitions and type
///   members, a plain type member and a nested module, all at the module-member
///   sort with module provenance.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 4 && added.iter().zip(["module_definition_member", "attributed_module_member", "module_type_member", "nested_module_member"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::ModuleMember && rule.prec() == p && rule.provenance().0 == "module_declaration")))]
fn module_members(
    out: &mut Vec<Rule>,
    p: Prec,
)
{
    let s = Sort::ModuleMember;
    // The plain and attributed members are **two rules, not one with an
    // optional prefix**. A form whose first symbol is a repetition has no
    // definite lead tile, and at a sort-hole position the melder then starts
    // the member at `def` or `type` and leaves the preceding `@[ … ]` block
    // outside it — an attribute silently detached from the member it
    // decorates. Splitting on the one token that distinguishes them gives each
    // form a definite lead and puts the block back inside the member; the
    // attributed form is one rule for both tails, so `@[` opens one reading.
    out.push(r(
        RuleName("module_definition_member"),
        Provenance("module_declaration"),
        s,
        p,
        seq([t(TileLabel("def")), regular_def_tail()]),
    ));
    out.push(r(
        RuleName("attributed_module_member"),
        Provenance("module_declaration"),
        s,
        p,
        attributed_module_member(),
    ));
    out.push(r(
        RuleName("module_type_member"),
        Provenance("module_declaration"),
        s,
        p,
        type_member_tail(),
    ));
    out.push(r(
        RuleName("nested_module_member"),
        Provenance("module_declaration"),
        s,
        p,
        nested_module_member(),
    ));
}

/// Build one **attributed** module member: at least one `@[ … ]` block, then
/// either the ordinary definition tail or a type member.
///
/// An attributed type member states the expectation of the check a
/// signature's component reads the member through; the lowering files the
/// block under the member's form.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one mandatory attribute block and any following attribute blocks
///   before either a def and its regular tail or a type member.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Seq(_))) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Alt(ref tails) if tails.len() == 2))))]
fn attributed_module_member() -> Regex
{
    seq([
        attr_block_inline(),
        repeat(attr_block_inline()),
        alt([
            seq([t(TileLabel("def")), regular_def_tail()]),
            type_member_tail(),
        ]),
    ])
}

/// Build a module type member, `type T = τ ;` or `type T(a : A, …) = τ ;`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `type`, a type name, an optional parameter list, `=`, a type hole
///   and `;`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 6 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "type")) && parts.get(5).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ";"))))]
fn type_member_tail() -> Regex
{
    seq([
        t(TileLabel("type")),
        t(TileLabel("type_identifier")),
        opt(head_params()),
        t(TileLabel("=")),
        h(Sort::Type),
        t(TileLabel(";")),
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
/// - requires: nothing.
/// - ensures: an attribute-style opener with an optional typed-binder list and
///   its closer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "@[")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "]"))))]
fn implicit_telescope() -> Regex
{
    seq([
        t(TileLabel("@[")),
        opt(comma1(implicit_param())),
        t(TileLabel("]")),
    ])
}

/// Build one declaration-level implicit binder: a typed name, or the bound
/// `i < n` a stage binder carries.
///
/// Lowercase binders use the ordinary name classes; uppercase binders such as
/// `A` are lexically offered as type identifiers by the labeler and remain
/// valid binder names at this parse-only stage. A bound names two binders of
/// the same telescope.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a binder-name menu followed by a mandatory colon and type hole,
///   or two names on either side of `<`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Alt(ref alternatives) if alternatives.len() == 2 && alternatives.first().is_some_and(|typed| matches!(typed.shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == ":")) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Sort(actual)) if actual == Sort::Type)))) && alternatives.get(1).is_some_and(|bound| matches!(bound.shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "<"))))))]
fn implicit_param() -> Regex
{
    alt([
        seq([
            alt([
                t(TileLabel("identifier")),
                t(TileLabel("type_variable")),
                t(TileLabel("type_identifier")),
            ]),
            t(TileLabel(":")),
            h(Sort::Type),
        ]),
        seq([
            t(TileLabel("identifier")),
            t(TileLabel("<")),
            t(TileLabel("identifier")),
        ]),
    ])
}

/// Build the non-recursive definition/signature tail after `def`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one shared name, optional implicit telescope and
///   signature/value/function tail alternatives.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 3 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "identifier")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Alt(ref alternatives) if alternatives.len() == 3))))]
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
/// a repair region the reader experiences as malformed input. The outer form
/// admits both spellings too, and the lowering declines a lowercase top-level
/// name by name; this slot carries no such ruling.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a module keyword, either name case, optional ascription and a
///   brace-delimited repetition of module-member holes.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in term forms, L3 grammar identity and corpus
///   role observations catch changed discriminators, delimiters and hole sorts.
///   The predicate observes the stated shape; source programs outside the
///   finite corpus are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(ensures: |ret| matches!(ret.view().shape(), RegexShape::Seq(ref parts) if parts.len() == 6 && parts.first().is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "module")) && parts.get(1).is_some_and(|part| matches!(part.shape(), RegexShape::Alt(_))) && parts.get(2).is_some_and(|part| matches!(part.shape(), RegexShape::Optional(_))) && parts.get(3).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "{")) && parts.get(4).is_some_and(|part| matches!(part.shape(), RegexShape::Repeat(inner) if matches!(inner.shape(), RegexShape::Sym(Sym::Sort(Sort::ModuleMember))))) && parts.get(5).is_some_and(|part| matches!(part.shape(), RegexShape::Sym(Sym::Tile(tile)) if tile.label == "}"))))]
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
/// - requires: nothing.
/// - ensures: appends the ordered atomic expression families, including the
///   hole and the wildcard, session forms, temporary access and the shell
///   block, at the supplied band; each rule's provenance is its name up to the
///   first `.`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the built-in band table, L3 grammar identity and corpus
///   role observations catch lost or reordered forms, changed provenance and
///   misplaced precedence bands. The predicate observes the appended metadata
///   without cloning the prior rules; arbitrary pre-existing prefixes and table
///   aliases are not exhausted.
/// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
#[spec(captures: before = out.len(), ensures: |()| out.get(before..).is_some_and(|added| added.len() == 33 && added.iter().zip(["hole", "wildcard.expression", "parenthesized_expression", "type_quote_expression", "list_expression", "block", "lambda_expression", "thunk_expression", "case_expression", "handle_expression", "if_expression", "for_expression", "while_expression", "loop_expression", "break_expression", "break_value_expression", "continue_expression", "co_expression", "glob_expression", "telescope_expression", "labelled_sum_expression", "lazy_record_expression", "offer_expression", "migrate_expression", "send_expression", "close_expression", "select_expression", "dup_expression", "drop_expression", "access_expression", "resume_expression", "abort_expression", "shell_block"]).all(|(rule, name)| rule.name().0 == name && rule.sort() == Sort::Expression && rule.prec() == p && rule.provenance().0 == name.split_once('.').map_or(name, |(stem, _)| stem))))]
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
    // The wildcard `_` where an expression is read: a term the elaborator
    // answers from the comparisons that force it. Its tile is the pattern
    // wildcard's, so the two read one node kind, as the two holes do.
    out.push(r(
        RuleName("wildcard.expression"),
        Provenance("wildcard"),
        s,
        p,
        t(TileLabel("_")),
    ));
    // The `(`-opened expression atoms — unit `( )`, parenthesized `( E )`, tuple
    // `( E , )` or `( E , E+ )`, and annotation `( E : T )` — share the `( E`
    // prefix and diverge only at the tile after the expression (`)` versus `,`
    // versus `:`), which for a long `E` sits arbitrarily far past the `(`, out
    // of reach of a bounded lookahead. They are factored into one form whose
    // tail alternates on that discriminating tile, so the `(` owns one mold and
    // the choice is locally decidable — the discriminator `≐`-continues exactly
    // one tail. The concrete language is unchanged; the folded kinds are
    // recorded as adaptations for the parity inventory.
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
                        // tuple: `( E , )` or `( E , E (, E)* ,? )`
                        seq([
                            t(TileLabel(",")),
                            opt(seq([
                                h(s),
                                opt(repeat1(seq([t(TileLabel(",")), h(s)]))),
                                opt(t(TileLabel(","))),
                            ])),
                            t(TileLabel(")")),
                        ]),
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
    // A type quoted where an expression stands, `type(T)`: the code of `T`.
    // No other expression opens with `type(`, so the quote reads the types an
    // expression would misread — a receive `?(S). T`, where `?` opens a hole,
    // and a labelled sum `+{ … }`, where `+{` opens an injection. The opener
    // is one tile, as `#{` and `${` are: the keyword `type` alone molds no
    // expression, so where a classifier is read it stays the stray keyword
    // that offers `Type`.
    out.push(r(
        RuleName("type_quote_expression"),
        Provenance("type_quote_expression"),
        s,
        p,
        seq([t(TileLabel("type(")), h(Sort::Type), t(TileLabel(")"))]),
    ));
    out.push(r(
        RuleName("list_expression"),
        Provenance("list_expression"),
        s,
        p,
        seq([t(TileLabel("[")), opt(comma1(h(s))), t(TileLabel("]"))]),
    ));
    let mut block_rule = r(RuleName("block"), Provenance("block"), s, p, block());
    for statement in [
        "val_statement",
        "bind_statement",
        "unpack_statement",
        "leta_statement",
        "hold_statement",
        "recv_statement",
        "acquire_statement",
        "release_statement",
        "fork_statement",
        "fork_shared_statement",
        "expression_statement",
    ] {
        block_rule.adaptations.push(Adaptation::new(
            RuleName("block"),
            SurfaceForm(statement),
            AdaptationReason("inlined into the block: a statement stands only among the statements of a block or of the body a form opens, whose own alternatives read it; at the top level the molder's expectation set names what a declaration needs"),
        ));
    }
    out.push(block_rule);
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
            alt([seq([t(TileLabel("{")), t(TileLabel("}"))]), arm_block()]),
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
    // The capability scope `handle c : I { … } with { pure(x) => e, oper
    // op(p, k) => e, … }`: a deep handler for the host interface `I` whose
    // body is handed the capability `c` it introduces, the only form that
    // brings a capability into a body's scope. The clauses follow the body:
    // the return clause, spelled with the returner's own keyword `pure`,
    // binds the body's result, and each operation clause, spelled with the
    // keyword a signature declares an operation with, binds the operation's
    // payload and its resumption. A clause is keyword-led after a `{` or `,`
    // this rule owns, so no expression hole competes with it. The tree-sitter
    // grammar has no handler, so the kind is in `PBG_ONLY_KINDS`.
    out.push(r(
        RuleName("handle_expression"),
        Provenance("handle_expression"),
        s,
        p,
        seq([
            t(TileLabel("handle")),
            t(TileLabel("identifier")),
            t(TileLabel(":")),
            t(TileLabel("type_identifier")),
            block(),
            t(TileLabel("with")),
            t(TileLabel("{")),
            handler_clause(),
            repeat(seq([t(TileLabel(",")), handler_clause()])),
            opt(t(TileLabel(","))),
            t(TileLabel("}")),
        ]),
    ));
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
    // are bare single-tile atoms (unlabeled, unit payload). `break(v)` leaves
    // the loop with a value: its parenthesis is a tile of its own form, so the
    // molder settles the two `break` molds by the next tile alone. A prefix
    // `break v` would not settle: an operand may stand beside an atom, and a
    // `;` reads as the shell's list-operator atom, so `break v` and `break;`
    // would each mold both ways with no obligation. These are PBG-only,
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
        RuleName("break_value_expression"),
        Provenance("break_value_expression"),
        s,
        p,
        seq([
            t(TileLabel("break")),
            t(TileLabel("(")),
            h(s),
            t(TileLabel(")")),
        ]),
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
    // The `#{`-opened expression forms — the telescope value `#{ }`, `#{ a, b
    // }`, `#{ .n = E, … }`, its `#{ n = E }` shorthand, and the record update
    // `#{ E | id = E, … }` — share the `#{` prefix. The hole-led ones diverge
    // only at the tile after the first entry: an update's `|` versus a
    // telescope's `,` or `}`. Declaring them as two rules would give `#{` two
    // hole-led Expression-sort molds, so the molder would decide
    // telescope-versus-update at the `#{` — a choice whose discriminating `|`
    // sits arbitrarily deep past nested `#{ … }` values (each carrying its own
    // `|`), out of a bounded lookahead's reach (`deep-record-update-cost`).
    // They are factored into one branch whose tail alternates on the
    // discriminating tile: the first entry fills the hole, and the following
    // `|`, `,` or `}` `≐`-continues exactly one tail — locally decidable with
    // no window — and the `|` reads as the form's own continuation
    // (continuation-rank 0), never the pipeline operator. A positional entry
    // is an `E`, and `E = E` the shorthand whose key the lowering reads as a
    // bare label.
    //
    // The leading-dot entries `.n = E` and `.0 = E` take a `#{` of their own,
    // decided by the very next tile: a `#{` that admits a hole after it and
    // also a `.` would let an operand stand before the form's `.`, so
    // `#{ p.x, p.y }` would read its projection dot as a label's. Each `#{`
    // instead has one kind of successor, so the dot after an operand is
    // always the projection's. A telescope is labelled throughout or
    // positional throughout; the concrete language is otherwise unchanged,
    // and the folded kinds are adaptations for the parity inventory.
    let mut telescope = r(
        RuleName("telescope_expression"),
        Provenance("telescope_expression"),
        s,
        p,
        alt([
            // labelled: `#{ .l = E, … }`
            seq([
                t(TileLabel("#{")),
                comma1(seq([dotted_label(), t(TileLabel("=")), h(s)])),
                t(TileLabel("}")),
            ]),
            seq([
                t(TileLabel("#{")),
                alt([
                    // the unit: `#{ }`
                    t(TileLabel("}")),
                    seq([
                        // the first entry: the update source, or a positional
                        // entry.
                        positional_entry(),
                        alt([
                            // update tail: `| id = E, … }`
                            seq([t(TileLabel("|")), comma1(record_field()), t(TileLabel("}"))]),
                            // telescope tail: `, entry`*, an optional trailing
                            // `,`.
                            seq([
                                repeat(seq([t(TileLabel(",")), positional_entry()])),
                                opt(t(TileLabel(","))),
                                t(TileLabel("}")),
                            ]),
                        ]),
                    ]),
                ]),
            ]),
        ]),
    );
    telescope.adaptations.push(Adaptation::new(
        RuleName("telescope_expression"),
        SurfaceForm("record_expression"),
        AdaptationReason("renamed into telescope_expression: the record literal is the telescope value `#{ … }` with labelled entries, the same former as the tuple"),
    ));
    telescope.adaptations.push(Adaptation::new(
        RuleName("telescope_expression"),
        SurfaceForm("record_field"),
        AdaptationReason("folded into the factored #{ family: the `.id = E` entry and its `id = E` shorthand are inlined (the shorthand's key is an expression hole), not a standalone form-first identifier competing with a bare variable"),
    ));
    telescope.adaptations.push(Adaptation::new(
        RuleName("telescope_expression"),
        SurfaceForm("record_update_expression"),
        AdaptationReason("factored into the #{ expression family: the update tail `| id = E, … }` shares the `#{ E` prefix and discriminates on the `|` tile after the source expression"),
    ));
    out.push(telescope);
    // The injection `+{ .ok = E }` into a sum over labels, positional as
    // `+{ .1 = E }`. Its `+` molds where an operand starts, so it never
    // competes with the infix `+`, which follows one.
    out.push(r(
        RuleName("labelled_sum_expression"),
        Provenance("labelled_sum_expression"),
        s,
        p,
        seq([
            t(TileLabel("+")),
            t(TileLabel("{")),
            dotted_label(),
            t(TileLabel("=")),
            h(s),
            t(TileLabel("}")),
        ]),
    ));
    // The anonymous copattern block `&{ .get => E, .put => E }`, the value of
    // a lazy record over labels: the clause `.l => E` of a `def rec` body,
    // labels positional as `.0 => E`, and `&{}` the empty lazy record.
    out.push(r(
        RuleName("lazy_record_expression"),
        Provenance("lazy_record_expression"),
        s,
        p,
        seq([
            t(TileLabel("&")),
            t(TileLabel("{")),
            opt(comma1(seq([dotted_label(), t(TileLabel("=>")), h(s)]))),
            t(TileLabel("}")),
        ]),
    ));
    session_expressions(out, p);
    access_expressions(out, p);
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

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_theory_graphs::PrecDag;
    use gandr_theory_graphs::PrecSpec;

    use super::comma1;
    use super::member_list;
    use super::repeat1;
    use super::rules;
    use crate::Pbg;
    use crate::PbgError;
    use crate::PrecName;
    use crate::PrecTable;
    use crate::Regex;
    use crate::Rule;
    use crate::RuleName;
    use crate::Sort;
    use crate::TileLabel;
    use crate::surface::PREC_GROUPS;
    use crate::surface::built_in_prec_table;

    #[test]
    fn assembly_reports_the_first_missing_band()
    {
        for absent in [
            ["item.singleton", "expression.atom"],
            ["pattern.or", "expression.pure"],
            ["expression.postfix", "expression.atom"],
        ] {
            let mut spec = PrecSpec::new();
            let mut names = Vec::new();
            for &(name, assoc) in PREC_GROUPS {
                if !absent.contains(&name) {
                    let id = spec.insert(name, assoc).expect("unique band");
                    names.push((PrecName(name), id));
                }
            }
            let partial = PrecTable::new(PrecDag::build(&spec).expect("acyclic bands"), names);
            assert_eq!(
                Err(PbgError::MissingPrec { name: absent[0] }),
                rules(&partial)
            );
        }
    }

    #[test]
    fn list_separators_are_not_optional_between_members()
    {
        let repeated_edges: &[(&str, &str)] = &[("member", "member")];
        let comma_edges: &[(&str, &str)] = &[(",", "member"), ("member", ",")];
        let member_edges: &[(&str, &str)] = &[
            (",", "member"),
            (";", "member"),
            ("member", ","),
            ("member", ";"),
        ];
        let repeat_one: fn(Regex) -> Regex = repeat1;
        for (assemble, expected, comma_closers) in [
            (repeat_one, repeated_edges, 0_usize),
            (comma1, comma_edges, 1),
            (member_list, member_edges, 1),
        ] {
            let table = built_in_prec_table().expect("built-in bands");
            let prec = table.prec(PrecName("expression.atom")).expect("atom band");
            let rule = Rule::new(
                RuleName("members"),
                Sort::Expression,
                prec,
                assemble(Regex::tile(TileLabel("member"))),
            );
            let grammar = Pbg::build(table.into_dag(), vec![rule]).expect("member grammar");
            let observed: BTreeSet<_> = grammar
                .adjacencies()
                .iter()
                .map(|&(left, right)| {
                    (
                        grammar.mold(left).expect("left occurrence").label,
                        grammar.mold(right).expect("right occurrence").label,
                    )
                })
                .collect();
            assert!(
                observed.iter().copied().eq(expected.iter().copied()),
                "{observed:?} != {expected:?}"
            );
            assert_eq!(
                comma_closers,
                grammar
                    .candidates(TileLabel(","))
                    .iter()
                    .filter(|&&mold| bool::from(grammar.mold_is_form_last(mold)))
                    .count()
            );
        }
    }
}
