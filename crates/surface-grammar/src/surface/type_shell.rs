//! The type, session-type, lexical and shell-context surface forms.

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

/// Builds the type, session-type, lexical and shell-context rules.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the type and session-type rules, then the lexical rules, then the
///   shell-context rules, each with the provenance of the named kind it
///   realises.
/// - fails: a group `precs` does not hold.
/// - panics: none.
///
/// # Errors
/// [`PbgError::MissingPrec`] naming the absent group.
pub(super) fn rules(precs: &PrecTable) -> Result<Vec<Rule>, PbgError>
{
    let mut rules = Vec::new();
    add_type_rules(&mut rules, precs)?;
    add_lexical_rules(&mut rules, precs)?;
    add_shell_rules(&mut rules, precs)?;
    Ok(rules)
}

/// Add type and session-type structural rules.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends this group's rules to `rules`, in order.
/// - fails: a group `precs` does not hold.
/// - panics: none.
///
/// # Errors
/// [`PbgError::MissingPrec`] naming the absent group.
fn add_type_rules(
    rules: &mut Vec<Rule>,
    precs: &PrecTable,
) -> Result<(), PbgError>
{
    let ty = Sort::Type;
    let type_atom = precs.prec(PrecName("type.atom"))?;
    let type_application = precs.prec(PrecName("type.application"))?;
    let type_product = precs.prec(PrecName("type.product"))?;
    let type_sum = precs.prec(PrecName("type.sum"))?;
    let type_union = precs.prec(PrecName("type.union"))?;
    let type_intersection = precs.prec(PrecName("type.intersection"))?;
    let type_lazy_product = precs.prec(PrecName("type.lazy_product"))?;
    let type_arrow = precs.prec(PrecName("type.arrow"))?;

    rules.push(rule(
        RuleName("forall_type"),
        ty,
        type_arrow,
        Regex::seq([
            tile(TileLabel("forall")),
            Regex::repeat(tile(TileLabel("type_variable"))),
            tile(TileLabel(".")),
            Regex::sort(ty),
        ]),
    ));
    // The first-class module package type `package [ T , U ] PAYLOAD`. The
    // bracketed list binds the signature's abstract type components over the
    // payload, which is the thunked module returner `U[r] (F …)`.
    //
    // **The grade is written once.** A package's grade and its payload thunk's
    // grade are the same `r`, so the surface carries no grade of its own and
    // the lowerer reads it off the payload — the invariant holds by
    // construction rather than by a check on two annotations that could
    // disagree.
    rules.push(rule(
        RuleName("package_type"),
        ty,
        type_application,
        Regex::seq([
            tile(TileLabel("package")),
            tile(TileLabel("[")),
            comma1(tile(TileLabel("type_identifier"))),
            tile(TileLabel("]")),
            Regex::sort(ty),
        ]),
    ));
    rules.push(rule(
        RuleName("function_type"),
        ty,
        type_arrow,
        Regex::seq([Regex::sort(ty), tile(TileLabel("->")), Regex::sort(ty)]),
    ));
    rules.push(binary_infix_rule(
        RuleName("union_type"),
        ty,
        type_union,
        TileLabel("|"),
    ));
    rules.push(binary_infix_rule(
        RuleName("intersection_type"),
        ty,
        type_intersection,
        TileLabel("/\\"),
    ));
    rules.push(binary_infix_rule(
        RuleName("lazy_product_type"),
        ty,
        type_lazy_product,
        TileLabel("&"),
    ));
    rules.push(binary_infix_rule(
        RuleName("sum_type"),
        ty,
        type_sum,
        TileLabel("+"),
    ));
    rules.push(binary_infix_rule(
        RuleName("product_type"),
        ty,
        type_product,
        TileLabel("*"),
    ));
    rules.push(rule(
        RuleName("f_type"),
        ty,
        type_application,
        Regex::seq([tile(TileLabel("F")), Regex::sort(ty)]),
    ));
    // The `grade` (`number` | `identifier` | `ω`) helper is inline-only.
    // Referencing it as `tile(TileLabel("grade"))` in the thunk-type annotation
    // left an unmatchable placeholder terminal — a real `U[1] T` could only
    // parse through `U`'s spurious `constructor` / `type_identifier` molds. The
    // grade shape is inlined so `U[1] T` molds directly, and the folded kind is
    // recorded as an adaptation.
    let mut u_type = rule(
        RuleName("u_type"),
        ty,
        type_application,
        Regex::seq([
            tile(TileLabel("U")),
            Regex::optional(Regex::seq([
                tile(TileLabel("[")),
                grade_shape(),
                tile(TileLabel("]")),
            ])),
            Regex::sort(ty),
        ]),
    );
    u_type.adaptations.push(Adaptation::new(
        RuleName("u_type"),
        SurfaceForm("grade"),
        AdaptationReason("folded into u_type / thunk_expression: the `number | identifier | ω` grade is inlined in the `[ … ]` annotation, not a placeholder tile nor a standalone type atom competing with a type variable"),
    ));
    rules.push(u_type);
    rules.push(rule(
        RuleName("at_type"),
        ty,
        type_application,
        Regex::seq([
            Regex::sort(ty),
            tile(TileLabel("at")),
            tile(TileLabel("identifier")),
        ]),
    ));
    // The identity type `Path(C, e1, e2)` is a production of its own, and the
    // reason is a **sort** rather than a preference.
    //
    // A generic `type_application` parses every argument at the type sort, so
    // reusing it for `Path` leaves the two endpoints parsed as types and
    // reinterpreted as values downstream. Only the spellings a type and a value
    // have in common survive that reinterpretation — an integer literal and a
    // bare name — which is why an endpoint like `comp(id(a), f)` cannot be
    // written however far the lowering is widened. **Its problem is upstream of
    // the lowering.**
    //
    // So the carrier stays type-sorted and the two endpoints are
    // **expression-sorted**, which is what they are: terms occurring in a type.
    rules.push(rule(
        RuleName("path_type"),
        ty,
        type_application,
        Regex::seq([
            tile(TileLabel("Path")),
            tile(TileLabel("(")),
            Regex::sort(ty),
            tile(TileLabel(",")),
            Regex::sort(Sort::Expression),
            tile(TileLabel(",")),
            Regex::sort(Sort::Expression),
            tile(TileLabel(")")),
        ]),
    ));
    rules.push(rule(
        RuleName("type_application"),
        ty,
        type_application,
        Regex::seq([
            tile(TileLabel("type_identifier")),
            tile(TileLabel("(")),
            comma1(Regex::sort(ty)),
            tile(TileLabel(")")),
        ]),
    ));
    rules.push(rule(
        RuleName("parenthesized_type"),
        ty,
        type_atom,
        Regex::seq([tile(TileLabel("(")), Regex::sort(ty), tile(TileLabel(")"))]),
    ));
    // The `record_type_field` (`id : T`) helper is inline-only. Referencing it as
    // a `tile(TileLabel("record_type_field"))` left an unmatchable placeholder
    // terminal (no lexeme carries that label) AND a standalone rule whose
    // `identifier` opener is a spurious form-first Type-sort competitor. The
    // field shape is inlined directly so a real `#{ id : T, … }` record type
    // molds, and the standalone kind is folded into `record_type` as an
    // adaptation.
    let mut record_type = rule(
        RuleName("record_type"),
        ty,
        type_atom,
        Regex::seq([
            tile(TileLabel("#{")),
            Regex::optional(comma1(field_shape(ty))),
            tile(TileLabel("}")),
        ]),
    );
    record_type.adaptations.push(Adaptation::new(
        RuleName("record_type"),
        SurfaceForm("record_type_field"),
        AdaptationReason("folded into record_type: the `id : T` field is inlined, not a placeholder tile nor a standalone form-first identifier competing at a type slot"),
    ));
    rules.push(record_type);
    rules.push(rule(
        RuleName("send_session_type"),
        ty,
        type_arrow,
        Regex::seq([
            tile(TileLabel("!")),
            Regex::sort(ty),
            tile(TileLabel(".")),
            Regex::sort(ty),
        ]),
    ));
    rules.push(rule(
        RuleName("receive_session_type"),
        ty,
        type_arrow,
        Regex::seq([
            tile(TileLabel("?")),
            Regex::sort(ty),
            tile(TileLabel(".")),
            Regex::sort(ty),
        ]),
    ));
    rules.push(rule(
        RuleName("end_session_type"),
        ty,
        type_atom,
        tile(TileLabel("end")),
    ));
    // The `session_field` (`id : T`) helper is inline-only. Like
    // `record_type_field`, referencing it as `tile(TileLabel("session_field"))`
    // left an unmatchable placeholder terminal and a standalone rule whose
    // `identifier` opener is a spurious form-first Type-sort competitor. The
    // field shape is inlined into both session-choice types so a real `+{ id :
    // T, … }` / `&{ … }` molds, and the folded kind is recorded on
    // `select_session_type`.
    let mut select_session = rule(
        RuleName("select_session_type"),
        ty,
        type_atom,
        Regex::seq([
            tile(TileLabel("+")),
            tile(TileLabel("{")),
            comma1(field_shape(ty)),
            tile(TileLabel("}")),
        ]),
    );
    select_session.adaptations.push(Adaptation::new(
        RuleName("select_session_type"),
        SurfaceForm("session_field"),
        AdaptationReason("folded away: the `id : T` session field is inlined into the select/offer session types, not a placeholder tile nor a standalone form-first identifier competing at a type slot"),
    ));
    rules.push(select_session);
    rules.push(rule(
        RuleName("offer_session_type"),
        ty,
        type_atom,
        Regex::seq([
            tile(TileLabel("&")),
            tile(TileLabel("{")),
            comma1(field_shape(ty)),
            tile(TileLabel("}")),
        ]),
    ));
    rules.push(rule(
        RuleName("mu_session_type"),
        ty,
        type_arrow,
        Regex::seq([
            tile(TileLabel("mu")),
            tile(TileLabel("type_variable")),
            tile(TileLabel(".")),
            Regex::sort(ty),
        ]),
    ));
    rules.push(rule(
        RuleName("primitive_type"),
        ty,
        type_atom,
        Regex::alt([
            tile(TileLabel("Any")),
            tile(TileLabel("Unknown")),
            tile(TileLabel("Never")),
            tile(TileLabel("Boolean")),
            tile(TileLabel("Integer")),
            tile(TileLabel("u32")),
            tile(TileLabel("u64")),
            tile(TileLabel("i32")),
            tile(TileLabel("i64")),
            tile(TileLabel("f32")),
            tile(TileLabel("f64")),
            tile(TileLabel("Char")),
            tile(TileLabel("String")),
            tile(TileLabel("Symbol")),
            tile(TileLabel("Unit")),
            tile(TileLabel("Void")),
        ]),
    ));
    // The gradual top `?` as a type atom: one spelling for the unknown type
    // on both sorts, with the consuming position deciding the sort — a value
    // position lowers it to the unknown value type, a computation position to
    // the unknown computation type, and the formatter prints both back as
    // `?`. The tree-sitter grammar produces no type atom here, so its
    // provenance is in `PBG_ONLY_KINDS`.
    //
    // The tile is shared with two forms the sort menus and continuation
    // discipline keep disjoint: the Expression-sort typed hole (`?` / `?name`)
    // never competes at a Type slot, and the receive-session `?T.S` — whose
    // `?` also molds at a Type frontier — wins exactly when a type, `.`, and a
    // session tail follow, while a bare `?` (or one closed by `;`, `)`, `,`,
    // or an infix operator) molds as this atom. This is the chosen alternative
    // to overloading the term-hole spelling for the computation sort: the atom
    // is structurally distinct from `hole`, so host escapes and nested
    // conditional bodies keep their existing CST fields.
    rules.push(rule(
        RuleName("unknown_type"),
        ty,
        type_atom,
        tile(TileLabel("?")),
    ));
    rules.push(rule(
        RuleName("type_identifier"),
        ty,
        type_atom,
        tile(TileLabel("type_identifier")),
    ));
    rules.push(rule(
        RuleName("type_variable"),
        ty,
        type_atom,
        tile(TileLabel("type_variable")),
    ));
    // Identity endpoints: a number literal is a Type-sort atom, so
    // `Path(Integer, 4, 4)` molds with literal endpoints. The Expression- and
    // Pattern-sort `number` realisations live in the term lexical forms
    // (`number.expression` / `number.pattern`); this is the Type-sort third
    // realisation of the same provenance, admissible only in a type hole (the
    // per-sort menus keep the three from tying, as `identifier` and
    // `type_variable` already do). A compound value-term endpoint is the
    // reserved term-in-type splice, not a form here.
    rules.push(Rule::with_provenance(
        RuleName("number.type"),
        Provenance("number"),
        ty,
        type_atom,
        tile(TileLabel("number")),
    ));
    Ok(())
}

/// Add lexical named node rules from the grammar suffix.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends this group's rules to `rules`, in order.
/// - fails: a group `precs` does not hold.
/// - panics: none.
///
/// # Errors
/// [`PbgError::MissingPrec`] naming the absent group.
fn add_lexical_rules(
    rules: &mut Vec<Rule>,
    precs: &PrecTable,
) -> Result<(), PbgError>
{
    let item = Sort::Item;
    let item_singleton = precs.prec(PrecName("item.singleton"))?;

    // The Expression-atom lexical forms `identifier` / `constructor` /
    // `boolean` / `number` / `typed_number` / `string` are declared once, by
    // the term lexical forms (the `*.expression` rules, beside their
    // Pattern-sort twins). A second declaration here would give each lexeme
    // two identical Expression-atom molds that tie on the molder's local key at
    // every operand position.
    rules.push(rule(
        RuleName("line_comment"),
        item,
        item_singleton,
        tile(TileLabel("line_comment")),
    ));
    rules.push(rule(
        RuleName("block_comment"),
        item,
        item_singleton,
        Regex::seq([
            tile(TileLabel("/*")),
            Regex::repeat(Regex::alt([
                tile(TileLabel("block_comment")),
                tile(TileLabel("block_comment_content")),
            ])),
            tile(TileLabel("*/")),
        ]),
    ));
    rules.push(rule(
        RuleName("shebang"),
        item,
        item_singleton,
        tile(TileLabel("shebang")),
    ));
    Ok(())
}

/// Add shell-context structural rules — the POSIX shell DSL surface.
///
/// # Shell-surface coverage
///
/// The shell forms below mold in the shell block's interior Expression hole
/// (`#!{ … }`), where command atoms juxtapose and the operator / separator
/// forms bind them. This table records what POSIX-shell surface the fragment
/// **folds in** (parses, zero-obligation) versus what is **deliberately out**.
/// Parse level only: the semantics are not this crate's.
///
/// ## Folded in
///
/// | Form                     | Surface                          | Realisation                                             |
/// | ------------------------ | -------------------------------- | ------------------------------------------------------- |
/// | simple command           | `cmd arg …`                      | `shell_word` atom juxtaposition (one word class)         |
/// | environment assignment   | `FOO=bar cmd`                    | `environment_assignment` (whole-token `NAME=` munch)     |
/// | single-quoted string     | `'…'` (verbatim run)             | `single_quoted_string` (opaque `single_quoted_content`)  |
/// | double-quoted string     | `"…"` (fragments + escapes)      | `double_quoted_string`                                   |
/// | simple parameter         | `$name`                          | `variable_expansion` (`$` branch)                        |
/// | braced parameter         | `${name}`                        | `variable_expansion` (`${` branch; PBG-only)             |
/// | parameter in a `"…"`      | `"… $name … ${name} …"`          | inline expansion in `double_quoted_string`               |
/// | pipeline                 | `a \| b`, `a \|& b`              | `pipeline` binary infix                                  |
/// | logical control          | `a && b`, `a \|\|`               | the `&&` / `\|\|` expression binaries                    |
/// | list separators          | `a ; b`, `a & b`                 | `list_operator` (`;` / `&`)                              |
/// | redirection              | `> >> < <& >& <>` + target       | `redirection_operator` + juxtaposed target               |
/// | file descriptor          | `2>`, `2>&1`                     | `file_descriptor` (a digit run before a redirect)        |
/// | subshell                 | `[ … ]`                          | `subshell` (distinct shell-context brackets)             |
/// | host escape              | `$( E )`                         | `host_escape` (a gandr expression interior)              |
///
/// ## Deliberately out (the POSIX tail)
///
/// Command substitution `$( … )` / `` `…` `` and the `$!{ … }` block form;
/// arithmetic expansion `$(( … ))`; parameter-expansion operators
/// (`${name:-word}`, `${#name}`, `${name%pat}`, `${name/a/b}`, …); here-docs
/// (`<<`, `<<-`) and here-strings (`<<<`); globs and brace / tilde expansion
/// (`*`, `?`, `[…]`-glob, `{a,b}`, `~`); the `case` / `for` / `while` / `if`
/// shell control words and shell functions; the environment-assignment prefix
/// SEMANTICS (`FOO=bar cmd` — the assignment token itself is folded in above);
/// command negation (`! cmd`); process substitution (`<( … )`); and job
/// control / history. Each is a later shell-stage widening, and each
/// parse-and-declines or lexes as an ordinary word today.
///
/// The placeholder rules kept for named-kind coverage — `shell_list`,
/// `and_expression` / `or_expression` (shell), `negation` — each need at
/// least one tile the labeler never emits (`shell_or`, `pipeline_operand`,
/// `shell_and`, `negation`), so none of them can fire; they cover their kind
/// by provenance.
///
/// `environment_assignment` is not one of them: the labeler reads
/// `NAME=value` as one token, and this rule molds it as one Expression atom.
/// Only the prefix semantics are left out, and they are declined by name
/// after parsing.
///
/// `command_substitution` is not one of them either. Its `list_operator` /
/// `shell_list` tiles are never emitted, but both are optional, so `$!{ … }`
/// molds on the `command_substitution_start` and `}` tiles the labeler emits,
/// and is declined by name after parsing.
///
/// The `command` / `command_name` / `argument` / `redirection` kinds have no
/// rule: a composite over placeholder tiles would add fresh-menu molds that
/// tie every shell word and file descriptor. Their kinds fold as adaptations
/// onto `shell_word` / `redirection_operator`; grouping the juxtaposed atoms
/// into name, arguments and redirections is the semantic stage's job.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends this group's rules to `rules`, in order.
/// - fails: a group `precs` does not hold.
/// - panics: none.
///
/// # Errors
/// [`PbgError::MissingPrec`] naming the absent group.
fn add_shell_rules(
    rules: &mut Vec<Rule>,
    precs: &PrecTable,
) -> Result<(), PbgError>
{
    let expr = Sort::Expression;
    let atom = precs.prec(PrecName("expression.atom"))?;
    let postfix = precs.prec(PrecName("expression.postfix"))?;
    let and_prec = precs.prec(PrecName("expression.and"))?;
    let or_prec = precs.prec(PrecName("expression.or"))?;

    rules.push(rule(
        RuleName("shell_list"),
        expr,
        atom,
        Regex::seq([
            tile(TileLabel("shell_or")),
            Regex::repeat(Regex::seq([
                tile(TileLabel("list_operator")),
                tile(TileLabel("shell_or")),
            ])),
            Regex::optional(tile(TileLabel("list_operator"))),
        ]),
    ));
    rules.push(rule(
        RuleName("list_operator"),
        expr,
        atom,
        Regex::alt([
            tile(TileLabel(";")),
            tile(TileLabel("&")),
            tile(TileLabel("newline")),
        ]),
    ));
    rules.push(rule(
        RuleName("or_expression"),
        expr,
        or_prec,
        Regex::seq([
            tile(TileLabel("shell_and")),
            Regex::repeat(Regex::seq([
                tile(TileLabel("||")),
                tile(TileLabel("shell_and")),
            ])),
        ]),
    ));
    rules.push(rule(
        RuleName("and_expression"),
        expr,
        and_prec,
        Regex::seq([
            tile(TileLabel("pipeline_operand")),
            Regex::repeat(Regex::seq([
                tile(TileLabel("&&")),
                tile(TileLabel("pipeline_operand")),
            ])),
        ]),
    ));
    // A shell pipeline `cmd | cmd` (and stderr-merging `cmd |& cmd`) is a binary
    // infix between two command expressions, exactly the shape the term binaries
    // (`&&`, `||`) take: a single `|` / `|&` tile with a recursive-sort hole on
    // each side, so the melder classifies it as an operator (paper Fig. 29's
    // Reduce) admissible in the shell block's expression hole. The tree-sitter
    // `pipeline` (`_shell_command (choice("|","|&") optional(_shell_command))+`)
    // chains the operator with a `repeat`, which the melder reads as a form-mid
    // continuation tile — inadmissible as an operator between two juxtaposed
    // command atoms; the binary shape keeps operator status. Both spellings
    // keep the `pipeline` provenance so the named-kind inventory covers the kind.
    rules.push(pipe_rule(
        RuleName("pipeline.pipe"),
        expr,
        postfix,
        TileLabel("|"),
    ));
    rules.push(pipe_rule(
        RuleName("pipeline.pipe_both"),
        expr,
        postfix,
        TileLabel("|&"),
    ));
    rules.push(rule(
        RuleName("negation"),
        expr,
        atom,
        tile(TileLabel("negation")),
    ));
    rules.push(rule(
        RuleName("environment_assignment"),
        expr,
        atom,
        tile(TileLabel("environment_assignment")),
    ));
    // ONE shell-word atom class. The tree-sitter grammar distinguishes
    // `command_name` / `argument` / `shell_word` — a distinction with no
    // PBG-parse-level content (all three are the same juxtaposed Expression
    // atom over the same lexeme class). Realised as composite rules
    // (`command`, `argument`, `redirection`) over placeholder tiles the
    // labeler never emits, they would put extra molds on the ShellWord fresh
    // menu (a `command_name` atom, a `command` form-start, a second
    // `shell_word` occurrence), so EVERY shell word would tie 3–4 candidates
    // and fire the molder's dry-run + lookahead machinery per word. A shell
    // word has exactly ONE mold instead (the molder's sole-admissible fast
    // path), and the folded kinds are recorded as adaptations below so
    // named-kind parity covers them. The command / argument STRUCTURE (name +
    // arguments as one node) is the semantic stage's job over the juxtaposed
    // atoms.
    let mut shell_word = rule(
        RuleName("shell_word"),
        expr,
        atom,
        tile(TileLabel("shell_word")),
    );
    shell_word.adaptations.push(Adaptation::new(
        RuleName("shell_word"),
        SurfaceForm("command_name"),
        AdaptationReason("folded into the single shell-word atom class: a command's name is positionally the first word of a juxtaposed command run, not a lexically distinct atom; a dedicated `command_name` mold would tie the shell-word menu and cost a dry-run per word"),
    ));
    shell_word.adaptations.push(Adaptation::new(
        RuleName("shell_word"),
        SurfaceForm("argument"),
        AdaptationReason("folded into the single shell-word atom class: the `argument` alternation (shell_word / variable_expansion / command_substitution / host_escape) has no member that is not a standalone atom already; another `shell_word` occurrence would only widen the shell-word menu"),
    ));
    shell_word.adaptations.push(Adaptation::new(
        RuleName("shell_word"),
        SurfaceForm("command"),
        AdaptationReason("folded into shell-block juxtaposition: a `command` composite (`negation? env* command_name command_part*`) would rest on placeholder tiles, and its `command_name` form-start mold would tie every shell word; a command is the juxtaposed run of word, string and expansion atoms between separators, grouped at the semantic stage"),
    ));
    rules.push(shell_word);
    rules.push(rule(
        RuleName("single_quoted_string"),
        expr,
        atom,
        Regex::seq([
            tile(TileLabel("'")),
            tile(TileLabel("single_quoted_content")),
            tile(TileLabel("'")),
        ]),
    ));
    // A shell double-quoted string `"…"`: a `"`-delimited run
    // of `double_string_fragment` text, `\.` escapes, and parameter expansions
    // (`$name` / `${name}`). The labeler's shell double-quote mode emits these
    // constituent tokens, so the string is one atom (interior spaces preserved),
    // not juxtaposed shell words. The parameter expansion is INLINED here (the
    // `$ variable_name` / `${ variable_name }` shapes, matching the labeler's
    // tokens) rather than a `variable_expansion` composite tile the labeler never
    // emits. The tree-sitter grammar also admits a `command_substitution`
    // inside the string; this surface does not (command substitution belongs
    // to the POSIX tail it leaves out) and records that as an adaptation — the
    // named kind stays covered by the standalone rule.
    let mut double_quoted_string = rule(
        RuleName("double_quoted_string"),
        expr,
        atom,
        Regex::seq([
            tile(TileLabel("\"")),
            Regex::repeat(Regex::alt([
                tile(TileLabel("double_string_fragment")),
                tile(TileLabel("escape_sequence")),
                dquote_variable_expansion(),
            ])),
            tile(TileLabel("\"")),
        ]),
    );
    double_quoted_string.adaptations.push(Adaptation::new(
        RuleName("double_quoted_string"),
        SurfaceForm("command_substitution"),
        AdaptationReason("the tree-sitter `double_quoted_string` interior admits a `command_substitution` `$!{ … }`; this surface leaves command substitution out, so the interior is fragments, escapes and parameter expansions only. The `command_substitution` named kind stays realised by its standalone rule; the inline `variable_expansion` shapes (`$ variable_name` / `${ variable_name }`) match the tokens the labeler emits."),
    ));
    rules.push(double_quoted_string);
    // A parameter expansion `$name` OR its braced form `${name}`.
    // The two spellings share ONE `variable_expansion` provenance
    // and discriminate on the opener tile (`$` vs `${`), so a shell parameter is
    // one construct with one eventual semantics seam. The braced form is a
    // divergence from the tree-sitter grammar (whose `variable_expansion` is
    // `$` `variable_name` alone), recorded as an adaptation. Its interior is a
    // `variable_name`, NOT a host-expression hole:
    // the labeler's shell-brace mode keeps the interior a shell parameter name,
    // DISTINCT from the string-interpolation `${ E }` (whose interior is host
    // tokens) — a shell parameter is not a gandr binding.
    let mut variable_expansion = rule(
        RuleName("variable_expansion"),
        expr,
        atom,
        Regex::alt([
            Regex::seq([tile(TileLabel("$")), tile(TileLabel("variable_name"))]),
            Regex::seq([
                tile(TileLabel("${")),
                tile(TileLabel("variable_name")),
                tile(TileLabel("}")),
            ]),
        ]),
    );
    variable_expansion.adaptations.push(Adaptation::new(
        RuleName("variable_expansion"),
        SurfaceForm("braced_variable_expansion"),
        AdaptationReason("the braced parameter form `${name}` is folded into variable_expansion as a second opener branch discriminating on the `${` tile. The tree-sitter grammar has only `$name`, so the braced form is PBG-only; its interior is a shell `variable_name`, kept distinct from the string-interpolation `${ E }` host-expression mechanism because a shell parameter name is not a host binding. The `${name:-word}` / `${#name}` operator forms belong to the POSIX tail this surface leaves out."),
    ));
    rules.push(variable_expansion);
    rules.push(rule(
        RuleName("variable_name"),
        expr,
        atom,
        tile(TileLabel("variable_name")),
    ));
    rules.push(rule(
        RuleName("command_substitution"),
        expr,
        atom,
        Regex::seq([
            tile(TileLabel("command_substitution_start")),
            Regex::optional(tile(TileLabel("list_operator"))),
            Regex::optional(tile(TileLabel("shell_list"))),
            tile(TileLabel("}")),
        ]),
    ));
    rules.push(rule(
        RuleName("host_escape"),
        expr,
        atom,
        Regex::seq([
            tile(TileLabel("$")),
            tile(TileLabel("(")),
            Regex::sort(expr),
            tile(TileLabel(")")),
        ]),
    ));
    // `subshell` (`[ … ]`): a bracket-delimited shell group whose commands
    // mold by juxtaposition in the interior Expression hole, exactly like the
    // shell block. Its brackets are distinct shell-context tiles
    // (`subshell_open` / `subshell_close`, emitted only inside a shell block),
    // so the host list literal's `[` menu is untouched. This is a divergence
    // from POSIX, where `[` is the `test` builtin and `( … )` is the subshell;
    // the gandr shell dialect spells a subshell `[ … ]`, keeping `( … )` free
    // for the `$( … )` host escape.
    let mut subshell = rule(
        RuleName("subshell"),
        expr,
        atom,
        Regex::seq([
            tile(TileLabel("subshell_open")),
            Regex::optional(Regex::sort(expr)),
            tile(TileLabel("subshell_close")),
        ]),
    );
    subshell.adaptations.push(Adaptation::new(
        RuleName("subshell"),
        SurfaceForm("subshell"),
        AdaptationReason("the gandr shell dialect spells a subshell `[ … ]`, not the POSIX `( … )` (`[` is the POSIX `test` builtin; `( … )` stays free for the `$( … )` host escape). Its brackets are distinct shell-context tiles (`subshell_open` / `subshell_close`) so the host list-literal `[` menu is not widened."),
    ));
    rules.push(subshell);
    rules.push(rule(
        RuleName("file_descriptor"),
        expr,
        atom,
        tile(TileLabel("file_descriptor")),
    ));
    // The redirection operators are single atoms; the `redirection` COMPOSITE
    // (`fd? op target`) was a dead rule over placeholder tiles (its
    // `redirection_operator` / `argument` / string tiles never molded — a real
    // `>` molds through THIS alternation) whose `file_descriptor` form-start
    // mold tied every fd token. It is folded here as an adaptation:
    // the fd / operator / target grouping is the semantic
    // stage's job over the juxtaposed atoms, exactly as it already was.
    let mut redirection_operator = rule(
        RuleName("redirection_operator"),
        expr,
        atom,
        Regex::alt([
            tile(TileLabel("<>")),
            tile(TileLabel("<&")),
            tile(TileLabel(">&")),
            tile(TileLabel(">>")),
            tile(TileLabel("<")),
            tile(TileLabel(">")),
        ]),
    );
    redirection_operator.adaptations.push(Adaptation::new(
        RuleName("redirection_operator"),
        SurfaceForm("redirection"),
        AdaptationReason("folded into juxtaposition: a `redirection` composite (`fd? op target`) would rest on placeholder tiles, and its `file_descriptor` form-start mold would tie every fd token; a redirection is the juxtaposed `fd? op target` atom run, grouped at the semantic stage"),
    ));
    rules.push(redirection_operator);
    Ok(())
}

/// Build a provenance-bearing rule whose name matches its source rule.
///
/// # Specification
/// trivial.
fn rule(
    name: RuleName,
    sort: Sort,
    prec: Prec,
    regex: Regex,
) -> Rule
{
    Rule::with_provenance(name, Provenance(name.0), sort, prec, regex)
}

/// Build a tile by label; mold identity is assigned at `Pbg` build.
///
/// # Specification
/// trivial.
fn tile(label: TileLabel) -> Regex
{
    Regex::tile(label)
}

/// Build a shell pipeline binary infix rule `E op E` under the `pipeline`
/// provenance, so both `|` and `|&` spellings realise the `pipeline` named
/// kind.
///
/// # Specification
/// trivial.
fn pipe_rule(
    name: RuleName,
    sort: Sort,
    prec: Prec,
    operator: TileLabel,
) -> Rule
{
    Rule::with_provenance(
        name,
        Provenance("pipeline"),
        sort,
        prec,
        Regex::seq([Regex::sort(sort), tile(operator), Regex::sort(sort)]),
    )
}

/// Build the inline parameter-expansion shape used inside a shell double-quoted
/// string: `$ variable_name` or `${ variable_name }`.
///
/// Inlined (not a `variable_expansion` composite tile) so it matches the
/// labeler's constituent tokens; the same two-branch shape the standalone
/// `variable_expansion` rule carries, keeping the simple and braced spellings
/// unified.
///
/// # Specification
/// trivial.
fn dquote_variable_expansion() -> Regex
{
    Regex::alt([
        Regex::seq([tile(TileLabel("$")), tile(TileLabel("variable_name"))]),
        Regex::seq([
            tile(TileLabel("${")),
            tile(TileLabel("variable_name")),
            tile(TileLabel("}")),
        ]),
    ])
}

/// Build a flat repeated infix type rule.
/// Build a binary infix type rule `T op T` at the given precedence band.
///
/// The operator is a single-tile infix between two recursive-sort holes, so the
/// melder classifies it as an infix operator (paper Fig. 29's Reduce), exactly
/// like the expression binaries `seq([h(s), t(op), h(s)])`. Chaining
/// (`A + B + C`) is the precedence machinery's job, reducing left-to-right in
/// an associative band. A `repeat(seq([op, T]))` tail would instead give the
/// operator an `op ≐ op` repeat-seam adjacency, which the melder reads as a
/// same-form continuation tile: the operator would then be a form-mid rather
/// than an operator and inadmissible in a sort hole (a type ascription
/// `x : A + B` could not mold its `+`). The binary shape keeps operator
/// status.
///
/// # Specification
/// trivial.
fn binary_infix_rule(
    name: RuleName,
    sort: Sort,
    prec: Prec,
    operator: TileLabel,
) -> Rule
{
    rule(
        name,
        sort,
        prec,
        Regex::seq([Regex::sort(sort), tile(operator), Regex::sort(sort)]),
    )
}

/// Build the inline grade shape `number | identifier | ω` for the `U[…]` type.
///
/// # Specification
/// trivial.
fn grade_shape() -> Regex
{
    Regex::alt([
        tile(TileLabel("number")),
        tile(TileLabel("identifier")),
        tile(TileLabel("ω")),
    ])
}

/// Build a comma-separated non-empty repetition.
///
/// # Specification
/// trivial.
fn comma1(item: Regex) -> Regex
{
    Regex::seq([
        item.clone(),
        Regex::repeat(Regex::seq([tile(TileLabel(",")), item])),
    ])
}

/// Build an inline `id : T` field shape, shared by record and session types.
///
/// # Specification
/// trivial.
fn field_shape(sort: Sort) -> Regex
{
    Regex::seq([
        tile(TileLabel("identifier")),
        tile(TileLabel(":")),
        Regex::sort(sort),
    ])
}
