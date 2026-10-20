use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionType;
use gandr_core_term::session::Step;
use gandr_kernel_term::FieldLabel;
use gandr_surface_grammar::NamedKind;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::lower::exits::tests::assert_same_body;
use crate::lower::exits::tests::spelled_within;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::DeclarationOutcome;
use crate::module::LoweredDeclaration;
use crate::module::LoweredModule;
use crate::origin::Labelled;
use crate::resolve::SurfaceName;

/// The seat exchange over strings: the seat's end forked to the child, the
/// operator's held by the rest of the block, with an intuitionistic parameter
/// and every receipt's binder standing between an endpoint and its uses.
const EXCHANGE: &str = "def exchange(n : Integer) -> -F Unit {\n\
     fork (c : ?String. mu turn. +{ report : !String. &{ next : turn, retire : end }, handoff : !String. end }) {\n\
       recv(c) as task;\n\
       select(c, report);\n\
       send(c, \"progress\");\n\
       offer(c) {\n\
         next => { select(c, handoff); send(c, \"notes\"); close(c) },\n\
         retire => close(c)\n\
       }\n\
     } as peer;\n\
     send(peer, \"task\");\n\
     offer(peer) {\n\
       report => {\n\
         recv(peer) as first;\n\
         select(peer, next);\n\
         offer(peer) {\n\
           report => { recv(peer) as second; select(peer, retire); close(peer) },\n\
           handoff => { recv(peer) as notes; close(peer) }\n\
         }\n\
       },\n\
       handoff => { recv(peer) as notes; close(peer) }\n\
     }\n\
   }\n";

/// One move along a protocol: past a send or a receive, or into the branch a
/// label names.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: a choice is entered only by a label.
/// - executable: none — the move holds no protocol to check against.
///
/// # Adequacy
/// - hypothesis: L3 — the protocol witness walks every former with these.
/// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
#[derive(Clone, Copy, Debug)]
enum Move
{
    /// Past an action that carries a payload, or onto the close.
    On,
    /// Into the branch of a choice the label names.
    Take(&'static str),
}

/// The declared type of `name` in `module`.
///
/// # Specification
/// - requires: `module` lowers a signature for `name`.
/// - ensures: that signature.
/// - fails: never.
/// - panics: if the declaration is missing or lowers no signature.
///
/// # Adequacy
/// - hypothesis: L3 — the protocol witnesses read each session type here.
/// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
#[spec(ensures: |ret| module.declarations().iter().any(|declaration| matches!(
    declaration.outcome(),
    DeclarationOutcome::Completed { declared_type, .. } | DeclarationOutcome::Uncompleted { declared_type } if declared_type == ret
)))]
fn declared_of(
    module: &LoweredModule<'_>,
    name: SurfaceName<'_>,
) -> ValueTypeId
{
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
    else {
        panic!("`{name}` is declared");
    };
    match declaration.outcome() {
        DeclarationOutcome::Completed { declared_type, .. }
        | DeclarationOutcome::Uncompleted { declared_type } => declared_type,
        other @ (DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => panic!("`{name}` lowers a signature: {other:?}"),
    }
}

/// The steps the session type `declared` takes along `moves`, one token per
/// step: `!P` and `?P` for a send and a receive of the payload `P`, `+l,…`
/// and `&l,…` for a select and an offer over their labels, `end` for the
/// close, which ends the walk.
///
/// # Specification
/// - requires: `declared` is a session type in `arena`, and each move fits the
///   step it is taken at.
/// - ensures: one token per move taken, the recursion unfolded as the protocol
///   steps.
/// - fails: never on accepted fixtures.
/// - panics: if `declared` is no session type, or a move does not fit.
///
/// # Adequacy
/// - hypothesis: L3 — the witness walks a select, an offer, a recursion back to
///   its binder, each payload and the close.
/// - witness: `lower::session::tests::a_session_type_lowers_to_its_protocol`
#[spec(ensures: |ret| ret.len() <= moves.len())]
fn walked(
    arena: &CoreArena,
    declared: ValueTypeId,
    moves: &[Move],
) -> Vec<String>
{
    let Some(held) = arena.value_type(declared)
    else {
        panic!("`{declared:?}` is in the arena");
    };
    let ValueType::Session(ref session) = *held
    else {
        panic!("a session type: {held:?}");
    };
    let named = |payload: ValueTypeId| match arena.value_type(payload) {
        Some(&ValueType::Base(base)) => format!("{base:?}"),
        other => format!("{other:?}"),
    };
    let mut at: SessionType = session.clone();
    let mut tokens = Vec::new();
    for &taken in moves {
        let step = at.step().expect("the protocol steps");
        let next = match step {
            Step::Send { payload, next } => {
                tokens.push(format!("!{}", named(payload)));
                next
            },
            Step::Receive { payload, next } => {
                tokens.push(format!("?{}", named(payload)));
                next
            },
            Step::Select(ref branches) | Step::Offer(ref branches) => {
                let polarity = if matches!(step, Step::Select(_)) {
                    "+"
                }
                else {
                    "&"
                };
                let mut token = String::from(polarity);
                for (index, label) in branches.labels().enumerate() {
                    if index > 0 {
                        token.push(',');
                    }
                    token.push_str(AsRef::<str>::as_ref(label));
                }
                tokens.push(token);
                let Move::Take(label) = taken
                else {
                    panic!("a choice is entered by a label");
                };
                match branches
                    .get(&FieldLabel::from(String::from(label)))
                    .expect("the branch steps")
                {
                    Maybe::Present(branch) => branch,
                    Maybe::Absent(_) => panic!("the choice names `{label}`"),
                }
            },
            Step::End => {
                tokens.push(String::from("end"));
                break;
            },
        };
        at = next;
    }

    tokens
}

/// Every session action under `root`, in a preorder walk through binds,
/// splits, lambdas, an offer's arms in label order and a fork's child before
/// its parent: one token per action, its kind, its endpoint's linear index
/// and the label it selects.
///
/// # Specification
/// - requires: `root` is in `arena`.
/// - ensures: one token per session action reached.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the exchange's actions at both ends, each asserted at its
///   endpoint.
/// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
#[spec(ensures: |ret| ret.iter().all(|token| !token.is_empty()))]
fn actions(
    arena: &CoreArena,
    root: ComputationId,
) -> Vec<String>
{
    let mut seen = Vec::new();
    let mut pending = Vec::from([root]);
    while let Some(next) = pending.pop() {
        match arena.computation(next) {
            Some(&Computation::Bind(first, second)) => pending.extend([second, first]),
            Some(&Computation::Lambda(under) | &Computation::Split { body: under, .. }) => {
                pending.push(under);
            },
            Some(&Computation::Session(ref action)) => {
                let kind = match *action {
                    SessionAction::Send { .. } => String::from("send"),
                    SessionAction::Receive { .. } => String::from("recv"),
                    SessionAction::Select { ref label, .. } => {
                        format!("select {}", AsRef::<str>::as_ref(label))
                    },
                    SessionAction::Offer { .. } => String::from("offer"),
                    SessionAction::Close { .. } => String::from("close"),
                    SessionAction::Fork { .. } => String::from("fork"),
                };
                seen.push(match action.endpoint() {
                    Maybe::Present(endpoint) => format!("{kind} @{}", u32::from(endpoint)),
                    Maybe::Absent(_) => kind,
                });
                pending.extend(action.computations().rev());
            },
            _ => {},
        }
    }

    seen
}

#[test]
fn a_session_type_lowers_to_its_protocol()
{
    let source = SourceText::from(
        "def seat : ?String. mu turn. +{ report : !String. &{ next : turn, retire : end }, handoff : !Integer. end } ;\n\
         def ticker : mu t. !Integer. (t) ;\n\
         def choose : +{ ok : !Integer. end } ;\n\
         def menu : &{ get : !Integer. end, put : ?String. end } ;\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    let seat = declared_of(&module, SurfaceName::from("seat"));
    assert_eq!(
        walked(&arena, seat, &[
            Move::On,
            Move::Take("report"),
            Move::On,
            Move::Take("next"),
            Move::Take("handoff"),
            Move::On,
            Move::On,
        ]),
        [
            "?String",
            "+handoff,report",
            "!String",
            "&next,retire",
            "+handoff,report",
            "!Integer",
            "end"
        ],
        "every former reads to its own step, each payload in its own slot, and `turn` returns to its `mu`"
    );
    assert_eq!(
        walked(&arena, seat, &[
            Move::On,
            Move::Take("report"),
            Move::On,
            Move::Take("retire"),
            Move::On,
        ]),
        [
            "?String",
            "+handoff,report",
            "!String",
            "&next,retire",
            "end"
        ],
        "each branch continues at its own state"
    );
    let ticker = declared_of(&module, SurfaceName::from("ticker"));
    assert_eq!(
        walked(&arena, ticker, &[Move::On, Move::On, Move::On]),
        ["!Integer", "!Integer", "!Integer"],
        "a variable under its `mu`, parenthesised, recurs"
    );
    let choose = declared_of(&module, SurfaceName::from("choose"));
    assert_eq!(
        walked(&arena, choose, &[Move::Take("ok"), Move::On, Move::On]),
        ["+ok", "!Integer", "end"],
        "braces at the root over session types are the select"
    );
    let menu = declared_of(&module, SurfaceName::from("menu"));
    assert_eq!(
        walked(&arena, menu, &[Move::Take("put"), Move::On, Move::On]),
        ["&get,put", "?String", "end"],
        "and the lazy record over them the offer"
    );
}

#[test]
fn each_state_answers_where_it_is_written()
{
    let text = "def seat : ?String. mu turn. +{ report : !String. &{ next : turn, retire : end }, \
                handoff : !Integer. end } ;\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(text), &mut arena);
    let written = |start: usize, end: usize| text.get(start .. end).unwrap_or_default();
    let state = |ty: ValueTypeId| match arena.value_type(ty) {
        Some(&ValueType::Session(ref session)) => Some(session.state()),
        _ => None,
    };
    let mut forms: Vec<(&str, Option<_>)> = module
        .origins()
        .value_types()
        .iter()
        .filter(|&&(ty, origin)| {
            origin.provenance() == crate::origin::Provenance::Written && state(ty).is_some()
        })
        .map(|&(ty, origin)| {
            let span = origin.span();
            (
                written(usize::from(span.start()), usize::from(span.end())),
                state(ty),
            )
        })
        .collect();
    forms.sort_unstable();
    let at = |form: &str| {
        forms
            .iter()
            .find(|&&(held, _)| held == form)
            .map(|&(_, at)| at)
    };
    for continuation in [
        "mu turn. +{ report : !String. &{ next : turn, retire : end }, handoff : !Integer. end }",
        "+{ report : !String. &{ next : turn, retire : end }, handoff : !Integer. end }",
        "!String. &{ next : turn, retire : end }",
        "&{ next : turn, retire : end }",
        "!Integer. end",
        "turn",
        "end",
    ] {
        assert!(
            at(continuation).is_some(),
            "`{continuation}` answers at its own state: {forms:?}"
        );
    }
    let labels: Vec<(&str, Option<_>)> = module
        .origins()
        .labels()
        .iter()
        .filter_map(|label| match label.labelled {
            crate::origin::Labelled::ValueType { ty, .. } => Some((
                written(
                    usize::from(label.span.start()),
                    usize::from(label.span.end()),
                ),
                state(ty),
            )),
            crate::origin::Labelled::CompType { .. }
            | crate::origin::Labelled::Value(_)
            | crate::origin::Labelled::Endpoint(_)
            | crate::origin::Labelled::Branch { .. }
            | crate::origin::Labelled::Bound(_) => None,
        })
        .collect();
    let named = |label: &str| {
        labels
            .iter()
            .find(|&&(held, _)| held == label)
            .map(|&(_, at)| at)
    };
    assert_eq!(
        named("report"),
        at("!String. &{ next : turn, retire : end }"),
        "a select's label answers at the state it continues with"
    );
    assert_eq!(
        named("next"),
        at("turn"),
        "an offer's label answers at its branch's state"
    );
    assert_eq!(
        named("turn"),
        at(
            "mu turn. +{ report : !String. &{ next : turn, retire : end }, handoff : !Integer. end }"
        ),
        "a `mu`'s variable answers at the state it binds"
    );
}

#[test]
fn a_malformed_protocol_is_refused_where_it_is_written()
{
    let source = SourceText::from(
        "def spin : mu t. t ;\n\
         def nested : !Integer. mu t. mu u. !Integer. t ;\n\
         def typed : !Integer. Integer ;\n\
         def free : !Integer. t ;\n\
         def positional : !Integer. +{ end, end } ;\n\
         def twice : !Integer. &{ go : end, go : end } ;\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    let mu = FormName::from(NamedKind("mu_session_type"));
    assert_eq!(
        refusal_of(&module, SurfaceName::from("spin")),
        LoweringRefusal::OutOfFragment {
            span: spelled_within(
                source,
                SourceText::from("spin : mu t. t"),
                SourceText::from("mu t. t")
            ),
            form: mu,
            sort: FragmentSort::ValueType,
            boundary: FragmentBoundary::NonContractive,
        },
        "a `mu` whose body is its own variable is not contractive"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("nested")),
        LoweringRefusal::OutOfFragment {
            span: spelled_within(
                source,
                SourceText::from("nested : !Integer. mu t. mu u. !Integer. t"),
                SourceText::from("mu t. mu u. !Integer. t")
            ),
            form: mu,
            sort: FragmentSort::ValueType,
            boundary: FragmentBoundary::NonContractive,
        },
        "nor one whose body is a `mu`, refused at the outer one"
    );
    for (name, written, continuation) in [
        ("typed", "typed : !Integer. Integer", "Integer"),
        ("free", "free : !Integer. t", "t"),
    ] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::OutOfFragment { span, sort: FragmentSort::Continuation, boundary: FragmentBoundary::WrongSort, .. }
                    if span == spelled_within(source, SourceText::from(written), SourceText::from(continuation))
            ),
            "`{name}`: a type no `mu` binds stands where a continuation is read"
        );
    }
    assert_eq!(
        refusal_of(&module, SurfaceName::from("positional")),
        LoweringRefusal::MalformedForm {
            span: spelled_within(
                source,
                SourceText::from("positional : !Integer. +{ end,"),
                SourceText::from("end")
            ),
            form: FormName::SELECT_SESSION_TYPE,
            fault: FormFault::MisplacedTile,
        },
        "a branch with no label has nothing to select"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("twice")),
            LoweringRefusal::DuplicateDefinition { name, span, .. }
                if name == SurfaceName::from("go")
                    && span == spelled_within(source, SourceText::from("twice : !Integer. &{ go : end, go"), SourceText::from("go"))
        ),
        "a label is offered once"
    );
}

#[test]
fn the_seat_exchange_lowers_both_ends()
{
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(EXCHANGE), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("exchange")));
    assert_eq!(
        actions(&arena, tail),
        [
            "fork",
            "recv @0",
            "select report @0",
            "send @0",
            "offer @0",
            "select handoff @0",
            "send @0",
            "close @0",
            "close @0",
            "send @0",
            "offer @0",
            "recv @0",
            "close @0",
            "recv @0",
            "select next @0",
            "offer @0",
            "recv @0",
            "close @0",
            "recv @0",
            "select retire @0",
            "close @0",
        ],
        "the seat's end is the child's, the operator's the parent's, and each names its endpoint by linear index past the parameter and every receipt"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn each_endpoint_answers_at_its_action()
{
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(EXCHANGE), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("exchange")));
    let mut reached = BTreeSet::new();
    let mut pending = Vec::from([tail]);
    while let Some(next) = pending.pop() {
        match arena.computation(next) {
            Some(&Computation::Bind(first, second)) => pending.extend([second, first]),
            Some(&Computation::Lambda(under) | &Computation::Split { body: under, .. }) => {
                pending.push(under);
            },
            Some(&Computation::Session(ref action)) => {
                if let Maybe::Present(_) = action.endpoint() {
                    let _fresh = reached.insert(next);
                }
                pending.extend(action.computations());
            },
            _ => {},
        }
    }
    let labelled: Vec<(&str, ComputationId)> = module
        .origins()
        .labels()
        .iter()
        .filter_map(|label| match label.labelled {
            Labelled::Endpoint(action) => Some((
                EXCHANGE
                    .get(usize::from(label.span.start()) .. usize::from(label.span.end()))
                    .unwrap_or(""),
                action,
            )),
            Labelled::ValueType { .. }
            | Labelled::CompType { .. }
            | Labelled::Value(_)
            | Labelled::Branch { .. }
            | Labelled::Bound(_) => None,
        })
        .collect();
    assert!(
        labelled
            .iter()
            .all(|&(written, _)| written == "c" || written == "peer"),
        "each label stands at an endpoint's name: {labelled:?}"
    );
    let named: BTreeSet<ComputationId> = labelled.iter().map(|&(_, action)| action).collect();
    assert_eq!(
        (labelled.len(), &named),
        (20, &reached),
        "each of the 20 actions the body holds is named by its endpoint once, through every \
         rewrite"
    );
    // #298: each offer arm's label names the branch it takes of the offer
    // the body holds, through every rewrite.
    let branches: Vec<(&str, ComputationId, &FieldLabel)> = module
        .origins()
        .labels()
        .iter()
        .filter_map(|written| match written.labelled {
            Labelled::Branch { action, ref label } => Some((
                EXCHANGE
                    .get(usize::from(written.span.start()) .. usize::from(written.span.end()))
                    .unwrap_or(""),
                action,
                label,
            )),
            Labelled::ValueType { .. }
            | Labelled::CompType { .. }
            | Labelled::Value(_)
            | Labelled::Endpoint(_)
            | Labelled::Bound(_) => None,
        })
        .collect();
    let offered = EXCHANGE.matches(" => ").count();
    assert!(
        branches.len() == offered
            && branches.iter().all(|&(written, action, label)| {
                *label == FieldLabel::from(String::from(written))
                    && reached.contains(&action)
                    && matches!(arena.computation(action), Some(&Computation::Session(SessionAction::Offer { ref arms, .. })) if arms.contains_key(label))
            }),
        "each of the {offered} offer arms answers by its label at the offer it arms: {branches:?}"
    );
}

#[test]
fn an_action_on_no_endpoint_is_refused()
{
    let source = SourceText::from(
        "def other = 1 ;\n\
         def parameter(n : Integer) -> -F Unit { close(n) }\n\
         def literal(n : Integer) -> -F Unit { send(3, n) }\n\
         def declared(n : Integer) -> -F Unit { select(other, go) }\n\
         def unbound(n : Integer) -> -F Unit { close(missing) }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    for (name, written, subject, form) in [
        ("parameter", "close(n)", "n", FormName::IDENTIFIER),
        ("literal", "send(3, n)", "3", FormName::NUMBER),
        (
            "declared",
            "select(other, go)",
            "other",
            FormName::IDENTIFIER,
        ),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::OutOfFragment {
                span: spelled_within(source, SourceText::from(written), SourceText::from(subject)),
                form,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Endpoint,
            },
            "`{name}`: only a name a fork binds is an endpoint"
        );
    }
    assert_eq!(
        refusal_of(&module, SurfaceName::from("unbound")),
        LoweringRefusal::UnresolvedName {
            span: spelled_within(
                source,
                SourceText::from("close(missing)"),
                SourceText::from("missing")
            ),
            name: SurfaceName::from("missing"),
        },
        "a name nothing binds is unresolved"
    );
}

#[test]
fn an_offer_arm_is_one_label()
{
    let source = SourceText::from(
        "def twice(n : Integer) -> -F Unit {\n\
           fork (c : &{ go : end }) { offer(c) { go => close(c), go => close(c) } } as d ;\n\
           select(d, go);\n\
           close(d)\n\
         }\n\
         def patterned(n : Integer) -> -F Unit {\n\
           fork (c : &{ go : end }) { offer(c) { 7 => close(c) } } as d ;\n\
           select(d, go);\n\
           close(d)\n\
         }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("twice")),
            LoweringRefusal::DuplicateDefinition { name, span, .. }
                if name == SurfaceName::from("go")
                    && span == spelled_within(source, SourceText::from("go => close(c), go"), SourceText::from("go"))
        ),
        "a label is armed once"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("patterned")),
        LoweringRefusal::OutOfFragment {
            span: spelled_within(source, SourceText::from("{ 7 =>"), SourceText::from("7")),
            form: FormName::from(NamedKind("literal_pattern")),
            sort: FragmentSort::Pattern,
            boundary: FragmentBoundary::Unadmitted,
        },
        "an arm's pattern is a label"
    );
}

#[test]
fn sharing_is_reserved_by_name()
{
    let source = SourceText::from(
        "def shared(n : Integer) -> -F Unit { fork !(c : end) { close(c) } ; return unit }\n\
         def acquired(n : Integer) -> -F Unit { acquire(n) as c ; return unit }\n\
         def released(n : Integer) -> -F Unit { release(n) as c ; return unit }\n\
         def duplicated(n : Integer) -> -F Unit { fork (c : end) { close(c) } as d ; dup(d) ; close(d) }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    for (name, written, keyword, form) in [
        (
            "shared",
            "fork !(c",
            "fork",
            FormName::FORK_SHARED_STATEMENT,
        ),
        (
            "acquired",
            "acquire(n)",
            "acquire",
            FormName::ACQUIRE_STATEMENT,
        ),
        (
            "released",
            "release(n)",
            "release",
            FormName::RELEASE_STATEMENT,
        ),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::OutOfFragment {
                span: spelled_within(source, SourceText::from(written), SourceText::from(keyword)),
                form,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::Reserved,
            },
            "`{name}`: a shared session's statement is reserved by its name"
        );
    }
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("duplicated")),
            LoweringRefusal::OutOfFragment { span, form, boundary: FragmentBoundary::Reserved, .. }
                if form == FormName::from(NamedKind("dup_expression"))
                    && span == spelled_within(source, SourceText::from("; dup(d) ;"), SourceText::from("dup(d)"))
        ),
        "and so is a shared endpoint's duplication"
    );
}

#[test]
fn a_fork_an_exit_would_continue_is_declined()
{
    let source = SourceText::from(
        "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
         def joined(n : Nat) -> -F Unit {\n\
           run m <- case n { Zero => return unit, Succ(p) => { fork (c : end) { close(c) } as d ; close(d) } } ;\n\
           return m\n\
         }\n\
         def tail(n : Nat) -> -F Unit {\n\
           case n { Zero => return unit, Succ(p) => { fork (c : end) { close(c) } as d ; close(d) } }\n\
         }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    assert_eq!(
        refusal_of(&module, SurfaceName::from("joined")),
        LoweringRefusal::OutOfFragment {
            span: spelled_within(
                source,
                SourceText::from("run m <- case n { Zero => return unit, Succ(p) => { fork"),
                SourceText::from("fork")
            ),
            form: FormName::FORK_STATEMENT,
            sort: FragmentSort::Computation,
            boundary: FragmentBoundary::Unadmitted,
        },
        "the rest an exit continues would sit under the fork's parent end"
    );
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    assert!(
        matches!(
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name() == SurfaceName::from("tail"))
                .map(LoweredDeclaration::outcome),
            Some(DeclarationOutcome::Completed { .. })
        ),
        "a fork in an arm no rest continues lowers"
    );
}

#[test]
fn an_exit_commutes_through_a_fork_s_parent_and_an_offer_s_arms()
{
    let source = SourceText::from(
        "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
         def forked(n : Nat) -> -F Unit {\n\
           fork (c : end) { close(c) } as d ;\n\
           close(d) ;\n\
           run m <- case n { Zero => return unit, Succ(p) => pure unit } ;\n\
           return m\n\
         }\n\
         def forked_by_hand(n : Nat) -> -F Unit {\n\
           fork (c : end) { close(c) } as d ;\n\
           close(d) ;\n\
           case n { Zero => return unit, Succ(p) => return unit }\n\
         }\n\
         def offered(n : Nat) -> -F Unit {\n\
           fork (c : +{ go : end }) { select(c, go) ; close(c) } as d ;\n\
           offer(d) { go => { close(d) ; run m <- case n { Zero => return unit, Succ(p) => pure unit } ; return m } }\n\
         }\n\
         def offered_by_hand(n : Nat) -> -F Unit {\n\
           fork (c : +{ go : end }) { select(c, go) ; close(c) } as d ;\n\
           offer(d) { go => { close(d) ; case n { Zero => return unit, Succ(p) => return unit } } }\n\
         }\n",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    for (written, by_hand) in [("forked", "forked_by_hand"), ("offered", "offered_by_hand")] {
        assert_same_body(
            &module,
            &arena,
            (SurfaceName::from(written), SurfaceName::from(by_hand)),
        );
    }
}
