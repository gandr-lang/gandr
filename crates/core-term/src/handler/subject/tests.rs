use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::RuleIndex;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;

use super::Answer;
use super::SubjectRule;
use super::Written;
use super::normalize;
use super::subject_rule;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::effect::EffectName;
use crate::effect::EffectOp;
use crate::effect::EffectSig;
use crate::effect::OperationName;
use crate::handler::Arity;
use crate::syntax::ComponentCount;
use crate::syntax::Computation;
use crate::syntax::Value;
use crate::syntax::Zone;

/// State's arities: `get` sends nothing and is replied one value, `put`
/// sends one value and is replied nothing.
///
/// # Specification
/// trivial.
fn state(name: &Name) -> Option<Arity>
{
    let count = ComponentCount::from;
    match name.as_ref() {
        "get" => Some(Arity {
            payload: count(0),
            reply: count(1),
        }),
        "put" => Some(Arity {
            payload: count(1),
            reply: count(0),
        }),
        _ => None,
    }
}

/// `get(bind x . rest)`.
///
/// # Specification
/// trivial.
fn get<N>(
    x: N,
    rest: FreeTerm,
) -> FreeTerm
where
    N: Into<Name>,
{
    FreeTerm::op("get", [FreeTerm::lam(x, rest)])
}

/// `put(s, rest)`, `s` a metavariable.
///
/// # Specification
/// trivial.
fn put<N>(
    s: N,
    rest: FreeTerm,
) -> FreeTerm
where
    N: Into<Name>,
{
    FreeTerm::op("put", [FreeTerm::var(s), rest])
}

/// `k` instantiated at the bound variables `at`.
///
/// # Specification
/// trivial.
fn k<Bound>(at: Bound) -> FreeTerm
where
    Bound: IntoIterator,
    Bound::Item: Into<Name>,
{
    FreeTerm::inst("k", at.into_iter().map(FreeTerm::bound))
}

/// Get-get, put-get and put-put, State's laws, each as written.
///
/// # Specification
/// trivial.
fn laws() -> [(FreeTerm, FreeTerm); 3]
{
    [
        (get("s", get("t", k(["s", "t"]))), get("s", k(["s", "s"]))),
        (
            put("s", get("t", k(["t"]))),
            put("s", FreeTerm::inst("k", [FreeTerm::var("s")])),
        ),
        (
            put("s", put("u", FreeTerm::var("k"))),
            put("u", FreeTerm::var("k")),
        ),
    ]
}

/// State's laws read as rewrites of a subject.
///
/// # Specification
/// trivial.
fn rules() -> Vec<SubjectRule>
{
    laws()
        .iter()
        .enumerate()
        .map(|(place, &(ref left, ref right))| {
            subject_rule(RuleIndex::from(place), (left, right), state)
                .unwrap_or_else(|| panic!("law {place} reads as a rewrite"))
        })
        .collect()
}

/// State's laws read as rewrites: get-get keeps its first get and answers the
/// second the first's reply, put-get keeps its put and answers the get the
/// put's payload, and put-put answers its first put the unit and keeps the
/// second (#2272).
#[test]
fn state_s_laws_read_as_rewrites_of_a_subject_2272()
{
    let [get_get, put_get, put_put] = <[SubjectRule; 3]>::try_from(rules())
        .unwrap_or_else(|rules| panic!("three rules: {rules:?}"));
    assert_eq!(get_get.answers, [Answer::Kept, Answer::Reply(0)]);
    assert_eq!(get_get.metas, 0);
    assert_eq!(put_get.answers, [Answer::Kept, Answer::Meta(0)]);
    assert_eq!(
        put_get
            .requests
            .first()
            .map(|request| request.payload.clone()),
        Some(Vec::from([Written::Meta(0)])),
        "the put sends its metavariable"
    );
    assert_eq!(put_put.answers, [Answer::Unit, Answer::Kept]);
    assert_eq!(put_put.metas, 2, "`s` and `u`");
    assert_eq!(
        put_put.rule(),
        RuleIndex::from(2_usize),
        "each rule keeps its place"
    );
}

/// A law no subject rewrite reads is none: one growing, one reordering its
/// requests, one dropping a reply its right side gives no value, one naming a
/// metavariable twice on its left, and one over an undeclared operation
/// (#2272).
#[test]
fn a_law_no_rewrite_reads_is_none_2272()
{
    let [(get_left, get_right), ..] = laws();
    let none = [
        ("growing", (get_right, get_left)),
        (
            "reordering",
            (put("s", get("t", k(["t"]))), get("t", put("s", k(["t"])))),
        ),
        (
            "dropping a reply it gives no value",
            (get("s", put("u", FreeTerm::var("k"))), FreeTerm::var("k")),
        ),
        (
            "naming a metavariable twice",
            (
                put("s", put("s", FreeTerm::var("k"))),
                put("s", FreeTerm::var("k")),
            ),
        ),
        (
            "over an undeclared operation",
            (
                FreeTerm::op("stop", [FreeTerm::var("k")]),
                FreeTerm::var("k"),
            ),
        ),
    ];
    for (name, (left, right)) in none {
        assert_eq!(
            subject_rule(RuleIndex::from(0_usize), (&left, &right), state),
            None,
            "a law {name} rewrites no subject"
        );
    }
}

/// The indices of the variables a built subject returns as a tuple.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Returning(&'static [u32]);

/// A subject over a State capability at its innermost binder, built step by
/// step.
///
/// # Specification
/// trivial.
struct Subject
{
    /// The arena the subject is minted into.
    arena: CoreArena,
    /// State's signature at an integer state.
    signature: EffectSig,
}

/// One step of a subject: a request of the capability at its index, or a
/// return of a value.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Step
{
    /// `x ← c.get()`, `c` at this index.
    Get(u32),
    /// `x ← c.put(v); split x {}`, `c` and the variable sent at these indices.
    Put(u32, u32),
    /// `x ← c.put(v); split x {}` sending the value `return ()` returns, a
    /// computation standing where a value is read, `c` at this index.
    PutComputed(u32),
    /// `x ← return ()`.
    Unit,
    /// `x ← force #0`, a step no rule reads past.
    Opaque,
}

impl Subject
{
    /// An empty arena and State's signature.
    ///
    /// # Specification
    /// trivial.
    fn new() -> Self
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_type_unit();
        let signature = EffectSig::new(EffectName::from("State"), [
            EffectOp {
                name: "get".into(),
                payload: unit,
                reply: integer,
            },
            EffectOp {
                name: "put".into(),
                payload: integer,
                reply: unit,
            },
        ])
        .unwrap_or_else(|conflict| panic!("State's two operations: {conflict:?}"));
        Self { arena, signature }
    }

    /// The variable at `index`.
    ///
    /// # Specification
    /// trivial.
    fn variable<Index>(
        &mut self,
        index: Index,
    ) -> ValueId
    where
        DeBruijnIndex: From<Index>,
    {
        self.arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    }

    /// The subject making `steps` in order, then returning the variables at
    /// `result`'s indices as a tuple.
    ///
    /// # Specification
    /// trivial.
    fn build(
        &mut self,
        steps: &[Step],
        Returning(result): Returning,
    ) -> ComputationId
    {
        let members: Vec<ValueId> = result.iter().map(|&index| self.variable(index)).collect();
        let tuple = self.arena.value_tuple(&members);
        let mut rest = self.arena.computation_return(tuple);
        for &step in steps.iter().rev() {
            let bound = match step {
                Step::Get(capability) => {
                    let capability = self.variable(capability);
                    let unit = self.arena.value_unit();
                    self.arena.computation_exercise(
                        capability,
                        self.signature.clone(),
                        OperationName::from("get"),
                        unit,
                    )
                },
                Step::Put(capability, sent) => {
                    let capability = self.variable(capability);
                    let sent = self.variable(sent);
                    let replied = self.variable(0_u32);
                    rest =
                        self.arena
                            .computation_split(replied, ComponentCount::from(0_usize), rest);
                    self.arena.computation_exercise(
                        capability,
                        self.signature.clone(),
                        OperationName::from("put"),
                        sent,
                    )
                },
                Step::PutComputed(capability) => {
                    let capability = self.variable(capability);
                    let unit = self.arena.value_unit();
                    let computed = self.arena.computation_return(unit);
                    let sent = self.arena.value_returned(computed);
                    let replied = self.variable(0_u32);
                    rest =
                        self.arena
                            .computation_split(replied, ComponentCount::from(0_usize), rest);
                    self.arena.computation_exercise(
                        capability,
                        self.signature.clone(),
                        OperationName::from("put"),
                        sent,
                    )
                },
                Step::Unit => {
                    let unit = self.arena.value_unit();
                    self.arena.computation_return(unit)
                },
                Step::Opaque => {
                    let forced = self.variable(0_u32);
                    self.arena.computation_force(forced)
                },
            };
            rest = self.arena.computation_bind(bound, rest);
        }
        rest
    }

    /// Each step `subject` binds along its spine, read back: an exercise by
    /// its operation, a return by its value, a bind of a return by both, and
    /// anything else by its debug reading.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &self,
        subject: ComputationId,
    ) -> Vec<String>
    {
        let mut read = Vec::new();
        let mut current = subject;
        loop {
            match self.arena.computation(current) {
                Some(&Computation::Bind(bound, rest)) => {
                    read.push(self.step(bound));
                    current = rest;
                },
                Some(&Computation::Split { body, .. }) => current = body,
                _ => return read,
            }
        }
    }

    /// One bound computation read back, its binds' parts joined by `; `.
    ///
    /// # Specification
    /// trivial.
    fn step(
        &self,
        bound: ComputationId,
    ) -> String
    {
        let mut read: Vec<String> = Vec::new();
        let mut pending = Vec::from([bound]);
        while let Some(next) = pending.pop() {
            match self.arena.computation(next) {
                Some(&Computation::Exercise { ref operation, .. }) => {
                    read.push(String::from(operation.as_ref()));
                },
                Some(&Computation::Ascribe { body, .. }) => pending.push(body),
                Some(&Computation::Return(value)) => {
                    read.push(format!("return {}", self.value(value)));
                },
                Some(&Computation::Bind(sent, returned)) => pending.extend([returned, sent]),
                other => read.push(format!("{other:?}")),
            }
        }
        read.join("; ")
    }

    /// One value read back: a variable by its index, the unit as `()`, a
    /// literal by its debug reading.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &self,
        value: ValueId,
    ) -> String
    {
        match self.arena.value(value) {
            Some(&Value::Variable { index, .. }) => format!("#{}", u32::from(index)),
            Some(&Value::Tuple(ref members)) if members.is_empty() => String::from("()"),
            other => format!("{other:?}"),
        }
    }
}

/// Two gets of one capability normalise to one, the second's binder bound to
/// the first's reply, and three to one, each later get bound to the first's
/// reply past the returns before it; the result reads the same binders
/// (#2272).
#[test]
fn two_gets_normalise_to_one_2272()
{
    let rules = rules();
    let mut subject = Subject::new();
    // c at #0: a ← c.get(); b ← c.get(); return (a, b).
    let two = subject.build(&[Step::Get(0), Step::Get(1)], Returning(&[1, 0]));
    let mut carried = Vec::new();
    let normal = normalize(&mut subject.arena, two, &rules, &mut carried);
    assert_eq!(subject.read(normal), ["get", "return #0"]);
    assert!(!carried.is_empty(), "every rebuilt step is reported");
    let Some(&Computation::Bind(_, rest)) = subject.arena.computation(normal)
    else {
        panic!("the normal form binds its get");
    };
    let Some(&Computation::Bind(answered, tail)) = subject.arena.computation(rest)
    else {
        panic!("and the return in the second's place");
    };
    assert!(
        matches!(subject.arena.computation(answered), Some(&Computation::Ascribe { body, .. })
            if matches!(subject.arena.computation(body), Some(Computation::Return(_)))),
        "the return is ascribed the reply's type: {:?}",
        subject.arena.computation(answered)
    );
    let Some(&Computation::Bind(.., original)) = subject.arena.computation(two).and_then(|first| {
        let &Computation::Bind(_, rest) = first
        else {
            panic!("the subject is a bind: {first:?}");
        };
        subject.arena.computation(rest)
    })
    else {
        panic!("the subject binds two gets");
    };
    assert_eq!(tail, original, "the rest of the subject is untouched");
    // c at #0: three gets.
    let three = subject.build(
        &[Step::Get(0), Step::Get(1), Step::Get(2)],
        Returning(&[2, 1, 0]),
    );
    let normal = normalize(&mut subject.arena, three, &rules, &mut Vec::new());
    assert_eq!(subject.read(normal), ["get", "return #0", "return #1"]);
}

/// State's laws normalise a spine: a put then a get to the put, the get
/// answered the stored value raised past the put's binder; two puts to the
/// second, the first's value bound before the unit is returned in its place
/// (#2272).
#[test]
fn state_s_laws_normalise_a_spine_2272()
{
    let rules = rules();
    let mut subject = Subject::new();
    // c at #0, x at #1: c.put(x); a ← c.get(); return a.
    let put_get = subject.build(&[Step::Put(0, 1), Step::Get(1)], Returning(&[0]));
    let normal = normalize(&mut subject.arena, put_get, &rules, &mut Vec::new());
    assert_eq!(subject.read(normal), ["put", "return #2"]);
    // c at #0, x at #1: c.put(x); c.put(x); return ().
    let put_put = subject.build(&[Step::Put(0, 1), Step::Put(1, 2)], Returning(&[]));
    let normal = normalize(&mut subject.arena, put_put, &rules, &mut Vec::new());
    assert_eq!(subject.read(normal), ["return #1; return ()", "put"]);
}

/// A run no rule instantiates stays: gets of two capabilities, a get behind a
/// step that is no return, a put whose value names the reply of the put
/// before it, and a get after a put whose value a computation returns, which
/// answering the get would run twice; a get behind a returned unit still
/// normalises (#2272).
#[test]
fn a_run_no_rule_instantiates_stays_2272()
{
    let rules = rules();
    let mut subject = Subject::new();
    // c at #0, d at #1: a ← c.get(); b ← d.get(), d at #2 there.
    let apart = subject.build(&[Step::Get(0), Step::Get(2)], Returning(&[1, 0]));
    let opaque = subject.build(
        &[Step::Get(0), Step::Opaque, Step::Get(2)],
        Returning(&[2, 0]),
    );
    // c at #0: u ← c.put(c); c.put(u), the second's value the first's reply.
    let naming = subject.build(&[Step::Put(0, 0), Step::Put(1, 0)], Returning(&[]));
    let computed = subject.build(&[Step::PutComputed(0), Step::Get(1)], Returning(&[0]));
    for (name, unchanged) in [
        ("apart", apart),
        ("opaque", opaque),
        ("naming", naming),
        ("computed", computed),
    ] {
        let mut carried = Vec::new();
        assert_eq!(
            normalize(&mut subject.arena, unchanged, &rules, &mut carried),
            unchanged,
            "{name} stays"
        );
        assert!(carried.is_empty(), "{name} reports nothing");
    }
    let behind = subject.build(
        &[Step::Get(0), Step::Unit, Step::Get(2)],
        Returning(&[2, 0]),
    );
    let normal = normalize(&mut subject.arena, behind, &rules, &mut Vec::new());
    assert_eq!(subject.read(normal), ["get", "return ()", "return #1"]);
}
