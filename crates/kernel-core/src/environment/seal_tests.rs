//! The tests of `seal` that build their fixtures with the judgement: each
//! one admits through `Environment` or reads through conversion, which stand
//! above the record, so it runs in this crate.

use alloc::collections::BTreeMap;

use gandr_kernel_strata::Level;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::SealScope;
use gandr_kernel_term::ValueType;

use crate::Environment;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::encoding::content_digest;
use crate::seal::unseal;

#[test]
fn only_a_manifest_atom_unfolds()
{
    let mut environment = Environment::new();
    for _ in 0_u8 .. 2 {
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Value, Level::zero());
            let integer = staging.arena().value_type_base(BaseType::Integer);
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                SealScope::Open,
            )
        };
        let _admitted = environment.add_decl(atom).expect("an atom admits");
    }
    let first = ConstantIndex::from(0_usize);
    let second = ConstantIndex::from(1_usize);
    let mut arena = environment.arena().clone();
    let pair = {
        let one = arena.value_type_abstract(first);
        let other = arena.value_type_abstract(second);
        arena.value_type_product(&[one, other])
    };
    assert_eq!(
        unseal(&mut arena, environment.entries(), &[], pair),
        Ok(pair),
        "outside every minting admission the type is returned as it is"
    );
    let unsealed = unseal(&mut arena, environment.entries(), &[second], pair)
        .expect("the walk reads every node");
    let integer = arena.value_type_base(BaseType::Integer);
    let sealed = arena.value_type_abstract(first);
    let expected = arena.value_type_product(&[sealed, integer]);
    assert_eq!(
        convertible_value_types(&arena, unsealed, expected),
        Convertibility::Convertible,
        "the manifest atom unfolds and the sealed one beside it is kept"
    );
}

#[test]
fn a_nested_atom_unseals_through_every_former()
{
    // `t` is sealed over the integer, and `u` over `t × t`: unsealing `u`
    // inside both admissions reaches the integer through `t`.
    let mut environment = Environment::new();
    let atom = {
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = staging.arena().value_type_base(BaseType::Integer);
        staging.abstract_type(
            LevelSignature::monomorphic(),
            kind,
            integer,
            SealScope::Open,
        )
    };
    let _t = environment.add_decl(atom).expect("t admits");
    let atom = {
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let t = staging
            .arena()
            .value_type_abstract(ConstantIndex::from(0_usize));
        let pair = staging.arena().value_type_product(&[t, t]);
        staging.abstract_type(LevelSignature::monomorphic(), kind, pair, SealScope::Open)
    };
    let _u = environment.add_decl(atom).expect("u admits over t");
    let manifest = [ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)];
    let mut arena = environment.arena().clone();
    let u = arena.value_type_abstract(ConstantIndex::from(1_usize));
    let list = arena.value_type_list(u);
    let returner = arena.comp_type_returner(list);
    let arrow = arena.comp_type_arrow(u, returner);
    let with = arena.comp_type_with(&[arrow, returner]);
    let thunk = arena.value_type_thunk(with);
    let record = arena.value_type_record(BTreeMap::from([(
        FieldLabel::from(alloc::string::String::from("f")),
        thunk,
    )]));
    let unsealed = unseal(&mut arena, environment.entries(), &manifest, record)
        .expect("the walk reads every node");
    let integer = arena.value_type_base(BaseType::Integer);
    let pair = arena.value_type_product(&[integer, integer]);
    let list = arena.value_type_list(pair);
    let returner = arena.comp_type_returner(list);
    let arrow = arena.comp_type_arrow(pair, returner);
    let with = arena.comp_type_with(&[arrow, returner]);
    let thunk = arena.value_type_thunk(with);
    let expected = arena.value_type_record(BTreeMap::from([(
        FieldLabel::from(alloc::string::String::from("f")),
        thunk,
    )]));
    assert_eq!(
        convertible_value_types(&arena, unsealed, expected),
        Convertibility::Convertible,
        "every former is rebuilt over its unsealed children"
    );
    assert!(
        matches!(arena.value_type(unsealed), Some(&ValueType::Record(_))),
        "and the root keeps its former"
    );
}

/// A child slot of a type former, numbered in the order [`build`] asks
/// for them.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Slot(usize);

/// A former's children as [`build`] asks for them: the unit type at each
/// slot, and `open` at the one slot it names.
///
/// # Specification
/// trivial.
struct Children
{
    /// The slot that holds `open`, if any.
    at: Option<Slot>,
    /// How many slots have been asked for.
    next: usize,
    /// The type the named slot holds.
    open: gandr_kernel_term::ValueTypeId,
}

impl Children
{
    /// The next slot as a value type.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &mut self,
        arena: &mut gandr_kernel_term::TermArena,
    ) -> gandr_kernel_term::ValueTypeId
    {
        let slot = Slot(self.next);
        self.next = self.next.saturating_add(1);
        if self.at == Some(slot) {
            self.open
        }
        else {
            arena.value_type_unit()
        }
    }

    /// The next slot as the returner of [`Children::value_type`]'s.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &mut self,
        arena: &mut gandr_kernel_term::TermArena,
    ) -> gandr_kernel_term::CompTypeId
    {
        let value_type = self.value_type(arena);
        arena.comp_type_returner(value_type)
    }
}

/// Every type former the unseal walk rebuilds over its children.
#[derive(Clone, Copy, Debug)]
enum Former
{
    Record,
    Product,
    Sum,
    Sigma,
    List,
    Lift,
    Staged,
    Path,
    Flow,
    Session,
    Thunk,
    Returner,
    Arrow,
    Pi,
    With,
}

/// `former` in `arena`, each child as `children` hands it out, as a value
/// type: a computation-type former under a thunk.
///
/// # Specification
/// trivial.
fn build(
    arena: &mut gandr_kernel_term::TermArena,
    former: Former,
    children: &mut Children,
) -> gandr_kernel_term::ValueTypeId
{
    let c = children;
    let unit = arena.value_unit();
    match former {
        Former::Record => {
            let fields = BTreeMap::from([
                (
                    FieldLabel::from(alloc::string::String::from("a")),
                    c.value_type(arena),
                ),
                (
                    FieldLabel::from(alloc::string::String::from("b")),
                    c.value_type(arena),
                ),
            ]);
            arena.value_type_record(fields)
        },
        Former::Product => {
            let parts = [c.value_type(arena), c.value_type(arena)];
            arena.value_type_product(&parts)
        },
        Former::Sum => {
            let parts = [c.value_type(arena), c.value_type(arena)];
            arena.value_type_sum(&parts)
        },
        Former::Sigma => {
            let (first, second) = (c.value_type(arena), c.value_type(arena));
            arena.value_type_sigma(first, second)
        },
        Former::List => {
            let element = c.value_type(arena);
            arena.value_type_list(element)
        },
        Former::Lift => {
            let inner = c.value_type(arena);
            arena.value_type_lift(inner, Level::zero())
        },
        Former::Staged => {
            let base = c.value_type(arena);
            let stage = gandr_kernel_term::Stage::At(gandr_kernel_term::StageId::from(0_usize));
            arena.value_type_staged(base, stage)
        },
        Former::Path => {
            let domain = c.value_type(arena);
            arena.value_type_path(domain, unit, unit)
        },
        Former::Flow => {
            let domain = c.value_type(arena);
            arena.value_type_flow(domain, unit, unit)
        },
        Former::Session => {
            let graph = alloc::sync::Arc::new(gandr_kernel_term::session::Graph {
                root: gandr_kernel_term::session::State(0),
                nodes: alloc::vec![gandr_kernel_term::session::Node::End],
            });
            let payloads = c.value_type(arena);
            arena.value_type_session(graph, payloads)
        },
        Former::Thunk => {
            let body = c.comp_type(arena);
            arena.value_type_thunk(body)
        },
        Former::Returner => {
            let result = c.value_type(arena);
            let returner = arena.comp_type_returner(result);
            arena.value_type_thunk(returner)
        },
        Former::Arrow => {
            let domain = c.value_type(arena);
            let codomain = c.comp_type(arena);
            let arrow = arena.comp_type_arrow(domain, codomain);
            arena.value_type_thunk(arrow)
        },
        Former::Pi => {
            let domain = c.value_type(arena);
            let codomain = c.comp_type(arena);
            let pi = arena.comp_type_pi(domain, codomain);
            arena.value_type_thunk(pi)
        },
        Former::With => {
            let components = [c.comp_type(arena), c.comp_type(arena)];
            let with = arena.comp_type_with(&components);
            arena.value_type_thunk(with)
        },
    }
}

/// Every former the walk passes is rebuilt exactly where a child
/// unsealed: a type no manifest atom reaches is returned as itself,
/// minting nothing, and an atom at any one child is unfolded there.
#[test]
fn every_former_rebuilds_exactly_where_a_child_unsealed()
{
    let mut environment = Environment::new();
    let atom = {
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = staging.arena().value_type_base(BaseType::Integer);
        staging.abstract_type(
            LevelSignature::monomorphic(),
            kind,
            integer,
            SealScope::Open,
        )
    };
    let _t = environment.add_decl(atom).expect("t admits");
    let manifest = [ConstantIndex::from(0_usize)];
    for former in [
        Former::Record,
        Former::Product,
        Former::Sum,
        Former::Sigma,
        Former::List,
        Former::Lift,
        Former::Staged,
        Former::Path,
        Former::Flow,
        Former::Session,
        Former::Thunk,
        Former::Returner,
        Former::Arrow,
        Former::Pi,
        Former::With,
    ] {
        let mut arena = environment.arena().clone();
        let sealed = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let integer = arena.value_type_base(BaseType::Integer);
        let mut closed = Children {
            at: None,
            next: 0,
            open: sealed,
        };
        let subject = build(&mut arena, former, &mut closed);
        let before = arena.watermark();
        assert_eq!(
            unseal(&mut arena, environment.entries(), &manifest, subject),
            Ok(subject),
            "no atom is under {former:?}, so it unseals to itself"
        );
        assert_eq!(
            arena.watermark(),
            before,
            "and {former:?} mints nothing on the way"
        );
        for slot in (0 .. closed.next).map(Slot) {
            let mut sealing = Children {
                at: Some(slot),
                next: 0,
                open: sealed,
            };
            let subject = build(&mut arena, former, &mut sealing);
            let mut unfolding = Children {
                at: Some(slot),
                next: 0,
                open: integer,
            };
            let expected = build(&mut arena, former, &mut unfolding);
            let unsealed = unseal(&mut arena, environment.entries(), &manifest, subject)
                .expect("the walk reads every node");
            assert_eq!(
                content_digest(&arena, AnyNode::ValueType(unsealed)),
                content_digest(&arena, AnyNode::ValueType(expected)),
                "{former:?}'s {slot:?} alone holds the atom, and it unfolds there"
            );
        }
    }
}
