use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;

use super::DefinitionChain;
use super::DefinitionEntry;
use super::DefinitionError;
use super::DefinitionHeight;
use super::DefinitionalEnvironment;
use super::ScopeId;
use super::Transparency;

#[test]
fn heights_rise_one_above_the_tallest_mention()
{
    let mut chain = DefinitionChain::new();
    let ground = chain.define(
        ConstantIndex::from(0_usize),
        GlobalIndex::from(0_u32),
        Transparency::Manifest,
        &[],
    );
    assert_eq!(
        Ok(DefinitionHeight::from(1_u32)),
        ground,
        "a definition mentioning nothing still unfolds once, so it is one above the floor"
    );
    let short = chain.define(
        ConstantIndex::from(1_usize),
        GlobalIndex::from(1_u32),
        Transparency::Manifest,
        &[ConstantIndex::from(0_usize)],
    );
    assert_eq!(
        Ok(DefinitionHeight::from(2_u32)),
        short,
        "one above the definition it mentions"
    );
    let tall = chain.define(
        ConstantIndex::from(2_usize),
        GlobalIndex::from(2_u32),
        Transparency::Manifest,
        &[ConstantIndex::from(1_usize)],
    );
    assert_eq!(Ok(DefinitionHeight::from(3_u32)), tall);
    let joined = chain.define(
        ConstantIndex::from(3_usize),
        GlobalIndex::from(3_u32),
        Transparency::Manifest,
        &[ConstantIndex::from(0_usize), ConstantIndex::from(2_usize)],
    );
    assert_eq!(
        Ok(DefinitionHeight::from(4_u32)),
        joined,
        "the maximum decides, not the first or the last mention"
    );
    let axiomatic = chain.define(
        ConstantIndex::from(5_usize),
        GlobalIndex::from(4_u32),
        Transparency::Opaque,
        &[ConstantIndex::from(4_usize)],
    );
    assert_eq!(
        Ok(DefinitionHeight::from(1_u32)),
        axiomatic,
        "a mention with no body — an axiom — sits on the floor and raises nothing, so \
             a definition over axioms alone is one above it like any other leaf definition"
    );
    assert!(
        chain
            .entries()
            .iter()
            .all(|entry| entry.height() > DefinitionHeight::default()),
        "no entry of the chain sits on the floor: the floor names what cannot unfold"
    );
}

#[test]
fn a_definition_out_of_admission_order_is_refused()
{
    let mut chain = DefinitionChain::new();
    let defined = chain.define(
        ConstantIndex::from(4_usize),
        GlobalIndex::from(0_u32),
        Transparency::Manifest,
        &[],
    );
    assert!(defined.is_ok());
    assert_eq!(
        Err(DefinitionError::AlreadyDefined {
            constant: ConstantIndex::from(4_usize)
        }),
        chain.define(
            ConstantIndex::from(4_usize),
            GlobalIndex::from(1_u32),
            Transparency::Manifest,
            &[]
        ),
        "the same position twice is refused by name"
    );
    assert_eq!(
        Err(DefinitionError::OutOfAdmissionOrder {
            constant: ConstantIndex::from(3_usize),
            latest: ConstantIndex::from(4_usize),
        }),
        chain.define(
            ConstantIndex::from(3_usize),
            GlobalIndex::from(1_u32),
            Transparency::Manifest,
            &[]
        ),
        "a position below the chain's last would break the one-pass height computation"
    );
    let later = chain.define(
        ConstantIndex::from(6_usize),
        GlobalIndex::from(2_u32),
        Transparency::Manifest,
        &[],
    );
    assert!(later.is_ok());
    assert_eq!(
        Err(DefinitionError::AlreadyDefined {
            constant: ConstantIndex::from(4_usize)
        }),
        chain.define(
            ConstantIndex::from(4_usize),
            GlobalIndex::from(3_u32),
            Transparency::Manifest,
            &[]
        ),
        "a position already in the chain is refused as a duplicate, not as an ordering \
             fault, however far back it sits"
    );
    assert_eq!(
        2_usize,
        chain.entries().len(),
        "a refused definition is not half-recorded"
    );
}

#[test]
fn a_forward_mention_is_refused()
{
    let mut chain = DefinitionChain::new();
    assert_eq!(
        Err(DefinitionError::ForwardReference {
            constant: ConstantIndex::from(1_usize),
            mention: ConstantIndex::from(1_usize),
        }),
        chain.define(
            ConstantIndex::from(1_usize),
            GlobalIndex::from(0_u32),
            Transparency::Manifest,
            &[ConstantIndex::from(1_usize)]
        ),
        "a body mentioning its own position is refused"
    );
    assert_eq!(
        Err(DefinitionError::ForwardReference {
            constant: ConstantIndex::from(1_usize),
            mention: ConstantIndex::from(2_usize),
        }),
        chain.define(
            ConstantIndex::from(1_usize),
            GlobalIndex::from(0_u32),
            Transparency::Manifest,
            &[ConstantIndex::from(2_usize)]
        ),
        "a body mentioning a later position is refused"
    );
    assert!(
        chain.entries().is_empty(),
        "neither refusal recorded anything"
    );
}

#[test]
fn a_chain_resolves_only_the_positions_it_holds()
{
    let mut chain = DefinitionChain::new();
    let recorded = [
        (ConstantIndex::from(0_usize), GlobalIndex::from(10_u32)),
        (ConstantIndex::from(2_usize), GlobalIndex::from(11_u32)),
        (ConstantIndex::from(4_usize), GlobalIndex::from(12_u32)),
    ];
    for (position, index) in recorded {
        let defined = chain.define(position, index, Transparency::Manifest, &[]);
        assert!(defined.is_ok());
    }
    for (position, index) in recorded {
        assert_eq!(
            Some(index),
            chain.entry(position).map(DefinitionEntry::body),
            "each recorded position resolves to its own body"
        );
    }
    assert!(
        chain.entry(ConstantIndex::from(1_usize)).is_none(),
        "a gap between two entries holds nothing"
    );
    assert!(
        chain.entry(ConstantIndex::from(9_usize)).is_none(),
        "a position past the chain holds nothing"
    );
}

#[test]
fn a_chain_carries_no_arena_and_clones_flat()
{
    let mut chain = DefinitionChain::new();
    let defined = chain.define(
        ConstantIndex::from(0_usize),
        GlobalIndex::from(7_u32),
        Transparency::Manifest,
        &[],
    );
    assert!(defined.is_ok());
    let copied = chain.clone();
    assert_eq!(chain, copied, "the clone is the chain");
    assert_eq!(
        chain
            .entry(ConstantIndex::from(0_usize))
            .map(DefinitionEntry::body),
        copied
            .entry(ConstantIndex::from(0_usize))
            .map(DefinitionEntry::body),
        "a content id means the same thing in the copy, because it names a canonical \
             table entry rather than a node"
    );
}

#[test]
fn a_scope_inherits_until_it_seals()
{
    let mut environment = DefinitionalEnvironment::new();
    let root = environment.root();
    let inner = environment.open_scope(root).expect("the root resolves");
    assert_eq!(
        Ok(Transparency::Manifest),
        environment.transparency(inner, ConstantIndex::from(0_usize), Transparency::Manifest),
        "a scope that states nothing answers with the declaration's own stance"
    );
    let sealed = environment.state(root, ConstantIndex::from(0_usize), Transparency::Opaque);
    assert_eq!(Ok(()), sealed);
    assert_eq!(
        Ok(Transparency::Opaque),
        environment.transparency(inner, ConstantIndex::from(0_usize), Transparency::Manifest),
        "an enclosing seal reaches the scopes beneath it"
    );
    assert_eq!(
        Ok(Transparency::Manifest),
        environment.transparency(inner, ConstantIndex::from(1_usize), Transparency::Manifest),
        "and it reaches only the definition it named"
    );
}

#[test]
fn an_inner_scope_reopens_what_its_parent_sealed()
{
    let mut environment = DefinitionalEnvironment::new();
    let root = environment.root();
    let inner = environment.open_scope(root).expect("the root resolves");
    let deeper = environment
        .open_scope(inner)
        .expect("the inner scope resolves");
    let sealed = environment.state(root, ConstantIndex::from(0_usize), Transparency::Opaque);
    assert_eq!(Ok(()), sealed);
    let reopened = environment.state(inner, ConstantIndex::from(0_usize), Transparency::Manifest);
    assert_eq!(Ok(()), reopened);
    assert_eq!(
        Ok(Transparency::Manifest),
        environment.transparency(deeper, ConstantIndex::from(0_usize), Transparency::Opaque),
        "the innermost statement wins, two scopes down"
    );
    assert_eq!(
        Ok(Transparency::Opaque),
        environment.transparency(root, ConstantIndex::from(0_usize), Transparency::Manifest),
        "and the outer scope still reads its own seal"
    );
}

#[test]
fn restating_a_stance_replaces_it()
{
    let mut environment = DefinitionalEnvironment::new();
    let root = environment.root();
    let sealed = environment.state(root, ConstantIndex::from(0_usize), Transparency::Opaque);
    assert_eq!(Ok(()), sealed);
    let reopened = environment.state(root, ConstantIndex::from(0_usize), Transparency::Manifest);
    assert_eq!(Ok(()), reopened);
    assert_eq!(
        Ok(Transparency::Manifest),
        environment.transparency(root, ConstantIndex::from(0_usize), Transparency::Opaque),
        "a scope states one stance per definition, not a stack of them"
    );
}

#[test]
fn an_unknown_scope_is_refused()
{
    let mut environment = DefinitionalEnvironment::new();
    let absent = ScopeId::from(7_usize);
    assert_eq!(
        Err(DefinitionError::UnknownScope { scope: absent }),
        environment.open_scope(absent)
    );
    assert_eq!(
        Err(DefinitionError::UnknownScope { scope: absent }),
        environment.state(absent, ConstantIndex::from(0_usize), Transparency::Opaque)
    );
    assert_eq!(
        Err(DefinitionError::UnknownScope { scope: absent }),
        environment.transparency(absent, ConstantIndex::from(0_usize), Transparency::Opaque)
    );
}
