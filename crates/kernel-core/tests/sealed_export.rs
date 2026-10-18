//! A sealed module's export, replayed by the kernel.
//!
//! The producing environment admits an abstract type open, the module's
//! members inside its minting admission, and closes it; the artifact carries
//! the atom's representation and the extent the environment drew. A replay
//! re-checks the members at the representation and every later declaration
//! against the atom, so the artifact's opacity is the kernel's own finding and
//! a rewritten copy fails at the declaration that broke.
//!
//! The sealed-export cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use gandr_kernel_core::Admission;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::SealExtent;
use gandr_kernel_term::SealScope;
use gandr_kernel_term::Sign;
use gandr_kernel_term::decode;
use gandr_kernel_term::encode;

/// The offset of the header's minted-atom count: past the four-byte magic
/// and the two-byte version.
const MINTED_ATOM_TABLE_COUNT_OFFSET: usize = 6;
/// The offset of the first minted-atom entry in a one-atom artifact.
const MINTED_ATOM_FIRST_ENTRY_OFFSET: usize = 7;

/// Every declaration the environment admitted, as it holds it, marked as
/// it was admitted, encoded over its arena.
///
/// # Specification
/// trivial.
fn export(environment: &Environment) -> EncodedArtifact
{
    let marked: Vec<_> = environment
        .entries()
        .iter()
        .map(|entry| {
            let mark = match entry.admission() {
                Admission::Checked => AdmissionMark::Checked,
                Admission::Unchecked => AdmissionMark::UncheckedBypass,
            };
            MarkedDeclaration::new(mark, entry.declaration().clone())
        })
        .collect();
    encode(environment.arena(), &marked)
}

/// A sealed counter: the atom `t` over the integer, `seed : t = 7` and
/// `keep : U (t → F t)`, whose provenance records the atom, then the seal.
///
/// # Specification
/// trivial.
fn sealed_counter() -> (Environment, CheckedId, CheckedId)
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
    let atom = environment.add_decl(atom).expect("the atom admits");
    let seed = {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_abstract(atom.position());
        let seven = staging
            .arena()
            .value_literal(Literal::Integer(IntegerLiteral::new(
                Sign::NonNegative,
                Magnitude::from_decimal_text(String::from("7")).expect("decimal digits"),
            )));
        staging.def(LevelSignature::monomorphic(), declared, seven)
    };
    let seed = environment
        .add_decl(seed)
        .expect("the seed checks at the representation inside the admission");
    let keep = {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let opaque = arena.value_type_abstract(atom.position());
        let returner = arena.comp_type_returner(opaque);
        let arrow = arena.comp_type_arrow(opaque, returner);
        let declared = arena.value_type_thunk(arrow);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(variable);
        let lambda = arena.computation_lambda(returned);
        let body = arena.value_thunk(lambda);
        staging.sealed_def(LevelSignature::monomorphic(), declared, body, vec![
            atom.position(),
        ])
    };
    let _keep = environment
        .add_decl(keep)
        .expect("the identity at the atom admits");
    let extent = environment.seal(atom).expect("the atom seals");
    assert_eq!(extent, SealExtent::from(2_usize), "after its two members");
    (environment, atom, seed)
}

/// The sealed counter with a client after the seal: `use : t = seed`.
///
/// # Specification
/// trivial.
fn sealed_counter_with_a_client() -> Environment
{
    let (mut environment, atom, seed) = sealed_counter();
    let client = {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_abstract(atom.position());
        let body = staging.arena().value_constant(seed.position());
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    let _client = environment
        .add_decl(client)
        .expect("a client reads the member at the atom");
    environment
}

#[test]
fn the_export_of_a_sealed_module_replays()
{
    let environment = sealed_counter_with_a_client();
    let bytes = export(&environment);
    let artifact = decode(bytes.as_image()).expect("the export decodes");
    let atoms: Vec<(usize, SealScope)> = artifact
        .declarations()
        .iter()
        .enumerate()
        .filter_map(|(position, marked)| match *marked.declaration().content() {
            DeclarationContent::AbstractType { scope, .. } => Some((position, scope)),
            DeclarationContent::Def { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::Data { .. } => None,
        })
        .collect();
    assert_eq!(
        atoms,
        vec![(0, SealScope::Closed(SealExtent::from(2_usize)))],
        "one abstract type, ahead of the members, holding the two members and not the client"
    );
    let replayed = Environment::replay(artifact.arena().clone(), artifact.declarations())
        .expect("the kernel re-admits the sealed module and its client");
    assert_eq!(replayed.entries().len(), 4);

    // The copy whose client reads the atom at its representation: the
    // client's declared type swapped for the integer.
    let mut arena = artifact.arena().clone();
    let mut tampered = artifact.declarations().to_vec();
    let client = tampered.last().expect("the client").declaration().clone();
    let DeclarationContent::Def { body, .. } = *client.content()
    else {
        panic!("the client is a definition");
    };
    let integer = arena.value_type_base(BaseType::Integer);
    let leaked =
        DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), integer, body);
    if let Some(last) = tampered.last_mut() {
        *last = MarkedDeclaration::new(AdmissionMark::Checked, leaked);
    }
    let refusal = Environment::replay(arena, &tampered)
        .expect_err("the representation does not leak past the seal");
    assert_eq!(refusal.position(), ConstantIndex::from(3_usize));
    assert!(
        matches!(refusal.error(), KernelError::ValueTypeMismatch(_)),
        "the client is refused as a type mismatch: {refusal:?}"
    );
}

#[test]
fn a_sealed_artifact_round_trips_and_re_mints_deterministically()
{
    let (environment, _atom, _seed) = sealed_counter();
    let bytes = export(&environment);
    let artifact = decode(bytes.as_image()).expect("a genuine sealed artifact decodes");
    let replayed = Environment::replay(artifact.arena().clone(), artifact.declarations())
        .expect("and replays");
    assert_eq!(
        Vec::from(export(&replayed)),
        Vec::from(bytes.clone()),
        "replay re-mints every atom to its recorded position and closes it where it closed"
    );
    let image = Vec::from(bytes);
    assert_eq!(
        image.get(MINTED_ATOM_TABLE_COUNT_OFFSET),
        Some(&1),
        "the header records exactly one minted atom"
    );
    assert_eq!(
        image.get(MINTED_ATOM_FIRST_ENTRY_OFFSET),
        Some(&0),
        "and it sits at admission position zero"
    );
}

#[test]
fn an_atom_downgraded_to_an_axiom_fails_to_replay()
{
    let (environment, _atom, _seed) = sealed_counter();
    let artifact = decode(export(&environment).as_image()).expect("the export decodes");
    let mut arena = artifact.arena().clone();
    let mut downgraded = artifact.declarations().to_vec();
    let kind = downgraded
        .first()
        .expect("the atom")
        .declaration()
        .declared_id();
    let axiom = DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), kind);
    if let Some(first) = downgraded.first_mut() {
        *first = MarkedDeclaration::new(AdmissionMark::Checked, axiom);
    }
    let rewritten = encode(&arena, &downgraded);
    let decoded = decode(rewritten.as_image())
        .expect("the rewritten artifact is well formed on the format plane");
    let refusal = Environment::replay(decoded.arena().clone(), decoded.declarations())
        .expect_err("but the member typed at the downgraded position does not re-admit");
    assert_eq!(refusal.position(), ConstantIndex::from(1_usize));
    assert_eq!(
        refusal.error(),
        &KernelError::NotAnAbstractType {
            index: ConstantIndex::from(0_usize)
        },
        "being an atom is resolved against the environment, not asserted by the reference"
    );
}

#[test]
fn sealing_provenance_round_trips_and_cannot_be_rewritten()
{
    let (environment, _atom, _seed) = sealed_counter();
    let bytes = export(&environment);
    let artifact = decode(bytes.as_image()).expect("the sealed artifact decodes");
    let replayed = Environment::replay(artifact.arena().clone(), artifact.declarations())
        .expect("the sealed artifact replays");
    assert_eq!(
        Vec::from(export(&replayed)),
        Vec::from(bytes.clone()),
        "the replayed environment re-serializes its provenance identically"
    );
    // The last segment is the identity member, ending `… | erasure 0 |
    // modes 0 | provenance 1, 0 | directedness 0`, so its provenance entry
    // is the artifact's second-to-last byte. Re-point it at position 1 —
    // the seed — which the member's declared type does not project onto.
    let mut rewritten = Vec::from(bytes);
    let entry = rewritten.len().saturating_sub(2);
    let slot = rewritten.get_mut(entry).expect("the provenance entry");
    assert_eq!(
        *slot, 0,
        "the provenance entry names the atom at position zero"
    );
    *slot = 1;
    let decoded = decode(gandr_kernel_term::ArtifactImage::from(rewritten.as_slice()))
        .expect("the provenance slot is well formed on the format plane");
    let refusal = Environment::replay(decoded.arena().clone(), decoded.declarations())
        .expect_err("a rewritten provenance is refused at the choke point");
    assert_eq!(
        refusal.error(),
        &KernelError::SealingProvenanceNotProjected {
            atom: ConstantIndex::from(1_usize)
        }
    );
}
