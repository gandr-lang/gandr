//! A site and a manifold, read from their files.
//!
//! A deployment binds a program's worlds to places and never enters the
//! program's identity. Its two files are gandr, each read as a workspace's
//! `members` is: checked alone over what it imports, then run. A site's file
//! declares `module Site : Model(Site)` of `std.manifold`, the key one place
//! proves, the sockets it is reached at, and the name of the secret proving
//! the key. A manifold's file declares `module Manifold : Model(Manifold)`, the
//! program it deploys, beside `pub def placements : List(Placement)`, each
//! world of the program placed at a site's model the manifold imports.
//! [`Site::read`] and [`Manifold::read`] read them into exactly what the
//! driver's `--net-bind` and `--world` flags build: the sockets a host binds
//! and the key it proves, and the [`WorldBindings`] a run ships by.
//!
//! # Judging a deployment
//!
//! A world written `world far requires [Console, store : Store with sort V =
//! String] ;` states, as a row, what a role placed at it needs of its site;
//! the site's file answers with a row of its own, `offers [Console, store =
//! Echo] ;`. [`Manifold::judged`] reads the program a manifold deploys before
//! any process starts: each placement names a world the program declares, and
//! each requiring world's site, found among the manifold's imports by its key,
//! answers its row entry by entry. A label is answered by the module the
//! offer binds to it, judged as the checker judges a functor's argument: the
//! program's own text, with the module imported and a functor over
//! `Model(Store) with sort V = String` applied to it, settles or names the type
//! the module holds instead. A host interface is answered when the offer lists
//! it and the site's `Authority` attenuates to its operations, judged in the
//! site's own text.
//!
//! # Boundaries
//!
//! - **The program by path.** A manifold names the program it deploys by its
//!   source's path, read from the manifold's own directory, and a run or a host
//!   of another source is refused. A located program's items have no content
//!   key yet, so no address names the program.
//! - **One process per world.** A placement counting other than one instance is
//!   refused by name.
//! - **A site's secret stays with its host.** The file names the secret, never
//!   its value. [`Site::secret`] reads the value where the host stands: from
//!   the `Secrets` model of `std.secret` a host's own file declares, or from
//!   the variable [`Site::variable`] names. A run never holds it: the model
//!   answers a sealed `Secret.T`, which never crosses to a world and prints
//!   opaque.
//! - **The module by its bare name.** The judgement imports each module the
//!   offer names by its name, because a functor applies a module by its name
//!   alone; a program declaring a module of one of those names is refused there
//!   as a clash, not as an offer the site lacks.
//! - **The check alone judges.** `gandr check` of a manifold judges its
//!   deployment; `gandr run --manifold` reads the bindings without it, and the
//!   offer is not yet the far world's authority (#3546).
//!
//! # References
//!
//! - `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — lineage: the compilation
//!   ruling, § compilation-recipe-refinements: a deployment binds roles to
//!   world keys, instance counts and discovery, and never enters an artifact's
//!   identity.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::fmt::Write as _;
use core::net::SocketAddr;
use core::str::FromStr as _;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::effect::host::HostSignatures;
use gandr_core_term::effect::host::declared;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_net::Lookup;
use gandr_runtime_net::NodeId;
use gandr_runtime_net::Peer;
use gandr_runtime_net::PeerError;
use gandr_runtime_net::Secret;
use gandr_runtime_net::WorldName;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::SettleReport;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::decode_escapes;
use gandr_surface_lowering::labelled;
use gandr_surface_lowering::requirement;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::compose::Composed;
use crate::entry::entries;
use crate::evaluate::Program;
use crate::evaluate::WorldBindings;
use crate::evaluate::declaration_name;
use crate::report::Goals;
use crate::report::Verb;
use crate::walk::Step;
use crate::workspace::Answered;
use crate::workspace::Spelling;
use crate::workspace::Unran;
use crate::workspace::answered_alone;
use crate::workspace::lowered_alone;
use crate::workspace::ran_alone;
use crate::workspace::sources_alone;
use crate::workspace::stepped_alone;

/// The prefix of the variable a site's secret is read from when no model is
/// given; the secret's name, spelled for the environment, follows it.
const SECRET_VARIABLE: &str = "GANDR_SECRET_";

/// One place a world runs at, as its file's `Site` model states it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Site
{
    /// The key the site proves.
    key: NodeId,
    /// The sockets it binds and is dialled at; none when it is found by its
    /// key alone.
    sockets: Vec<SocketAddr>,
    /// The name of the secret proving the key.
    secret: String,
}

impl Site
{
    /// The site the file at `file` states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the file checked alone over what it imports, and its
    ///   `Site.key`, `Site.sockets` and `Site.secret` run: the key read as 64
    ///   hexadecimal digits, each `,`-separated entry of the sockets, blank
    ///   entries skipped, read as `ip:port`, and the secret's name kept as
    ///   written.
    /// - provides: the place `gandr host --site` binds and proves.
    /// - fails: as [`Undeployed`] names, at the first field that does not read.
    /// - panics: none.
    /// - executable: none — each field is run on the program's machine, which a
    ///   predicate could only check by running it again; the witness observes
    ///   each outcome.
    ///
    /// # Errors
    /// [`Undeployed::Unread`], [`Undeployed::Refused`],
    /// [`Undeployed::Undeclared`], [`Undeployed::Unstrung`],
    /// [`Undeployed::Unkeyed`] and [`Undeployed::Unsocketed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus site reads its key, socket and secret's
    ///   name; a site whose key and socket do not read, one declaring no
    ///   sockets and one declaring no secret are refused at that field.
    /// - witness: `manifold::tests::a_site_and_a_manifold_read_from_their_files_3374`
    /// - witness: `manifold::tests::a_field_that_does_not_read_is_refused_by_name_3374`
    #[inline]
    pub fn read(file: &Path) -> Result<Self, Undeployed>
    {
        let [key, sockets, secret] = ran_alone(file, [
            Stated::Key.name(),
            Stated::Sockets.name(),
            Stated::Secret.name(),
        ])
        .map_err(|unran| Undeployed::of(file, unran))?;
        let key = strung(file, Stated::Key, key)?;
        let key = NodeId::from_str(&key).map_err(|refused| Undeployed::Unkeyed {
            file: file.to_path_buf(),
            refused,
        })?;
        let sockets = socketed(file, Written(&strung(file, Stated::Sockets, sockets)?))?;
        let secret = strung(file, Stated::Secret, secret)?;
        Ok(Self {
            key,
            sockets,
            secret,
        })
    }

    /// The key the site proves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn key(&self) -> NodeId
    {
        self.key
    }

    /// The sockets the site binds and is dialled at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sockets(&self) -> &[SocketAddr]
    {
        &self.sockets
    }

    /// How a peer is found where this site is reached: by multicast DNS when
    /// it names no socket, and at the sockets peers name otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lookup(&self) -> Lookup
    {
        discovered(&self.sockets)
    }

    /// The variable a host's environment holds the site's secret in when it
    /// is given no `Secrets` model: `GANDR_SECRET_` and the secret's name,
    /// upper-cased, each character other than a letter, a digit or `_` spelled
    /// `_`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`SECRET_VARIABLE`] followed by one character per character
    ///   of the secret's name: its ASCII upper case when it is an ASCII letter,
    ///   itself when it is an ASCII digit or `_`, and `_` otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `far` is `GANDR_SECRET_FAR`, and a name holding a
    ///   hyphen, a dot and a non-ASCII letter spells each as `_`.
    /// - witness: `manifold::tests::a_site_reads_its_secret_from_the_model_given_3375`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body maps each character of the name once; the check maps it once more"
        )
    )]
    #[spec(ensures: |ret| ret.strip_prefix(SECRET_VARIABLE).is_some_and(|spelled|
        spelled.chars().eq(self.secret.chars().map(|character| match character {
            | 'a'..='z' => character.to_ascii_uppercase(),
            | 'A'..='Z' | '0'..='9' | '_' => character,
            | _ => '_',
        }))))]
    #[inline]
    #[must_use]
    pub fn variable(&self) -> String
    {
        let mut variable = String::from(SECRET_VARIABLE);
        variable.extend(self.secret.chars().map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character.to_ascii_uppercase()
            }
            else {
                '_'
            }
        }));
        variable
    }

    /// The secret proving the site's key, read where `from` says.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: from a model's file, its `Secrets.secret` applied to the
    ///   secret's name, as [`answered_alone`] reads it, sealed answer and all;
    ///   from the environment, the variable [`Self::variable`] names. Either
    ///   text is read as [`Secret`] reads its spelling, and the secret is the
    ///   one proving the site's key.
    /// - provides: the secret `gandr host --site` proves the site's key with.
    /// - fails: as [`Undeployed`] names; no refusal spells the secret.
    /// - panics: none.
    /// - executable: none — the model's answer is a run of its program, and the
    ///   environment is the process's; the witness observes each outcome.
    ///
    /// # Errors
    /// From a model: [`Undeployed::Unread`], [`Undeployed::Refused`],
    /// [`Undeployed::Undeclared`] and [`Undeployed::Unanswered`]. From the
    /// environment: [`Undeployed::Unsecreted`]. Either:
    /// [`Undeployed::Unkeyable`] and [`Undeployed::Unproven`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus secrets model answers the far site's
    ///   secret, which proves its key; a model answering another site's secret
    ///   is unproven, one answering no key is unkeyable without being spelled,
    ///   and a file declaring no model is undeclared. The environment's
    ///   outcomes are observed by the driver's
    ///   `a_host_reads_its_site_s_secret_by_name_3375`.
    /// - witness: `manifold::tests::a_site_reads_its_secret_from_the_model_given_3375`
    #[inline]
    pub fn secret(
        &self,
        from: Secrets<'_>,
    ) -> Result<Secret, Undeployed>
    {
        let (text, secreted) = match from {
            Secrets::Model(file) => {
                let answered = answered_alone(
                    file,
                    Stated::Secrets.name(),
                    StringLiteral::new(self.secret.clone()),
                )
                .map_err(|unran| Undeployed::of(file, unran))?;
                let secreted = Secreted::Model {
                    file: file.to_path_buf(),
                    name: self.secret.clone(),
                };
                match answered {
                    Maybe::Present(Answered::Text(text)) => (text, secreted),
                    Maybe::Present(Answered::Other(ended)) => {
                        return Err(Undeployed::Unanswered {
                            from: secreted,
                            ended,
                        });
                    },
                    Maybe::Absent(declaration_name::Absent::Undeclared) => {
                        return Err(Undeployed::Undeclared {
                            file: file.to_path_buf(),
                            field: Stated::Secrets,
                        });
                    },
                }
            },
            Secrets::Environment => {
                let variable = self.variable();
                match std::env::var(&variable) {
                    Ok(text) => (text, Secreted::Variable(variable)),
                    Err(std::env::VarError::NotPresent) => {
                        return Err(Undeployed::Unsecreted { variable });
                    },
                    Err(std::env::VarError::NotUnicode(_)) => {
                        return Err(Undeployed::Unkeyable {
                            from: Secreted::Variable(variable),
                        });
                    },
                }
            },
        };
        let Ok(secret) = Secret::from_str(text.trim())
        else {
            return Err(Undeployed::Unkeyable { from: secreted });
        };
        let proving = secret.node_id();
        if proving != self.key {
            return Err(Undeployed::Unproven {
                site: self.key,
                proving,
                from: secreted,
            });
        }
        Ok(secret)
    }
}

/// The binding of a program's worlds onto sites, as its file's `Manifold`
/// model and `placements` state it.
#[derive(Clone, Debug)]
pub struct Manifold
{
    /// The manifold's own file.
    file: PathBuf,
    /// The program's source, its path joined to the manifold's directory.
    artifact: PathBuf,
    /// Each world placed, with the key of the site it is placed at, in the
    /// order `placements` lists them.
    placed: Vec<(WorldName, NodeId)>,
    /// Each world placed, bound to its site.
    bindings: WorldBindings,
    /// How a runner finds the sites: by multicast DNS when a site names no
    /// socket.
    lookup: Lookup,
}

impl Manifold
{
    /// The manifold the file at `file` states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the file checked alone over what it imports, and its
    ///   `Manifold.artifact` and `placements` run: the artifact's path joined
    ///   to the file's directory, and each placement read as a world bound to
    ///   the peer its key and sockets spell, a world placed twice keeping its
    ///   last; a runner finds sites by multicast DNS when any placement names
    ///   no socket.
    /// - provides: the bindings `gandr run --manifold` ships by and `gandr host
    ///   --manifold` serves by.
    /// - fails: as [`Undeployed`] names, at the first field or placement that
    ///   does not read.
    /// - panics: none.
    /// - executable: none — as [`Site::read`].
    ///
    /// # Errors
    /// [`Undeployed::Unread`], [`Undeployed::Refused`],
    /// [`Undeployed::Undeclared`], [`Undeployed::Unstrung`],
    /// [`Undeployed::Unplaced`], [`Undeployed::Replicated`],
    /// [`Undeployed::Unkeyed`] and [`Undeployed::Unsocketed`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus manifold binds `far` to the corpus site's
    ///   peer and deploys the migration model; a manifold placing a world twice
    ///   over, one declaring no placements and one whose placements are no list
    ///   of them are refused at that field.
    /// - witness: `manifold::tests::a_site_and_a_manifold_read_from_their_files_3374`
    /// - witness: `manifold::tests::a_field_that_does_not_read_is_refused_by_name_3374`
    #[inline]
    pub fn read(file: &Path) -> Result<Self, Undeployed>
    {
        let [artifact, placements] =
            ran_alone(file, [Stated::Artifact.name(), Stated::Placements.name()])
                .map_err(|unran| Undeployed::of(file, unran))?;
        let artifact = file.parent().unwrap_or_else(|| Path::new("")).join(strung(
            file,
            Stated::Artifact,
            artifact,
        )?);
        let came = match placements {
            Maybe::Present(came) => came,
            Maybe::Absent(declaration_name::Absent::Undeclared) => {
                return Err(Undeployed::Undeclared {
                    file: file.to_path_buf(),
                    field: Stated::Placements,
                });
            },
        };
        let Some(placed) = Spelling::from(came.as_str()).placements()
        else {
            return Err(Undeployed::Unplaced {
                file: file.to_path_buf(),
                came,
            });
        };
        let mut bindings = Vec::with_capacity(placed.len());
        let mut worlds = Vec::with_capacity(placed.len());
        let mut lookup = Lookup::Explicit;
        for Placed {
            name,
            key,
            sockets,
            count,
        } in placed
        {
            if count != "1" {
                return Err(Undeployed::Replicated {
                    file: file.to_path_buf(),
                    world: name,
                    count,
                });
            }
            let key = NodeId::from_str(&key).map_err(|refused| Undeployed::Unkeyed {
                file: file.to_path_buf(),
                refused,
            })?;
            let sockets = socketed(file, Written(&sockets))?;
            if discovered(&sockets) == Lookup::Mdns {
                lookup = Lookup::Mdns;
            }
            let world = WorldName::from(name.as_str());
            bindings.push((
                world.clone(),
                sockets.into_iter().fold(Peer::new(key), Peer::at),
            ));
            worlds.push((world, key));
        }
        Ok(Self {
            file: file.to_path_buf(),
            artifact,
            placed: worlds,
            bindings: bindings.into_iter().collect(),
            lookup,
        })
    }

    /// Whether the source at `program` is the program this manifold deploys.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing when `program` and the artifact's path name one file;
    ///   [`Undeployed::Elsewhere`] naming both otherwise, and when either names
    ///   no file.
    /// - provides: the refusal of a run or a host of another program than the
    ///   manifold deploys.
    /// - fails: [`Undeployed::Elsewhere`].
    /// - panics: none.
    /// - executable: none — the clause reads the file system again.
    ///
    /// # Errors
    /// [`Undeployed::Elsewhere`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus manifold deploys the migration model and
    ///   refuses its one-process sibling.
    /// - witness: `manifold::tests::a_site_and_a_manifold_read_from_their_files_3374`
    #[inline]
    pub fn deploying(
        &self,
        program: &Path,
    ) -> Result<(), Undeployed>
    {
        match (self.artifact.canonicalize(), program.canonicalize()) {
            (Ok(artifact), Ok(given)) if artifact == given => Ok(()),
            (Ok(_) | Err(_), Ok(_) | Err(_)) => Err(Undeployed::Elsewhere {
                artifact: self.artifact.clone(),
                program: program.to_path_buf(),
            }),
        }
    }

    /// The declaration a source states a manifold's artifact at, when the
    /// source is a manifold's: its program is `program`, its own declarations
    /// are those `report` reports, and one of them is `Manifold.artifact`.
    ///
    /// # Specification
    /// - requires: `report` is the report of the source `program` composes.
    /// - ensures: the declaration `Manifold.artifact` names among those
    ///   `report` reports, as a package's manifest fields are read among its
    ///   library's own; `Undeclared` when none of them is, so the theory's
    ///   operation an import of `std.manifold` brings is no manifold's.
    /// - fails: a source stating no artifact of its own is the typed absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifold checked states its artifact, and a site
    ///   beside it, importing `std.manifold`, does not.
    /// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(constant) => report.declarations().iter().any(|declaration| declaration.constant() == constant),
        Maybe::Absent(declaration_name::Absent::Undeclared) => true,
    })]
    #[inline]
    pub fn stated(
        program: &Program<'_>,
        report: &SettleReport<'_>,
    ) -> Maybe<ConstantIndex, declaration_name::Absent>
    {
        program.named_among(
            Stated::Artifact.name(),
            report
                .declarations()
                .iter()
                .map(DeclarationReport::constant),
        )
    }

    /// The deployment judged before any process starts: each placement's
    /// world resolved among the worlds of the program this manifold deploys,
    /// and each world written `world w requires [ … ] ;` placed only at a site
    /// whose `offers` answers each entry of the row.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the program at the artifact's path lowered over what it
    ///   imports. Each placement, in the order `placements` lists them, whose
    ///   world the program declares nothing of is [`Undeployed::Unworlded`],
    ///   and one naming a declaration the lowering refused is
    ///   [`Undeployed::Misworlded`]. A placement of a world written with a
    ///   requirement finds its site's file among the files this manifold lays
    ///   out over, the one whose `Site.key` runs to the placement's key, and is
    ///   [`Undeployed::Unsited`] when none does; the row is then judged entry
    ///   by entry against the file's offer, each entry unanswered an
    ///   [`Undeployed::Unoffered`] in written order. Empty when every placement
    ///   holds.
    /// - provides: the deployment check `gandr check` of a manifold makes.
    /// - fails: never; each refusal is an entry, and a program that cannot be
    ///   read or lowered is the one entry.
    /// - panics: none.
    /// - executable: none — each judgement checks another source, which a
    ///   predicate could only observe by checking it again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus deployment of a world requiring `Console`
    ///   and a labelled `Store` at a site answering both holds, and so does the
    ///   migration model's, whose worlds require nothing; a site binding no
    ///   module to a label, one binding a module at other sorts, one not
    ///   listing a host interface, and one whose authority does not hold an
    ///   interface it lists are each refused naming the entry, and a world the
    ///   program lacks is refused by name.
    /// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
    #[inline]
    #[must_use]
    pub fn judged(&self) -> Vec<Undeployed>
    {
        let text = match std::fs::read_to_string(&self.artifact) {
            Ok(text) => text,
            Err(error) => {
                return Vec::from([Undeployed::Unread {
                    file: self.artifact.clone(),
                    message: error.to_string(),
                }]);
            },
        };
        let program = SourceText::from(text.as_str());
        let worlds = match lowered_alone(&self.artifact, program, declared) {
            Ok(worlds) => worlds,
            Err(unran) => return Vec::from([Undeployed::of(&self.artifact, unran)]),
        };
        let required = self.placed.iter().any(|&(ref world, _)| {
            matches!(worlds.get(world), Some(&Declared::World(Maybe::Present(_))))
        });
        let sites = if required {
            self.sites()
        }
        else {
            BTreeMap::new()
        };
        let mut refused = Vec::new();
        for &(ref world, key) in &self.placed {
            let refusal = match worlds.get(world) {
                Some(&Declared::World(Maybe::Absent(_))) => continue,
                Some(&Declared::World(Maybe::Present(ref entries))) => {
                    let Some(site) = sites.get(&key)
                    else {
                        refused.push(Undeployed::Unsited {
                            manifold: self.file.clone(),
                            world: world.clone(),
                            key,
                        });
                        continue;
                    };
                    let offering = Offering {
                        artifact: &self.artifact,
                        program,
                        world,
                        entries,
                        site,
                    };
                    refused.extend(offering.judged());
                    continue;
                },
                Some(&Declared::Refused(ref why)) => Undeployed::Misworlded {
                    artifact: self.artifact.clone(),
                    world: world.clone(),
                    why: why.clone(),
                },
                None => Undeployed::Unworlded {
                    manifold: self.file.clone(),
                    artifact: self.artifact.clone(),
                    world: world.clone(),
                },
            };
            refused.push(refusal);
        }
        refused
    }

    /// The site each file this manifold lays out over states, by the key its
    /// `Site.key` runs to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per key that the `Site.key` of a file of the
    ///   manifold's unit, the file checked alone, runs to as a string reading
    ///   as a key: the first such file in the unit's order, named from the
    ///   working directory where it stands below it. A file declaring no site,
    ///   or whose key does not read, is none's.
    /// - provides: the files [`Self::judged`] matches each placement's site to.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Site::read`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::judged`].
    /// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
    fn sites(&self) -> BTreeMap<NodeId, PathBuf>
    {
        let here = std::env::current_dir().and_then(|here| here.canonicalize());
        sources_alone(&self.file)
            .unwrap_or_default()
            .into_iter()
            .filter_map(|source| {
                let [key] = ran_alone(&source, [Stated::Key.name()]).ok()?;
                let key = NodeId::from_str(&strung(&source, Stated::Key, key).ok()?).ok()?;
                let named = match here {
                    Ok(ref here) => source
                        .strip_prefix(here)
                        .map_or_else(|_outside| source.clone(), Path::to_path_buf),
                    Err(_) => source,
                };
                Some((key, named))
            })
            .fold(BTreeMap::new(), |mut sites, (key, named)| {
                let _first = sites.entry(key).or_insert(named);
                sites
            })
    }

    /// How a runner finds the sites this manifold places worlds at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lookup(&self) -> Lookup
    {
        self.lookup
    }

    /// The world bindings this manifold makes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_bindings(self) -> WorldBindings
    {
        self.bindings
    }
}

/// One placement as its spelling reads, before its key and sockets do.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Placed
{
    /// The world's name.
    pub name: String,
    /// The site's key, as written.
    pub key: String,
    /// The site's sockets, as written.
    pub sockets: String,
    /// How many processes run the world, as spelled.
    pub count: String,
}

/// A field a site's, a manifold's or a secrets model's file states.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Stated
{
    /// `Site.key`.
    Key,
    /// `Site.sockets`.
    Sockets,
    /// `Site.secret`.
    Secret,
    /// `Manifold.artifact`.
    Artifact,
    /// `placements`.
    Placements,
    /// `Secrets.secret`.
    Secrets,
}

impl Stated
{
    /// The declaration's path among the file's declarations.
    ///
    /// # Specification
    /// trivial.
    fn name(self) -> SurfaceName<'static>
    {
        SurfaceName::from(match self {
            Self::Key => "Site.key",
            Self::Sockets => "Site.sockets",
            Self::Secret => "Site.secret",
            Self::Artifact => "Manifold.artifact",
            Self::Placements => "placements",
            Self::Secrets => "Secrets.secret",
        })
    }
}

/// Where a host reads its site's secret from.
#[derive(Clone, Copy, Debug)]
pub enum Secrets<'file>
{
    /// The `Secrets` model of `std.secret` the file declares.
    Model(&'file Path),
    /// The process's environment, at [`Site::variable`].
    Environment,
}

/// Where a secret was read, for a refusal naming it without its value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Secreted
{
    /// A model's answer at the secret's name.
    Model
    {
        /// The model's file.
        file: PathBuf,
        /// The secret's name.
        name: String,
    },
    /// An environment variable.
    Variable(String),
}

impl fmt::Display for Secreted
{
    /// The read, as a host would write it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Model { ref file, ref name } => write!(
                f,
                "`{}(\"{name}\")` of `{}`",
                Stated::Secrets.name(),
                file.display()
            ),
            Self::Variable(ref variable) => write!(f, "`{variable}`"),
        }
    }
}

impl fmt::Display for Stated
{
    /// The declaration's path.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.name())
    }
}

/// Why a site's or a manifold's file deploys nothing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Undeployed
{
    /// The file cannot be read.
    Unread
    {
        /// The file.
        file: PathBuf,
        /// What reading it met.
        message: String,
    },
    /// The file does not compose, or is refused as a whole.
    Refused
    {
        /// The file.
        file: PathBuf,
        /// Why, spelled.
        why: String,
    },
    /// The file declares no such field.
    Undeclared
    {
        /// The file.
        file: PathBuf,
        /// The field it lacks.
        field: Stated,
    },
    /// The field runs to something other than a string.
    Unstrung
    {
        /// The file.
        file: PathBuf,
        /// The field.
        field: Stated,
        /// What its run came to, spelled.
        came: String,
    },
    /// A key does not read.
    Unkeyed
    {
        /// The file.
        file: PathBuf,
        /// Why the key does not read.
        refused: PeerError,
    },
    /// A socket is no `ip:port`.
    Unsocketed
    {
        /// The file.
        file: PathBuf,
        /// The entry, as written.
        entry: String,
        /// Why it does not read.
        reason: String,
    },
    /// `placements` runs to something other than a list of placements.
    Unplaced
    {
        /// The file.
        file: PathBuf,
        /// What its run came to, spelled.
        came: String,
    },
    /// A placement runs its world as other than one process.
    Replicated
    {
        /// The file.
        file: PathBuf,
        /// The world.
        world: String,
        /// The count, as spelled.
        count: String,
    },
    /// The source given is not the program the manifold deploys.
    Elsewhere
    {
        /// The program's path, as the manifold resolves it.
        artifact: PathBuf,
        /// The source given.
        program: PathBuf,
    },
    /// The host's secret proves another key than the site's.
    Unproven
    {
        /// The site's key.
        site: NodeId,
        /// The key the secret proves.
        proving: NodeId,
        /// Where the secret was read.
        from: Secreted,
    },
    /// The environment holds no secret for the site.
    Unsecreted
    {
        /// The variable read.
        variable: String,
    },
    /// A secret read spells no key.
    Unkeyable
    {
        /// Where it was read.
        from: Secreted,
    },
    /// A `Secrets` model answers the site's secret with other than a string.
    Unanswered
    {
        /// The model's read.
        from: Secreted,
        /// How its run ended instead, spelled.
        ended: String,
    },
    /// A placement names a world the program declares nothing of.
    Unworlded
    {
        /// The manifold's file.
        manifold: PathBuf,
        /// The program it deploys.
        artifact: PathBuf,
        /// The world placed.
        world: WorldName,
    },
    /// A placement names a declaration of the program the lowering refused.
    Misworlded
    {
        /// The program.
        artifact: PathBuf,
        /// The world placed.
        world: WorldName,
        /// The refusal, spelled.
        why: String,
    },
    /// A world written with a requirement is placed at a site no file the
    /// manifold imports states.
    Unsited
    {
        /// The manifold's file.
        manifold: PathBuf,
        /// The world placed.
        world: WorldName,
        /// The key the placement's site proves.
        key: NodeId,
    },
    /// A site does not answer an entry of the row the world placed at it
    /// requires.
    Unoffered
    {
        /// The site's file.
        site: PathBuf,
        /// The world placed.
        world: WorldName,
        /// The entry refused: a theory's label, or a host interface's name.
        entry: String,
        /// Why the site's offer does not answer it, spelled.
        why: String,
    },
}

impl Undeployed
{
    /// The refusal of the file `file` that [`ran_alone`] could not run.
    ///
    /// # Specification
    /// trivial.
    fn of(
        file: &Path,
        unran: Unran,
    ) -> Self
    {
        let file = file.to_path_buf();
        match unran {
            Unran::Unread { message } => Self::Unread { file, message },
            Unran::Refused { why } => Self::Refused { file, why },
        }
    }
}

impl fmt::Display for Undeployed
{
    /// What refused, naming the file and the field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unread {
                ref file,
                ref message,
            } => write!(f, "`{}` cannot be read: {message}", file.display()),
            Self::Refused { ref file, ref why } => {
                write!(f, "`{}` is refused as a whole: {why}", file.display())
            },
            Self::Undeclared { ref file, field } => write!(
                f,
                "`{}` declares no `{field}`: declare {}",
                file.display(),
                match field {
                    Stated::Key | Stated::Sockets | Stated::Secret => {
                        "`module Site : Model(Site)` from `std.manifold`"
                    },
                    Stated::Artifact => "`module Manifold : Model(Manifold)` from `std.manifold`",
                    Stated::Placements => "`pub def placements : List(Placement)`",
                    Stated::Secrets => {
                        "`module Secrets : Model(Secrets) with sort K = Secret.T` from `std.secret`"
                    },
                }
            ),
            Self::Unstrung {
                ref file,
                field,
                ref came,
            } => write!(
                f,
                "`{field}` of `{}` runs to `{came}`, not to a string",
                file.display()
            ),
            Self::Unkeyed {
                ref file,
                ref refused,
            } => write!(f, "a key of `{}` does not read: {refused}", file.display()),
            Self::Unsocketed {
                ref file,
                ref entry,
                ref reason,
            } => write!(
                f,
                "the socket `{entry}` of `{}` is no `ip:port`: {reason}",
                file.display()
            ),
            Self::Unplaced { ref file, ref came } => write!(
                f,
                "`placements` of `{}` runs to `{came}`, not to a list of placements",
                file.display()
            ),
            Self::Replicated {
                ref file,
                ref world,
                ref count,
            } => write!(
                f,
                "`{}` runs `{world}` as {count} instances: a world runs as one process",
                file.display()
            ),
            Self::Elsewhere {
                ref artifact,
                ref program,
            } => write!(
                f,
                "the manifold deploys `{}`, not `{}`",
                artifact.display(),
                program.display()
            ),
            Self::Unproven {
                site,
                proving,
                ref from,
            } => write!(
                f,
                "the site proves the key {site}, and the secret read from {from} proves \
                 {proving}: give the site's own secret there"
            ),
            Self::Unsecreted { ref variable } => write!(
                f,
                "no secret is given for the site: set `{variable}`, or give a `Secrets` model \
                 with `--secrets`"
            ),
            Self::Unkeyable { ref from } => write!(
                f,
                "the secret read from {from} spells no key: give 64 hexadecimal digits"
            ),
            Self::Unanswered {
                ref from,
                ref ended,
            } => {
                write!(f, "{from} answers no string: its run ended `{ended}`")
            },
            Self::Unworlded {
                ref manifold,
                ref artifact,
                ref world,
            } => write!(
                f,
                "`{}` places `{world}`, a world `{}` does not declare: place one of its worlds",
                manifold.display(),
                artifact.display()
            ),
            Self::Misworlded {
                ref artifact,
                ref world,
                ref why,
            } => write!(
                f,
                "the world `{world}` of `{}` is refused: {why}",
                artifact.display()
            ),
            Self::Unsited {
                ref manifold,
                ref world,
                key,
            } => write!(
                f,
                "`{}` places `{world}` at the site {key}, which no file it imports states: \
                 import the site's file",
                manifold.display()
            ),
            Self::Unoffered {
                ref site,
                ref world,
                ref entry,
                ref why,
            } => write!(
                f,
                "`{world}` requires `{entry}`, and the site `{}` does not answer it: {why}",
                site.display()
            ),
        }
    }
}

impl core::error::Error for Undeployed
{
}

/// The string `came` spells, decoded, as the field `field` of the file
/// `file` ran to.
///
/// # Specification
/// trivial.
fn strung(
    file: &Path,
    field: Stated,
    came: Maybe<String, declaration_name::Absent>,
) -> Result<String, Undeployed>
{
    let came = match came {
        Maybe::Present(came) => came,
        Maybe::Absent(declaration_name::Absent::Undeclared) => {
            return Err(Undeployed::Undeclared {
                file: file.to_path_buf(),
                field,
            });
        },
    };
    came.strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .map(|content| decode_escapes(SourceFragment::from(content)))
        .ok_or_else(|| Undeployed::Unstrung {
            file: file.to_path_buf(),
            field,
            came: came.clone(),
        })
}

/// The sockets `written` lists, `,`-separated, blank entries skipped.
///
/// # Specification
/// trivial.
fn socketed(
    file: &Path,
    Written(written): Written<'_>,
) -> Result<Vec<SocketAddr>, Undeployed>
{
    written
        .split(',')
        .map(str::trim)
        .filter(|entry| !entry.is_empty())
        .map(|entry| {
            SocketAddr::from_str(entry).map_err(|refused| Undeployed::Unsocketed {
                file: file.to_path_buf(),
                entry: String::from(entry),
                reason: refused.to_string(),
            })
        })
        .collect()
}

/// How a peer reached at `sockets` is found: by its key alone, over
/// multicast DNS, when there are none.
///
/// # Specification
/// trivial.
fn discovered(sockets: &[SocketAddr]) -> Lookup
{
    if sockets.is_empty() {
        Lookup::Mdns
    }
    else {
        Lookup::Explicit
    }
}

/// A field's text as its file's run spelled it, decoded.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Written<'text>(&'text str);

/// What a program declares under a name a placement may give: a world, with
/// the row it requires as the program writes it, or a declaration the
/// lowering refused.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Declared
{
    /// A world, and its requirement row's entries.
    World(Maybe<Vec<Entry>, requirement::Absent>),
    /// A refused declaration, its refusal spelled.
    Refused(String),
}

/// One entry of a world's requirement row, as the program writes it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Entry
{
    /// The label code at the world performs through; none for an interface
    /// named whole.
    label: Maybe<String, labelled::Absent>,
    /// The interface's name.
    interface: String,
    /// The sorts the entry fixes, as written after the interface's name, `
    /// with sort V = String`; empty for a host interface.
    manifest: String,
}

/// The bytes `span` covers in `text`, owned; none when `text` does not hold
/// them.
///
/// # Specification
/// trivial.
fn spelled(
    text: SourceText<'_>,
    span: ByteSpan,
) -> Option<String>
{
    text.as_ref()
        .get(usize::from(span.start()) .. usize::from(span.end()))
        .map(String::from)
}

/// Each world and each refused declaration of `module`, by its name, the
/// requirement read off the unit's text `text`.
///
/// # Specification
/// - requires: `text` is the text `module`'s spans index.
/// - ensures: one entry per declaration of `module` that lowers to a world,
///   with its requirement row's entries in written order, or that the lowering
///   refused, with its refusal; a later declaration of one name keeps its
///   entry. A requirement whose bytes `text` does not hold is refused.
/// - fails: never.
/// - panics: none.
/// - executable: none — the entries are a reading of the module, which a clause
///   would restate whole.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Manifold::judged`].
/// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
fn declared(
    module: &LoweredModule<'_>,
    text: SourceText<'_>,
) -> BTreeMap<WorldName, Declared>
{
    module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let declared = match declaration.outcome() {
                DeclarationOutcome::World => match module.requirement(declaration) {
                    Maybe::Present(required) => required
                        .iter()
                        .map(|entry| {
                            Some(Entry {
                                label: match entry.label {
                                    Maybe::Present(span) => Maybe::Present(spelled(text, span)?),
                                    Maybe::Absent(absent) => Maybe::Absent(absent),
                                },
                                interface: spelled(text, entry.interface)?,
                                manifest: spelled(
                                    text,
                                    ByteSpan::new(entry.interface.end(), entry.written.end())
                                        .ok()?,
                                )?,
                            })
                        })
                        .collect::<Option<Vec<Entry>>>()
                        .map_or_else(
                            || {
                                Declared::Refused(String::from(
                                    "its requirement's bytes stand outside the program's text",
                                ))
                            },
                            |entries| Declared::World(Maybe::Present(entries)),
                        ),
                    Maybe::Absent(absent) => Declared::World(Maybe::Absent(absent)),
                },
                DeclarationOutcome::Refused(refusal) => Declared::Refused(refusal.to_string()),
                DeclarationOutcome::Completed { .. }
                | DeclarationOutcome::Uncompleted { .. }
                | DeclarationOutcome::Bodied { .. }
                | DeclarationOutcome::Data(_)
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_) => return None,
            };
            Some((WorldName::from(declaration.name().as_ref()), declared))
        })
        .collect()
}

/// A site's offer, as its file writes it.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Offer
{
    /// Each host interface the site grants, by its name.
    granted: BTreeSet<String>,
    /// Each label the site answers, with the name of the module answering it.
    answered: BTreeMap<String, String>,
}

/// The offer the site's module `module` writes, read off the unit's text
/// `text`.
///
/// # Specification
/// - requires: `text` is the text `module`'s spans index.
/// - ensures: the host interfaces and the labels with their modules the
///   module's `offers` writes; the empty offer when it writes none, or when
///   `text` does not hold its bytes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Manifold::judged`].
/// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
#[spec(ensures: |ret| ret.granted.len() <= match module.offer() { Maybe::Present(offer) => offer.granted.len(), Maybe::Absent(_) => 0 })]
fn offered(
    module: &LoweredModule<'_>,
    text: SourceText<'_>,
) -> Offer
{
    let Maybe::Present(offered) = module.offer()
    else {
        return Offer::default();
    };
    let granted = offered
        .granted
        .iter()
        .map(|&interface| spelled(text, interface))
        .collect::<Option<BTreeSet<String>>>();
    let answered = offered
        .answered
        .iter()
        .map(|&(label, answering)| Some((spelled(text, label)?, spelled(text, answering)?)))
        .collect::<Option<BTreeMap<String, String>>>();
    match (granted, answered) {
        (Some(granted), Some(answered)) => Offer { granted, answered },
        (None, _) | (_, None) => Offer::default(),
    }
}

/// The alias the deployment check imports a site's file under.
const SITE_ALIAS: &str = "deployedSite";

/// The functor the deployment check writes for each label: its parameter is a
/// model of the label's theory at the sorts the requirement fixes, followed by
/// the label's position in the row.
const REQUIRED: &str = "DeployedRequirement";

/// The application the deployment check judges for each label: the functor
/// applied to the module the site answers the label with, followed by the
/// label's position in the row.
const OFFERED: &str = "DeployedOffer";

/// The definition the deployment check writes into a site's file for each
/// host interface: the site's authority attenuated to the interface's
/// operations, followed by the entry's position in the row.
const GRANTED: &str = "deployedGrant";

/// An entry's position in the row it stands in, counted from zero in written
/// order.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Position(usize);

/// A label the site binds a module to: the entry, its position, and the
/// module's name.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Bound<'judged>
{
    /// The entry's position in its row.
    position: Position,
    /// The entry.
    entry: &'judged Entry,
    /// The name of the module the site binds the entry's label to.
    module: &'judged str,
}

/// A host interface the site lists: the entry's position, and the host's
/// signature of the interface.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Listed<'judged>
{
    /// The entry's position in its row.
    position: Position,
    /// The interface's signature, its operations the grant must hold.
    signature: &'judged EffectSig,
}

/// The bytes the deployment check wrote for one entry, in the text it
/// judges.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Wrote
{
    /// The entry's position in its row.
    position: Position,
    /// Where the written lines start.
    start: ByteOffset,
    /// Where they end.
    end: ByteOffset,
}

/// A world's requirement row judged against the offer of the site it is
/// placed at.
#[derive(Clone, Copy, Debug)]
struct Offering<'judged>
{
    /// The program's source.
    artifact: &'judged Path,
    /// The program's text.
    program: SourceText<'judged>,
    /// The world placed.
    world: &'judged WorldName,
    /// The row the world requires, its entries as the program writes them.
    entries: &'judged [Entry],
    /// The file of the site it is placed at.
    site: &'judged Path,
}

impl Offering<'_>
{
    /// Each entry of the row the site does not answer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the site's file lowered alone for its offer, and each entry
    ///   judged against it in written order. A host interface, an entry whose
    ///   interface the host declares, is answered when the offer lists it and
    ///   the site's own text, with [`GRANTED`] attenuating its `Authority` to
    ///   the interface's operations, holds them ([`Self::granted`]). A theory's
    ///   label is answered when the offer binds a module to it that the
    ///   program's text, with the module imported and [`OFFERED`] applying
    ///   [`REQUIRED`] to it, takes at `Model(T)` and the sorts the entry fixes
    ///   ([`Self::modelled`]). Empty when every entry is answered.
    /// - provides: the member-by-member judgement of [`Manifold::judged`].
    /// - fails: never; each entry unanswered is an [`Undeployed::Unoffered`]
    ///   naming it, by the label for a theory and by its name for a host
    ///   interface, and a site's file that does not read or lower refuses every
    ///   entry.
    /// - panics: none.
    /// - executable: none — the judgement checks the program and the site
    ///   again, which a predicate could only observe by checking them once
    ///   more.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Manifold::judged`].
    /// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
    fn judged(self) -> Vec<Undeployed>
    {
        let mut arena = CoreArena::new();
        let table = HostSignatures::new(&mut arena);
        let signature = |entry: &Entry| {
            table
                .as_ref()
                .map_or(Maybe::Absent(declared::Absent::Undeclared), |table| {
                    table.named(&EffectName::from(entry.interface.as_str()))
                })
        };
        let unoffered = |entry: &Entry, why: String| Undeployed::Unoffered {
            site: self.site.to_path_buf(),
            world: self.world.clone(),
            entry: match (signature(entry), &entry.label) {
                (Maybe::Absent(_), &Maybe::Present(ref label)) => label.clone(),
                (Maybe::Present(_), _) | (_, &Maybe::Absent(_)) => entry.interface.clone(),
            },
            why,
        };
        let every = |why: &str| {
            self.entries
                .iter()
                .map(|entry| unoffered(entry, String::from(why)))
                .collect()
        };
        if let Err(ref conflict) = table {
            return every(&conflict.to_string());
        }
        let site = match std::fs::read_to_string(self.site) {
            Ok(site) => site,
            Err(error) => return every(&error.to_string()),
        };
        let offer = match lowered_alone(self.site, SourceText::from(site.as_str()), offered) {
            Ok(offer) => offer,
            Err(Unran::Unread { message: why } | Unran::Refused { why }) => return every(&why),
        };
        let mut why: BTreeMap<Position, String> = BTreeMap::new();
        let mut bound = Vec::new();
        let mut listed = Vec::new();
        for (at, entry) in self.entries.iter().enumerate() {
            let position = Position(at);
            match (signature(entry), &entry.label) {
                (Maybe::Present(signature), _) => {
                    if offer.granted.contains(&entry.interface) {
                        listed.push(Listed {
                            position,
                            signature,
                        });
                    }
                    else {
                        let _first =
                            why.insert(position, String::from("the site's offer does not list it"));
                    }
                },
                (Maybe::Absent(_), &Maybe::Present(ref label)) => match offer.answered.get(label) {
                    Some(module) => bound.push(Bound {
                        position,
                        entry,
                        module,
                    }),
                    None => {
                        let _first = why.insert(
                            position,
                            String::from("the site's offer binds no module to it"),
                        );
                    },
                },
                (Maybe::Absent(_), &Maybe::Absent(_)) => {},
            }
        }
        why.extend(self.modelled(&bound));
        why.extend(self.granted(SourceText::from(site.as_str()), &listed));
        why.into_iter()
            .filter_map(|(Position(at), why)| Some(unoffered(self.entries.get(at)?, why)))
            .collect()
    }

    /// Why each label the site binds a module to is not answered by it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the program's text, followed by an import of the site's file
    ///   by its path from the program's directory, under [`SITE_ALIAS`] and
    ///   listing each module of `bound`, and per label the functor [`REQUIRED`]
    ///   over a model of the label's theory at the entry's sorts and
    ///   [`OFFERED`] applying it to the module, judged at the program's path as
    ///   [`stepped_alone`] judges a text; each label whose lines a diagnostic
    ///   marks, with that diagnostic spelled. The modules are imported by their
    ///   bare names because a functor applies a module by its name, so a
    ///   program declaring a module of one of their names is refused here.
    /// - fails: never; a text refused as a whole refuses every label.
    /// - panics: none.
    /// - executable: none — as [`Self::judged`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module at the sorts the requirement fixes is taken,
    ///   and one at other sorts is refused naming both types.
    /// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
    fn modelled(
        self,
        bound: &[Bound<'_>],
    ) -> BTreeMap<Position, String>
    {
        if bound.is_empty() {
            return BTreeMap::new();
        }
        let Some(address) = addressed(self.artifact, self.site)
        else {
            return bound
                .iter()
                .map(|label| {
                    (
                        label.position,
                        String::from("no path from the program's directory spells its file"),
                    )
                })
                .collect();
        };
        let modules: BTreeSet<&str> = bound.iter().map(|label| label.module).collect();
        let mut written = format!(
            "{program}\nimport \"{address}\" as {SITE_ALIAS} ({modules});\n",
            program = self.program,
            modules = modules.into_iter().collect::<Vec<_>>().join(", "),
        );
        let mut wrote = Vec::with_capacity(bound.len());
        for label in bound {
            let start = ByteOffset::from(written.len());
            let _written = write!(
                written,
                "module {REQUIRED}{at}(M : Model({interface}){manifest}) {{}}\nmodule \
                 {OFFERED}{at} = {REQUIRED}{at}({module});\n",
                at = label.position.0,
                interface = label.entry.interface,
                manifest = label.entry.manifest,
                module = label.module,
            );
            wrote.push(Wrote {
                position: label.position,
                start,
                end: ByteOffset::from(written.len()),
            });
        }
        judge(self.artifact, SourceText::from(written.as_str()), &wrote)
    }

    /// Why each host interface the site lists is not held by its authority.
    ///
    /// # Specification
    /// - requires: `site` is the text of the site's file.
    /// - ensures: `site`, followed per interface of `listed` holding an
    ///   operation by [`GRANTED`], a function from `Authority` to the
    ///   capability holding the interface's operations, judged at the site's
    ///   path as [`stepped_alone`] judges a text; each interface whose line a
    ///   diagnostic marks, with that diagnostic spelled. An interface holding
    ///   no operation is held by any authority.
    /// - fails: never; a text refused as a whole refuses every interface.
    /// - panics: none.
    /// - executable: none — as [`Self::judged`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `Console`, which `std.authority`'s `Authority` holds,
    ///   is granted, and `Net`, which it does not, is refused naming both
    ///   capabilities.
    /// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
    fn granted(
        self,
        site: SourceText<'_>,
        listed: &[Listed<'_>],
    ) -> BTreeMap<Position, String>
    {
        let mut written = format!("{site}\n");
        let mut wrote = Vec::with_capacity(listed.len());
        for interface in listed {
            let mut operations = interface.signature.operations();
            let Some(first) = operations.next()
            else {
                continue;
            };
            let start = ByteOffset::from(written.len());
            let _written = write!(
                written,
                "def {GRANTED}{at}(authority : Authority) -> Cap {{ ",
                at = interface.position.0,
            );
            written.push_str(first.name.as_ref());
            for operation in operations {
                written.push_str(", ");
                written.push_str(operation.name.as_ref());
            }
            written.push_str(" } { authority }\n");
            wrote.push(Wrote {
                position: interface.position,
                start,
                end: ByteOffset::from(written.len()),
            });
        }
        if wrote.is_empty() {
            return BTreeMap::new();
        }
        judge(self.site, SourceText::from(written.as_str()), &wrote)
    }
}

/// Why each entry of `wrote` does not check, `written` judged at `source`.
///
/// # Specification
/// - requires: each of `wrote` holds bytes of `written`, none overlapping.
/// - ensures: `written` judged at `source` as [`stepped_alone`] judges a text;
///   for each entry whose bytes the primary span of a diagnostic `check` gives
///   begins in, the first such diagnostic: its refusal's name, its message and
///   its primary mark. A text refused or faulted as a whole is every entry's
///   refusal.
/// - fails: never.
/// - panics: none.
/// - executable: none — the diagnostics are the walk's own reading of the text,
///   which a clause would restate whole.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Offering::judged`].
/// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
fn judge(
    source: &Path,
    written: SourceText<'_>,
    wrote: &[Wrote],
) -> BTreeMap<Position, String>
{
    let every = |why: &str| {
        wrote
            .iter()
            .map(|entry| (entry.position, String::from(why)))
            .collect()
    };
    let read = stepped_alone(source, written, |step| {
        match step {
            Step::Source {
                composed: Composed::Settled { .. },
                ..
            } => {},
            Step::Source {
                composed: Composed::Refused(refusal),
                ..
            } => return every(&refusal.to_string()),
            Step::Fault { ref fault, .. } => return every(&fault.to_string()),
        }
        let starts: BTreeMap<ByteOffset, Wrote> =
            wrote.iter().map(|&entry| (entry.start, entry)).collect();
        let mut refused: BTreeMap<Position, String> = BTreeMap::new();
        for diagnostic in entries(&step, Verb::Check(Goals::Gated)) {
            let Maybe::Present(span) = diagnostic.span
            else {
                continue;
            };
            let Some((_, &entry)) = starts.range(..= span.start()).next_back()
            else {
                continue;
            };
            if span.start() < entry.end {
                let _first = refused.entry(entry.position).or_insert_with(|| {
                    let mut why = String::new();
                    if let Maybe::Present(ref identifier) = diagnostic.identifier {
                        let _written = write!(why, "{identifier}: ");
                    }
                    let _written = write!(why, "{}", diagnostic.message.text);
                    if let Some(primary) = diagnostic.annotations.first() {
                        let _written = write!(why, "; {}", primary.label);
                    }
                    why
                });
            }
        }
        refused
    });
    match read {
        Ok(refused) => refused,
        Err(Unran::Unread { message: why } | Unran::Refused { why }) => every(&why),
    }
}

/// The address an import in the program at `artifact` reaches the file `site`
/// by: its path from the program's directory, `./` before one that does not
/// climb, each `\` and `"` escaped.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the components of `site`'s canonical path after those it shares
///   with the canonical directory of `artifact`, after one `..` per component
///   of that directory it does not share; none when either path does not
///   canonicalize or the address is no text.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the file system.
///
/// # Adequacy
/// - hypothesis: L3 — a site beside the program, and one in a directory the
///   program's directory does not hold.
/// - witness: `manifold::tests::a_world_s_row_is_judged_against_its_site_s_offer_3523`
fn addressed(
    artifact: &Path,
    site: &Path,
) -> Option<String>
{
    let program = artifact.canonicalize().ok()?;
    let from = program.parent()?;
    let to = site.canonicalize().ok()?;
    let shared = from
        .components()
        .zip(to.components())
        .take_while(|&(here, there)| here == there)
        .count();
    let climbs = from.components().count().saturating_sub(shared);
    let mut path = PathBuf::from(if climbs == 0 { "." } else { ".." });
    path.extend(core::iter::repeat_n("..", climbs.saturating_sub(1)));
    path.extend(to.components().skip(shared));
    Some(path.to_str()?.replace('\\', "\\\\").replace('"', "\\\""))
}

#[cfg(test)]
mod tests;
