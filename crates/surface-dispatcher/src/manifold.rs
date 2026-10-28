//! A site and a manifold, read from their files.
//!
//! A deployment binds a program's worlds to places and never enters the
//! program's identity. Its two files are gandr, each read as a workspace's
//! `members` is: checked alone over what it imports, then run. A site's file
//! declares `module Site : Model(Site)` of `std.manifold`, the key one place
//! proves, the sockets it is reached at, and the name of the secret proving
//! the key. A manifold's file declares `module Manifold : Model(Manifold)`, the
//! program it deploys, beside `pub def placements : List(Placement)`, each
//! world of the program bound to a site. [`Site::read`] and [`Manifold::read`]
//! read them into exactly what the driver's `--net-bind` and `--world` flags
//! build: the sockets a host binds and the key it proves, and the
//! [`WorldBindings`] a run ships by.
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
//!
//! # References
//!
//! - `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — lineage: the compilation
//!   ruling, § compilation-recipe-refinements: a deployment binds roles to
//!   world keys, instance counts and discovery, and never enters an artifact's
//!   identity.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::net::SocketAddr;
use core::str::FromStr as _;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_net::Lookup;
use gandr_runtime_net::NodeId;
use gandr_runtime_net::Peer;
use gandr_runtime_net::PeerError;
use gandr_runtime_net::Secret;
use gandr_runtime_net::WorldName;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::decode_escapes;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use crate::evaluate::WorldBindings;
use crate::evaluate::declaration_name;
use crate::workspace::Answered;
use crate::workspace::Spelling;
use crate::workspace::Unran;
use crate::workspace::answered_alone;
use crate::workspace::ran_alone;

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
    /// The program's source, its path joined to the manifold's directory.
    artifact: PathBuf,
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
            bindings.push((
                WorldName::from(name.as_str()),
                sockets.into_iter().fold(Peer::new(key), Peer::at),
            ));
        }
        Ok(Self {
            artifact,
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

#[cfg(test)]
mod tests;
