//! A site and a manifold, read from their files.
//!
//! A deployment binds a program's worlds to places and never enters the
//! program's identity. Its two files are gandr, each read as a workspace's
//! `members` is: checked alone over what it imports, then run. A site's file
//! declares `module Site : Model(Site)` of `std.manifold`, the key one place
//! proves and the sockets it is reached at. A manifold's file declares
//! `module Manifold : Model(Manifold)`, the program it deploys, beside `pub
//! def placements : List(Placement)`, each world of the program bound to a
//! site. [`Site::read`] and [`Manifold::read`] read them into exactly what the
//! driver's `--net-bind` and `--world` flags build: the sockets a host binds
//! and the key it proves, and the [`WorldBindings`] a run ships by.
//!
//! # Boundaries
//!
//! - **The program by path.** A manifold names the program it deploys by its
//!   source's path, read from the manifold's own directory, and a run or a host
//!   of another source is refused. A located program's items have no content
//!   key yet, so no address names the program.
//! - **One process per world.** A placement counting other than one instance is
//!   refused by name.
//! - **A site's secret stays with its host.** The file names the public key;
//!   the hosting process proves it with the secret it holds.
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

use gandr_runtime_net::Lookup;
use gandr_runtime_net::NodeId;
use gandr_runtime_net::Peer;
use gandr_runtime_net::PeerError;
use gandr_runtime_net::WorldName;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::decode_escapes;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use crate::evaluate::WorldBindings;
use crate::evaluate::declaration_name;
use crate::workspace::Spelling;
use crate::workspace::Unran;
use crate::workspace::ran_alone;

/// One place a world runs at, as its file's `Site` model states it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Site
{
    /// The key the site proves.
    key: NodeId,
    /// The sockets it binds and is dialled at; none when it is found by its
    /// key alone.
    sockets: Vec<SocketAddr>,
}

impl Site
{
    /// The site the file at `file` states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the file checked alone over what it imports, and its
    ///   `Site.key` and `Site.sockets` run: the key read as 64 hexadecimal
    ///   digits, and each `,`-separated entry of the sockets, blank entries
    ///   skipped, read as `ip:port`.
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
    /// - hypothesis: L3 — the corpus site reads its key and socket; a site
    ///   whose key and socket do not read and one declaring no sockets are
    ///   refused at that field.
    /// - witness: `manifold::tests::a_site_and_a_manifold_read_from_their_files_3374`
    /// - witness: `manifold::tests::a_field_that_does_not_read_is_refused_by_name_3374`
    #[inline]
    pub fn read(file: &Path) -> Result<Self, Undeployed>
    {
        let [key, sockets] = ran_alone(file, [Stated::Key.name(), Stated::Sockets.name()])
            .map_err(|unran| Undeployed::of(file, unran))?;
        let key = strung(file, Stated::Key, key)?;
        let key = NodeId::from_str(&key).map_err(|refused| Undeployed::Unkeyed {
            file: file.to_path_buf(),
            refused,
        })?;
        let sockets = socketed(file, Written(&strung(file, Stated::Sockets, sockets)?))?;
        Ok(Self { key, sockets })
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

    /// Whether the key `proving` is the site's.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing when `proving` is the site's key;
    ///   [`Undeployed::Unproven`] naming both keys otherwise.
    /// - provides: the refusal of a host whose secret proves another key than
    ///   the site it hosts.
    /// - fails: [`Undeployed::Unproven`].
    /// - panics: none.
    /// - executable: none — the clause is the keys' equality the body computes,
    ///   a constant-time walk over both; the witness observes both outcomes.
    ///
    /// # Errors
    /// [`Undeployed::Unproven`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus site is proven by its key and refused for
    ///   another.
    /// - witness: `manifold::tests::a_site_and_a_manifold_read_from_their_files_3374`
    #[inline]
    pub fn proven(
        &self,
        proving: NodeId,
    ) -> Result<(), Undeployed>
    {
        if proving == self.key {
            return Ok(());
        }
        Err(Undeployed::Unproven {
            site: self.key,
            proving,
        })
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

/// A field a site's or a manifold's file states.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Stated
{
    /// `Site.key`.
    Key,
    /// `Site.sockets`.
    Sockets,
    /// `Manifold.artifact`.
    Artifact,
    /// `placements`.
    Placements,
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
            Self::Artifact => "Manifold.artifact",
            Self::Placements => "placements",
        })
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
                    Stated::Key | Stated::Sockets => {
                        "`module Site : Model(Site)` from `std.manifold`"
                    },
                    Stated::Artifact => "`module Manifold : Model(Manifold)` from `std.manifold`",
                    Stated::Placements => "`pub def placements : List(Placement)`",
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
            Self::Unproven { site, proving } => write!(
                f,
                "the site proves the key {site}, and the secret given proves {proving}: give the \
                 site's secret in `GANDR_NET_SECRET`"
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

#[cfg(test)]
mod tests;
