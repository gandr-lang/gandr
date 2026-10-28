use std::path::Path;
use std::path::PathBuf;

use gandr_runtime_net::Lookup;
use gandr_runtime_net::NodeId;
use gandr_runtime_net::Secret;
use gandr_runtime_net::WorldName;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::Manifold;
use super::Secreted;
use super::Secrets;
use super::Site;
use super::Stated;
use super::Undeployed;
use crate::compose::Composed;
use crate::walk::Step;
use crate::workspace::stepped_alone;

/// The corpus directory holding the migration model, its site and its
/// manifold.
///
/// # Specification
/// trivial.
fn worlds() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/worlds")
}

/// The key the corpus site names.
const SITE_KEY: &str = "ed4928c628d1c2c6eae90338905995612959273a5c63f93636c14614ac8737d1";

/// The key another secret proves: the two-process test's server's.
const OTHER_KEY: &str = "8139770ea87d175f56a35466c34c7ecccb8d8a91b4ee37a25df60f5b8fc9b394";

#[test]
fn a_site_and_a_manifold_read_from_their_files_3374()
{
    let worlds = worlds();
    let site = Site::read(&worlds.join("two-processes.site.gandr")).expect("the site reads");
    let key: NodeId = SITE_KEY.parse().expect("the key is hex");
    assert_eq!(
        (site.key(), site.sockets().to_vec(), site.lookup()),
        (
            key,
            Vec::from(["127.0.0.1:7433".parse().expect("a socket")]),
            Lookup::Explicit
        ),
        "the site reads its key and its one socket"
    );
    let manifold =
        Manifold::read(&worlds.join("two-processes.manifold.gandr")).expect("the manifold reads");
    assert_eq!(
        manifold.deploying(&worlds.join("two-processes.gandr")),
        Ok(()),
        "the manifold deploys the migration model beside it"
    );
    assert!(
        matches!(
            manifold.deploying(&worlds.join("twice.gandr")),
            Err(Undeployed::Elsewhere { .. })
        ),
        "and no other source"
    );
    assert_eq!(
        manifold.lookup(),
        Lookup::Explicit,
        "its site names a socket"
    );
    let bindings = manifold.into_bindings();
    assert_eq!(
        (
            bindings
                .peer(&WorldName::from("far"))
                .map(ToString::to_string),
            bindings.peer(&WorldName::from("near")).is_none()
        ),
        (Some(format!("{SITE_KEY}@127.0.0.1:7433")), true),
        "`far` is bound to the site's peer and `near` to nothing"
    );
}

/// A scratch tree holding `std.manifold` where the corpus imports it from, and
/// `file` beside where the corpus keeps its worlds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Scratch(PathBuf);

/// A file's text after its import of `std.manifold`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Text<'text>(&'text str);

impl Scratch
{
    /// A fresh tree named for `case`, `std.manifold`, `std.secret` and
    /// `std.authority` laid in it.
    ///
    /// # Specification
    /// trivial.
    fn new(case: &Path) -> Self
    {
        let root = std::env::temp_dir().join(format!(
            "gandr-dispatcher-manifold-{}-{}",
            case.display(),
            std::process::id()
        ));
        if root.exists() {
            std::fs::remove_dir_all(&root).expect("a stale scratch tree is removed");
        }
        let std = root.join("library/std/src");
        std::fs::create_dir_all(&std).expect("the library directory is created");
        std::fs::create_dir_all(root.join("corpus/model/worlds"))
            .expect("the worlds directory is created");
        for module in ["manifold.gandr", "secret.gandr", "authority.gandr"] {
            std::fs::copy(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../../library/std/src")
                    .join(module),
                std.join(module),
            )
            .expect("the module of `std` is copied");
        }
        Self(root)
    }

    /// Write `text` under the worlds directory as `name`, after the imports of
    /// `std.manifold` and `std.secret`, and return its path.
    ///
    /// # Specification
    /// trivial.
    fn file(
        &self,
        name: &Path,
        Text(text): Text<'_>,
    ) -> PathBuf
    {
        let path = self.0.join("corpus/model/worlds").join(name);
        std::fs::write(
            &path,
            format!(
                "import \"../../../library/std/src/manifold.gandr\";\nimport \
                 \"../../../library/std/src/secret.gandr\";\n{text}"
            ),
        )
        .expect("the file is written");
        path
    }
}

impl Drop for Scratch
{
    /// Remove the tree.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        let _removed = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn a_field_that_does_not_read_is_refused_by_name_3374()
{
    let scratch = Scratch::new(Path::new("refused"));
    let manifold = |name: &str, placements: &str| {
        scratch.file(
            Path::new(name),
            Text(&format!(
                "pub module Manifold : Model(Manifold) {{\n  def artifact = \"p.gandr\";\n}}\n{placements}"
            )),
        )
    };
    let twice = manifold(
        "twice.gandr",
        &format!(
            "pub module Site : Model(Site) {{\n  def key = \"{SITE_KEY}\";\n  def sockets = \
             \"\";\n  def secret = \"far\";\n}}\npub def placements : List(Placement) = \
             [Instances(\"far\", pack Site at Model(Site), 2)];\n"
        ),
    );
    assert!(
        matches!(
            Manifold::read(&twice),
            Err(Undeployed::Replicated { ref world, ref count, .. }) if world == "far" && count == "2"
        ),
        "a world run as two processes is refused, naming it and its count"
    );
    let unplaced = manifold("unplaced.gandr", "");
    assert!(
        matches!(
            Manifold::read(&unplaced),
            Err(Undeployed::Undeclared {
                field: Stated::Placements,
                ..
            })
        ),
        "a manifold listing no placements is refused at `placements`"
    );
    let listed = manifold(
        "listed.gandr",
        "pub def placements : List(String) = [\"far\"];\n",
    );
    assert!(
        matches!(
            Manifold::read(&listed),
            Err(Undeployed::Unplaced { ref came, .. }) if came == "cons(\"far\", nil)"
        ),
        "placements that are no placements are refused with what they ran to"
    );
    let site = |name: &str, key: &str, sockets: &str| {
        scratch.file(
            Path::new(name),
            Text(&format!(
                "pub module Site : Model(Site) {{\n  def key = \"{key}\";\n  def sockets = \
                 \"{sockets}\";\n  def secret = \"far\";\n}}\n"
            )),
        )
    };
    assert!(
        matches!(
            Site::read(&site("unkeyed.gandr", "abc", "")),
            Err(Undeployed::Unkeyed { .. })
        ),
        "a key that is no key is refused"
    );
    assert!(
        matches!(
            Site::read(&site("unsocketed.gandr", SITE_KEY, "127.0.0.1:7433, nowhere")),
            Err(Undeployed::Unsocketed { ref entry, .. }) if entry == "nowhere"
        ),
        "a socket that is no `ip:port` is refused, naming the entry"
    );
    assert_eq!(
        Site::read(&site("found.gandr", SITE_KEY, "")).map(|site| site.lookup()),
        Ok(Lookup::Mdns),
        "a site naming no socket is found by its key alone"
    );
}

/// The theory a site's own model answers a labelled `Store` with, and two
/// models of it: one at strings, one at integers.
const KEPT: &str = "pub theory Kept {\n  sort V : Type+;\n  sort C : Type;\n  oper get : (key \
                    : V, k : pi+ (v : V). C) --> C;\n  oper put : (key : V, value : V, k : C) \
                    --> C;\n}\npub module Echo : Model(Kept) with sort V = String {\n  type C = \
                    String;\n  def get(key : String, k : String => String) -> String { k(key) \
                    }\n  def put(key : String, value : String, k : String) -> String { k }\n}\npub \
                    module Counted : Model(Kept) with sort V = Integer {\n  type C = Integer;\n  \
                    def get(key : Integer, k : Integer => Integer) -> Integer { k(key) }\n  def \
                    put(key : Integer, value : Integer, k : Integer) -> Integer { k }\n}\n";

#[test]
fn a_world_s_row_is_judged_against_its_site_s_offer_3523()
{
    let judged = |path: &Path| Manifold::read(path).expect("the manifold reads").judged();
    let worlds = worlds();
    let deployments = worlds.join("../deployments");
    assert_eq!(
        judged(&deployments.join("offers.manifold.gandr")),
        Vec::new(),
        "a site granting `Console` and answering `store` with a model of its own takes `far`"
    );
    assert_eq!(
        judged(&worlds.join("two-processes.manifold.gandr")),
        Vec::new(),
        "a world requiring nothing is placed at a site offering nothing"
    );
    let states = |path: &Path| {
        let text = std::fs::read_to_string(path).expect("the source reads");
        stepped_alone(path, SourceText::from(text.as_str()), |step| {
            let Step::Source {
                composed:
                    Composed::Settled {
                        program, report, ..
                    },
                ..
            } = step
            else {
                return false;
            };
            matches!(Manifold::stated(&program, &report), Maybe::Present(_))
        })
    };
    assert_eq!(
        (
            states(&deployments.join("offers.manifold.gandr")),
            states(&deployments.join("offers.site.gandr"))
        ),
        (Ok(true), Ok(false)),
        "a manifold states its own artifact, and a site importing `std.manifold` beside it \
         states none"
    );
    let refused = judged(&worlds.join("../../pathological/worlds/offers.gandr"));
    assert!(
        matches!(
            refused.as_slice(),
            [
                Undeployed::Unoffered { entry: console, why: unlisted, .. },
                Undeployed::Unoffered { entry: store, why: typed, .. },
                Undeployed::Unworlded { world: nowhere, .. },
            ] if console == "Console"
                && unlisted.contains("does not list it")
                && store == "store"
                && typed.contains("expected `String`, found `Integer`")
                && nowhere.as_ref() == "nowhere"
        ),
        "an interface the offer leaves out, a label bound at other sorts, and a world the \
         program lacks are each refused by name: {refused:?}"
    );

    let scratch = Scratch::new(Path::new("offered"));
    let _program = scratch.file(
        Path::new("p.gandr"),
        Text(
            "pub theory Store {\n  sort V : Type+;\n  sort C : Type;\n  oper get : (key : V, k : \
             pi+ (v : V). C) --> C;\n  oper put : (key : V, value : V, k : C) --> C;\n}\npub \
             world far requires [Console, store : Store with sort V = String];\npub world netted \
             requires [Net];\npub world lost requires [Missing];\n",
        ),
    );
    let key = |byte: &str| {
        byte.repeat(32)
            .parse::<Secret>()
            .expect("the secret is hex")
            .node_id()
    };
    let site = |name: &str, key: &str, offers: &str| {
        scratch.file(
            Path::new(name),
            Text(&format!(
                "import \"../../../library/std/src/authority.gandr\";\n{KEPT}{offers}pub module \
                 Site : Model(Site) {{\n  def key = \"{key}\";\n  def sockets = \"\";\n  def \
                 secret = \"far\";\n}}\npub def site : Model(Site) = pack Site at \
                 Model(Site);\n"
            )),
        )
    };
    let _answered = site(
        "answered.gandr",
        SITE_KEY,
        "pub offers [Console, Net, store = Echo];\n",
    );
    let _typed = site(
        "typed.gandr",
        OTHER_KEY,
        "pub offers [Console, store = Counted];\n",
    );
    let _bare = site("bare.gandr", &key("22").to_string(), "");
    let local = key("11");
    let manifold = scratch.file(
        Path::new("m.gandr"),
        Text(&format!(
            "import \"./answered.gandr\" as answered;\nimport \"./typed.gandr\" as typed;\nimport \
             \"./bare.gandr\" as bare;\npub module Manifold : Model(Manifold) {{\n  def artifact \
             = \"p.gandr\";\n}}\npub module Local : Model(Site) {{\n  def key = \"{local}\";\n  \
             def sockets = \"\";\n  def secret = \"local\";\n}}\npub def placements : \
             List(Placement) = [\n  At(\"far\", answered.site),\n  At(\"far\", typed.site),\n  \
             At(\"far\", bare.site),\n  At(\"netted\", answered.site),\n  At(\"far\", pack Local \
             at Model(Site)),\n  At(\"lost\", typed.site),\n];\n"
        )),
    );
    let refused = judged(&manifold);
    assert!(
        matches!(
            refused.as_slice(),
            [
                Undeployed::Unoffered { entry: typed, why: sorts, .. },
                Undeployed::Unoffered { entry: console, why: unlisted, .. },
                Undeployed::Unoffered { entry: store, why: unbound, .. },
                Undeployed::Unoffered { entry: net, why: unheld, .. },
                Undeployed::Unsited { .. },
                Undeployed::Misworlded { world: lost, .. },
            ] if typed == "store"
                && sorts.contains("expected `String`, found `Integer`")
                && console == "Console"
                && unlisted.contains("does not list it")
                && store == "store"
                && unbound.contains("binds no module to it")
                && net == "Net"
                && unheld.contains("CapabilityAmplified")
                && lost.as_ref() == "lost"
        ),
        "a row answered whole holds; a label bound at other sorts is refused naming both \
         types, an offer leaving an entry out is refused at each, an interface the site's \
         authority does not hold is refused naming the capability, a site no imported file \
         states is unsited, and a refused world is refused as it is: {refused:?}"
    );
}

#[test]
fn a_site_reads_its_secret_from_the_model_given_3375()
{
    let worlds = worlds();
    let site = Site::read(&worlds.join("two-processes.site.gandr")).expect("the site reads");
    let key: NodeId = SITE_KEY.parse().expect("the key is hex");
    assert_eq!(
        site.variable(),
        "GANDR_SECRET_FAR",
        "the site's secret `far` is read from its upper-cased variable"
    );
    assert_eq!(
        site.secret(Secrets::Model(&worlds.join("two-processes.secrets.gandr")))
            .map(|secret| secret.node_id()),
        Ok(key),
        "the corpus model answers the secret proving the site's key, sealed as it is"
    );
    let scratch = Scratch::new(Path::new("secrets"));
    let named = scratch.file(
        Path::new("named.gandr"),
        Text(&format!(
            "pub module Site : Model(Site) {{\n  def key = \"{SITE_KEY}\";\n  def sockets = \
             \"\";\n  def secret = \"far-site.é\";\n}}\n"
        )),
    );
    assert_eq!(
        Site::read(&named).map(|site| site.variable()),
        Ok(String::from("GANDR_SECRET_FAR_SITE__")),
        "a hyphen, a dot and a letter outside ASCII are each spelled `_`"
    );
    let model = |name: &str, text: &str| {
        scratch.file(
            Path::new(name),
            Text(&format!(
                "pub module Secrets : Model(Secrets) with sort K = Secret.T {{\n  def \
                 secret(name : String) -> Secret.T {{ Secret.seal(\"{text}\") }}\n}}\n"
            )),
        )
    };
    let other = model("other.gandr", &"02".repeat(32));
    assert_eq!(
        site.secret(Secrets::Model(&other))
            .map(|secret| secret.node_id()),
        Err(Undeployed::Unproven {
            site: key,
            proving: OTHER_KEY.parse().expect("the key is hex"),
            from: Secreted::Model {
                file: other.clone(),
                name: String::from("far"),
            },
        }),
        "a secret proving another key is refused, naming both keys and the model"
    );
    let unkeyable = model("unkeyable.gandr", "hunter2");
    let refused = site
        .secret(Secrets::Model(&unkeyable))
        .map(|secret| secret.node_id());
    assert_eq!(
        refused,
        Err(Undeployed::Unkeyable {
            from: Secreted::Model {
                file: unkeyable,
                name: String::from("far"),
            },
        }),
        "a secret spelling no key is refused"
    );
    assert!(
        refused.is_err_and(|refusal| !refusal.to_string().contains("hunter2")),
        "and the refusal never spells the secret"
    );
    let modelless = scratch.file(Path::new("modelless.gandr"), Text("pub def other = 1;\n"));
    assert_eq!(
        site.secret(Secrets::Model(&modelless))
            .map(|secret| secret.node_id()),
        Err(Undeployed::Undeclared {
            file: modelless,
            field: Stated::Secrets,
        }),
        "a file declaring no `Secrets` model is refused at `Secrets.secret`"
    );
}
