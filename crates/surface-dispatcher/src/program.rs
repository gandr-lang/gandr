//! A checked module as a program: each declaration focused into the command
//! IL once, and what a run reads of it.
//!
//! The composition builds a program for each module it settles, and a
//! closure keeps the part a document laid after it continues
//! ([`Focused`]). This module holds the data of a program, its construction
//! and its reads. The runs stand above the dispatcher, in the run stage
//! (`gandr-surface-evaluate`), which the composition reaches through
//! [`Engine`](crate::Engine).
//!
//! # A program is its declarations
//!
//! A program is the module's declarations, each a constant the machine
//! unfolds on demand. An accepted declaration's elaborated body is focused
//! once, when the program is built. A declaration owed its body, refused, or
//! whose body does not focus is carried as itself, the machine's opaque
//! constant. A position the program skips holds no declaration.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::ops::Range;

use anodized::spec;
use gandr_core_checker::Judged;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Verdict;
use gandr_core_incremental::Footprint;
use gandr_core_incremental::Reference;
use gandr_core_incremental::footprints;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::FocusRefusal;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Writers;
use gandr_core_sequent::focus_definition;
use gandr_core_sequent::spawn_independent_definitions;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::hole::HoleId;
use gandr_core_term::world::World;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_emitter::Play;
use gandr_runtime_net::NodeId;
use gandr_runtime_net::Peer;
use gandr_runtime_net::WorldName;
use gandr_surface_corpus::RunSpelling;
use gandr_surface_corpus::reads_spelled;
use gandr_surface_corpus::stating_reads;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::constant_paths;
use gandr_surface_diagnostics::read_by;
use gandr_surface_lowering::ChannelName;
use gandr_surface_lowering::Container;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::ENTRY;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::entry_shape;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::present_type;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::compose::item_program;
use crate::entry::entered::Entry;
use crate::entry::entered::program_entry;
use crate::entry::evaluation::declaration_name;
use crate::entry::evaluation::hole_site;
use crate::entry::evaluation::last_declared;
use crate::entry::worlds::WorldBindings;
use crate::typed::hidden_members;

quenchant_shape::reason_enum! {
    /// Why a program keeps no concurrent schedule of its definitions.
    pub mod concurrent {
        /// Every run unfolds the definitions as focused.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The judgement named no writer, so no definition holds a marked
            /// cut.
            Unmarked,
            /// The schedule's rewrite refused a node, so every run takes the
            /// sequential schedule.
            Refused,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a play is reported by no channel name.
    pub mod channel {
        /// The play's fork names no channel.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No source wrote the fork that opened it.
            Unnamed,
        }
    }
}

/// A checked module, focused and ready to run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program<'source>
{
    /// Every focused definition, and each command minted to run one.
    arena: CommandArena,
    /// What each constant unfolds to, by admission position.
    definitions: Definitions,
    /// The definitions with each marked cut rewritten into a spawn of its
    /// writer and a read of its handle: what a concurrent run unfolds.
    scheduled: Maybe<Definitions, concurrent::Absent>,
    /// Each declaration's name and standing, by admission position; a
    /// position no declaration holds is absent.
    declarations: BTreeMap<ConstantIndex, DeclaredRun<'source>>,
    /// The path of each constant in the source that declares it, by
    /// admission position: what a declaration is found by.
    names: Vec<String>,
    /// The name the printer writes for each constant in the source the
    /// program is read for, by admission position.
    printed: Vec<String>,
    /// The path of the module whose signature hides each hidden member, by
    /// the member's admission position.
    hidden: BTreeMap<ConstantIndex, String>,
    /// The path of the module that sealed the atom with no mark each
    /// declaration's declared type holds, by the declaration's admission
    /// position: a run of it is opaque at that module, whatever it reads back
    /// to.
    kept: BTreeMap<ConstantIndex, String>,
    /// The declared type, spelled on one line in each spelling, of each
    /// declaration whose run can reach a hidden member or is kept by a seal,
    /// by admission position and spelling.
    sealed: BTreeMap<(ConstantIndex, Spelling), String>,
    /// The name each fork the focused definitions hold gives its channel,
    /// its child end's binder as written, by the fork's command: a traced run
    /// reports each play by it.
    channels: BTreeMap<CommandId, ChannelName>,
    /// The constructors of the module's data declarations, by family.
    families: Families,
    /// The spelling its values and sealed types are written in.
    spelling: Spelling,
    /// The `main` the source run declares at its top level, when it declares
    /// one at an entry's type.
    entry: Maybe<Entry, program_entry::Absent>,
    /// The worlds the entry holds a capability for, in its `entry`
    /// attribute's order: the worlds a run of it may migrate to.
    reaches: Vec<ConstantIndex>,
    /// Where the program's sources write each hole an entry run can reach.
    holes: BTreeMap<HoleId, Maybe<ByteSpan, hole_site::Absent>>,
    /// The admission positions of the declarations the source run writes,
    /// among which its last declaration is read: every position, unless the
    /// source is laid after others in its unit.
    own: Range<ConstantIndex>,
    /// What each declaration stating a `reads` mentions, spelled as its
    /// payload is written, by admission position: none for a module whose
    /// declarations state none.
    reads: BTreeMap<ConstantIndex, RunSpelling>,
}

/// The part of a program a module's leading declarations make: each of them
/// focused, with the sealed type of each whose run reaches a hidden member and
/// the channel name of each fork they write. A program over a module they lead
/// continues it ([`Program::after`]).
///
/// # Specification
/// - executable: none — a data type; [`Program::after`] states what continuing
///   it answers.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Program::after`].
/// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
#[derive(Clone, Debug, Default)]
pub struct Focused<'source>
{
    /// Every focused definition.
    arena: CommandArena,
    /// What each constant unfolds to, by admission position.
    definitions: Definitions,
    /// Each declaration's name and standing, by admission position.
    declarations: BTreeMap<ConstantIndex, DeclaredRun<'source>>,
    /// The sealed declared types, by admission position and spelling.
    sealed: BTreeMap<(ConstantIndex, Spelling), String>,
    /// The name each fork gives its channel, by the fork's command.
    channels: BTreeMap<CommandId, ChannelName>,
}

impl Focused<'_>
{
    /// Share the focused rows with every copy made after
    /// ([`CommandArena::freeze`]): a program continuing a copy
    /// ([`Program::after`]) copies only the rows it focuses itself.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the arena's watermark, every definition and every declaration
    ///   are unchanged, and a program continuing it answers as one continuing
    ///   it unfrozen.
    /// - provides: the closure's focused program, which each document judged
    ///   after it continues at the cost of the document's own rows.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Program::after`]: a closure judged once, its
    ///   program frozen, judges each document as a whole judgement does.
    /// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
    #[spec(
        captures: entry = self.arena.watermark(),
        ensures: self.arena.watermark() == entry,
    )]
    #[inline]
    pub(crate) fn freeze(&mut self)
    {
        self.arena.freeze();
    }
}

/// One declaration of a program: its name and how it stands for a run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclaredRun<'source>
{
    /// The declared name.
    pub name: SurfaceName<'source>,
    /// How the declaration stands for a run.
    pub slot: Slot,
}

/// How one declaration stands for a run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Slot
{
    /// Its body focused; the constants the body refers to.
    Defined(Vec<ConstantIndex>),
    /// The checker refused it and its lowered body focused: it runs only as
    /// the root of a refused run, and any other run reaching it stops there as
    /// at a refusal; the constants the body refers to.
    Refused(Vec<ConstantIndex>),
    /// The machine carries it as itself, for the reason given.
    Opaque(Opacity),
}

/// Why the machine carries a declaration as itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Opacity
{
    /// A native datatype declares constructors, not an executable value.
    Data,
    /// It is owed its body, or waits on holes that are: running into it is
    /// blame.
    Owed,
    /// It was refused, by the lowering or the checker with no body that
    /// focuses, or the checker accepted it and recorded no body: there is
    /// nothing to run.
    Refused,
    /// Its body did not focus.
    Unfocused(FocusRefusal),
}

impl<'source> Program<'source>
{
    /// The program `module` and its verdicts describe, its accepted bodies
    /// read out of `core`.
    ///
    /// # Specification
    /// - requires: `verdicts` are the checker's report for `module`, judged
    ///   over `core`; the module's admission positions ascend and may skip a
    ///   position no declaration holds.
    /// - ensures: one entry per declaration of `module`, at its own admission
    ///   position, so a reference a body holds reads the declaration it names.
    ///   A declaration checked or synthesised has its elaborated body focused
    ///   and is defined as it; one owed its body is carried as itself; one the
    ///   checker refused has its lowered body focused, run only as the root of
    ///   [`Self::evaluate_refused`]; one refused by the lowering, or by the
    ///   checker with no body that focuses, or whose body does not focus, is
    ///   carried as itself and never run. A skipped position holds no
    ///   declaration and an opaque definition; a position met again keeps its
    ///   first declaration. Each member a module matched against a signature
    ///   keeps out of its interface is hidden at that module's path, and each
    ///   declaration whose references reach a hidden member, transitively,
    ///   holds its declared type spelled on one line, in each spelling, where
    ///   the printer can lay it out. Its values are spelled in
    ///   [`Spelling::Unicode`].
    /// - provides: the program every run of the module's declarations shares.
    /// - fails: never; a body that does not focus is the declaration's
    ///   standing, not a failure of the program.
    /// - panics: none.
    /// - intension: one focusing per accepted or checker-refused declaration;
    ///   nothing runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sources holding an accepted, an owed, a refused and
    ///   an unfocusable declaration are built and each run asserted at its
    ///   exact outcome. A module whose positions skip one keeps every
    ///   declaration at its admission position, a later body's reference to an
    ///   earlier one runs, and the skipped position is undeclared.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_run_reaching_a_goal_blames_it`
    /// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
    /// - witness: `evaluate::tests::a_skipped_admission_position_holds_no_declaration`
    #[spec(
        ensures: |ref ret| ret.spelling == Spelling::Unicode && usize::from(ret.definitions.len())
                == module.declarations().iter().map(|lowered| usize::from(lowered.constant()).saturating_add(1)).max().unwrap_or(0)
            && ret.declarations.keys().all(|constant| module.declarations().iter().any(|lowered| lowered.constant() == *constant))
            && module.declarations().iter().all(|lowered| ret.declarations.get(&lowered.constant()).is_some_and(|declared|
                module.declarations().iter().find(|first| first.constant() == lowered.constant()).is_some_and(|first| declared.name == first.name())))
            && (0..usize::from(ret.definitions.len())).all(|position| {
                let constant = ConstantIndex::from(position);
                match (ret.definitions.get(constant), ret.declarations.get(&constant).map(|declared| &declared.slot)) {
                    (Some(Definition::Transparent(producer)), Some(&(Slot::Defined(_) | Slot::Refused(_)))) => ret.arena.producer(producer).is_some(),
                    (Some(Definition::Opaque), Some(&Slot::Opaque(_)) | None) => true,
                    _ => false,
                }
            })
    )]
    #[must_use]
    pub(crate) fn new(
        core: &CoreArena,
        module: &LoweredModule<'source>,
        verdicts: &ModuleReport,
    ) -> Self
    {
        Self::after(Focused::default(), core, module, verdicts, &Writers::NONE)
    }

    /// [`Self::new`] continuing `focused`, the part of the program the
    /// module's leading declarations make: its declarations are taken as
    /// focused and sealed, and only the later ones are focused and spelled.
    /// Each later accepted body focuses each bind of `writers` apart, its
    /// binder marked independent.
    ///
    /// # Specification
    /// - requires: as [`Self::new`]; `focused` is [`Self::into_focused`] of the
    ///   program of a module whose declarations lead `module`'s, judged over an
    ///   arena `core` extends, its verdicts leading `verdicts`. `writers` names
    ///   computations of `core` the checker typed as performing nothing.
    /// - ensures: the program [`Self::new`] builds of `module`, but each later
    ///   accepted body focused with `writers`. When `writers` names a writer,
    ///   the program also keeps its definitions rewritten by
    ///   [`spawn_independent_definitions`], for a concurrent run to unfold.
    /// - provides: a document's program at the cost of its own declarations.
    /// - fails: never; a schedule the rewrite refuses leaves every run
    ///   sequential.
    /// - panics: none.
    /// - executable: none — the clause is [`Self::new`]'s answer over the whole
    ///   module; the witness compares the two.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document judged after a closure judged once
    ///   composes, its program included, as on a fresh judgement of the
    ///   closure; a position no declaration takes is skipped; a run naming a
    ///   hidden member reads the declared type the program sealed. Widening the
    ///   sealed filter to a declaration before `focused`'s boundary or one
    ///   reaching no hidden member changes no run: the first was sealed by the
    ///   leading program in the same spelling, and only a run whose read-back
    ///   mentions a hidden member reads the seal, which such a declaration's
    ///   run never does. A program focused with the tree sum's writers keeps
    ///   its definitions scheduled, and a program focused with none keeps none.
    /// - witness: `compose::tests::a_closure_judged_once_judges_each_document_alike_776`
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling`
    /// - witness: `evaluate::tests::a_skipped_admission_position_holds_no_declaration`
    /// - witness: `evaluate::tests::a_run_naming_a_hidden_member_is_opaque_at_its_module`
    /// - witness: `evaluate::tests::a_tree_sum_composed_concurrently_answers_as_the_sequential_schedule_2954`
    #[must_use]
    #[cfg_attr(feature = "hotpath", hotpath::measure)]
    pub(crate) fn after(
        focused: Focused<'source>,
        core: &CoreArena,
        module: &LoweredModule<'source>,
        verdicts: &ModuleReport,
        writers: &Writers,
    ) -> Self
    {
        let Focused {
            mut arena,
            mut definitions,
            mut declarations,
            mut sealed,
            mut channels,
        } = focused;
        // A program keeps of focusing's table only each fork's source, as
        // the name it gives its channel, so a continued focusing starts an
        // empty table; the leading program's names are already in
        // `channels`.
        let mut provenance = Provenance::new();
        let boundary = usize::from(definitions.len());
        let mut judged = verdicts.judged().iter().peekable();
        for lowered in module.declarations() {
            let constant = lowered.constant();
            let verdict = judged
                .next_if(|answer| answer.constant() == constant)
                .map(Judged::verdict);
            if usize::from(constant) < usize::from(definitions.len()) {
                continue;
            }
            let body = verdicts.definitions().get(&constant).copied();
            let (definition, slot) = match (verdict, body) {
                (Some(Verdict::Data), _) => (Definition::Opaque, Slot::Opaque(Opacity::Data)),
                (Some(Verdict::Checked { .. } | Verdict::Synthesised { .. }), Some(body)) => {
                    match focus_definition(core, body, &mut arena, &mut provenance, writers) {
                        Ok(producer) => (
                            Definition::Transparent(producer),
                            Slot::Defined(references(core, body)),
                        ),
                        Err(refusal) => (
                            Definition::Opaque,
                            Slot::Opaque(Opacity::Unfocused(refusal)),
                        ),
                    }
                },
                (Some(Verdict::Owed(_) | Verdict::Suspended(_)), _) => {
                    (Definition::Opaque, Slot::Opaque(Opacity::Owed))
                },
                (Some(Verdict::Refused(_)), _) => match lowered.outcome() {
                    DeclarationOutcome::Completed { body, .. }
                    | DeclarationOutcome::Bodied { body } => focus_definition(
                        core,
                        body,
                        &mut arena,
                        &mut provenance,
                        &gandr_core_sequent::Writers::NONE,
                    )
                    .map_or(
                        (Definition::Opaque, Slot::Opaque(Opacity::Refused)),
                        |producer| {
                            (
                                Definition::Transparent(producer),
                                Slot::Refused(references(core, body)),
                            )
                        },
                    ),
                    DeclarationOutcome::Uncompleted { .. }
                    | DeclarationOutcome::Data(_)
                    | DeclarationOutcome::Codata(_)
                    | DeclarationOutcome::Abstract(_)
                    | DeclarationOutcome::World
                    | DeclarationOutcome::Refused(_) => {
                        (Definition::Opaque, Slot::Opaque(Opacity::Refused))
                    },
                },
                (Some(Verdict::Checked { .. } | Verdict::Synthesised { .. }) | None, _) => {
                    (Definition::Opaque, Slot::Opaque(Opacity::Refused))
                },
            };
            while usize::from(definitions.len()) < usize::from(constant) {
                let _skipped = definitions.push(Definition::Opaque);
            }
            let _position = definitions.push(definition);
            let _fresh = declarations.insert(constant, DeclaredRun {
                name: lowered.name(),
                slot,
            });
        }
        let origins = module.origins();
        channels.extend(provenance.sessions().filter_map(|(command, source)| {
            match origins.fork(source) {
                Maybe::Present(name) => Some((command, name.clone())),
                Maybe::Absent(_) => None,
            }
        }));
        let names = constant_paths(module);
        let mut printed = names.clone();
        read_by(module, module.unit().last(), &mut printed);
        // A run's value is read back into an arena of its own, whose cases
        // the module's would misname.
        let families = Families::declared(module);
        let hidden = hidden_members(module);
        let kept = kept_members(core, module, verdicts);
        if !hidden.is_empty() || !kept.is_empty() {
            let reaching = reaching(&declarations, &hidden);
            let printing: Vec<Name<'_>> = printed
                .iter()
                .map(|name| Name::from(name.as_str()))
                .collect();
            let constructors = families.naming();
            let source = CoreSource::new(core, &printing).naming(&constructors);
            // A leading declaration's references, and the members it can
            // reach, are the leading module's, so its type was spelled
            // there.
            sealed.extend(
                verdicts
                    .judged()
                    .iter()
                    .filter(|judged| {
                        usize::from(judged.constant()) >= boundary
                            && (reaching.contains(&judged.constant())
                                || kept.contains_key(&judged.constant()))
                    })
                    .filter_map(|judged| match judged.verdict() {
                        Verdict::Checked { declared, .. } | Verdict::Suspended(declared) => {
                            Some((judged.constant(), declared.id()))
                        },
                        Verdict::Synthesised { synthesised, .. } => {
                            Some((judged.constant(), synthesised.produced().id()))
                        },
                        Verdict::Data | Verdict::Owed(_) | Verdict::Refused(_) => None,
                    })
                    .flat_map(|(constant, declared)| {
                        [Spelling::Unicode, Spelling::Ascii]
                            .map(|spelling| ((constant, spelling), declared))
                    })
                    .filter_map(|((constant, spelling), declared)| {
                        present_type(
                            &source,
                            CoreNode::ValueType(declared),
                            PageWidth::from(u32::from(u16::MAX)),
                            Style {
                                form: Form::Sugared,
                                spelling,
                            },
                        )
                        .ok()
                        .map(|spelled| ((constant, spelling), spelled.to_string()))
                    }),
            );
        }
        let entry = entry_of(core, module, verdicts);
        let reads = footprint_spellings(core, module);
        let scheduled = if *writers == Writers::NONE {
            Maybe::Absent(concurrent::Absent::Unmarked)
        }
        else {
            spawn_independent_definitions(&mut arena, &definitions)
                .map_or(Maybe::Absent(concurrent::Absent::Refused), Maybe::Present)
        };
        Self {
            arena,
            definitions,
            scheduled,
            declarations,
            names,
            printed,
            hidden,
            kept,
            sealed,
            channels,
            families,
            spelling: Spelling::Unicode,
            reaches: reaches(module, entry),
            entry,
            holes: hole_sites(core, module),
            own: ConstantIndex::from(0_usize) .. ConstantIndex::from(usize::MAX),
            reads,
        }
    }

    /// The part of this program a module laid after its module continues
    /// ([`Self::after`]): its focused declarations, sealed types and channel
    /// names.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn into_focused(self) -> Focused<'source>
    {
        let Self {
            arena,
            definitions,
            declarations,
            sealed,
            channels,
            ..
        } = self;
        Focused {
            arena,
            definitions,
            declarations,
            sealed,
            channels,
        }
    }

    /// This program, its values and sealed types written in `spelling`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every later run spells its value, or its sealed type, in
    ///   `spelling`; what runs is unchanged.
    /// - provides: the reader's spelling for `gandr run` and the session; a
    ///   `runs` expectation is compared in the program's own spelling, Unicode,
    ///   before any face asks for another.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value holding a relation runs to its spelling in
    ///   each spelling.
    /// - witness: `evaluate::tests::a_value_runs_to_its_spelling_in_either_spelling_782`
    #[spec(ensures: self.spelling == spelling)]
    #[inline]
    pub fn spell_in(
        &mut self,
        spelling: Spelling,
    )
    {
        self.spelling = spelling;
    }

    /// This program, run as the source whose declarations stand at the
    /// admission positions `own`.
    ///
    /// # Specification
    /// - requires: `own` holds exactly the positions of the declarations the
    ///   source writes.
    /// - ensures: [`Self::last_declared`] reads only the declarations at `own`;
    ///   nothing else changes.
    /// - provides: a source laid after the prelude and its imports reads its
    ///   own last declaration, never theirs.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the store is a move; [`Self::last_declared`] states
    ///   what it changes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a script declaring nothing, laid after the prelude,
    ///   has no program.
    /// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[inline]
    pub(crate) fn run_within(
        &mut self,
        own: Range<ConstantIndex>,
    )
    {
        self.own = own;
    }

    /// The declaration the source run declares last.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the highest admission position among the source's own
    ///   ([`Self::run_within`]): the name the source declared last for the
    ///   first time.
    /// - provides: the declarations a source writes end there.
    /// - fails: [`last_declared::Absent::NoDeclaration`] when the source
    ///   declares no name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source of several names, a later declaration of an
    ///   earlier name among them, a source of none, and a source of none laid
    ///   after the prelude.
    /// - witness: `evaluate::tests::the_last_declared_is_the_last_name_a_source_declares`
    /// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(last) => self.own.contains(&last) && self.declarations.contains_key(&last),
        Maybe::Absent(last_declared::Absent::NoDeclaration) => true,
    })]
    #[inline]
    pub fn last_declared(&self) -> Maybe<ConstantIndex, last_declared::Absent>
    {
        match self.declarations.range(self.own.clone()).next_back() {
            Some((&last, _)) => Maybe::Present(last),
            None => Maybe::Absent(last_declared::Absent::NoDeclaration),
        }
    }

    /// The name of the declaration at `constant`.
    ///
    /// # Specification
    /// - requires: nothing; any admission position may be queried.
    /// - ensures: the name stored at the exact position, or `Undeclared` when
    ///   no declaration holds the position, without truncating the index.
    /// - fails: an absent name is the typed absence, never a substitute name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct names retain their positions across a later
    ///   definition of an earlier name; empty and maximal-index queries are
    ///   absent.
    /// - witness: `evaluate::tests::the_last_declared_is_the_last_name_a_source_declares`
    #[spec(ensures: |ret| match (self.declarations.get(&constant), ret) {
        (Some(declared), Maybe::Present(name)) => declared.name == name,
        (None, Maybe::Absent(declaration_name::Absent::Undeclared)) => true,
        _ => false,
    })]
    #[inline]
    pub fn name(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<SurfaceName<'source>, declaration_name::Absent>
    {
        self.declarations.get(&constant).map_or(
            Maybe::Absent(declaration_name::Absent::Undeclared),
            |declared| Maybe::Present(declared.name),
        )
    }

    /// The declaration whose path from the top level is `path`, its segments
    /// joined by `.`: the last one declared at it when several are.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the highest admission position that holds a declaration and
    ///   whose path is `path`, as [`constant_paths`] spells it; `Undeclared`
    ///   when none is.
    /// - provides: the reading of a package's manifest fields by their path,
    ///   `Package.name`.
    /// - fails: an absent path is the typed absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's member is found by its whole path and not
    ///   by its bare name, and a path no declaration holds is undeclared.
    /// - witness: `evaluate::tests::a_member_is_named_by_its_whole_path_2687`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(constant) => self.declarations.contains_key(&constant)
            && self.names.get(usize::from(constant)).is_some_and(|name| name == path.as_ref()),
        Maybe::Absent(declaration_name::Absent::Undeclared) => true,
    })]
    #[inline]
    pub fn named(
        &self,
        path: SurfaceName<'_>,
    ) -> Maybe<ConstantIndex, declaration_name::Absent>
    {
        self.names
            .iter()
            .enumerate()
            .rev()
            .map(|(position, name)| (ConstantIndex::from(position), name))
            .find(|&(constant, name)| {
                name == path.as_ref() && self.declarations.contains_key(&constant)
            })
            .map_or(
                Maybe::Absent(declaration_name::Absent::Undeclared),
                |(constant, _)| Maybe::Present(constant),
            )
    }

    /// The declaration among `among` whose path from the top level is
    /// `path`: the last of them when several are.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the highest admission position of `among` that holds a
    ///   declaration and whose path is `path`, as [`Self::named`] reads one;
    ///   `Undeclared` when none of them is.
    /// - provides: the reading of a package's manifest fields among its package
    ///   source's own declarations, when its program holds another package
    ///   source declaring the same paths.
    /// - fails: an absent path is the typed absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member's path is found among declarations holding
    ///   it and not among ones that do not; a path among none is undeclared.
    /// - witness: `evaluate::tests::a_path_is_named_among_the_declarations_given_2687`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(constant) => self.declarations.contains_key(&constant)
            && self.names.get(usize::from(constant)).is_some_and(|name| name == path.as_ref()),
        Maybe::Absent(declaration_name::Absent::Undeclared) => true,
    })]
    #[inline]
    pub fn named_among<Among>(
        &self,
        path: SurfaceName<'_>,
        among: Among,
    ) -> Maybe<ConstantIndex, declaration_name::Absent>
    where
        Among: IntoIterator<Item = ConstantIndex>,
    {
        among
            .into_iter()
            .filter(|&constant| {
                self.declarations.contains_key(&constant)
                    && self
                        .names
                        .get(usize::from(constant))
                        .is_some_and(|name| name == path.as_ref())
            })
            .max()
            .map_or(
                Maybe::Absent(declaration_name::Absent::Undeclared),
                Maybe::Present,
            )
    }

    /// Each declaration whose accepted body did not focus, with the focusing's
    /// refusal, in admission order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the declarations whose bodies failed focusing, with
    ///   their own names and refusals, in admission order; other slots are
    ///   absent.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — anodized rejects postconditions on this opaque
    ///   iterator return type with E0562; observing the sequence requires
    ///   instrumentation support rather than changing the public signature.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — four codes, three of them reached through references,
    ///   are never listed, and the one transport the machine does not lower is;
    ///   other focusing refusal kinds are not generated.
    /// - witness: `evaluate::tests::a_code_and_every_reference_to_it_run_to_the_type_it_quotes`
    #[inline]
    pub fn focus_refusals(&self)
    -> impl Iterator<Item = (SurfaceName<'source>, FocusRefusal)> + '_
    {
        self.declarations
            .values()
            .filter_map(|declared| match declared.slot {
                Slot::Opaque(Opacity::Unfocused(refusal)) => Some((declared.name, refusal)),
                Slot::Defined(_)
                | Slot::Refused(_)
                | Slot::Opaque(Opacity::Data | Opacity::Owed | Opacity::Refused) => None,
            })
    }

    /// The declaration this program starts at: the `main` its source declares
    /// at the top level, at an entry's type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn entry(&self) -> Maybe<Entry, program_entry::Absent>
    {
        self.entry
    }

    /// The name `play`'s fork gives its channel, as the source writes it.
    ///
    /// # Specification
    /// - ensures: the binder the fork whose command opened the play writes at
    ///   its protocol; unnamed for a fork no source wrote.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::evaluate_traced`].
    /// - witness: `evaluate::tests::a_traced_run_names_each_channel_by_its_fork_3338`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(name) => self.channels.get(&play.fork).is_some_and(|held| held == name),
        Maybe::Absent(_) => !self.channels.contains_key(&play.fork),
    })]
    #[inline]
    pub fn channel(
        &self,
        play: &Play,
    ) -> Maybe<&ChannelName, channel::Absent>
    {
        self.channels
            .get(&play.fork)
            .map_or(Maybe::Absent(channel::Absent::Unnamed), Maybe::Present)
    }

    /// The parts of this program a run reads, the arena it mints its
    /// commands into among them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn parts(&mut self) -> Parts<'_, 'source>
    {
        Parts {
            arena: &mut self.arena,
            definitions: &self.definitions,
            scheduled: &self.scheduled,
            declarations: &self.declarations,
            names: &self.names,
            printed: &self.printed,
            hidden: &self.hidden,
            kept: &self.kept,
            sealed: &self.sealed,
            channels: &self.channels,
            families: &self.families,
            spelling: self.spelling,
            reaches: &self.reaches,
            holes: &self.holes,
            reads: &self.reads,
        }
    }

    /// Every world the entry holds a capability for, each bound to the host
    /// `here`: the bindings of a host that hosts every world shipped to it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn here(
        &self,
        here: NodeId,
    ) -> WorldBindings
    {
        self.reaches
            .iter()
            .filter_map(|&world| self.names.get(usize::from(world)))
            .map(|name| (WorldName::from(name.as_str()), Peer::new(here)))
            .collect()
    }
}

/// The parts of a program a run reads, borrowed from it: the arena it mints
/// its commands into, and the rest as the program holds it.
///
/// # Specification
/// - executable: none — a data type; [`Program::parts`] borrows it.
#[derive(Debug)]
pub struct Parts<'run, 'source>
{
    /// Every focused definition, and each command minted to run one.
    pub arena: &'run mut CommandArena,
    /// What each constant unfolds to, by admission position.
    pub definitions: &'run Definitions,
    /// The definitions a concurrent run unfolds, or why the program keeps
    /// none.
    pub scheduled: &'run Maybe<Definitions, concurrent::Absent>,
    /// Each declaration's name and standing, by admission position.
    pub declarations: &'run BTreeMap<ConstantIndex, DeclaredRun<'source>>,
    /// The path of each constant in the source that declares it.
    pub names: &'run Vec<String>,
    /// The name the printer writes for each constant.
    pub printed: &'run Vec<String>,
    /// The path of the module whose signature hides each hidden member.
    pub hidden: &'run BTreeMap<ConstantIndex, String>,
    /// The path of the module that sealed each kept declaration.
    pub kept: &'run BTreeMap<ConstantIndex, String>,
    /// The sealed declared types, by admission position and spelling.
    pub sealed: &'run BTreeMap<(ConstantIndex, Spelling), String>,
    /// The name each fork gives its channel, by the fork's command.
    pub channels: &'run BTreeMap<CommandId, ChannelName>,
    /// The constructors of the module's data declarations, by family.
    pub families: &'run Families,
    /// The spelling its values and sealed types are written in.
    pub spelling: Spelling,
    /// The worlds the entry holds a capability for.
    pub reaches: &'run Vec<ConstantIndex>,
    /// Where the program's sources write each hole an entry run can reach.
    pub holes: &'run BTreeMap<HoleId, Maybe<ByteSpan, hole_site::Absent>>,
    /// What each declaration stating a `reads` mentions.
    pub reads: &'run BTreeMap<ConstantIndex, RunSpelling>,
}

impl Parts<'_, '_>
{
    /// The world this program declares under `name`, its last declaration of
    /// that name.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn world_named(
        &self,
        name: &WorldName,
    ) -> Option<World>
    {
        self.declarations
            .iter()
            .rev()
            .find(|&(_, declared)| declared.name.as_ref() == name.as_ref())
            .map(|(&constant, _)| World::Declared(constant))
    }

    /// The first world the entry holds a capability for that `bindings`
    /// bind to no host.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn unbound(
        &self,
        bindings: &WorldBindings,
    ) -> Option<ConstantIndex>
    {
        self.reaches.iter().copied().find(|&world| {
            self.names
                .get(usize::from(world))
                .is_none_or(|name| bindings.peer(&WorldName::from(name.as_str())).is_none())
        })
    }
}

/// Each declaration outside a seal whose declared type holds the seal's atom
/// with no mark, with the path of the module that sealed it: a run of it
/// answers a value whose representation stays inside the seal.
///
/// # Specification
/// - requires: `verdicts` judged `module` over `core`.
/// - ensures: every judged declaration with a declared or synthesised type for
///   which [`ModuleReport::unmarked_atom`] meets an atom `module` declares,
///   unless the declaration stands in the module that declares the atom or one
///   nested in it, keyed by its position and holding the path, joined by `.`,
///   of the module the atom is declared in, or the atom's own name when it
///   stands at the top level.
/// - fails: never.
/// - panics: none.
/// - intension: a module with no coerced structure is skipped without a walk;
///   otherwise one walk of each declared type.
///
/// # Adequacy
/// - hypothesis: L3 — a run answering a secret, one answering it in a list, one
///   answering a marked report and a member run inside its own seal.
/// - witness: `evaluate::tests::a_run_answering_an_unmarked_sealed_type_is_opaque_at_its_seal_3375`
#[spec(ensures: |ref ret| ret.keys().all(|constant| verdicts.judged().iter().any(|judged| judged.constant() == *constant)))]
fn kept_members(
    core: &CoreArena,
    module: &LoweredModule<'_>,
    verdicts: &ModuleReport,
) -> BTreeMap<ConstantIndex, String>
{
    let mut kept = BTreeMap::new();
    if !module
        .structures()
        .iter()
        .any(|structure| structure.coerced().0)
    {
        return kept;
    }
    let declarations: BTreeMap<ConstantIndex, _> = module
        .declarations()
        .iter()
        .map(|declaration| (declaration.constant(), declaration))
        .collect();
    for judged in verdicts.judged() {
        let declared = match judged.verdict() {
            Verdict::Checked { declared, .. } | Verdict::Suspended(declared) => declared.id(),
            Verdict::Synthesised { synthesised, .. } => synthesised.produced().id(),
            Verdict::Data | Verdict::Owed(_) | Verdict::Refused(_) => continue,
        };
        let Maybe::Present(atom) = verdicts.unmarked_atom(core, declared)
        else {
            continue;
        };
        let Some(&sealing) = declarations.get(&atom)
        else {
            continue;
        };
        // A declaration's path is its container's, then its own name.
        let mut seal = module.path_of(sealing);
        let _name = seal.pop();
        let within = !seal.is_empty()
            && declarations.get(&judged.constant()).is_some_and(|run| {
                let mut container = module.path_of(run);
                let _name = container.pop();
                container.starts_with(&seal)
            });
        if within {
            continue;
        }
        let named = if seal.is_empty() {
            Vec::from([sealing.name()])
        }
        else {
            seal
        };
        let mut joined = String::new();
        for (index, segment) in named.iter().enumerate() {
            if index > 0 {
                joined.push('.');
            }
            joined.push_str(AsRef::<str>::as_ref(segment));
        }
        let _first = kept.insert(judged.constant(), joined);
    }
    kept
}

/// Every declaration whose references reach a member of `hidden`, directly or
/// through other declarations, the hidden members among them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the least set holding every hidden member and every defined
///   declaration one of whose references the set holds.
/// - fails: never.
/// - panics: none.
/// - intension: one pass building each constant's referrers, then a walk over
///   them from the hidden members on an explicit stack, each declaration
///   entered once.
///
/// # Adequacy
/// - hypothesis: L3 — as [`hidden_members`]: a model's interface operations
///   reach its helpers through their bodies.
/// - witness: `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`
#[spec(ensures: |ref ret| hidden.keys().all(|constant| ret.contains(constant)))]
fn reaching(
    declarations: &BTreeMap<ConstantIndex, DeclaredRun<'_>>,
    hidden: &BTreeMap<ConstantIndex, String>,
) -> BTreeSet<ConstantIndex>
{
    let mut referrers: BTreeMap<ConstantIndex, Vec<ConstantIndex>> = BTreeMap::new();
    for (&constant, declared) in declarations {
        if let Slot::Defined(ref referred) = declared.slot {
            for &target in referred {
                referrers.entry(target).or_default().push(constant);
            }
        }
    }
    let mut reached: BTreeSet<ConstantIndex> = hidden.keys().copied().collect();
    let mut pending: Vec<ConstantIndex> = reached.iter().copied().collect();
    while let Some(target) = pending.pop() {
        for &referrer in referrers.get(&target).into_iter().flatten() {
            if reached.insert(referrer) {
                pending.push(referrer);
            }
        }
    }
    reached
}

/// How a declaration reads when its item's content holds a node no arena
/// resolves: no footprint, and no `reads` payload writes this.
const UNRESOLVED_NODE: &str = "no footprint: a node of the item does not resolve";

/// How a declaration reads when its footprint holds a reference to no item:
/// no `reads` payload writes this.
const UNRESOLVED_REFERENCE: &str = "no footprint: a reference names no item";

/// What each declaration of `module` that states a `reads` mentions, spelled
/// as a `reads` payload writes it, by admission position.
///
/// # Specification
/// - requires: `module` was lowered into `core`.
/// - ensures: empty when no declaration states a `reads` ([`stating_reads`]);
///   else one spelling for each such declaration that is an item of the
///   module's item program ([`item_program`]), [`footprint_spelled`] of the
///   footprint read off its content table's roots.
/// - fails: never; a module whose positions do not ascend has no item program,
///   and no declaration of it has a footprint.
/// - panics: none.
/// - intension: the item program is built once, over a copy of `core`, and only
///   for a module one of whose declarations states what it reads.
///
/// # Adequacy
/// - hypothesis: L3 — a source whose declarations read a data type, its
///   constructors, a function and nothing, each settled against its claim.
/// - witness: `tests::corpus::a_reads_claim_settles_against_the_carried_footprint_2520`
#[spec(ensures: |ref ret| ret.keys().all(|constant| stating_reads(module).contains(constant)))]
fn footprint_spellings(
    core: &CoreArena,
    module: &LoweredModule<'_>,
) -> BTreeMap<ConstantIndex, RunSpelling>
{
    let stating: BTreeSet<ConstantIndex> = stating_reads(module).into_iter().collect();
    if stating.is_empty() {
        return BTreeMap::new();
    }
    let Ok(program) = item_program(module, core.clone())
    else {
        return BTreeMap::new();
    };
    program
        .items()
        .iter()
        .zip(footprints(&program))
        .filter(|&(item, _)| stating.contains(&item.declaration().constant()))
        .map(|(item, footprint)| (item.declaration().constant(), footprint_spelled(&footprint)))
        .collect()
}

/// The `reads` spelling of `footprint`: each item it names, by its key.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`reads_spelled`] of the keys of the items `footprint` reads, in
///   any position; [`UNRESOLVED_NODE`] for an opaque footprint, and for no
///   other, and [`UNRESOLVED_REFERENCE`] for one reading a position no item
///   holds, or a key that is no text.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`footprint_spellings`].
/// - witness: `tests::corpus::a_reads_claim_settles_against_the_carried_footprint_2520`
#[spec(ensures: |ref ret| (footprint.opacity() == gandr_core_incremental::Opacity::Opaque)
    == (*ret == RunSpelling::from(String::from(UNRESOLVED_NODE))))]
fn footprint_spelled(footprint: &Footprint) -> RunSpelling
{
    if footprint.opacity() == gandr_core_incremental::Opacity::Opaque {
        return RunSpelling::from(String::from(UNRESOLVED_NODE));
    }
    let mut names = Vec::with_capacity(footprint.reads().len());
    for read in footprint.reads() {
        let Reference::Item { ref key, .. } = *read
        else {
            return RunSpelling::from(String::from(UNRESOLVED_REFERENCE));
        };
        let Ok(name) = core::str::from_utf8(<&[u8]>::from(key.name()))
        else {
            return RunSpelling::from(String::from(UNRESOLVED_REFERENCE));
        };
        names.push(name);
    }
    reads_spelled(names)
}

/// The constants `body` refers to, outside its types.
///
/// # Specification
/// - requires: the reachable term graph is finite and acyclic; missing ids are
///   ignored rather than followed.
/// - ensures: one index per reference occurrence, preserving multiplicity;
///   quoted types and static code do not contribute references, and neither
///   does a hole. A constant root contributes only itself and an atomic
///   non-reference root contributes none.
/// - fails: never.
/// - panics: none.
/// - intension: traversal uses an explicit worklist without recursion.
///
/// # Adequacy
/// - hypothesis: L3 — real transitive source references prevent unsafe runs,
///   and a nested core value retains repeated references rather than
///   deduplicating. Every core wrapper is not separately generated.
/// - witness: `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`
/// - witness: `evaluate::tests::structured_values_keep_repeated_references_and_field_order`
#[spec(ensures: |ref ret| match core.value(body) {
    Some(&Value::Constant(constant)) => ret.iter().copied().eq([constant]),
    Some(&Value::Primitive { .. } |
&(Value::ListNil | Value::Variable { .. } | Value::Literal(_) | Value::Quote(_) |
Value::QuoteComputation(_) | Value::StaticLambda(_) |
Value::StaticApplication(..) | Value::Hole(_) | Value::Web(_) | Value::Row(_))) | None => ret.is_empty(),
    Some(&(Value::Constructor { .. } | Value::Record(_)) |
&Value::Reify(_) |
&Value::Univalence(..) |
&(Value::ListCons(..) | Value::PathRefl(_) | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::Compose { .. } | Value::Fill { .. } | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::RecordUpdate { .. } | Value::PathProduct(..) |
Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) | Value::Dialogue(_) |
Value::PathEquiv { .. } | Value::Tuple(_) | Value::Injection(..) |
Value::Lift { .. } | Value::Thunk(_) | Value::Mark { .. } | Value::Ascribe { .. })) => true,
})]
pub fn references(
    core: &CoreArena,
    body: ValueId,
) -> Vec<ConstantIndex>
{
    /// A node still to visit.
    #[derive(Clone, Copy)]
    enum Node
    {
        /// A value.
        Value(ValueId),
        /// A computation.
        Computation(ComputationId),
    }
    let mut referred = Vec::new();
    let mut pending = Vec::from([Node::Value(body)]);
    while let Some(node) = pending.pop() {
        match node {
            Node::Value(id) => {
                match core.value(id) {
                    Some(&Value::Constructor { ref fields, .. }) => {
                        pending.extend(fields.iter().copied().map(Node::Value));
                    },
                    Some(&Value::Record(ref fields)) => {
                        pending.extend(fields.values().copied().map(Node::Value));
                    },
                    Some(&Value::Reify(ref frames)) => {
                        pending.extend(frames.iter().filter_map(|frame| match *frame {
                            gandr_core_term::control::StackFrame::Apply(value) => {
                                Some(Node::Value(value))
                            },
                            gandr_core_term::control::StackFrame::Bind(body) => {
                                Some(Node::Computation(body))
                            },
                            gandr_core_term::control::StackFrame::Project(_) => None,
                        }));
                    },

                    Some(&Value::Constant(constant)) => referred.push(constant),
                    Some(
                        &(Value::PathProduct(first, second)
                        | Value::Funext(first, second)
                        | Value::Equiv(first, second)
                        | Value::Univalence(first, second)
                        | Value::Ua {
                            forward: first,
                            backward: second,
                            ..
                        }
                        | Value::PathEquiv {
                            forward: first,
                            backward: second,
                            ..
                        }
                        | Value::ListCons(first, second)
                        | Value::Then(first, second)
                        | Value::FlowProduct(first, second)
                        | Value::FunctionFlow(first, second)
                        | Value::RecordUpdate {
                            base: first,
                            overlay: second,
                        }),
                    ) => {
                        pending.extend([Node::Value(first), Node::Value(second)]);
                    },
                    Some(&Value::SessionRelated {
                        source,
                        target,
                        payloads,
                        ..
                    }) => {
                        pending.extend([source, target, payloads].map(Node::Value));
                    },
                    Some(&Value::Tuple(ref components)) => {
                        pending.extend(components.iter().map(|&component| Node::Value(component)));
                    },
                    // The realisation folds the cells' own nodes, so the
                    // cells alone carry each reference once.
                    Some(&Value::Compose { ref cells, .. }) => {
                        pending.extend(cells.iter().map(|&cell| Node::Value(cell)));
                    },
                    Some(&Value::Fill {
                        generator,
                        ref cells,
                        ..
                    }) => {
                        pending.push(Node::Computation(generator));
                        pending.extend(cells.iter().map(|&cell| Node::Value(cell)));
                    },
                    Some(
                        &(Value::PathRefl(inner)
                        | Value::Here(inner)
                        | Value::Stay(inner)
                        | Value::Forward(inner)
                        | Value::Injection(_, inner)
                        | Value::Lift { body: inner, .. }
                        | Value::Mark { body: inner, .. }
                        | Value::Ascribe { value: inner, .. }),
                    ) => {
                        pending.push(Node::Value(inner));
                    },
                    Some(&Value::Recorded(ref moves)) => {
                        pending.extend(moves.iter().filter_map(|step| match step.payload() {
                            Maybe::Present(payload) => Some(Node::Value(payload)),
                            Maybe::Absent(_) => None,
                        }));
                    },
                    Some(&Value::Dialogue(ref moves)) => {
                        pending.extend(moves.iter().filter_map(
                            |turn| match turn.movement.payload() {
                                Maybe::Present(payload) => Some(Node::Value(payload)),
                                Maybe::Absent(_) => None,
                            },
                        ));
                    },
                    Some(
                        &Value::Thunk(computation)
                        | &Value::Returned(computation)
                        | &Value::Nested(computation)
                        | &Value::Run(computation),
                    ) => {
                        pending.push(Node::Computation(computation));
                    },
                    Some(
                        &Value::Primitive { .. }
                        | &(Value::Variable { .. }
                        | Value::ListNil
                        | Value::Literal(_)
                        | Value::Quote(_)
                        | Value::QuoteComputation(_)
                        | Value::StaticLambda(_)
                        | Value::StaticApplication(..)
                        | Value::Hole(_)
                        | Value::Web(_)
                        | Value::Row(_)),
                    )
                    | None => {},
                }
            },
            Node::Computation(id) => match core.computation(id) {
                Some(&Computation::DataCase {
                    scrutinee,
                    ref branches,
                    ..
                }) => {
                    pending.push(Node::Value(scrutinee));
                    pending.extend(branches.iter().copied().map(Node::Computation));
                },
                Some(
                    &(Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _)),
                ) => {
                    pending.push(Node::Value(record));
                },
                Some(&Computation::Perform { payload, .. }) => pending.push(Node::Value(payload)),
                Some(
                    &(Computation::Handle {
                        subject,
                        on_return,
                        ref clauses,
                        ..
                    }
                    | Computation::Scope {
                        subject,
                        on_return,
                        ref clauses,
                        ..
                    }),
                ) => {
                    pending.extend([Node::Computation(subject), Node::Computation(on_return)]);
                    pending.extend(clauses.iter().map(|clause| Node::Computation(clause.body)));
                },
                Some(&Computation::Exercise {
                    capability,
                    payload,
                    ..
                }) => pending.extend([Node::Value(capability), Node::Value(payload)]),
                Some(
                    &(Computation::Resume(value, body)
                    | Computation::Split {
                        scrutinee: value,
                        body,
                        ..
                    }),
                ) => {
                    pending.extend([Node::Value(value), Node::Computation(body)]);
                },
                Some(
                    &(Computation::Reset(body)
                    | Computation::Shift(body)
                    | Computation::Project(_, body)
                    | Computation::Ascribe { body, .. }),
                ) => pending.push(Node::Computation(body)),
                Some(&Computation::With(ref components)) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| Node::Computation(component)),
                    );
                },

                Some(
                    &(Computation::ListFold {
                        list,
                        on_nil,
                        on_cons,
                        ..
                    }
                    | Computation::ListCase {
                        list,
                        on_nil,
                        on_cons,
                    }),
                ) => pending.extend([
                    Node::Value(list),
                    Node::Computation(on_nil),
                    Node::Computation(on_cons),
                ]),
                Some(&Computation::Primitive { ref arguments, .. }) => {
                    pending.extend(arguments.iter().copied().map(Node::Value));
                },
                Some(
                    &(Computation::Transport(path, value)
                    | Computation::PathTransport { path, value, .. }),
                ) => {
                    pending.extend([Node::Value(path), Node::Value(value)]);
                },
                Some(&Computation::Ride { flow, value, .. }) => {
                    pending.extend([Node::Value(flow), Node::Value(value)]);
                },
                Some(&Computation::TelescopeTransport {
                    path,
                    start,
                    over,
                    value,
                    ..
                }) => {
                    pending.extend([path, start, over, value].map(Node::Value));
                },
                Some(&(Computation::Lambda(inner) | Computation::LinearLambda(inner))) => {
                    pending.push(Node::Computation(inner));
                },
                Some(&Computation::Application(head, argument)) => {
                    pending.extend([Node::Computation(head), Node::Value(argument)]);
                },
                Some(
                    &(Computation::Return(value)
                    | Computation::Abandon(value)
                    | Computation::Force(value)
                    | Computation::Decompose(value)),
                ) => {
                    pending.push(Node::Value(value));
                },
                Some(&Computation::Bind(bound, rest)) => {
                    pending.extend([Node::Computation(bound), Node::Computation(rest)]);
                },
                Some(&Computation::BindAll { bound, body, .. }) => {
                    pending.extend([Node::Computation(bound), Node::Computation(body)]);
                },
                Some(&Computation::ReturnAll(ref values)) => {
                    pending.extend(values.iter().map(|&value| Node::Value(value)));
                },
                Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => {
                    pending.push(Node::Value(scrutinee));
                    pending.extend(branches.iter().map(|&branch| Node::Computation(branch)));
                },
                Some(&(Computation::Mark { body, .. } | Computation::Fixpoint { body, .. })) => {
                    pending.push(Node::Computation(body));
                },
                Some(&Computation::Session(ref action)) => {
                    pending.extend(action.values().map(Node::Value));
                    pending.extend(action.computations().map(Node::Computation));
                },
                Some(&Computation::Memory(ref form)) => {
                    pending.extend(form.values().map(Node::Value));
                    pending.extend(form.computations().map(Node::Computation));
                },
                Some(&Computation::World(ref form)) => {
                    pending.extend(form.values().map(Node::Value));
                    pending.extend(form.computations().map(Node::Computation));
                },
                Some(&Computation::Hole(_)) | None => {},
            },
        }
    }
    referred
}

/// The entry of the program over `module`: the `main` declared at the top
/// level of its last source, the one run, when the checker took it at an
/// entry's type.
///
/// # Specification
/// - requires: `verdicts` judged `module` over `core`.
/// - ensures: the admission position of the declaration named [`ENTRY`] at the
///   top level of the last source any top-level declaration of `module` stands
///   in — a stray, named by the token it opens with, is none — with the
///   arguments its declared type reads, when its verdict states a type
///   [`entry_shape()`] answers; the undeclared absence otherwise.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the module's sources and the verdicts
///   as the body does; the witness observes the entries.
///
/// # Adequacy
/// - hypothesis: L3 — a source declaring `main` of each entry type beside
///   another name, one declaring none, one whose module's member is the only
///   `main`, and one running `main()` after declaring it.
/// - witness: `evaluate::entry::tests::the_entry_is_the_main_of_the_source_run_1881`
fn entry_of(
    core: &CoreArena,
    module: &LoweredModule<'_>,
    verdicts: &ModuleReport,
) -> Maybe<Entry, program_entry::Absent>
{
    let undeclared = Maybe::Absent(program_entry::Absent::Undeclared);
    let top = |container: Container| match container {
        Container::TopLevel(source) => Some(source),
        Container::Module(_) => None,
    };
    let Some(run) = module
        .declarations()
        .iter()
        .filter_map(|lowered| top(lowered.container()))
        .max()
    else {
        return undeclared;
    };
    let Some(constant) = module
        .declarations()
        .iter()
        .filter(|lowered| {
            lowered.name().as_ref() == ENTRY
                && lowered.role() != Role::Held
                && top(lowered.container()) == Some(run)
        })
        .map(LoweredDeclaration::constant)
        .next_back()
    else {
        return undeclared;
    };
    let declared = verdicts
        .judged()
        .iter()
        .find(|judged| judged.constant() == constant)
        .and_then(|judged| match judged.verdict() {
            Verdict::Checked { declared, .. } | Verdict::Suspended(declared) => Some(declared.id()),
            Verdict::Synthesised { .. }
            | Verdict::Data
            | Verdict::Owed(_)
            | Verdict::Refused(_) => None,
        });
    match declared.map(|declared| entry_shape(core, declared)) {
        Some(Maybe::Present(arguments)) => Maybe::Present(Entry {
            constant,
            arguments,
        }),
        Some(Maybe::Absent(_)) | None => undeclared,
    }
}

/// The worlds `entry`'s declaration holds a capability for, in its `entry`
/// attribute's order: none for a module with no entry, or an entry no such
/// attribute decorates.
///
/// # Specification
/// - requires: `entry` is the entry of `module`.
/// - ensures: the worlds after the first — the home — that the entry's
///   attribute names, as [`LoweredModule::worlds`] answers them.
/// - fails: never.
/// - panics: none.
/// - executable: none — the answer is the module's attribute table read at the
///   entry's keys.
///
/// # Adequacy
/// - hypothesis: L3 — an entry holding a capability for a world no binding
///   names is refused before it runs, and one whose bindings bind it runs.
/// - witness: `tests::run::a_world_no_binding_names_is_refused_before_the_run`
fn reaches(
    module: &LoweredModule<'_>,
    entry: Maybe<Entry, program_entry::Absent>,
) -> Vec<ConstantIndex>
{
    let Maybe::Present(Entry { constant, .. }) = entry
    else {
        return Vec::new();
    };
    module
        .declarations()
        .iter()
        .rfind(|lowered| lowered.constant() == constant)
        .and_then(|lowered| module.worlds(lowered).get(1 ..))
        .map(<[ConstantIndex]>::to_vec)
        .unwrap_or_default()
}

/// Where `module` writes each hole a run can reach, by its name: the span of
/// the one hole bearing it, or the shared absence where holes of several
/// sources share one name.
///
/// # Specification
/// - requires: `module` was lowered into `core`.
/// - ensures: every hole a computation of `module`'s origins holds is keyed; a
///   name every such computation writes at one span maps to that span, and one
///   written at two spans to [`hole_site::Absent::Shared`].
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the walk over the origins.
///
/// # Adequacy
/// - hypothesis: L3 — a run reaching a hole is reported at the hole's span.
/// - witness: `evaluate::entry::tests::a_hole_reached_stops_the_entry_by_name_1881`
fn hole_sites(
    core: &CoreArena,
    module: &LoweredModule<'_>,
) -> BTreeMap<HoleId, Maybe<ByteSpan, hole_site::Absent>>
{
    let mut sites = BTreeMap::new();
    for &(computation, origin) in module.origins().computations() {
        let Some(&Computation::Hole(hole)) = core.computation(computation)
        else {
            continue;
        };
        let span = origin.span();
        let _held = sites
            .entry(hole)
            .and_modify(|site: &mut Maybe<ByteSpan, hole_site::Absent>| {
                if *site != Maybe::Present(span) {
                    *site = Maybe::Absent(hole_site::Absent::Shared);
                }
            })
            .or_insert(Maybe::Present(span));
    }
    sites
}
