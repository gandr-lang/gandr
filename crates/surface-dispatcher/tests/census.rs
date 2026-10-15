//! The presentation census: every entry of every corpus source's type table
//! and every value a corpus declaration states it runs to, spelled, and each
//! `?` the printer writes counted by why.

extern crate alloc;

/// The census, in a `cfg(test)` module so the crate's lint wall reads it as
/// test code rather than as shipping code.
#[cfg(test)]
mod census
{
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_corpus::Outcome;
    use gandr_surface_corpus::Stated;
    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::Declared;
    use gandr_surface_dispatcher::Evaluation;
    use gandr_surface_dispatcher::RoundTrip;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::TypeTable;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_grammar::built_in;
    use gandr_surface_pretty::Form;
    use gandr_surface_pretty::PageWidth;
    use gandr_surface_pretty::Presentation;
    use gandr_surface_pretty::Unreadable;
    use gandr_surface_pretty::Unspelled;
    use gandr_surface_syntax::ByteOffset;
    use quenchant_shape::shape::Maybe;

    /// The page a hover spells on.
    const PAGE: u32 = 80;

    /// The corpus directory `name`, under the corpus crate.
    ///
    /// # Specification
    /// trivial.
    fn root(name: &Path) -> PathBuf
    {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus")
            .join(name)
    }

    /// The honest set: the reasons whose `?` says what the checker knows.
    const HONEST: [Unspelled; 5] = [
        Unspelled::Unreadable(Unreadable::UnknownType),
        Unspelled::Unreadable(Unreadable::Hole),
        Unspelled::Unreadable(Unreadable::Mark),
        Unspelled::Unreadable(Unreadable::Lift),
        Unspelled::Unreadable(Unreadable::NumericAtom),
    ];

    /// Where a presentation was read.
    #[derive(Clone, Copy, Debug)]
    enum Site
    {
        /// A type-table entry starting at this byte.
        Entry(ByteOffset),
        /// A declaration's type.
        Declaration,
        /// The value the declaration at this admission position runs to.
        Run(ConstantIndex),
    }

    impl core::fmt::Display for Site
    {
        /// The byte, the declaration or the run position.
        ///
        /// # Specification
        /// trivial.
        fn fmt(
            &self,
            f: &mut core::fmt::Formatter<'_>,
        ) -> core::fmt::Result
        {
            match *self {
                Self::Entry(at) => write!(f, "{}", usize::from(at)),
                Self::Declaration => f.write_str("declaration"),
                Self::Run(constant) => write!(f, "run {}", usize::from(constant)),
            }
        }
    }

    /// What the census counted.
    #[derive(Debug, Default)]
    struct Census
    {
        /// Presentations read.
        read: usize,
        /// Presentations holding a `?`, by why.
        reasons: BTreeMap<String, usize>,
        /// Each presentation holding a `?` outside the honest set: the
        /// source, the offset and the reasons.
        dishonest: Vec<String>,
    }

    impl Census
    {
        /// Count `presentation`, read at `site` of `path`.
        ///
        /// # Specification
        /// trivial.
        fn count(
            &mut self,
            path: &Path,
            site: Site,
            presentation: &Presentation,
        )
        {
            self.read = self.read.saturating_add(1);
            for &reason in presentation.unspelled() {
                let tally = self.reasons.entry(format!("{reason:?}")).or_default();
                *tally = tally.saturating_add(1);
            }
            if presentation
                .unspelled()
                .iter()
                .any(|reason| !HONEST.contains(reason))
            {
                self.dishonest.push(format!(
                    "{}@{site}: `{presentation}` {:?}",
                    path.display(),
                    presentation.unspelled()
                ));
            }
        }
    }

    #[test]
    fn every_typed_entry_spells_without_a_dishonest_question_mark()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let page = PageWidth::from(PAGE);
        let mut census = Census::default();
        let mut values = 0_usize;
        let mut walk = Walk::new(vec![root(Path::new("strict")), root(Path::new("fixture"))]);
        while let Maybe::Present(step) = walk.step() {
            let Step::Source {
                path,
                text,
                composed,
                ..
            } = step
            else {
                continue;
            };
            if let Ok(table) = TypeTable::of(&grammar, text) {
                for entry in table.entries(page, Form::Sugared) {
                    let Maybe::Present(entry) = entry
                    else {
                        continue;
                    };
                    let site = Site::Entry(entry.span().start());
                    census.count(path, site, entry.ty());
                    if let Maybe::Present(expected) = entry.expected() {
                        census.count(path, site, expected);
                    }
                }
                for (_, declared) in table.declarations(page, Form::Sugared) {
                    if let Maybe::Present(Declared::Typed(ty)) = declared {
                        census.count(path, Site::Declaration, &ty);
                    }
                }
            }
            if let Composed::Settled {
                report,
                mut program,
                ..
            } = composed
            {
                let stated: BTreeSet<String> = report
                    .declarations()
                    .iter()
                    .filter(|declaration| {
                        matches!(declaration.stated(), Stated::Verdict(Outcome::Runs(_)))
                    })
                    .map(|declaration| declaration.name().to_string())
                    .collect();
                let Maybe::Present(last) = program.target()
                else {
                    continue;
                };
                for position in 0_usize ..= usize::from(last) {
                    let constant = ConstantIndex::from(position);
                    let Maybe::Present(name) = program.name(constant)
                    else {
                        continue;
                    };
                    if !stated.contains(&name.to_string()) {
                        continue;
                    }
                    if let Evaluation::Value(value) = program.evaluate(constant) {
                        values = values.saturating_add(1);
                        census.count(path, Site::Run(constant), value.presentation());
                    }
                }
            }
        }
        eprintln!("presentations read: {}", census.read);
        eprintln!("run values read: {values}");
        for (reason, count) in &census.reasons {
            eprintln!("| {reason} | {count} |");
        }
        assert!(values > 0_usize, "the corpus states run values");
        assert!(census.read > 0_usize, "the corpus holds typed entries");
        assert_eq!(
            census.dishonest,
            Vec::<String>::new(),
            "every `?` is a member of the honest set"
        );
    }

    /// The printed types that do not read back to their certificate's, by how,
    /// above which the printer or the reading has regressed: each count must
    /// not rise, and a commit lowering one moves its row. Absolute counts,
    /// so a corpus source deleted takes its misses with it.
    ///
    /// - `Different`: a spelling that reads back as another type — an unused
    ///   binder printed (#398), a session state or a capability region dropped
    ///   (#400), a term inside a type read as another (#402).
    /// - `Open`: a type naming a binder in scope, not read (#403).
    /// - `Refused`: a spelling that parses and refuses to lower (#401, #402).
    /// - `Unknown`: a type the printer writes with `?`, which the census of
    ///   honest `?` holds; nothing to read back.
    /// - `Unparsed`: a spelling the grammar refuses (#401).
    /// - `Unspelled`: a type the printer could not spell at all.
    const READ_BACK_MISSES: [(&str, usize); 6] = [
        ("Different", 350),
        ("Open", 1247),
        ("Refused", 30),
        ("Unknown", 129),
        ("Unparsed", 174),
        ("Unspelled", 0),
    ];

    /// The read-back sweep: every printed type of each corpus source read back
    /// against its certificate.
    ///
    /// In the plain build the sweep reads every source under every profile:
    /// its ceilings are absolute counts over the whole corpus, which a
    /// sample's counts can never rise above, so a change that moves one would
    /// pass its pull request and fail only `main`'s nightly run (#454). The
    /// counts do not depend on the build, so with specifications enforced it
    /// reads its sample, which holds the enforced run to the test bound, and
    /// every source under the `sweeps` profile. Every run prints the counts.
    mod sweeps
    {
        use gandr_workflow_sweep::Sample;
        use gandr_workflow_sweep::SampleName;
        use gandr_workflow_sweep::SampleSize;
        use gandr_workflow_sweep::Sweep;

        use super::*;

        /// The sample with specifications enforced: sixty-four sources,
        /// ranked by their BLAKE3 digest under this name, at least one of each
        /// corpus class — `strict` and each directory below `fixture` — and
        /// every source the change adds or modifies (`gandr-workflow-sweep`).
        const SAMPLE: Sample = Sample {
            name: SampleName("every_printed_type_reads_back_to_its_certificate"),
            size: SampleSize(64),
        };

        #[test]
        fn every_printed_type_reads_back_to_its_certificate()
        {
            let grammar = built_in().expect("the built-in grammar builds");
            let page = PageWidth::from(PAGE);
            let sources = gandr_workflow_sweep::corpus::sources().expect("the corpus reads");
            let visited: BTreeSet<PathBuf> = if cfg!(anodized_panic) {
                let sweep = Sweep::asked().expect("the run's sweep resolves");
                let visited = sweep.visit(SAMPLE, &sources);
                assert!(
                    visited.len() >= SAMPLE.size.0,
                    "the sample is drawn: {}",
                    visited.len()
                );
                visited.into_iter().map(|source| source.path).collect()
            }
            else {
                sources.into_iter().map(|source| source.path).collect()
            };
            let corpus = gandr_workflow_sweep::corpus::directory().expect("the corpus resolves");
            let mut trips: BTreeMap<&str, usize> = BTreeMap::new();
            let mut walk = Walk::new(vec![corpus.join("strict"), corpus.join("fixture")]);
            while let Maybe::Present(step) = walk.step() {
                let Step::Source { path, text, .. } = step
                else {
                    continue;
                };
                if !visited.contains(path) {
                    continue;
                }
                let Ok(table) = TypeTable::of(&grammar, text)
                else {
                    continue;
                };
                for read in table.read_back(&grammar, page, Form::Sugared) {
                    let class = match read.trip {
                        RoundTrip::Equal => "Equal",
                        RoundTrip::Different => "Different",
                        RoundTrip::Open => "Open",
                        RoundTrip::Refused(_) => "Refused",
                        RoundTrip::Unknown => "Unknown",
                        RoundTrip::Unparsed => "Unparsed",
                        RoundTrip::Unspelled => "Unspelled",
                    };
                    *trips.entry(class).or_default() += 1;
                }
            }
            for (class, count) in &trips {
                eprintln!("| {class} | {count} |");
            }
            assert!(
                trips.get("Equal").is_some_and(|&equal| equal > 0_usize),
                "the corpus's printed types read back"
            );
            let risen: Vec<String> = READ_BACK_MISSES
                .iter()
                .filter_map(|&(class, ceiling)| {
                    let count = trips.get(class).copied().unwrap_or_default();
                    (count > ceiling).then(|| format!("{class}: {count}, above {ceiling}"))
                })
                .collect();
            assert_eq!(
                risen,
                Vec::<String>::new(),
                "printed types that do not read back"
            );
        }
    }
}
