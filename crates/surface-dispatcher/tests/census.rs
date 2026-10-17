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
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::TypeTable;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_dispatcher::lay_out;
    use gandr_surface_dispatcher::reprinted;
    use gandr_surface_dispatcher::signed;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_pretty::Form;
    use gandr_surface_pretty::PageWidth;
    use gandr_surface_pretty::Presentation;
    use gandr_surface_pretty::Unreadable;
    use gandr_surface_pretty::Unspelled;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
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

    /// `text` with every run of whitespace collapsed to one space and the ends
    /// stripped: the spelling a fixed point compares.
    ///
    /// # Specification
    /// trivial.
    fn collapsed(text: SourceText<'_>) -> String
    {
        text.as_ref()
            .split_whitespace()
            .collect::<Vec<&str>>()
            .join(" ")
    }

    /// The table of the walk's source at `path`, typed beside the siblings it
    /// imports: the walk's `text` lays out the source's import closure, its
    /// own text from `base`, and read as one source the importer's imports
    /// resolve to nothing and refuse every declaration of it (#552).
    ///
    /// # Specification
    /// trivial.
    fn typed(
        grammar: &Pbg,
        path: &Path,
        root: SourceRoot,
        (text, base): (SourceText<'_>, ByteOffset),
    ) -> Option<TypeTable>
    {
        let own = SourceText::from(text.as_ref().get(usize::from(base) ..)?);
        match lay_out(grammar, path, root, own) {
            Maybe::Present(laid) => TypeTable::of_unit(
                grammar,
                SourceText::from(laid.text.as_str()),
                &laid.unit,
                laid.base,
            )
            .ok(),
            Maybe::Absent(_) => TypeTable::of(grammar, text).ok(),
        }
    }

    /// The printer as a fixed point over the values the corpus states: each
    /// run value and normal form, printed, read back in its source and printed
    /// again, is the same spelling after whitespace collapses. A spelling the
    /// grammar reads as another value prints otherwise.
    #[derive(Debug, Default)]
    struct Fixed
    {
        /// Spellings read back and printed again.
        read: usize,
        /// Each spelling that printed otherwise or did not read back: the
        /// source, the spelling and what came back.
        moved: Vec<String>,
    }

    impl Fixed
    {
        /// Read `spelled` back in `table`, signed as `signed`'s run returns
        /// it, and compare its reprint.
        ///
        /// # Specification
        /// trivial.
        fn value(
            &mut self,
            path: &Path,
            table: &TypeTable,
            grammar: &Pbg,
            signed: Maybe<ConstantIndex, signed::Absent>,
            spelled: SourceText<'_>,
        )
        {
            self.read = self.read.saturating_add(1);
            let again = table.reprint_value(grammar, signed, spelled);
            if !matches!(again, Maybe::Present(ref again) if collapsed(SourceText::from(again.as_str())) == collapsed(spelled))
            {
                self.moved.push(format!(
                    "{}: `{spelled}` reprints as {again:?}",
                    path.display()
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
        let mut fixed = Fixed::default();
        let mut values = 0_usize;
        let mut walk = Walk::new(vec![root(Path::new("strict")), root(Path::new("fixture"))]);
        while let Maybe::Present(step) = walk.step() {
            let Step::Source {
                path,
                root,
                text,
                base,
                composed,
                ..
            } = step
            else {
                continue;
            };
            let table = typed(&grammar, path, root, (text, base));
            if let Some(ref table) = table {
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
                // Each normal form the corpus states, as the printer wrote it:
                // the side after `~>`.
                if let Some(ref table) = table {
                    for declaration in report.declarations() {
                        if let Stated::Verdict(Outcome::Normalizes(ref spelled)) =
                            *declaration.stated()
                            && let Some((_, normal)) = spelled.as_ref().split_once("~>")
                        {
                            fixed.value(
                                path,
                                table,
                                &grammar,
                                Maybe::Absent(signed::Absent::Unsigned),
                                SourceText::from(normal.trim()),
                            );
                        }
                    }
                }
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
                        if let Some(ref table) = table
                            && value.presentation().unspelled().is_empty()
                        {
                            fixed.value(
                                path,
                                table,
                                &grammar,
                                Maybe::Present(constant),
                                SourceText::from(value.presentation().as_ref()),
                            );
                        }
                    }
                }
            }
        }
        eprintln!("presentations read: {}", census.read);
        eprintln!("run values read: {values}");
        eprintln!("values read back and printed again: {}", fixed.read);
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
        assert!(
            fixed.read > 0_usize,
            "the corpus states values to print again"
        );
        assert_eq!(
            fixed.moved,
            Vec::<String>::new(),
            "every printed value reads back to a value printed alike"
        );
    }

    /// The read-back sweep: every printed type of each corpus source read back
    /// against its certificate, counted by how the trip ends and printed as a
    /// report. The counts are a measurement, not a gate (#467): a regression
    /// in the printer or the reading is pinned by a witness named for its
    /// issue, never by a count every landing must move. The classes:
    ///
    /// - `Equal`: the spelling reads back to the certificate's type.
    /// - `Different`: a spelling that reads back as another type.
    /// - `Open`: a type naming a binder or a capability scope of its context
    ///   that no parameter list declares: a binder the table keeps no type for,
    ///   a capability scope, or a context the read under it refuses.
    /// - `Refused`: a spelling that parses and refuses to lower.
    /// - `Unknown`: a type the printer writes with `?`, which the census of
    ///   honest `?` holds; nothing to read back.
    /// - `Unparsed`: a spelling the grammar refuses.
    /// - `Unspelled`: a type the printer could not spell at all.
    ///
    /// A visited type that reads back as another, does not parse, refuses to
    /// lower or cannot be laid out fails the sweep by name, as does one whose
    /// reading prints again otherwise (the printer as a fixed point): every
    /// printed type is a written type that reads back to its certificate.
    ///
    /// The sweep visits its sample under every pull-request profile and every
    /// source under the `sweeps` profile, as every sweep does
    /// (`gandr-workflow-sweep`); the nightly run prints the whole corpus's
    /// counts.
    mod sweeps
    {
        use gandr_workflow_sweep::Sample;
        use gandr_workflow_sweep::SampleName;
        use gandr_workflow_sweep::SampleSize;
        use gandr_workflow_sweep::Sweep;

        use super::*;

        /// The sample: sixty-four sources, ranked by their BLAKE3 digest under
        /// this name, at least one of each corpus class — `strict` and each
        /// directory below `fixture` — and every source the change adds or
        /// modifies (`gandr-workflow-sweep`).
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
            let sweep = Sweep::asked().expect("the run's sweep resolves");
            let visited = sweep.visit(SAMPLE, &sources);
            assert!(
                visited.len() >= SAMPLE.size.0,
                "the sample is drawn: {}",
                visited.len()
            );
            let visited: BTreeSet<PathBuf> =
                visited.into_iter().map(|source| source.path).collect();
            let corpus = gandr_workflow_sweep::corpus::directory().expect("the corpus resolves");
            let mut trips: BTreeMap<&str, usize> = BTreeMap::new();
            let mut unread: Vec<String> = Vec::new();
            let mut moved: Vec<String> = Vec::new();
            let mut walk = Walk::new(vec![corpus.join("strict"), corpus.join("fixture")]);
            while let Maybe::Present(step) = walk.step() {
                let Step::Source {
                    path,
                    root,
                    text,
                    base,
                    ..
                } = step
                else {
                    continue;
                };
                if !visited.contains(path) {
                    continue;
                }
                let Some(table) = typed(&grammar, path, root, (text, base))
                else {
                    continue;
                };
                for read in table.read_back(&grammar, page, Form::Sugared) {
                    let class = match read.trip {
                        RoundTrip::Equal => "Equal",
                        RoundTrip::Open => "Open",
                        RoundTrip::Unknown => "Unknown",
                        RoundTrip::Different => {
                            unread.push(format!(
                                "{}: `{}` reads back as another type",
                                path.display(),
                                read.spelled
                            ));
                            "Different"
                        },
                        RoundTrip::Refused(ref refusal) => {
                            unread.push(format!(
                                "{}: `{}` refuses: {refusal}",
                                path.display(),
                                read.spelled
                            ));
                            "Refused"
                        },
                        RoundTrip::Unparsed => {
                            unread.push(format!(
                                "{}: `{}` does not parse",
                                path.display(),
                                read.spelled
                            ));
                            "Unparsed"
                        },
                        RoundTrip::Unspelled => {
                            unread.push(format!(
                                "{}: {:?} is unspelled",
                                path.display(),
                                read.site
                            ));
                            "Unspelled"
                        },
                    };
                    *trips.entry(class).or_default() += 1;
                    // The fixed point: the spelling's reading, printed again,
                    // is the spelling.
                    match read.reprinted {
                        Maybe::Present(ref again)
                            if collapsed(SourceText::from(again.as_str()))
                                != collapsed(SourceText::from(read.spelled.as_str())) =>
                        {
                            moved.push(format!(
                                "{}: `{}` reprints as `{again}`",
                                path.display(),
                                read.spelled
                            ));
                        },
                        Maybe::Absent(reprinted::Absent::Unspelled) => {
                            moved.push(format!(
                                "{}: `{}` reads back to a type the printer cannot lay out",
                                path.display(),
                                read.spelled
                            ));
                        },
                        Maybe::Present(_)
                        | Maybe::Absent(reprinted::Absent::Unlowered | reprinted::Absent::Unrun) =>
                            {},
                    }
                }
            }
            for (class, count) in &trips {
                eprintln!("| {class} | {count} |");
            }
            assert!(
                trips.get("Equal").is_some_and(|&equal| equal > 0_usize),
                "the corpus's printed types read back"
            );
            assert_eq!(
                moved,
                Vec::<String>::new(),
                "every printed type is the printer's fixed point"
            );
            assert_eq!(
                unread,
                Vec::<String>::new(),
                "every printed type reads back to its certificate"
            );
        }
    }
}
