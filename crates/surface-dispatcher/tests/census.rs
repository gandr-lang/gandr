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
                | Self::Entry(at) => write!(f, "{}", usize::from(at)),
                | Self::Declaration => f.write_str("declaration"),
                | Self::Run(constant) => write!(f, "run {}", usize::from(constant)),
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
}
