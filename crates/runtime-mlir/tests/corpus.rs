//! The agreement of the executor and the compiled code on the corpus: each
//! `runs` item of `corpus/model/programs` that the lowering accepts gives one
//! answer on both, and each item that it refuses is counted by the name of the
//! refusal. They run under the feature `full`, which links the shim.
//!
//! Each source is composed alone, with no prelude and no import, as
//! `gandr_surface_dispatcher::compose` composes it. The lowering takes each
//! definition of a module, and the prelude has definitions outside the
//! lowering. The answer of the executor is the run of the settle comparison.
//! The compiled code is the module with the entry of the item, linked with the
//! `ld.lld` of the pin. Its exit code is the low byte of the answer.

#![cfg(feature = "full")]

extern crate alloc;

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use std::path::Path;

    use gandr_core_checker::Verdict;
    use gandr_core_sequent::Definition as Focused;
    use gandr_core_term::ValueTypeId;
    use gandr_kernel_term::ConstantIndex;
    use gandr_runtime_mlir::Definition;
    use gandr_runtime_mlir::ENTRY;
    use gandr_runtime_mlir::Entry;
    use gandr_runtime_mlir::Lowered;
    use gandr_runtime_mlir::Symbol;
    use gandr_runtime_mlir::compile;
    use gandr_runtime_mlir::lower;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_corpus::Outcome;
    use gandr_surface_corpus::Stated;
    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::HostGrant;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::judge;
    use gandr_surface_dispatcher::lower_source;
    use gandr_surface_evaluate::Evaluator;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    /// The directory of the programs of the corpus.
    const PROGRAMS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../corpus/model/programs");

    /// The target of each compiled program.
    const TRIPLE: &str = "x86_64-unknown-linux-gnu";

    /// What the compiled code of one `runs` item came to.
    #[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum Came
    {
        /// The compiled code exits with the low byte of the answer of the
        /// executor.
        Agreed,
        /// The step that refused the item, and the name of its refusal.
        Refused(String),
    }

    /// The low byte of a literal of a width as the executor spells it, such as
    /// `255u8` or `-1i8`: the exit code of a program that answers it.
    ///
    /// # Specification
    /// trivial.
    fn low_byte(spelled: &str) -> Option<i32>
    {
        let digits = spelled.find(['u', 'i']).filter(|&at| at > 0)?;
        let (number, suffix) = spelled.split_at(digits);
        let width = suffix.get(1 ..)?;
        if width.is_empty() || !width.bytes().all(|byte| byte.is_ascii_digit()) {
            return None;
        }
        let value: i128 = number.parse().ok()?;
        i32::try_from(value.rem_euclid(256)).ok()
    }

    /// Compile `lowered` with `entry`, link it with the `ld.lld` of the pin,
    /// run it, and give its exit code.
    ///
    /// # Specification
    /// trivial.
    fn exit_code(
        lowered: &Lowered<'_>,
        entry: Entry<'_>,
        label: &str,
    ) -> i32
    {
        let text = format!("{lowered}{entry}");
        let object = compile(text.as_str().into(), TRIPLE.into()).unwrap_or_else(|error| {
            panic!("{label}: the shim refuses the module: {error}\n{text}")
        });
        let directory =
            std::env::temp_dir().join(format!("gandr-corpus-{label}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let object_path = directory.join("main.o");
        let executable = directory.join("main");
        std::fs::write(&object_path, object.as_ref()).unwrap();
        let toolchain = std::env::var_os("GANDR_MLIR_TOOLCHAIN")
            .unwrap_or_else(|| panic!("GANDR_MLIR_TOOLCHAIN names the archive of the pin"));
        let linked = std::process::Command::new(Path::new(&toolchain).join("bin").join("ld.lld"))
            .arg("-o")
            .arg(&executable)
            .args(["--entry", ENTRY])
            .arg(&object_path)
            .output()
            .unwrap();
        assert!(
            linked.status.success(),
            "{label}: ld.lld refuses the object:\n{}\n{text}",
            String::from_utf8_lossy(&linked.stderr)
        );
        let run = std::process::Command::new(&executable).status().unwrap();
        std::fs::remove_dir_all(&directory).unwrap();
        run.code()
            .unwrap_or_else(|| panic!("{label}: a signal ends the compiled code"))
    }

    /// Each `runs` item of the program at `path`, by its name, with what its
    /// compiled code came to.
    ///
    /// # Specification
    /// trivial.
    fn items(path: &Path) -> Vec<(String, Came)>
    {
        let grammar = built_in().expect("the built-in surface passes each gate");
        let text = std::fs::read_to_string(path).unwrap();
        let source = SourceText::from(text.as_str());
        let file = path.file_stem().unwrap().to_string_lossy().into_owned();
        let lowering = lower_source(&grammar, source, &mut LoweringCount::default())
            .unwrap_or_else(|fault| panic!("{file}: the source parses and lowers: {fault:?}"));
        let gandr_surface_dispatcher::Lowered::Module { module, arena } = lowering.into_lowered()
        else {
            return vec![(
                file,
                Came::Refused(String::from("surface: the source as a whole")),
            )];
        };
        let (settled, admission) = judge::<Evaluator>(
            CorpusRoot::Fixture,
            (module, source),
            arena,
            &HostGrant::UNBOUNDED,
        )
        .into_parts();
        let Ok(Composed::Settled {
            report, program, ..
        }) = settled
        else {
            return vec![(
                file,
                Came::Refused(String::from("settle: the source as a whole")),
            )];
        };
        let declared: BTreeMap<ConstantIndex, ValueTypeId> = admission
            .verdicts()
            .judged()
            .iter()
            .filter_map(|judged| match judged.verdict() {
                Verdict::Checked { declared, .. } => Some((judged.constant(), declared.id())),
                Verdict::Synthesised { synthesised, .. } => {
                    Some((judged.constant(), synthesised.produced().id()))
                },
                Verdict::Data | Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_) => {
                    None
                },
            })
            .collect();
        let names: Vec<String> = (0 .. usize::from(program.definitions().len()))
            .map(
                |position| match program.name(ConstantIndex::from(position)) {
                    Maybe::Present(name) => String::from(name.as_ref()),
                    Maybe::Absent(_) => String::new(),
                },
            )
            .collect();
        let definitions: Result<Vec<Definition<'_>>, String> = names
            .iter()
            .enumerate()
            .map(|(position, name)| {
                let constant = ConstantIndex::from(position);
                match (program.definitions().get(constant), declared.get(&constant)) {
                    (Some(Focused::Transparent(value)), Some(&signature)) => Ok(Definition {
                        name: Symbol::from(name.as_str()),
                        value,
                        signature,
                    }),
                    (Some(Focused::Transparent(_)), None) => {
                        Err(String::from("focus: a definition with no declared type"))
                    },
                    (Some(Focused::Opaque) | None, _) => Err(String::from(
                        "focus: a declaration the machine carries as itself",
                    )),
                }
            })
            .collect();
        let lowered = definitions.and_then(|definitions| {
            lower(program.arena(), admission.arena(), &definitions)
                .map_err(|form| format!("lower: {form:?}"))
        });
        report
            .declarations()
            .iter()
            .filter(|declaration| matches!(declaration.stated(), Stated::Verdict(Outcome::Runs(_))))
            .map(|declaration| {
                let label = format!("{file}.{}", declaration.name().as_ref());
                let outcome = declaration.outcome();
                let Outcome::Runs(ref spelled) = outcome
                else {
                    return (label, Came::Refused(format!("alone: {outcome}")));
                };
                let came = match lowered {
                    Err(ref refusal) => Came::Refused(refusal.clone()),
                    Ok(ref lowered) => match lowered.entry(declaration.constant()) {
                        Err(form) => Came::Refused(format!("entry: {form:?}")),
                        Ok(entry) => {
                            let code = exit_code(lowered, entry, &label);
                            assert_eq!(
                                Some(code),
                                low_byte(spelled.as_ref()),
                                "{label}: the compiled code exits with the low byte of `{spelled}`"
                            );
                            Came::Agreed
                        },
                    },
                };
                (label, came)
            })
            .collect()
    }

    #[test]
    fn each_accepted_runs_item_of_the_programs_gives_one_answer_on_both()
    {
        let mut paths: Vec<_> = std::fs::read_dir(PROGRAMS)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "gandr")
            })
            .collect();
        paths.sort();
        let mut agreed = Vec::new();
        let mut refused: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for path in &paths {
            for (label, came) in items(path) {
                match came {
                    Came::Agreed => agreed.push(label),
                    Came::Refused(name) => refused.entry(name).or_default().push(label),
                }
            }
        }
        eprintln!("agreed: {agreed:?}\nrefused: {refused:#?}");
        assert_eq!(
            agreed,
            [
                "exit-code.wrapped_byte",
                "exit-code.answer",
                "exit-code.exit_code",
                "export-add.small_sum",
                "fnv-step.offset_with_a",
                "fnv-step.offset_with_zero",
                "fnv-step.greatest_with_zero",
                "left.missing",
                "left.left_word",
                "pick.taken",
                "pick.skipped",
                "pick.picked",
                "saturate.small",
                "saturate.large",
                "saturate.direct",
                "saturate.saturated"
            ],
            "the items whose compiled code gives the answer of the executor"
        );
        let counts: Vec<(&str, usize)> = refused
            .iter()
            .map(|(name, labels)| (name.as_str(), labels.len()))
            .collect();
        assert_eq!(
            counts,
            [
                ("alone: refuses ImportUnresolved", 1),
                ("entry: Signature", 4)
            ],
            "the refused items, counted by the name of the refusal: {refused:#?}"
        );
    }
}
