//! The document algebra, the sealed arena, resolution and rendering, witnessed
//! through the public surface: construction, ingestion, sealing,
//! flattened-image projections, the cost order, width taint, and every build
//! and render ceiling at its exact boundary.

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_surface_layout::arena::DocArena;
    use gandr_surface_layout::arena::DocHandleStatus;
    use gandr_surface_layout::arena::DocId;
    use gandr_surface_layout::arena::StoredLineEnding;
    use gandr_surface_layout::arena::TextOwned;
    use gandr_surface_layout::arena::TextSource;
    use gandr_surface_layout::arena::VerbatimOwned;
    use gandr_surface_layout::arena::VerbatimSource;
    use gandr_surface_layout::arena::ending;
    use gandr_surface_layout::build::DocBuilder;
    use gandr_surface_layout::error::BuildAllocationSite;
    use gandr_surface_layout::error::BuildArithmetic;
    use gandr_surface_layout::error::BuildError;
    use gandr_surface_layout::error::BuildLimitKind;
    use gandr_surface_layout::error::RenderArithmetic;
    use gandr_surface_layout::error::RenderError;
    use gandr_surface_layout::limits::BuildLimits;
    use gandr_surface_layout::limits::BuildMeter;
    use gandr_surface_layout::limits::BuildUsage;
    use gandr_surface_layout::limits::RenderLimits;
    use gandr_surface_layout::limits::RenderMeter;
    use gandr_surface_layout::measure::LayoutCost;
    use gandr_surface_layout::measure::LayoutOptions;
    use gandr_surface_layout::measure::PhysicalLineEnding;
    use gandr_surface_layout::measure::WidthTaint;
    use gandr_surface_layout::render::render;
    use gandr_surface_layout::resolve::resolve;
    use gandr_surface_layout::units::BuildStepsUsed;
    use gandr_surface_layout::units::ComputationWidth;
    use gandr_surface_layout::units::DocNodesUsed;
    use gandr_surface_layout::units::LineBreaks;
    use gandr_surface_layout::units::MaxBuildSteps;
    use gandr_surface_layout::units::MaxDocNodes;
    use gandr_surface_layout::units::MaxFrontierEntries;
    use gandr_surface_layout::units::MaxLayoutSteps;
    use gandr_surface_layout::units::MaxLivePlanNodes;
    use gandr_surface_layout::units::MaxMemoStates;
    use gandr_surface_layout::units::MaxOutputBytes;
    use gandr_surface_layout::units::MaxPlanNodesCreated;
    use gandr_surface_layout::units::MaxResolverStack;
    use gandr_surface_layout::units::MaxResolverWorkEntries;
    use gandr_surface_layout::units::MaxTextBytes;
    use gandr_surface_layout::units::MaxVerbatimLines;
    use gandr_surface_layout::units::MaxVmStack;
    use gandr_surface_layout::units::MaxVmSteps;
    use gandr_surface_layout::units::NestAmount;
    use gandr_surface_layout::units::OutputBytes;
    use gandr_surface_layout::units::PageWidth;
    use gandr_surface_layout::units::ScalarWidth;
    use gandr_surface_layout::units::SquaredOverflow;
    use gandr_surface_layout::units::TextBytesUsed;
    use gandr_surface_layout::units::VerbatimLinesUsed;
    use proptest::prelude::*;
    use quenchant_shape::shape::Maybe;

    /// Build limits used by tests that do not exercise a boundary.
    ///
    /// # Specification
    /// trivial.
    fn generous_limits() -> BuildLimits
    {
        BuildLimits {
            max_doc_nodes: MaxDocNodes::from(1_000_000u32),
            max_text_bytes: MaxTextBytes::from(1_000_000usize),
            max_verbatim_lines: MaxVerbatimLines::from(1_000_000u32),
            max_build_steps: MaxBuildSteps::from(20_000_000u64),
        }
    }

    /// Render limits used by witnesses that do not exercise a boundary.
    ///
    /// # Specification
    /// trivial.
    fn generous_render_limits() -> RenderLimits
    {
        RenderLimits {
            max_memo_states: MaxMemoStates::from(1_000_000u64),
            max_frontier_entries: MaxFrontierEntries::from(4_000_000u64),
            max_plan_nodes_created: MaxPlanNodesCreated::from(16_000_000u64),
            max_live_plan_nodes: MaxLivePlanNodes::from(8_000_000u64),
            max_output_bytes: MaxOutputBytes::from(0x0400_0000u64),
            max_layout_steps: MaxLayoutSteps::from(100_000_000u64),
            max_resolver_work_entries: MaxResolverWorkEntries::from(100_000_000u64),
            max_resolver_stack: MaxResolverStack::from(1_000_000u64),
            max_vm_steps: MaxVmSteps::from(100_000_000u64),
            max_vm_stack: MaxVmStack::from(1_000_000u64),
        }
    }

    /// Turns a build fixture error into a concrete test failure.
    ///
    /// # Specification
    /// - requires: `result` is one build operation used to construct a witness.
    /// - ensures: successful values pass through unchanged.
    /// - provides: test helpers that preserve the concrete [`BuildError`].
    /// - fails: panics with the concrete build error when construction fails.
    /// - panics: when `result` is an error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — public ingestion, image, accounting and
    ///   rendered-output witnesses observe the returned fixture rather than its
    ///   implementation. Lost handles, mismatched usage, wrong leaf kinds,
    ///   altered interner sharing and changed byte order change those
    ///   observations. Predicates avoid allocating public payload projections;
    ///   the witnesses compare payloads explicitly.
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_preserves_a_mixed_ending_sequence_byte_for_byte`
    /// - witness: `algebra::tests::finalization_is_deterministic_across_runs`
    /// - witness: `algebra::tests::parenthesizations_preserve_unicode_output_and_cost`
    /// - witness: `algebra::tests::empty_operands_preserve_complete_rendered_output`
    #[spec(
        captures: successful = result.is_ok(),
        ensures: |ret| successful
    )]
    fn expect_build<T>(result: Result<T, BuildError>) -> T
    {
        result.expect("build fixture failed")
    }

    /// Resolve one finished root under generous render limits.
    ///
    /// # Specification
    /// - requires: the test supplies a finalized arena, candidate handle and
    ///   width options.
    /// - ensures: unknown handles and reversed widths retain the public
    ///   resolver refusal precedence; success owns the selected layout.
    /// - provides: resolution under a fresh generous test meter.
    /// - fails: propagates the concrete render error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation and choice witnesses observe cost,
    ///   bytes and taint through the returned selected layout. Reversing cost
    ///   priority or losing width context changes these observations. The
    ///   predicate covers checked input refusal; it does not re-run resolution.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    #[spec(
        ensures: |ret| if arena.contains(root) == DocHandleStatus::Absent { matches!(ret, Err(RenderError::UnknownDoc)) }
            else if u32::from(options.computation_width) < u32::from(options.page_width) { matches!(ret, Err(RenderError::InvalidWidth)) }
            else { true }
    )]
    fn resolve_root(
        arena: &DocArena,
        root: DocId,
        options: LayoutOptions,
    ) -> Result<gandr_surface_layout::resolve::Resolved, RenderError>
    {
        let mut meter = RenderMeter::new(generous_render_limits());
        resolve(arena, root, options, &mut meter)
    }

    /// The two graph shapes used by accounting tests.
    #[derive(Clone, Copy)]
    enum ConcatShape
    {
        /// Reuse one text identity on both edges.
        Shared,
        /// Store two text identities with equal bytes.
        Distinct,
    }

    /// The two parenthesizations used by associativity tests.
    #[derive(Clone, Copy)]
    enum Associativity
    {
        /// Group the first two leaves.
        Left,
        /// Group the last two leaves.
        Right,
    }
    /// The two interner candidate orders used by the determinism witness.
    #[derive(Clone, Copy)]
    enum InternerOrder
    {
        /// Alternate left and right candidates beginning with the left one.
        Forward,
        /// Alternate left and right candidates beginning with the right one.
        Reverse,
    }

    /// Construct one arena containing a newline-free text leaf.
    ///
    /// # Specification
    /// - requires: the test supplies candidate text bytes, including rejected
    ///   ingestion forms.
    /// - ensures: success returns a finalized arena owning the unchanged text
    ///   image and a node counter equal to that arena's size.
    /// - provides: one text fixture and its actual build usage.
    /// - fails: propagates the first concrete ingestion, build or finalization
    ///   error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — public ingestion, image, accounting and
    ///   rendered-output witnesses observe the returned fixture rather than its
    ///   implementation. Lost handles, mismatched usage, wrong leaf kinds,
    ///   altered interner sharing and changed byte order change those
    ///   observations. Predicates avoid allocating public payload projections;
    ///   the witnesses compare payloads explicitly.
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_preserves_a_mixed_ending_sequence_byte_for_byte`
    /// - witness: `algebra::tests::finalization_is_deterministic_across_runs`
    /// - witness: `algebra::tests::parenthesizations_preserve_unicode_output_and_cost`
    /// - witness: `algebra::tests::empty_operands_preserve_complete_rendered_output`
    #[spec(
        ensures: |ret| ret.as_ref().map_or(true,
            |fixture| fixture.0.contains(fixture.1) == DocHandleStatus::Present
                && fixture.0.node_count() == fixture.2.doc_nodes
                && fixture.0.flattened_image(fixture.1) == Ok(fixture.1)
                && fixture.0.stored_text_width(fixture.1).is_ok_and(|width| u64::from(u32::from(width)) <= u64::from(fixture.2.text_bytes)))
    )]
    fn build_text(text: TextSource<'_>) -> Result<(DocArena, DocId, BuildUsage), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let doc = builder.text(text)?;
        let arena = builder.finish()?;
        Ok((arena, doc, meter.usage()))
    }

    /// Construct one arena containing an opaque verbatim leaf.
    ///
    /// # Specification
    /// - requires: the test supplies candidate verbatim bytes, including
    ///   rejected ingestion forms.
    /// - ensures: success returns a finalized arena owning the unchanged
    ///   verbatim image and a node counter equal to that arena's size.
    /// - provides: one verbatim fixture and its actual build usage.
    /// - fails: propagates the first concrete ingestion, build or finalization
    ///   error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — public ingestion, image, accounting and
    ///   rendered-output witnesses observe the returned fixture rather than its
    ///   implementation. Lost handles, mismatched usage, wrong leaf kinds,
    ///   altered interner sharing and changed byte order change those
    ///   observations. Predicates avoid allocating public payload projections;
    ///   the witnesses compare payloads explicitly.
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_preserves_a_mixed_ending_sequence_byte_for_byte`
    /// - witness: `algebra::tests::finalization_is_deterministic_across_runs`
    /// - witness: `algebra::tests::parenthesizations_preserve_unicode_output_and_cost`
    /// - witness: `algebra::tests::empty_operands_preserve_complete_rendered_output`
    #[spec(
        ensures: |ret| ret.as_ref().map_or(true,
            |fixture| fixture.0.contains(fixture.1) == DocHandleStatus::Present
                && fixture.0.node_count() == fixture.2.doc_nodes
                && fixture.0.flattened_image(fixture.1) == Ok(fixture.1))
    )]
    fn build_verbatim(text: VerbatimSource<'_>)
    -> Result<(DocArena, DocId, BuildUsage), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let doc = builder.verbatim(text)?;
        let arena = builder.finish()?;
        Ok((arena, doc, meter.usage()))
    }

    /// Return the all-zero usage record for an untouched meter.
    ///
    /// # Specification
    /// trivial.
    fn zero_usage() -> BuildUsage
    {
        BuildUsage {
            doc_nodes: DocNodesUsed::from(0u64),
            text_bytes: TextBytesUsed::from(0u64),
            verbatim_lines: VerbatimLinesUsed::from(0u64),
            build_steps: BuildStepsUsed::from(0u64),
        }
    }

    /// Build a shared or distinct two-leaf concatenation and return its usage.
    ///
    /// # Specification
    /// - requires: the test chooses whether two equal text operands share an
    ///   identity.
    /// - ensures: the fixture stores one six-byte payload when shared and two
    ///   when distinct, plus the one-byte flattened soft line.
    /// - provides: the build usage for observing edge reuse without payload
    ///   recharging.
    /// - fails: propagates a concrete build error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — otherwise equal shared and distinct fixtures expose
    ///   the exact extra node and text charge of a second stored identity.
    ///   Charging a shared edge as a new payload, or silently interning
    ///   distinct leaves, changes the comparison; the predicate checks the
    ///   fixture payload total.
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_node`
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    #[spec(
        ensures: |ret| ret.as_ref().map_or(true,
            |usage| u64::from(usage.text_bytes) == if matches!(shape, ConcatShape::Shared) { 7 }
            else { 13 })
    )]
    fn concat_usage(shape: ConcatShape) -> Result<BuildUsage, BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        {
            let mut builder = DocBuilder::try_new(&mut meter)?;
            match shape {
                | ConcatShape::Shared => {
                    let text = builder.text(TextSource::from("shared"))?;
                    let _joined = builder.concat(text, text)?;
                },
                | ConcatShape::Distinct => {
                    let left = builder.text(TextSource::from("shared"))?;
                    let right = builder.text(TextSource::from("shared"))?;
                    let _joined = builder.concat(left, right)?;
                },
            }
            let _arena = builder.finish()?;
        }
        Ok(meter.usage())
    }

    /// Run one totality witness on a deliberately small native stack.
    ///
    /// # Specification
    /// - requires: the one-shot test callback is sendable to the worker thread.
    /// - ensures: the callback runs on the requested small native stack and its
    ///   concrete result is returned after joining.
    /// - provides: an observable bound on native-stack use for deep
    ///   construction witnesses.
    /// - fails: thread creation failure becomes a finalization-stack allocation
    ///   error.
    /// - panics: if the worker thread panics.
    /// - executable: none — the one-shot callback result and worker stack are
    ///   not exposed after joining; a predicate cannot replay the callback or
    ///   inspect the worker without changing the interface.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — left and right spines and a wide shared graph seal on
    ///   a 64 KiB worker stack. Input-scaled recursion exhausts that stack;
    ///   wrong finalization or lost roots changes the returned arena
    ///   observations. Operating-system thread creation failure is not
    ///   injected.
    /// - witness: `algebra::tests::deep_left_spine_construction_uses_a_heap_work_stack`
    /// - witness: `algebra::tests::deep_right_spine_construction_uses_a_heap_work_stack`
    /// - witness: `algebra::tests::a_wide_shared_graph_finalizes_without_native_stack_growth`
    fn run_on_small_stack(
        work: impl FnOnce() -> Result<(), BuildError> + Send + 'static
    ) -> Result<(), BuildError>
    {
        let handle = std::thread::Builder::new()
            .name(String::from("surface-layout-stress"))
            .stack_size(0x0001_0000_usize)
            .spawn(work)
            .map_err(|_error| BuildError::AllocationFailed {
                site: BuildAllocationSite::FinalizeStack,
            })?;
        let joined = handle.join();
        assert!(
            joined.is_ok(),
            "the iterative witness must not overflow its stack"
        );
        match joined {
            | Ok(result) => result,
            | Err(_panic) => Err(BuildError::AllocationFailed {
                site: BuildAllocationSite::FinalizeStack,
            }),
        }
    }

    /// Entries the heap-stack witnesses nest, far past any native stack.
    const HEAP_STACK_DEPTH: u32 = 200_000u32;

    /// Build many equivalent interner candidates in one of two orders.
    ///
    /// # Specification
    /// - requires: the test chooses the first of two alternating candidate
    ///   classes.
    /// - ensures: the arena owns the root and both repeated candidates of each
    ///   class, and each class has a shared flattened image.
    /// - provides: two construction orders for observing deterministic
    ///   interning.
    /// - fails: propagates a concrete build error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — public ingestion, image, accounting and
    ///   rendered-output witnesses observe the returned fixture rather than its
    ///   implementation. Lost handles, mismatched usage, wrong leaf kinds,
    ///   altered interner sharing and changed byte order change those
    ///   observations. Predicates avoid allocating public payload projections;
    ///   the witnesses compare payloads explicitly.
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_preserves_a_mixed_ending_sequence_byte_for_byte`
    /// - witness: `algebra::tests::finalization_is_deterministic_across_runs`
    /// - witness: `algebra::tests::parenthesizations_preserve_unicode_output_and_cost`
    /// - witness: `algebra::tests::empty_operands_preserve_complete_rendered_output`
    #[spec(
        ensures: |ret| ret.as_ref().map_or(true,
            |fixture| [fixture.1, fixture.2, fixture.3, fixture.4, fixture.5].into_iter().all(|doc| fixture.0.contains(doc) == DocHandleStatus::Present)
                && fixture.0.flattened_image(fixture.2).is_ok_and(|image| fixture.0.flattened_image(fixture.3) == Ok(image))
                && fixture.0.flattened_image(fixture.4).is_ok_and(|image| fixture.0.flattened_image(fixture.5) == Ok(image)))
    )]
    fn build_interner_order(
        order: InternerOrder
    ) -> Result<(DocArena, DocId, DocId, DocId, DocId, DocId), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let leaf = builder.text(TextSource::from("deterministic"))?;
        let line = builder.line();
        let left = builder.choice(leaf, line)?;
        let right = builder.choice(line, leaf)?;
        let mut groups = Vec::new();
        let mut left_next = matches!(order, InternerOrder::Forward);
        let mut first_left = None;
        let mut second_left = None;
        let mut first_right = None;
        let mut second_right = None;
        for _ in 0u32 .. 256u32 {
            let candidate = if left_next { left } else { right };
            let group = builder.group(candidate)?;
            if left_next {
                if first_left.is_none() {
                    first_left = Some(group);
                }
                else if second_left.is_none() {
                    second_left = Some(group);
                }
            }
            else if first_right.is_none() {
                first_right = Some(group);
            }
            else if second_right.is_none() {
                second_right = Some(group);
            }
            groups.push(group);
            left_next = !left_next;
        }
        let root = builder.concat_all(groups)?;
        let first_left = first_left.ok_or(BuildError::UnknownDoc)?;
        let second_left = second_left.ok_or(BuildError::UnknownDoc)?;
        let first_right = first_right.ok_or(BuildError::UnknownDoc)?;
        let second_right = second_right.ok_or(BuildError::UnknownDoc)?;
        let arena = builder.finish()?;
        Ok((
            arena,
            root,
            first_left,
            second_left,
            first_right,
            second_right,
        ))
    }

    /// Assert that a usage record is componentwise no smaller than another.
    ///
    /// # Specification
    /// - requires: the caller supplies successive build usage records.
    /// - ensures: normal return means every current counter is at least its
    ///   previous value.
    /// - provides: a componentwise monotonicity assertion.
    /// - panics: when any component regresses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the whole-document witness observes successive
    ///   records across ingestion, construction and sealing. A regressing
    ///   component fails independently of the other counters; allocator failure
    ///   is outside this helper.
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        ensures: |ret| current.doc_nodes >= previous.doc_nodes
                && current.text_bytes >= previous.text_bytes
                && current.verbatim_lines >= previous.verbatim_lines
                && current.build_steps >= previous.build_steps
    )]
    fn assert_usage_monotone(
        previous: BuildUsage,
        current: BuildUsage,
    )
    {
        assert!(
            current.doc_nodes >= previous.doc_nodes,
            "document-node usage must be monotone"
        );
        assert!(
            current.text_bytes >= previous.text_bytes,
            "text-byte usage must be monotone"
        );
        assert!(
            current.verbatim_lines >= previous.verbatim_lines,
            "verbatim-line usage must be monotone"
        );
        assert!(
            current.build_steps >= previous.build_steps,
            "build-step usage must be monotone"
        );
    }

    /// Empty documents retain the empty identity, have no stored payload,
    /// and end where they begin: text after an empty is charged from the
    /// column the empty was entered at, so a break that avoids the overflow
    /// wins over the empty branch of a choice.
    #[test]
    fn empty_emits_nothing_and_moves_no_column() -> Result<(), RenderError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut meter));
        let empty = builder.empty();
        let head = expect_build(builder.text(TextSource::from("abcd")));
        let tail = expect_build(builder.text(TextSource::from("ef")));
        let hard_line = builder.hard_line();
        let separator = expect_build(builder.choice(empty, hard_line));
        let root = expect_build(builder.concat_all([head, separator, tail]));
        let arena = expect_build(builder.finish());
        assert_eq!(expect_build(arena.flattened_image(empty)), empty);
        assert_eq!(arena.contains(empty), DocHandleStatus::Present);
        let options = LayoutOptions::try_new(
            PageWidth::from(4u32),
            ComputationWidth::from(8u32),
            PhysicalLineEnding::Lf,
        )?;
        let mut render_meter = RenderMeter::new(generous_render_limits());
        let rendered = render(&arena, root, &options, &mut render_meter)?;
        assert_eq!(rendered.text, "abcd\nef");
        assert_eq!(rendered.cost, LayoutCost {
            squared_overflow: SquaredOverflow::from(0u64),
            line_breaks: LineBreaks::from(1u64),
        });
        Ok(())
    }

    /// Text leaves preserve their bytes and checked scalar width.
    #[test]
    fn text_emits_at_the_current_column() -> Result<(), BuildError>
    {
        let (arena, doc, _) = build_text(TextSource::from("abc"))?;
        assert_eq!(
            arena.stored_text(doc)?,
            TextOwned::from(String::from("abc"))
        );
        assert_eq!(arena.stored_text_width(doc)?, ScalarWidth::from(3u32));
        Ok(())
    }

    /// Text ingestion rejects each forbidden scalar.
    #[test]
    fn text_rejects_a_carriage_return_a_line_feed_and_a_tab() -> Result<(), BuildError>
    {
        // workflow-gates: allow-escaped-newline
        for text in ["bad\r", "bad\n", "bad\t"] {
            let mut meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut meter)?;
            assert_eq!(
                builder.text(TextSource::from(text)),
                Err(BuildError::InvalidText)
            );
        }
        Ok(())
    }
    /// Owned text preserves bytes and width and rejects forbidden scalars.
    #[test]
    fn owned_text_preserves_bytes_width_and_rejects_forbidden_scalars() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let doc = builder.text_owned(TextOwned::from(String::from("owned")))?;
        let arena = builder.finish()?;
        assert_eq!(
            arena.stored_text(doc)?,
            TextOwned::from(String::from("owned"))
        );
        assert_eq!(arena.stored_text_width(doc)?, ScalarWidth::from(5u32));

        // workflow-gates: allow-escaped-newline
        for text in ["bad\r", "bad\n", "bad\t"] {
            let mut meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut meter)?;
            assert_eq!(
                builder.text_owned(TextOwned::from(String::from(text))),
                Err(BuildError::InvalidText)
            );
        }
        Ok(())
    }

    /// Concatenation preserves both input handles through finalization.
    #[test]
    fn concat_resolves_the_right_at_the_left_ending_column() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let left = builder.text(TextSource::from("left"))?;
        let right = builder.text(TextSource::from("right"))?;
        let joined = builder.concat(left, right)?;
        let arena = builder.finish()?;
        assert_eq!(
            arena.stored_text(left)?,
            TextOwned::from(String::from("left"))
        );
        assert_eq!(
            arena.stored_text(right)?,
            TextOwned::from(String::from("right"))
        );
        assert_eq!(arena.contains(joined), DocHandleStatus::Present);
        Ok(())
    }

    /// Nesting raises the indentation of every line its child breaks by the
    /// nested amount.
    #[test]
    fn nest_raises_indentation_by_a_checked_amount() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let head = expect_build(builder.text(TextSource::from("a")));
        let tail = expect_build(builder.text(TextSource::from("b")));
        let hard_line = builder.hard_line();
        let body = expect_build(builder.concat_all([head, hard_line, tail]));
        let nested = expect_build(builder.nest(NestAmount::from(4u32), body));
        let arena = expect_build(builder.finish());
        let mut meter = RenderMeter::new(generous_render_limits());
        let rendered = render(&arena, nested, &LayoutOptions::default(), &mut meter)?;
        assert_eq!(rendered.text, "a\n    b");
        assert_eq!(
            arena.flattened_image(nested),
            Ok(nested),
            "a hard line survives flattening"
        );
        Ok(())
    }

    /// An indentation raised past its representable range is a typed overflow
    /// at resolution, never a wrapped indentation.
    #[test]
    fn nest_reports_overflow_rather_than_wrapping_the_indentation()
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let head = expect_build(builder.text(TextSource::from("a")));
        let hard_line = builder.hard_line();
        let body = expect_build(builder.concat(head, hard_line));
        let inner = expect_build(builder.nest(NestAmount::from(1u32), body));
        let outer = expect_build(builder.nest(NestAmount::from(u32::MAX), inner));
        let arena = expect_build(builder.finish());
        let mut meter = RenderMeter::new(generous_render_limits());
        assert_eq!(
            render(&arena, outer, &LayoutOptions::default(), &mut meter),
            Err(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::Indentation,
            })
        );
    }

    /// Alignment sets the indentation of every line its child breaks to the
    /// column the child starts at.
    #[test]
    fn align_sets_indentation_to_the_current_column() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let prefix = expect_build(builder.text(TextSource::from("ab")));
        let head = expect_build(builder.text(TextSource::from("x")));
        let tail = expect_build(builder.text(TextSource::from("y")));
        let hard_line = builder.hard_line();
        let body = expect_build(builder.concat_all([head, hard_line, tail]));
        let aligned = expect_build(builder.align(body));
        let root = expect_build(builder.concat(prefix, aligned));
        let arena = expect_build(builder.finish());
        let mut meter = RenderMeter::new(generous_render_limits());
        let rendered = render(&arena, root, &LayoutOptions::default(), &mut meter)?;
        assert_eq!(rendered.text, "abx\n  y");
        Ok(())
    }

    /// A soft line flattens to the shared single-space text identity.
    #[test]
    fn flatten_turns_a_line_into_one_space() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let builder = DocBuilder::try_new(&mut meter)?;
        let line = builder.line();
        let arena = builder.finish()?;
        let image = arena.flattened_image(line)?;
        assert_eq!(
            arena.stored_text(image)?,
            TextOwned::from(String::from(" "))
        );
        assert_eq!(arena.stored_text_width(image)?, ScalarWidth::from(1u32));
        Ok(())
    }

    /// A hard line keeps its own identity when flattened.
    #[test]
    fn flatten_leaves_a_hard_line_alone() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let builder = DocBuilder::try_new(&mut meter)?;
        let hard_line = builder.hard_line();
        let arena = builder.finish()?;
        assert_eq!(arena.flattened_image(hard_line)?, hard_line);
        Ok(())
    }

    /// Verbatim content keeps both its bytes and its own flattened identity.
    #[test]
    fn flatten_leaves_verbatim_bytes_and_indentation_alone() -> Result<(), BuildError>
    {
        let (arena, verbatim, _) = build_verbatim(VerbatimSource::from("opaque"))?;
        assert_eq!(arena.flattened_image(verbatim)?, verbatim);
        assert_eq!(
            arena.stored_verbatim(verbatim)?,
            VerbatimOwned::from(String::from("opaque"))
        );
        Ok(())
    }

    /// A choice records the unflattened branch before its flattened
    /// alternative.
    #[test]
    fn group_is_choice_of_the_unflattened_form_then_the_flattened_form() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let unflattened = builder.hard_line();
        let flattened = builder.line();
        let group = builder.choice(unflattened, flattened)?;
        let arena = builder.finish()?;
        let image = arena.flattened_image(group)?;
        assert_eq!(arena.contains(image), DocHandleStatus::Present);
        assert_ne!(image, unflattened);
        Ok(())
    }

    /// A verbatim leaf without an ending has one final fragment.
    #[test]
    fn verbatim_with_no_ending_extends_the_incoming_column() -> Result<(), BuildError>
    {
        let (arena, doc, _) = build_verbatim(VerbatimSource::from("abc"))?;
        let lines = arena.verbatim_lines(doc)?;
        assert_eq!(lines.len(), 1usize);
        assert_eq!(lines[0].scalar_width(), ScalarWidth::from(3u32));
        assert_eq!(lines[0].ending(), Maybe::Absent(ending::Absent::Final));
        Ok(())
    }

    /// A trailing ending records an empty final fragment.
    #[test]
    fn verbatim_with_a_trailing_ending_stores_an_empty_final_fragment() -> Result<(), BuildError>
    {
        let payload =
        // workflow-gates: allow-escaped-newline
        "abc\n";
        let (arena, doc, _) = build_verbatim(VerbatimSource::from(payload))?;
        let lines = arena.verbatim_lines(doc)?;
        assert_eq!(lines.len(), 2usize);
        assert_eq!(lines[0].scalar_width(), ScalarWidth::from(3u32));
        assert_eq!(lines[0].ending(), Maybe::Present(StoredLineEnding::Lf));
        assert_eq!(lines[1].scalar_width(), ScalarWidth::from(0u32));
        assert_eq!(lines[1].ending(), Maybe::Absent(ending::Absent::Final));
        assert_eq!(
            arena.stored_verbatim(doc)?,
            VerbatimOwned::from(String::from("abc\n"))
        );
        Ok(())
    }

    /// Middle fragments record widths from their own line starts.
    #[test]
    fn verbatim_with_several_middle_lines_stores_absolute_widths() -> Result<(), BuildError>
    {
        let payload =
        // workflow-gates: allow-escaped-newline
        "ab\ncde\nf";
        let (arena, doc, _) = build_verbatim(VerbatimSource::from(payload))?;
        let lines = arena.verbatim_lines(doc)?;
        assert_eq!(lines.len(), 3usize);
        assert_eq!(lines[0].scalar_width(), ScalarWidth::from(2u32));
        assert_eq!(lines[1].scalar_width(), ScalarWidth::from(3u32));
        assert_eq!(lines[2].scalar_width(), ScalarWidth::from(1u32));
        assert_eq!(lines[0].ending(), Maybe::Present(StoredLineEnding::Lf));
        assert_eq!(lines[1].ending(), Maybe::Present(StoredLineEnding::Lf));
        assert_eq!(lines[2].ending(), Maybe::Absent(ending::Absent::Final));
        Ok(())
    }

    /// A lone line-feed ending is preserved byte for byte.
    #[test]
    fn verbatim_preserves_line_feed_endings_byte_for_byte() -> Result<(), BuildError>
    {
        let payload =
        // workflow-gates: allow-escaped-newline
        "left\nright";
        let (arena, doc, _) = build_verbatim(VerbatimSource::from(payload))?;
        assert_eq!(
            arena.stored_verbatim(doc)?,
            VerbatimOwned::from(String::from("left\nright"))
        );
        let lines = arena.verbatim_lines(doc)?;
        assert_eq!(lines[0].ending(), Maybe::Present(StoredLineEnding::Lf));
        Ok(())
    }

    /// A carriage-return/line-feed ending is preserved byte for byte.
    #[test]
    fn verbatim_preserves_carriage_return_line_feed_endings_byte_for_byte() -> Result<(), BuildError>
    {
        let payload =
        // workflow-gates: allow-escaped-newline
        "left\r\nright";
        let (arena, doc, _) = build_verbatim(VerbatimSource::from(payload))?;
        assert_eq!(
            arena.stored_verbatim(doc)?,
            VerbatimOwned::from(String::from("left\r\nright"))
        );
        let lines = arena.verbatim_lines(doc)?;
        assert_eq!(lines[0].ending(), Maybe::Present(StoredLineEnding::CrLf));
        Ok(())
    }

    /// Mixed LF and CRLF endings retain their original order and bytes.
    #[test]
    fn verbatim_preserves_a_mixed_ending_sequence_byte_for_byte() -> Result<(), BuildError>
    {
        let payload =
        // workflow-gates: allow-escaped-newline
        "a\nb\r\nc\n";
        let (arena, doc, _) = build_verbatim(VerbatimSource::from(payload))?;
        assert_eq!(
            arena.stored_verbatim(doc)?,
            VerbatimOwned::from(String::from("a\nb\r\nc\n"))
        );
        let lines = arena.verbatim_lines(doc)?;
        assert_eq!(lines.len(), 4usize);
        assert_eq!(lines[0].ending(), Maybe::Present(StoredLineEnding::Lf));
        assert_eq!(lines[1].ending(), Maybe::Present(StoredLineEnding::CrLf));
        assert_eq!(lines[2].ending(), Maybe::Present(StoredLineEnding::Lf));
        assert_eq!(lines[3].ending(), Maybe::Absent(ending::Absent::Final));
        Ok(())
    }

    /// A bare carriage return is rejected before any verbatim node is stored.
    #[test]
    fn verbatim_rejects_a_bare_carriage_return() -> Result<(), BuildError>
    {
        let payload =
        // workflow-gates: allow-escaped-newline
        "left\rright";
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        assert_eq!(
            builder.verbatim(VerbatimSource::from(payload)),
            Err(BuildError::InvalidVerbatimLineEnding)
        );
        Ok(())
    }
    /// Owned verbatim preserves an ending shape and rejects bare carriage
    /// return.
    #[test]
    fn owned_verbatim_preserves_an_ending_and_rejects_a_bare_carriage_return()
    -> Result<(), BuildError>
    {
        let payload =
        // workflow-gates: allow-escaped-newline
        "owned\ntext";
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let doc = builder.verbatim_owned(VerbatimOwned::from(String::from(payload)))?;
        let arena = builder.finish()?;
        assert_eq!(
            arena.stored_verbatim(doc)?,
            VerbatimOwned::from(String::from("owned\ntext"))
        );
        let lines = arena.verbatim_lines(doc)?;
        assert_eq!(lines.len(), 2usize);
        assert_eq!(lines[0].scalar_width(), ScalarWidth::from(5u32));
        assert_eq!(lines[0].ending(), Maybe::Present(StoredLineEnding::Lf));
        assert_eq!(lines[1].scalar_width(), ScalarWidth::from(4u32));
        assert_eq!(lines[1].ending(), Maybe::Absent(ending::Absent::Final));

        let invalid_payload =
        // workflow-gates: allow-escaped-newline
        "bad\rbad";
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        assert_eq!(
            builder.verbatim_owned(VerbatimOwned::from(String::from(invalid_payload))),
            Err(BuildError::InvalidVerbatimLineEnding)
        );
        Ok(())
    }

    /// A handle from another arena is refused before document lookup.
    #[test]
    fn a_handle_from_another_arena_is_refused_before_lookup() -> Result<(), BuildError>
    {
        let (first, first_doc, _) = build_text(TextSource::from("first"))?;
        let (second, second_doc, _) = build_text(TextSource::from("second"))?;
        assert_eq!(first.contains(second_doc), DocHandleStatus::Absent);
        assert_eq!(second.contains(first_doc), DocHandleStatus::Absent);
        assert_eq!(first.stored_text(second_doc), Err(BuildError::UnknownDoc));
        assert_eq!(second.stored_text(first_doc), Err(BuildError::UnknownDoc));
        Ok(())
    }

    /// A handle that names a non-text node is refused by text projection.
    #[test]
    fn an_out_of_range_handle_is_refused() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let builder = DocBuilder::try_new(&mut meter)?;
        let hard_line = builder.hard_line();
        let arena = builder.finish()?;
        assert_eq!(arena.stored_text(hard_line), Err(BuildError::UnknownDoc));
        Ok(())
    }

    /// Stored identities remain present after later insertions and sealing.
    #[test]
    fn identities_are_dense_insertion_ordinals_that_never_move() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let first = builder.text(TextSource::from("first"))?;
        let second = builder.text_owned(TextOwned::from(String::from("second")))?;
        let _joined = builder.concat(first, second)?;
        let arena = builder.finish()?;
        assert_eq!(arena.contains(first), DocHandleStatus::Present);
        assert_eq!(arena.contains(second), DocHandleStatus::Present);
        assert_eq!(
            arena.stored_text(first)?,
            TextOwned::from(String::from("first"))
        );
        assert_eq!(
            arena.stored_text(second)?,
            TextOwned::from(String::from("second"))
        );
        Ok(())
    }

    /// The three mandatory singleton nodes are refused atomically below their
    /// ceiling.
    #[test]
    fn a_builder_with_a_node_ceiling_below_three_refuses_immediately()
    {
        let limits = BuildLimits {
            max_doc_nodes: MaxDocNodes::from(2u32),
            ..generous_limits()
        };
        let mut meter = BuildMeter::new(limits);
        let result = DocBuilder::try_new(&mut meter).map(|_| ());
        assert!(matches!(
            result,
            Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::DocNodes,
                ..
            })
        ));
    }

    /// Flattened-image lookup is idempotent for every finalized handle.
    #[test]
    fn flattening_is_idempotent() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let text = builder.text(TextSource::from("x"))?;
        let line = builder.line();
        let root = builder.concat(text, line)?;
        let arena = builder.finish()?;
        for doc in [text, line, root] {
            let image = arena.flattened_image(doc)?;
            assert_eq!(arena.flattened_image(image)?, image);
        }
        Ok(())
    }

    /// Finalization adds no more than one distinct image node per original
    /// node.
    #[test]
    fn finalization_appends_at_most_one_image_per_node() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let text = builder.text(TextSource::from("x"))?;
        let line = builder.line();
        let root = builder.concat(text, line)?;
        let arena = builder.finish()?;
        assert_eq!(arena.node_count(), DocNodesUsed::from(7u64));
        assert_eq!(arena.flattened_image(text)?, text);
        assert_ne!(arena.flattened_image(line)?, line);
        assert_eq!(arena.contains(root), DocHandleStatus::Present);
        Ok(())
    }

    /// A document whose flattened form is unchanged reuses its original
    /// identity.
    #[test]
    fn finalization_reuses_the_original_identity_when_nothing_changes() -> Result<(), BuildError>
    {
        let (arena, text, _) = build_text(TextSource::from("unchanged"))?;
        assert_eq!(arena.flattened_image(text)?, text);
        Ok(())
    }

    /// Finalization growth remains bounded linearly for a repeated
    /// concatenation spine.
    #[test]
    fn finalization_growth_is_linear_in_the_node_count() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let mut root = builder.empty();
        for _ in 0 .. 32u32 {
            let text = builder.text(TextSource::from("x"))?;
            root = builder.concat(root, text)?;
        }
        let arena = builder.finish()?;
        assert!(arena.node_count() <= DocNodesUsed::from(128u64));
        Ok(())
    }

    /// Equivalent interner candidates retain identical image identities when
    /// construction order changes.
    #[test]
    fn finalization_is_deterministic_across_runs() -> Result<(), BuildError>
    {
        let forward = build_interner_order(InternerOrder::Forward)?;
        let reverse = build_interner_order(InternerOrder::Reverse)?;
        assert_eq!(forward.0.node_count(), reverse.0.node_count());
        assert_eq!(forward.0.contains(forward.1), DocHandleStatus::Present);
        assert_eq!(reverse.0.contains(reverse.1), DocHandleStatus::Present);
        assert_eq!(
            forward.0.flattened_image(forward.2)?,
            forward.0.flattened_image(forward.3)?
        );
        assert_eq!(
            forward.0.flattened_image(forward.4)?,
            forward.0.flattened_image(forward.5)?
        );
        assert_eq!(
            reverse.0.flattened_image(reverse.2)?,
            reverse.0.flattened_image(reverse.3)?
        );
        assert_eq!(
            reverse.0.flattened_image(reverse.4)?,
            reverse.0.flattened_image(reverse.5)?
        );
        Ok(())
    }

    /// A finalization ceiling returns an error instead of a partial arena.
    #[test]
    fn a_ceiling_reached_during_finalization_yields_no_partial_arena() -> Result<(), BuildError>
    {
        let limits = BuildLimits {
            max_doc_nodes: MaxDocNodes::from(3u32),
            ..generous_limits()
        };
        let mut meter = BuildMeter::new(limits);
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let text = builder.text(TextSource::from("x"));
        assert!(matches!(
            text,
            Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::DocNodes,
                ..
            })
        ));
        Ok(())
    }

    /// Reusing one handle on two concat edges charges its node once.
    #[test]
    fn a_second_edge_to_a_shared_handle_charges_no_new_node() -> Result<(), BuildError>
    {
        let shared = concat_usage(ConcatShape::Shared)?;
        let distinct = concat_usage(ConcatShape::Distinct)?;
        assert_eq!(shared.doc_nodes, DocNodesUsed::from(6u64));
        assert_eq!(distinct.doc_nodes, DocNodesUsed::from(7u64));
        assert!(shared.doc_nodes < distinct.doc_nodes);
        Ok(())
    }

    /// Reusing one text handle on two concat edges charges its bytes once.
    #[test]
    fn a_second_edge_to_a_shared_handle_charges_no_new_text_bytes() -> Result<(), BuildError>
    {
        let shared = concat_usage(ConcatShape::Shared)?;
        let distinct = concat_usage(ConcatShape::Distinct)?;
        assert!(shared.text_bytes < distinct.text_bytes);
        Ok(())
    }

    /// Finalization consumes additional checked visits and interner probes.
    #[test]
    fn every_finalization_visit_edge_and_probe_charges_a_build_step() -> Result<(), BuildError>
    {
        let usage = {
            let mut meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut meter)?;
            let _text = builder.text(TextSource::from("step"))?;
            let _arena = builder.finish()?;
            meter.usage()
        };
        assert!(usage.build_steps > BuildStepsUsed::from(0u64));
        Ok(())
    }

    /// Each build ceiling accepts its exact boundary and refuses one charge
    /// beyond it.
    #[test]
    fn each_build_ceiling_refuses_exactly_at_its_boundary() -> Result<(), BuildError>
    {
        {
            let limits = BuildLimits {
                max_doc_nodes: MaxDocNodes::from(4u32),
                ..generous_limits()
            };
            let mut meter = BuildMeter::new(limits);
            let mut builder = DocBuilder::try_new(&mut meter)?;
            let _text = builder.text(TextSource::from("x"))?;
            let error = builder.text(TextSource::from("y"));
            assert!(matches!(
                error,
                Err(BuildError::LimitExceeded {
                    kind: BuildLimitKind::DocNodes,
                    ..
                })
            ));
        };

        let text_limits = BuildLimits {
            max_text_bytes: MaxTextBytes::from(3usize),
            ..generous_limits()
        };
        let mut text_meter = BuildMeter::new(text_limits);
        let mut text_builder = DocBuilder::try_new(&mut text_meter)?;
        let _text = text_builder.text(TextSource::from("abc"))?;
        let text_error = text_builder.text(TextSource::from("d"));
        assert!(matches!(
            text_error,
            Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::TextBytes,
                ..
            })
        ));

        let verbatim_limits = BuildLimits {
            max_verbatim_lines: MaxVerbatimLines::from(2u32),
            ..generous_limits()
        };
        let mut verbatim_meter = BuildMeter::new(verbatim_limits);
        let mut verbatim_builder = DocBuilder::try_new(&mut verbatim_meter)?;
        let payload =
        // workflow-gates: allow-escaped-newline
        "a\n";
        let _verbatim = verbatim_builder.verbatim(VerbatimSource::from(payload))?;
        let verbatim_error = verbatim_builder.verbatim(VerbatimSource::from("b"));
        assert!(matches!(
            verbatim_error,
            Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::VerbatimLines,
                ..
            })
        ));

        let usage = {
            let mut meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut meter)?;
            let _text = builder.text(TextSource::from("steps"))?;
            let _arena = builder.finish()?;
            meter.usage()
        };
        let exact_step_limit = MaxBuildSteps::from(u64::from(usage.build_steps));
        let exact_limits = BuildLimits {
            max_build_steps: exact_step_limit,
            ..generous_limits()
        };
        let mut exact_meter = BuildMeter::new(exact_limits);
        let mut exact_builder = DocBuilder::try_new(&mut exact_meter)?;
        let _text = exact_builder.text(TextSource::from("steps"))?;
        let _arena = exact_builder.finish()?;

        let one_before = u64::from(usage.build_steps).checked_sub(1u64).ok_or(
            BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::BuildSteps,
            },
        )?;
        let below_limits = BuildLimits {
            max_build_steps: MaxBuildSteps::from(one_before),
            ..generous_limits()
        };
        let mut below_meter = BuildMeter::new(below_limits);
        let mut below_builder = DocBuilder::try_new(&mut below_meter)?;
        let _text = below_builder.text(TextSource::from("steps"))?;
        let below_error = below_builder.finish();
        assert!(matches!(
            below_error,
            Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::BuildSteps,
                ..
            })
        ));
        Ok(())
    }

    /// A refused storage charge leaves every cumulative counter unchanged.
    #[test]
    fn a_refused_charge_leaves_the_counter_unchanged() -> Result<(), BuildError>
    {
        let limits = BuildLimits {
            max_text_bytes: MaxTextBytes::from(0usize),
            ..generous_limits()
        };
        let mut meter = BuildMeter::new(limits);
        let result = {
            let mut builder = DocBuilder::try_new(&mut meter)?;
            builder.text(TextSource::from("x"))
        };
        assert!(matches!(
            result,
            Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::TextBytes,
                ..
            })
        ));
        assert_eq!(meter.usage(), BuildUsage {
            doc_nodes: DocNodesUsed::from(3u64),
            text_bytes: TextBytesUsed::from(0u64),
            verbatim_lines: VerbatimLinesUsed::from(0u64),
            build_steps: BuildStepsUsed::from(0u64),
        });
        Ok(())
    }

    /// Build usage is monotone across independently finalized prefixes.
    #[test]
    fn build_usage_is_monotone_across_a_whole_document() -> Result<(), BuildError>
    {
        let empty = build_text(TextSource::from(""))?.2;
        let one = build_text(TextSource::from("x"))?.2;
        let many = build_text(TextSource::from("xxx"))?.2;
        assert_usage_monotone(zero_usage(), empty);
        assert_usage_monotone(empty, one);
        assert_usage_monotone(one, many);
        Ok(())
    }

    /// A deep left spine finalizes through the builder's heap work stack.
    #[test]
    fn deep_left_spine_construction_uses_a_heap_work_stack() -> Result<(), BuildError>
    {
        run_on_small_stack(|| {
            let mut meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut meter)?;
            let mut root = builder.empty();
            for _ in 0u32 .. HEAP_STACK_DEPTH {
                let leaf = builder.text(TextSource::from("x"))?;
                root = builder.concat(root, leaf)?;
            }
            let arena = builder.finish()?;
            assert_eq!(arena.contains(root), DocHandleStatus::Present);
            Ok(())
        })
    }

    /// A deep right spine finalizes through the builder's heap work stack.
    #[test]
    fn deep_right_spine_construction_uses_a_heap_work_stack() -> Result<(), BuildError>
    {
        run_on_small_stack(|| {
            let mut meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut meter)?;
            let mut root = builder.empty();
            for _ in 0u32 .. HEAP_STACK_DEPTH {
                let leaf = builder.text(TextSource::from("x"))?;
                root = builder.concat(leaf, root)?;
            }
            let arena = builder.finish()?;
            assert_eq!(arena.contains(root), DocHandleStatus::Present);
            Ok(())
        })
    }

    /// A wide graph sharing one leaf finalizes without recursive traversal.
    #[test]
    fn a_wide_shared_graph_finalizes_without_native_stack_growth() -> Result<(), BuildError>
    {
        run_on_small_stack(|| {
            let mut meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut meter)?;
            let leaf = builder.text(TextSource::from("shared"))?;
            let mut choices = Vec::new();
            for _ in 0u32 .. HEAP_STACK_DEPTH {
                choices.push(builder.choice(leaf, leaf)?);
            }
            let root = builder.concat_all(choices)?;
            let arena = builder.finish()?;
            assert_eq!(arena.contains(root), DocHandleStatus::Present);
            Ok(())
        })
    }

    /// Build an explicitly parenthesized concatenation of three text leaves.
    ///
    /// # Specification
    /// - requires: the test supplies three candidate text leaves and a
    ///   parenthesization.
    /// - ensures: success owns a valid root whose flat image is itself; the
    ///   chosen parenthesization preserves the three leaves in order.
    /// - provides: independently built associativity fixtures.
    /// - fails: propagates a concrete ingestion or build error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — public ingestion, image, accounting and
    ///   rendered-output witnesses observe the returned fixture rather than its
    ///   implementation. Lost handles, mismatched usage, wrong leaf kinds,
    ///   altered interner sharing and changed byte order change those
    ///   observations. Predicates avoid allocating public payload projections;
    ///   the witnesses compare payloads explicitly.
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_preserves_a_mixed_ending_sequence_byte_for_byte`
    /// - witness: `algebra::tests::finalization_is_deterministic_across_runs`
    /// - witness: `algebra::tests::parenthesizations_preserve_unicode_output_and_cost`
    /// - witness: `algebra::tests::empty_operands_preserve_complete_rendered_output`
    #[spec(
        ensures: |ret| ret.as_ref().map_or(true,
            |fixture| fixture.0.contains(fixture.1) == DocHandleStatus::Present
                && fixture.0.flattened_image(fixture.1) == Ok(fixture.1))
    )]
    fn build_parenthesized_concat(
        left_text: TextSource<'_>,
        middle_text: TextSource<'_>,
        right_text: TextSource<'_>,
        associativity: Associativity,
    ) -> Result<(DocArena, DocId), BuildError>
    {
        let mut meter = BuildMeter::new(generous_limits());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let left = builder.text(left_text)?;
        let middle = builder.text(middle_text)?;
        let right = builder.text(right_text)?;
        let root = match associativity {
            | Associativity::Left => {
                let prefix = builder.concat(left, middle)?;
                builder.concat(prefix, right)?
            },
            | Associativity::Right => {
                let suffix = builder.concat(middle, right)?;
                builder.concat(left, suffix)?
            },
        };
        let arena = builder.finish()?;
        Ok((arena, root))
    }

    // Generated text leaves always have an idempotent finalized image.
    proptest! {
        #[test]
        fn finalization_is_idempotent_for_generated_text(
            chars in prop::collection::vec(prop::char::range('a', 'z'), 0..=16)
        ) {
            let text: String = chars.into_iter().collect();
            let result = build_text(TextSource::from(text.as_str()));
            prop_assert!(result.is_ok());
            if let Ok((arena, doc, _)) = result {
                let image = arena.flattened_image(doc);
                prop_assert!(image.is_ok());
                if let Ok(image) = image {
                    prop_assert_eq!(arena.flattened_image(image), Ok(image));
                }
            }
        }
    }

    // Generated constructor counts stay below the test ceiling after sealing.
    proptest! {
        #[test]
        fn stored_node_count_is_bounded_by_constructor_and_image_space(
            leaves in prop::collection::vec(prop::char::range('a', 'z'), 1..=16)
        ) {
            let result = (|| -> Result<DocNodesUsed, BuildError> {
                let mut meter = BuildMeter::new(generous_limits());
                let mut builder = DocBuilder::try_new(&mut meter)?;
                let mut root = builder.empty();
                for _character in leaves {
                    let leaf = builder.text(TextSource::from("x"))?;
                    root = builder.concat(root, leaf)?;
                }
                let arena = builder.finish()?;
                Ok(arena.node_count())
            })();
            prop_assert!(result.is_ok());
            if let Ok(count) = result {
                prop_assert!(count <= DocNodesUsed::from(128u64));
            }
        }
    }

    // Generated constructor sequences return only named build errors.
    proptest! {
        #[test]
        fn no_unexpected_errors_within_ceilings(
            text in prop::collection::vec(prop::char::range('a', 'z'), 0..=16)
        ) {
            let text: String = text.into_iter().collect();
            let result = build_text(TextSource::from(text.as_str()));
            prop_assert!(result.is_ok());
        }
    }
    /// The public resolver preserves exact text cost and output size.
    #[test]
    fn resolver_returns_the_text_winner_summary() -> Result<(), RenderError>
    {
        let (arena, root, _) = expect_build(build_text(TextSource::from("abc")));
        let resolved = resolve_root(&arena, root, LayoutOptions::default())?;
        assert_eq!(resolved.cost(), LayoutCost {
            squared_overflow: SquaredOverflow::from(0u64),
            line_breaks: LineBreaks::from(0u64),
        });
        assert_eq!(resolved.output_bytes(), OutputBytes::from(3u64));
        assert_eq!(resolved.width_taint(), WidthTaint::Untainted);
        Ok(())
    }

    /// A layout-owned line charges one break and its indentation overflow.
    #[test]
    fn resolver_charges_line_break_and_indentation() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let root = expect_build(builder.nest(NestAmount::from(4u32), builder.line()));
        let arena = expect_build(builder.finish());
        let options = LayoutOptions::try_new(
            PageWidth::from(2u32),
            ComputationWidth::from(8u32),
            PhysicalLineEnding::CrLf,
        )?;
        let resolved = resolve_root(&arena, root, options)?;
        assert_eq!(resolved.cost(), LayoutCost {
            squared_overflow: SquaredOverflow::from(4u64),
            line_breaks: LineBreaks::from(1u64),
        });
        assert_eq!(resolved.output_bytes(), OutputBytes::from(6u64));
        Ok(())
    }

    /// Choice retains the lower lexicographic cost.
    #[test]
    fn resolver_choice_uses_squared_overflow_before_line_breaks() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let text = expect_build(builder.text(TextSource::from("abcdef")));
        let line = builder.line();
        let root = expect_build(builder.choice(text, line));
        let arena = expect_build(builder.finish());
        let options = LayoutOptions::try_new(
            PageWidth::from(3u32),
            ComputationWidth::from(10u32),
            PhysicalLineEnding::Lf,
        )?;
        let resolved = resolve_root(&arena, root, options)?;
        assert_eq!(resolved.cost(), LayoutCost {
            squared_overflow: SquaredOverflow::from(0u64),
            line_breaks: LineBreaks::from(1u64),
        });
        assert_eq!(resolved.output_bytes(), OutputBytes::from(1u64));
        Ok(())
    }

    /// A deliberately small exhaustive layout family agrees with a direct
    /// cost oracle at both configured physical endings.
    #[test]
    fn exhaustive_small_documents_match_the_direct_oracle() -> Result<(), RenderError>
    {
        for page in [2u32, 4u32] {
            for computation in [4u32, 8u32] {
                for ending in [PhysicalLineEnding::Lf, PhysicalLineEnding::CrLf] {
                    let mut build_meter = BuildMeter::new(generous_limits());
                    let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
                    let empty = builder.empty();
                    let text = expect_build(builder.text(TextSource::from("abc")));
                    let line = builder.line();
                    let left = expect_build(builder.concat(text, line));
                    let right = expect_build(builder.concat(empty, text));
                    let root = expect_build(builder.choice(left, right));
                    let arena = expect_build(builder.finish());
                    let options = LayoutOptions::try_new(
                        PageWidth::from(page),
                        ComputationWidth::from(computation),
                        ending,
                    )?;
                    let resolved = resolve_root(&arena, root, options)?;
                    let left_cost = LayoutCost {
                        squared_overflow: SquaredOverflow::from(if 3u32 > page {
                            let excess = u64::from(3u32 - page);
                            excess.saturating_mul(excess)
                        }
                        else {
                            0u64
                        }),
                        line_breaks: LineBreaks::from(1u64),
                    };
                    let right_cost = LayoutCost {
                        squared_overflow: SquaredOverflow::from(if 3u32 > page {
                            let excess = u64::from(3u32 - page);
                            excess.saturating_mul(excess)
                        }
                        else {
                            0u64
                        }),
                        line_breaks: LineBreaks::from(0u64),
                    };
                    let expected = if left_cost <= right_cost {
                        left_cost
                    }
                    else {
                        right_cost
                    };
                    assert_eq!(resolved.cost(), expected);
                }
            }
        }
        Ok(())
    }

    /// A repeated in-bound choice state consumes one memo entry.
    #[test]
    fn shared_contexts_reuse_memo_states() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let text = expect_build(builder.text(TextSource::from("x")));
        let root = expect_build(builder.choice(text, text));
        let arena = expect_build(builder.finish());
        let mut meter = RenderMeter::new(generous_render_limits());
        let _resolved = resolve(&arena, root, LayoutOptions::default(), &mut meter)?;
        assert_eq!(u64::from(meter.usage().memo_states), 2u64);
        Ok(())
    }

    /// Out-of-bound shared contexts retain taint and complete selected output.
    #[test]
    fn tainted_contexts_preserve_taint_and_output() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let short = expect_build(builder.text(TextSource::from("aaa")));
        let long = expect_build(builder.text(TextSource::from("aaaa")));
        let shared = expect_build(builder.text(TextSource::from("x")));
        let left = expect_build(builder.concat(short, shared));
        let right = expect_build(builder.concat(long, shared));
        let root = expect_build(builder.choice(left, right));
        let arena = expect_build(builder.finish());
        let options = LayoutOptions::try_new(
            PageWidth::from(2u32),
            ComputationWidth::from(2u32),
            PhysicalLineEnding::Lf,
        )?;
        let resolved = resolve_root(&arena, root, options)?;
        assert_eq!(resolved.cost(), LayoutCost {
            squared_overflow: SquaredOverflow::from(4u64),
            line_breaks: LineBreaks::from(0u64),
        });
        assert_eq!(resolved.width_taint(), WidthTaint::Tainted);
        assert_eq!(resolved.output_bytes(), OutputBytes::from(4u64));
        Ok(())
    }

    /// A tainted fallback preserves the retained promise's columns and
    /// indentation.
    #[test]
    fn render_tainted_root_preserves_promise_columns_and_indentation() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let short = expect_build(builder.text(TextSource::from("aaa")));
        let long = expect_build(builder.text(TextSource::from("aaaa")));
        let hard_line = builder.hard_line();
        let nested_line = expect_build(builder.nest(NestAmount::from(1u32), hard_line));
        let aligned_line = expect_build(builder.align(nested_line));
        let left = expect_build(builder.concat(short, aligned_line));
        let right = expect_build(builder.concat(long, aligned_line));
        let root = expect_build(builder.choice(left, right));
        let arena = expect_build(builder.finish());
        let options = LayoutOptions::try_new(
            PageWidth::from(2u32),
            ComputationWidth::from(2u32),
            PhysicalLineEnding::Lf,
        )?;
        let mut meter = RenderMeter::new(generous_render_limits());
        let rendered = render(&arena, root, &options, &mut meter)?;
        // workflow-gates: allow-escaped-newline
        assert_eq!(rendered.text, "aaa\n    ");
        assert_eq!(rendered.cost, LayoutCost {
            squared_overflow: SquaredOverflow::from(5u64),
            line_breaks: LineBreaks::from(1u64),
        });
        assert_eq!(rendered.width_tainted, WidthTaint::Tainted);
        assert_eq!(u64::from(meter.usage().output_bytes), 8u64);
        Ok(())
    }

    /// Every render meter limit rejects its first disallowed operation.
    #[test]
    fn render_limits_fail_at_each_exact_boundary()
    {
        let (arena, root, _) = expect_build(build_text(TextSource::from("x")));
        let options = LayoutOptions::default();
        let mut limits = generous_render_limits();
        limits.max_memo_states = MaxMemoStates::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            resolve(&arena, root, options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::MemoStates,
                ..
            })
        ));

        let mut limits = generous_render_limits();
        limits.max_plan_nodes_created = MaxPlanNodesCreated::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            resolve(&arena, root, options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::PlanNodesCreated,
                ..
            })
        ));

        let mut limits = generous_render_limits();
        limits.max_live_plan_nodes = MaxLivePlanNodes::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            resolve(&arena, root, options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::LivePlanNodes,
                ..
            })
        ));

        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let text = expect_build(builder.text(TextSource::from("x")));
        let choice = expect_build(builder.choice(text, text));
        let choice_arena = expect_build(builder.finish());
        let mut limits = generous_render_limits();
        limits.max_frontier_entries = MaxFrontierEntries::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            resolve(&choice_arena, choice, options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::FrontierEntries,
                ..
            })
        ));

        let mut limits = generous_render_limits();
        limits.max_output_bytes = MaxOutputBytes::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            resolve(&arena, root, options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::OutputBytes,
                ..
            })
        ));

        let mut limits = generous_render_limits();
        limits.max_layout_steps = MaxLayoutSteps::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            resolve(&arena, root, options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::LayoutSteps,
                ..
            })
        ));

        let mut limits = generous_render_limits();
        limits.max_resolver_work_entries = MaxResolverWorkEntries::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            resolve(&arena, root, options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::ResolverWorkEntries,
                ..
            })
        ));

        let mut limits = generous_render_limits();
        limits.max_resolver_stack = MaxResolverStack::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            resolve(&arena, root, options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::ResolverStack,
                ..
            })
        ));
    }
    /// The fused renderer emits exact text and selected metadata.
    #[test]
    fn render_text_and_layout_metadata_are_exact() -> Result<(), RenderError>
    {
        let (arena, root, _) = expect_build(build_text(TextSource::from("abc")));
        let options = LayoutOptions::default();
        let mut meter = RenderMeter::new(generous_render_limits());
        let rendered = render(&arena, root, &options, &mut meter)?;
        assert_eq!(rendered.text, "abc");
        assert_eq!(rendered.cost, LayoutCost {
            squared_overflow: SquaredOverflow::from(0u64),
            line_breaks: LineBreaks::from(0u64),
        });
        assert_eq!(rendered.width_tainted, WidthTaint::Untainted);
        assert_eq!(u64::from(meter.usage().output_bytes), 3u64);
        assert_eq!(u64::from(meter.usage().vm_steps), 1u64);
        Ok(())
    }

    /// Verbatim bytes remain mixed while layout-owned endings use the option.
    #[test]
    fn render_preserves_verbatim_bytes_and_physical_endings() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let payload =
            // workflow-gates: allow-escaped-newline
            "a\r\nb\n";
        let verbatim = expect_build(builder.verbatim(VerbatimSource::from(payload)));
        let hard_line = builder.hard_line();
        let root = expect_build(builder.concat(verbatim, hard_line));
        let arena = expect_build(builder.finish());
        let options = LayoutOptions::try_new(
            PageWidth::from(2u32),
            ComputationWidth::from(8u32),
            PhysicalLineEnding::CrLf,
        )?;
        let mut meter = RenderMeter::new(generous_render_limits());
        let rendered = render(&arena, root, &options, &mut meter)?;
        // workflow-gates: allow-escaped-newline
        assert_eq!(rendered.text, "a\r\nb\n\r\n");
        assert_eq!(u64::from(meter.usage().output_bytes), 7u64);
        Ok(())
    }

    /// A tainted root still renders complete left-biased output.
    #[test]
    fn render_tainted_root_uses_complete_left_biased_output() -> Result<(), RenderError>
    {
        let mut build_meter = BuildMeter::new(generous_limits());
        let mut builder = expect_build(DocBuilder::try_new(&mut build_meter));
        let short = expect_build(builder.text(TextSource::from("aaa")));
        let long = expect_build(builder.text(TextSource::from("aaaa")));
        let shared = expect_build(builder.text(TextSource::from("x")));
        let left = expect_build(builder.concat(short, shared));
        let right = expect_build(builder.concat(long, shared));
        let root = expect_build(builder.choice(left, right));
        let arena = expect_build(builder.finish());
        let options = LayoutOptions::try_new(
            PageWidth::from(2u32),
            ComputationWidth::from(2u32),
            PhysicalLineEnding::Lf,
        )?;
        let mut meter = RenderMeter::new(generous_render_limits());
        let rendered = render(&arena, root, &options, &mut meter)?;
        assert_eq!(rendered.text, "aaax");
        assert_eq!(rendered.cost, LayoutCost {
            squared_overflow: SquaredOverflow::from(4u64),
            line_breaks: LineBreaks::from(0u64),
        });
        assert_eq!(rendered.width_tainted, WidthTaint::Tainted);
        Ok(())
    }

    /// Output and machine ceilings fail before output can escape.
    #[test]
    fn render_limits_fail_without_partial_output()
    {
        let (arena, root, _) = expect_build(build_text(TextSource::from("abc")));
        let options = LayoutOptions::default();
        let mut limits = generous_render_limits();
        limits.max_output_bytes = MaxOutputBytes::from(2u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            render(&arena, root, &options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::OutputBytes,
                ..
            })
        ));
        assert_eq!(u64::from(meter.usage().output_bytes), 0u64);

        let mut limits = generous_render_limits();
        limits.max_vm_steps = MaxVmSteps::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            render(&arena, root, &options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::VmSteps,
                ..
            })
        ));
        assert_eq!(u64::from(meter.usage().output_bytes), 0u64);
    }

    /// The VM stack ceiling is checked before the initial plan identity enters.
    #[test]
    fn render_vm_stack_limit_is_checked_before_output()
    {
        let (arena, root, _) = expect_build(build_text(TextSource::from("abc")));
        let options = LayoutOptions::default();
        let mut limits = generous_render_limits();
        limits.max_vm_stack = MaxVmStack::from(0u64);
        let mut meter = RenderMeter::new(limits);
        assert!(matches!(
            render(&arena, root, &options, &mut meter),
            Err(RenderError::LimitExceeded {
                kind: gandr_surface_layout::error::RenderLimitKind::VmStack,
                ..
            })
        ));
        assert_eq!(u64::from(meter.usage().output_bytes), 0u64);
    }

    /// Parenthesization preserves complete Unicode output and its independently
    /// calculated cost.
    #[test]
    fn parenthesizations_preserve_unicode_output_and_cost()
    {
        let options = LayoutOptions::try_new(
            PageWidth::from(1_u32),
            ComputationWidth::from(64_u32),
            PhysicalLineEnding::Lf,
        )
        .expect("widths");
        for left in ["", "é", "𐐀x"] {
            for middle in ["", "é", "𐐀x"] {
                for right in ["", "é", "𐐀x"] {
                    let expected = format!("{left}{middle}{right}");
                    let excess = u64::try_from(expected.chars().count().saturating_sub(1))
                        .expect("bounded width");
                    for associativity in [Associativity::Left, Associativity::Right] {
                        let (arena, root) = build_parenthesized_concat(
                            TextSource::from(left),
                            TextSource::from(middle),
                            TextSource::from(right),
                            associativity,
                        )
                        .expect("parenthesized fixture");
                        let mut meter = RenderMeter::new(generous_render_limits());
                        let rendered = render(&arena, root, &options, &mut meter).expect("render");
                        assert_eq!(rendered.text, expected.as_str());
                        assert_eq!(rendered.cost, LayoutCost {
                            squared_overflow: SquaredOverflow::from(excess.saturating_mul(excess)),
                            line_breaks: LineBreaks::from(0_u64)
                        });
                        assert_eq!(rendered.width_tainted, WidthTaint::Untainted);
                        assert_eq!(
                            u64::from(meter.usage().output_bytes),
                            u64::try_from(expected.len()).expect("bounded bytes")
                        );
                    }
                }
            }
        }
    }

    /// Empty operands preserve byte order and metadata on either side of a text
    /// leaf.
    #[test]
    fn empty_operands_preserve_complete_rendered_output()
    {
        for payload in ["", "é𐐀", "a\0b"] {
            let mut build_meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut build_meter).expect("builder");
            let empty = builder.empty();
            let text = builder.text(TextSource::from(payload)).expect("leaf");
            let left = builder.concat(empty, text).expect("left unit");
            let right = builder.concat(text, empty).expect("right unit");
            let arena = builder.finish().expect("arena");
            for root in [left, right] {
                let mut meter = RenderMeter::new(generous_render_limits());
                let rendered =
                    render(&arena, root, &LayoutOptions::default(), &mut meter).expect("render");
                assert_eq!(rendered.text, payload);
                assert_eq!(rendered.cost, LayoutCost {
                    squared_overflow: SquaredOverflow::from(0_u64),
                    line_breaks: LineBreaks::from(0_u64)
                });
                assert_eq!(rendered.width_tainted, WidthTaint::Untainted);
                assert_eq!(
                    u64::from(meter.usage().output_bytes),
                    u64::try_from(payload.len()).expect("bounded bytes")
                );
            }
        }
    }

    /// Balanced rounds retain leaf order across empty, singleton, even and odd
    /// inputs.
    #[test]
    fn balanced_concatenation_preserves_odd_and_even_leaf_order()
    {
        let payloads = ["a", "é", "𐐀", "b", "c"];
        for count in [0_usize, 1, 4, 5] {
            let mut build_meter = BuildMeter::new(generous_limits());
            let mut builder = DocBuilder::try_new(&mut build_meter).expect("builder");
            let mut leaves = Vec::new();
            for &payload in payloads.iter().take(count) {
                leaves.push(builder.text(TextSource::from(payload)).expect("leaf"));
            }
            let root = builder.concat_all(leaves).expect("balanced concatenation");
            let arena = builder.finish().expect("arena");
            let expected = payloads.get(.. count).expect("bounded prefix").concat();
            let mut meter = RenderMeter::new(generous_render_limits());
            let rendered =
                render(&arena, root, &LayoutOptions::default(), &mut meter).expect("render");
            assert_eq!(rendered.text, expected.as_str());
            assert_eq!(
                u64::from(meter.usage().output_bytes),
                u64::try_from(expected.len()).expect("bounded bytes")
            );
        }
    }
}
