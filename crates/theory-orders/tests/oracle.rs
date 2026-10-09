#[cfg(test)]
mod oracle
{
    //! Reference-oracle property tests for `OrderMaintenance` over the public
    //! API.
    //!
    //! A generated sequence of insertions and removals is replayed against a
    //! naive `Vec` model. After every operation the structure's iteration
    //! order, length, and handle sequence must match the model, and at the end
    //! O(1) comparison must agree with list order for every pair. The model
    //! is an external oracle: it shares no code with the structure, so a
    //! mutant that perturbs a label, a link, or the comparison direction
    //! diverges from it.
    //!
    //! The narrow-universe relabel and capacity paths are exercised by the
    //! crate's in-module unit tests, which reach the test-only narrow
    //! constructor. This target complements them with a full-universe relabel
    //! stress test and the broad randomized cross-check.

    use gandr_theory_orders::OrderError;
    use gandr_theory_orders::OrderMaintenance;
    use gandr_theory_orders::Pos;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::Strategy;
    use proptest::prelude::any;
    use proptest::prop_assert_eq;
    use proptest::prop_oneof;
    use proptest::proptest;

    /// Semantic payload observed by the oracle value extractor.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct OracleValue(u64);

    /// A zero-based rank into the model, reduced modulo the current length
    /// when applied so it always names a live element of a non-empty
    /// structure.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct OracleRank(usize);

    /// A rank already reduced into the model's index range, so it names an
    /// element of both the model and the parallel handle list.
    ///
    /// Distinct from [`OracleRank`]: a rank is whatever the generator
    /// produced, an index has been checked against a length. Keeping them
    /// apart is what stops an unreduced rank reaching a lookup.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct OracleIndex(usize);

    /// One edit applied to both the structure and the reference model.
    #[derive(Clone, Copy, Debug)]
    enum Op
    {
        /// Append at the end.
        PushBack(OracleValue),
        /// Prepend at the front.
        PushFront(OracleValue),
        /// Insert after the element at the reduced rank.
        InsertAfter(OracleRank, OracleValue),
        /// Insert before the element at the reduced rank.
        InsertBefore(OracleRank, OracleValue),
        /// Remove the element at the reduced rank.
        Remove(OracleRank),
    }

    /// A failure of the oracle harness itself, as distinct from a
    /// disagreement between the structure and the model.
    ///
    /// A disagreement is an assertion, because that is the property under
    /// test. The variants here are the ways the harness can fail to apply an
    /// edit it intended to apply — none of which the generator should be
    /// able to produce, so each one surfacing is itself a finding rather
    /// than a panic buried in a helper.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum OracleFailure
    {
        /// The structure refused an operation the model accepted.
        Order(OrderError),
        /// A generated rank did not reduce into the model's index range,
        /// which can only happen if the model is empty at a point the
        /// harness treats as non-empty.
        RankNotReducible,
        /// A reduced rank did not name an element of the model or of the
        /// parallel handle list, so the two fell out of step.
        RankOutOfRange,
        /// Advancing an index one past the reduced rank overflowed.
        IndexOverflow,
    }

    impl From<OrderError> for OracleFailure
    {
        /// The structure's failure as a harness failure.
        ///
        /// # Specification
        /// trivial.
        fn from(value: OrderError) -> Self
        {
            Self::Order(value)
        }
    }

    /// Reduces a generated rank into the model's index range.
    ///
    /// Taking the model itself rather than its length keeps the collection
    /// that defines the range visible at the call site, and leaves no
    /// length to name.
    ///
    /// # Specification
    /// - requires: nothing; any generated rank may be offered.
    /// - ensures: returns the rank reduced modulo the model's length, so the
    ///   result names an element of the model whenever the model is non-empty.
    /// - provides: the one narrowing from a generated rank to an index the
    ///   model and the parallel handle list both accept.
    /// - fails: [`OracleFailure::RankNotReducible`] when the model is empty,
    ///   which the harness's own emptiness guards preclude.
    /// - panics: none.
    fn reduce(
        rank: OracleRank,
        model: &[OracleValue],
    ) -> Result<OracleIndex, OracleFailure>
    {
        rank.0
            .checked_rem(model.len())
            .map(OracleIndex)
            .ok_or(OracleFailure::RankNotReducible)
    }

    /// A generator for a single [`Op`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields each of the five [`Op`] variants, with payloads and
    ///   ranks drawn over the whole range of their types.
    /// - provides: the edit alphabet the replay draws from; every variant being
    ///   present is what makes the cross-check reach appending, prepending,
    ///   both interior insertions, and removal.
    /// - panics: none.
    fn op_strategy() -> impl Strategy<Value = Op>
    {
        prop_oneof![
            any::<u64>().prop_map(|value| Op::PushBack(OracleValue(value))),
            any::<u64>().prop_map(|value| Op::PushFront(OracleValue(value))),
            (any::<usize>(), any::<u64>())
                .prop_map(|(rank, value)| Op::InsertAfter(OracleRank(rank), OracleValue(value))),
            (any::<usize>(), any::<u64>())
                .prop_map(|(rank, value)| Op::InsertBefore(OracleRank(rank), OracleValue(value))),
            any::<usize>().prop_map(|rank| Op::Remove(OracleRank(rank))),
        ]
    }

    /// The payloads of `order` in list order.
    ///
    /// # Specification
    /// trivial.
    fn values(order: &OrderMaintenance<OracleValue>) -> Vec<OracleValue>
    {
        order.iter().map(|(_pos, &value)| value).collect()
    }

    /// The handles of `order` in list order.
    ///
    /// # Specification
    /// trivial.
    fn handles_of(order: &OrderMaintenance<OracleValue>) -> Vec<Pos>
    {
        order.iter().map(|(pos, _value)| pos).collect()
    }

    /// Asserts O(1) comparison agrees with list rank for every ordered pair.
    ///
    /// # Specification
    /// - requires: `order` is any structure whose links resolve.
    /// - ensures: returns only when every ordered pair of handles compares as
    ///   their list ranks do.
    /// - provides: the check that the constant-time comparison agrees with the
    ///   linear rank it stands in for.
    /// - panics: panics on the first pair whose comparison disagrees with its
    ///   rank pair.
    fn assert_pairwise_comparison(order: &OrderMaintenance<OracleValue>)
    {
        let handles = handles_of(order);
        for (left_rank, &left) in handles.iter().enumerate() {
            for (right_rank, &right) in handles.iter().enumerate() {
                assert_eq!(
                    order.cmp(left, right),
                    Some(left_rank.cmp(&right_rank)),
                    "O(1) comparison agrees with list order"
                );
            }
        }
    }

    /// Replays `ops` against the structure and a `Vec` model, checking
    /// agreement after each step and pairwise comparison at the end.
    ///
    /// Agreement failures are assertions, since agreement is the property
    /// under test. Failures of the harness itself return [`OracleFailure`],
    /// so the caller — always a `#[test]` body — decides how they surface;
    /// the helper itself stays free of `expect`.
    ///
    /// # Specification
    /// - requires: `ops` is any generated edit sequence; an edit naming a rank
    ///   in an empty structure is skipped rather than refused.
    /// - ensures: returns `Ok` only when, after every applied edit, the
    ///   structure's payload sequence, length, and handle sequence all equal
    ///   the model's, and every pair compares as its rank pair does at the end.
    /// - provides: the cross-check against an oracle that shares no code with
    ///   the structure, so a perturbed label, link, or comparison direction
    ///   diverges from it.
    /// - fails: [`OracleFailure`] when the harness cannot apply an edit it
    ///   intended to apply, which the generator should not be able to produce.
    /// - panics: panics on any disagreement with the model, which is the
    ///   property under test.
    fn replay(ops: &[Op]) -> Result<(), OracleFailure>
    {
        let mut order: OrderMaintenance<OracleValue> = OrderMaintenance::new()?;
        let mut model: Vec<OracleValue> = Vec::new();
        let mut handles: Vec<Pos> = Vec::new();
        for op in ops {
            match *op {
                | Op::PushBack(value) => {
                    let pos = order.push_back(value)?;
                    model.push(value);
                    handles.push(pos);
                },
                | Op::PushFront(value) => {
                    let pos = order.push_front(value)?;
                    model.insert(0, value);
                    handles.insert(0, pos);
                },
                | Op::InsertAfter(rank, value) => {
                    if model.is_empty() {
                        continue;
                    }
                    let index = reduce(rank, &model)?;
                    let anchor = handles
                        .get(index.0)
                        .copied()
                        .ok_or(OracleFailure::RankOutOfRange)?;
                    let pos = order.insert_after(anchor, value)?;
                    let after = index.0.checked_add(1).ok_or(OracleFailure::IndexOverflow)?;
                    model.insert(after, value);
                    handles.insert(after, pos);
                },
                | Op::InsertBefore(rank, value) => {
                    if model.is_empty() {
                        continue;
                    }
                    let index = reduce(rank, &model)?;
                    let anchor = handles
                        .get(index.0)
                        .copied()
                        .ok_or(OracleFailure::RankOutOfRange)?;
                    let pos = order.insert_before(anchor, value)?;
                    model.insert(index.0, value);
                    handles.insert(index.0, pos);
                },
                | Op::Remove(rank) => {
                    if model.is_empty() {
                        continue;
                    }
                    let index = reduce(rank, &model)?;
                    let target = handles
                        .get(index.0)
                        .copied()
                        .ok_or(OracleFailure::RankOutOfRange)?;
                    let expected = model
                        .get(index.0)
                        .copied()
                        .ok_or(OracleFailure::RankOutOfRange)?;
                    assert_eq!(
                        order.remove(target),
                        Ok(Some(expected)),
                        "remove returns the modelled payload"
                    );
                    model.remove(index.0);
                    handles.remove(index.0);
                },
            }
            assert_eq!(values(&order), model, "iteration order matches the model");
            assert_eq!(
                usize::from(order.len()),
                model.len(),
                "length matches the model"
            );
            assert_eq!(
                handles_of(&order),
                handles,
                "the handle sequence matches the model"
            );
        }
        assert_pairwise_comparison(&order);
        Ok(())
    }

    #[test]
    fn relabel_stress_at_full_universe()
    {
        // Inserting many elements after one fixed anchor halves the local
        // label gap each time, so even the full 2^62 universe relabels
        // after a few dozen insertions — this drives the relabel path
        // without the test-only narrow constructor.
        let mut order: OrderMaintenance<OracleValue> =
            OrderMaintenance::new().expect("structure id allocation succeeds in oracle test");
        let anchor = order.push_back(OracleValue(0)).expect("push_back succeeds");
        order
            .push_back(OracleValue(u64::MAX))
            .expect("push_back succeeds");
        let count: u64 = 300;
        for value in 1 ..= count {
            order
                .insert_after(anchor, OracleValue(value))
                .expect("insert_after succeeds under relabel");
        }
        let capacity = usize::try_from(count)
            .expect("count fits in usize")
            .checked_add(2)
            .expect("count + 2 fits in usize");
        let mut expected: Vec<OracleValue> = Vec::with_capacity(capacity);
        expected.push(OracleValue(0));
        expected.extend((1 ..= count).rev().map(OracleValue));
        expected.push(OracleValue(u64::MAX));
        assert_eq!(
            values(&order),
            expected,
            "full-universe relabeling preserves order"
        );
        assert_pairwise_comparison(&order);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// A random op sequence keeps the structure in lock-step with the model.
        #[test]
        fn matches_reference_model(ops in proptest::collection::vec(op_strategy(), 0 .. 80))
        {
            prop_assert_eq!(
                replay(&ops),
                Ok(()),
                "the oracle harness applies every generated edit"
            );
        }
    }
}
