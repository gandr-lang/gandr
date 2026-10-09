//! The sharing measure against the erasure, and inside a small stack.
//!
//! # The expansion is what the unshared walk visits
//!
//! Every closed value sketch of up to nine nodes is generated over a unit, an
//! opaque pair, occurrences at distance zero and one, an injection, a pair and
//! a share, with each occurrence placed at its share's next preorder position
//! and each share's arity the number of occurrences its body holds. A share
//! whose body holds none of its occurrences is minted at arity zero, so the
//! class holds roots validation refuses as well as roots it accepts.
//!
//! A refused root must be refused by the measure in validation's own words.
//! An accepted root is erased, and the erased term walked as a tree — the
//! unfolding that inlines every leg at each of its occurrences, which is what
//! the unshared pipeline walks — gives the expansion size the measure must
//! report. The erasure and the walk read nothing the measure computes, and the
//! share, occurrence and node counts and the share depth are read off the
//! sketch the overlay was minted from.
//!
//! # The heap stack is observed
//!
//! A chain of shares nested through their bodies is measured inside a thread
//! with a deliberately small stack: its task stack, its stack of legs in scope
//! and its result stack each grow with the chain, and a per-node recursive
//! measure would need a frame per link.

/// The expansion oracle, shared with the deep suites.
#[cfg(test)]
#[path = "support/unfolding.rs"]
mod unfolding;

/// The measure's suite, in a `cfg(test)` module so the crate's lint wall
/// reads it as test code rather than as shipping code.
#[cfg(test)]
mod measure
{
    use gandr_core_nbe::Bound;
    use gandr_core_nbe::MeasureFault;
    use gandr_core_nbe::Overlay;
    use gandr_core_nbe::OverlayId;
    use gandr_core_nbe::OverlayValueId;
    use gandr_core_nbe::OverlayWatermark;
    use gandr_core_nbe::ShareArity;
    use gandr_core_nbe::ShareDistance;
    use gandr_core_nbe::SharePosition;
    use gandr_core_nbe::Sharing;
    use gandr_core_nbe::SharingMeasure;
    use gandr_core_nbe::ValueGraft;
    use gandr_core_nbe::ValueNode;
    use gandr_core_nbe::erase_value;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueId;
    use gandr_kernel_term::Side;

    use crate::unfolding::CoreNode;
    use crate::unfolding::Quantities;
    use crate::unfolding::Unfolded;
    use crate::unfolding::unfolded;

    /// The most nodes a generated sketch holds. Nine keeps the class near a
    /// hundred thousand sketches, a quarter of which validate, and admits
    /// three shares nested in one another.
    const MAX_NODES: usize = 9;

    /// The deepest scope the generator tells apart: no generated occurrence
    /// counts out past two shares, so every scope past one share is alike.
    const DEEPEST_SCOPE: usize = 2;

    /// The number of links in the deep chain. Each link opens a scope, queues
    /// a task and leaves a result waiting, so a per-node recursive measure
    /// would need a frame per link.
    const CHAIN_LINKS: usize = 100_000;

    /// A stack far too small for a per-node recursive measure over the chain,
    /// and ample for a walk whose stacks are on the heap.
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    /// One node of a sketch, in preorder.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Token
    {
        /// A grafted unit.
        Unit,
        /// An opaque core value.
        Opaque,
        /// An occurrence of the share this many shares out.
        Occurrence(ShareDistance),
        /// A left injection of the node that follows.
        Injection,
        /// A pair of the two nodes that follow.
        Pair,
        /// A share whose leg and then body follow.
        Share,
    }

    /// One node of a placed sketch: each occurrence at its position and each
    /// share at its arity.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Placed
    {
        /// A grafted unit.
        Unit,
        /// An opaque core value.
        Opaque,
        /// An occurrence.
        Occurrence(Bound),
        /// A left injection.
        Injection,
        /// A pair.
        Pair,
        /// A share of this arity.
        Share(ShareArity),
    }

    /// What a sketch counts on its own: every quantity but the expansion.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    struct Counted
    {
        /// The share tokens.
        shares: u64,
        /// The occurrence tokens.
        occurrences: u64,
        /// The most share tokens on one path down from the root.
        depth: u64,
        /// The tokens.
        nodes: u64,
    }

    /// A share whose body the forward placement pass is inside, or is about
    /// to enter.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Scope
    {
        /// The share's index in the sketch.
        share: usize,
        /// The index its body starts at.
        body_start: usize,
        /// The index one past its body's end.
        body_end: usize,
        /// The occurrences of it placed so far.
        taken: u32,
    }

    /// Every closed sketch of at most [`MAX_NODES`] nodes, in no particular
    /// order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each preorder token sequence that forms one tree of at most
    ///   [`MAX_NODES`] nodes in which every occurrence counts out to a share
    ///   whose body encloses it, exactly once.
    /// - provides: the generated class the expansion oracle is asked over.
    /// - panics: none.
    fn sketches() -> Vec<Vec<Token>>
    {
        // `by_size[size][scope]` holds every sketch of `size` nodes closed under
        // `scope` enclosing shares. A share's leg stands in its own scope and
        // its body in one more; past the deepest the generator tells apart, a
        // scope is the deepest.
        let mut by_size: Vec<Vec<Vec<Vec<Token>>>> = Vec::from([Vec::new()]);
        for size in 1 ..= MAX_NODES {
            let below = size.saturating_sub(1);
            // Only the root's row is wanted at the largest size.
            let scopes = if size == MAX_NODES {
                1
            }
            else {
                DEEPEST_SCOPE.saturating_add(1)
            };
            let mut row: Vec<Vec<Vec<Token>>> = Vec::new();
            for scope in 0 .. scopes {
                let mut here: Vec<Vec<Token>> = Vec::new();
                if size == 1 {
                    here.push(Vec::from([Token::Unit]));
                    here.push(Vec::from([Token::Opaque]));
                    for distance in 0 .. scope {
                        let distance = u32::try_from(distance).expect("a scope fits a distance");
                        here.push(Vec::from([Token::Occurrence(ShareDistance::from(
                            distance,
                        ))]));
                    }
                }
                else {
                    for child in &by_size[below][scope] {
                        let mut sketch = Vec::with_capacity(size);
                        sketch.push(Token::Injection);
                        sketch.extend_from_slice(child);
                        here.push(sketch);
                    }
                    let inner = scope.saturating_add(1).min(DEEPEST_SCOPE);
                    for left in 1 .. below {
                        let right = below.saturating_sub(left);
                        for first in &by_size[left][scope] {
                            for second in &by_size[right][scope] {
                                let mut sketch = Vec::with_capacity(size);
                                sketch.push(Token::Pair);
                                sketch.extend_from_slice(first);
                                sketch.extend_from_slice(second);
                                here.push(sketch);
                            }
                            for body in &by_size[right][inner] {
                                let mut sketch = Vec::with_capacity(size);
                                sketch.push(Token::Share);
                                sketch.extend_from_slice(first);
                                sketch.extend_from_slice(body);
                                here.push(sketch);
                            }
                        }
                    }
                }
                row.push(here);
            }
            by_size.push(row);
        }
        by_size
            .into_iter()
            .filter_map(|row| row.into_iter().next())
            .flatten()
            .collect()
    }

    /// Place a sketch's occurrences and size its shares, and count what the
    /// sketch counts on its own.
    ///
    /// # Specification
    /// - requires: `sketch` is one of [`sketches`].
    /// - ensures: the sketch node for node, each occurrence at the next
    ///   preorder position of the share its distance names, counting a share's
    ///   leg outside that share's scope, and each share at the number of
    ///   occurrences that name it; with the share, occurrence and node tokens
    ///   counted and the most share tokens on one path down from the root.
    /// - provides: the overlay the oracle compares, and the four quantities it
    ///   reads off the sketch.
    /// - panics: when the sketch is not one tree or an occurrence counts out
    ///   past every scope, which the requirement excludes.
    fn placed(sketch: &[Token]) -> (Vec<Placed>, Counted)
    {
        // Backwards: each subtree's end and the most shares on one path down
        // it, the leftmost completed subtree on top.
        let mut ends = vec![0_usize; sketch.len()];
        let mut completed: Vec<(usize, u64)> = Vec::new();
        for (index, &token) in sketch.iter().enumerate().rev() {
            let subtree = match token {
                | Token::Unit | Token::Opaque | Token::Occurrence(_) => {
                    (index.saturating_add(1), 0_u64)
                },
                | Token::Injection => completed.pop().expect("an injection has its child"),
                | Token::Pair | Token::Share => {
                    let (_leg_end, left_depth) = completed.pop().expect("a left child");
                    let (end, right_depth) = completed.pop().expect("a right child");
                    let own = u64::from(token == Token::Share);
                    (end, left_depth.max(right_depth).saturating_add(own))
                },
            };
            ends[index] = subtree.0;
            completed.push(subtree);
        }
        let (_end, depth) = completed.pop().expect("a sketch is one tree");

        // Forwards, in preorder: a share's scope opens where its body starts
        // and closes where its body ends, and an occurrence takes the next
        // position of the scope its distance names.
        let mut scopes: Vec<Scope> = Vec::new();
        let mut waiting: Vec<Scope> = Vec::new();
        let mut arities = vec![0_u32; sketch.len()];
        let mut placed = Vec::with_capacity(sketch.len());
        let mut counted = Counted {
            depth,
            ..Counted::default()
        };
        for index in 0 ..= sketch.len() {
            while let Some(closed) = scopes.pop_if(|scope| scope.body_end <= index) {
                arities[closed.share] = closed.taken;
            }
            if let Some(opened) = waiting.pop_if(|scope| scope.body_start == index) {
                scopes.push(opened);
            }
            let Some(&token) = sketch.get(index)
            else {
                break;
            };
            counted.nodes = counted.nodes.saturating_add(1);
            placed.push(match token {
                | Token::Unit => Placed::Unit,
                | Token::Opaque => Placed::Opaque,
                | Token::Occurrence(distance) => {
                    counted.occurrences = counted.occurrences.saturating_add(1);
                    let out = usize::try_from(u32::from(distance)).expect("a distance fits");
                    let named = scopes
                        .len()
                        .checked_sub(1)
                        .and_then(|innermost| innermost.checked_sub(out))
                        .expect("the class is closed");
                    let scope = &mut scopes[named];
                    let position = SharePosition::from(scope.taken);
                    scope.taken = scope.taken.saturating_add(1);
                    Placed::Occurrence(Bound { distance, position })
                },
                | Token::Injection => Placed::Injection,
                | Token::Pair => Placed::Pair,
                | Token::Share => {
                    counted.shares = counted.shares.saturating_add(1);
                    waiting.push(Scope {
                        share: index,
                        body_start: ends[index.saturating_add(1)],
                        body_end: ends[index],
                        taken: 0,
                    });
                    // Sized below, once its body has closed.
                    Placed::Share(ShareArity::default())
                },
            });
        }
        for (node, &arity) in placed.iter_mut().zip(&arities) {
            if let Placed::Share(ref mut sized) = *node {
                *sized = ShareArity::from(arity);
            }
        }
        (placed, counted)
    }

    /// Mint a placed sketch into `overlay`, its opaque nodes holding `opaque`.
    ///
    /// # Specification
    /// - requires: `placed` is one tree, as [`placed`] answers it.
    /// - ensures: the root of a fresh value overlay node for node as `placed`
    ///   holds it, every child minted before its parent.
    /// - provides: the overlay the generated case measures.
    /// - panics: when `placed` is not one tree or a mint is refused, which the
    ///   requirement and the id ceiling exclude.
    fn minted(
        overlay: &mut Overlay,
        placed: &[Placed],
        opaque: ValueId,
    ) -> OverlayValueId
    {
        let mut built: Vec<OverlayValueId> = Vec::new();
        for &node in placed.iter().rev() {
            let value = match node {
                | Placed::Unit => ValueNode::Grafted(ValueGraft::Unit),
                | Placed::Opaque => ValueNode::Opaque(opaque),
                | Placed::Occurrence(bound) => ValueNode::Bound(bound),
                | Placed::Injection => {
                    let injected = built.pop().expect("an injection has its child");
                    ValueNode::Grafted(ValueGraft::Injection(Side::Left, injected))
                },
                | Placed::Pair => {
                    let first = built.pop().expect("a pair has its first component");
                    let second = built.pop().expect("a pair has its second component");
                    ValueNode::Grafted(ValueGraft::Pair(first, second))
                },
                | Placed::Share(arity) => {
                    let leg = built.pop().expect("a share has its leg");
                    let body = built.pop().expect("a share has its body");
                    ValueNode::Shared(Sharing {
                        arity,
                        leg: OverlayId::Value(leg),
                        body,
                    })
                },
            };
            built.push(
                overlay
                    .mint_value(value)
                    .expect("every child was minted before its parent"),
            );
        }
        let root = built.pop().expect("a sketch is one tree");
        assert!(built.is_empty(), "and only one");
        root
    }

    /// `⟨x₀, link⟩[x₀ ← ⟨⟩]` per link over a unit: [`CHAIN_LINKS`] shares
    /// nested through their bodies.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an overlay whose root is the outermost of [`CHAIN_LINKS`]
    ///   links, each a share of arity one over a unit leg whose body pairs its
    ///   occurrence with the link below.
    /// - provides: the deep chain the small-stack case measures.
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn nested_bodies() -> (Overlay, OverlayValueId)
    {
        let mut overlay = Overlay::new();
        let mut nested = overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Unit))
            .expect("a leaf names no child");
        let mut remaining = CHAIN_LINKS;
        while remaining > 0 {
            let leg = overlay
                .mint_value(ValueNode::Grafted(ValueGraft::Unit))
                .expect("a leaf names no child");
            let read = overlay
                .mint_value(ValueNode::Bound(Bound {
                    distance: ShareDistance::from(0_u32),
                    position: SharePosition::from(0_u32),
                }))
                .expect("an occurrence names no child");
            let body = overlay
                .mint_value(ValueNode::Grafted(ValueGraft::Pair(read, nested)))
                .expect("both components resolve");
            nested = overlay
                .mint_value(ValueNode::Shared(Sharing {
                    arity: ShareArity::from(1_u32),
                    leg: OverlayId::Value(leg),
                    body,
                }))
                .expect("the leg and the body resolve");
            remaining = remaining.saturating_sub(1);
        }
        (overlay, nested)
    }

    #[test]
    fn the_expansion_size_is_what_the_unshared_walk_visits()
    {
        let mut core = CoreArena::new();
        let held_unit = core.value_unit();
        let opaque = core.value_pair(held_unit, held_unit);
        let before = core.clone();
        let mark = core.watermark();

        let mut overlay = Overlay::new();
        let mut accepted = 0_u32;
        let mut refused = 0_u32;
        let mut above = 0_u32;
        let mut below = 0_u32;
        for sketch in sketches() {
            overlay.truncate_to(OverlayWatermark::default());
            let (placed, counted) = placed(&sketch);
            let root = minted(&mut overlay, &placed, opaque);
            let measured = SharingMeasure::of(&overlay, OverlayId::Value(root));
            match overlay.validate(OverlayId::Value(root)) {
                | Err(refusal) => {
                    assert_eq!(
                        Err(MeasureFault::Refused(refusal)),
                        measured,
                        "a refused root is refused by the measure in validation's words"
                    );
                    refused = refused.saturating_add(1);
                },
                | Ok(()) => {
                    let measured =
                        measured.expect("an accepted root of the class fits the counter");
                    let erased =
                        erase_value(&overlay, root, &mut core).expect("an accepted root erases");
                    let Unfolded(expansion) = unfolded(&core, CoreNode::Value(erased), &before);
                    assert_eq!(
                        Quantities {
                            shares: counted.shares,
                            occurrences: counted.occurrences,
                            depth: counted.depth,
                            nodes: counted.nodes,
                            expansion,
                        },
                        Quantities::from(measured),
                        "the counts are the sketch's and the expansion is the erased term's \
                         size walked as a tree"
                    );
                    if expansion > counted.nodes {
                        above = above.saturating_add(1);
                    }
                    if expansion < counted.nodes {
                        below = below.saturating_add(1);
                    }
                    core.truncate_to(mark);
                    accepted = accepted.saturating_add(1);
                },
            }
        }
        assert_eq!(
            (25_764, 81_634),
            (accepted, refused),
            "the class is every closed sketch of up to nine nodes; a refused one holds a share \
             whose body holds none of its occurrences"
        );
        assert!(
            above > 0 && below > 0,
            "and it holds roots whose expansion lies above their node count and roots whose \
             expansion lies below it"
        );
    }

    #[test]
    fn a_deep_overlay_is_measured_inside_a_small_stack()
    {
        let measured = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let (overlay, root) = nested_bodies();
                let measured = SharingMeasure::of(&overlay, OverlayId::Value(root))
                    .expect("the chain validates and fits the counter");
                let links = u64::try_from(CHAIN_LINKS).expect("the chain's length fits a counter");
                assert_eq!(
                    Quantities {
                        shares: links,
                        occurrences: links,
                        depth: links,
                        nodes: links.saturating_mul(4).saturating_add(1),
                        expansion: links.saturating_mul(2).saturating_add(1),
                    },
                    Quantities::from(measured),
                    "every link is one share deeper, four nodes larger, and two nodes larger \
                     unshared"
                );

                let mut erased = CoreArena::new();
                let before = erased.clone();
                let erased_root = erase_value(&overlay, root, &mut erased)
                    .expect("the chain validates and erases");
                assert_eq!(
                    Unfolded(u64::from(measured.expansion())),
                    unfolded(&erased, CoreNode::Value(erased_root), &before),
                    "the expansion is the erased chain's size walked as a tree"
                );
            })
            .expect("the small-stack thread starts")
            .join();
        assert!(
            measured.is_ok(),
            "validation, the measure and erasure all keep their depth on the heap"
        );
    }
}
