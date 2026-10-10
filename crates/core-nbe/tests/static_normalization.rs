// Specification backfill pending (gandr-lang/gandr#9): the executable-
// specification lints are allowed until this crate's own backfill lands.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        spec_attribute_present,
        adequacy_present,
        maybe_shape,
        erased_error_signature
    )
)]
//! Static normalization through the public surface: a defined operator at an
//! instance reads back as the ground type it stands for, two reduction orders
//! over generated well-kinded terms reach the readback's normal form, and a
//! static term far deeper than a host stack normalizes inside a small one.
//!
//! The static fragment is the simply kinded λ-calculus over codes, so every
//! term has a normal form and every reduction order reaches it. The evaluator
//! and the readback are one reduction order — call-by-value into closures,
//! read back under binders — and the confluence case sets two more beside it,
//! written by substitution: leftmost-outermost and leftmost-innermost.

#[cfg(test)]
mod static_normalization
{
    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::LoweredChain;
    use gandr_core_nbe::ReadbackMode;
    use gandr_core_nbe::eval_value;
    use gandr_core_nbe::readback_value;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Transparency;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueType;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_core_term::instantiate_value;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GlobalIndex;

    /// Fuel far above what any case needs, so a case fails on its property
    /// rather than on the budget.
    const AMPLE: u32 = 4_000_000;

    /// The depth of the deep case's chains.
    const CHAIN_LINKS: usize = 20_000;

    /// A stack far too small for a per-node recursive evaluation or readback
    /// over the chains, and ample for machines whose task stacks are on the
    /// heap.
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    /// Evaluate `term` and read it back in the spending mode.
    ///
    /// # Specification
    /// trivial.
    fn normal_form(
        core: &mut CoreArena,
        chain: &LoweredChain,
        term: ValueId,
    ) -> ValueId
    {
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let evaluated = eval_value(core, &mut domain, definitions, Fuel::from(AMPLE), term)
            .expect("a well-kinded static term evaluates");
        readback_value(
            core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            Fuel::from(AMPLE),
            evaluated,
        )
        .expect("its value reads back")
    }

    /// A node of a static term: a code, or a type a quote carries.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Position
    {
        Value(ValueId),
        ValueType(ValueTypeId),
    }

    /// The children of `position`, left to right.
    ///
    /// # Specification
    /// trivial.
    fn children(
        core: &CoreArena,
        position: Position,
    ) -> Vec<Position>
    {
        match position {
            | Position::Value(id) => match core.value(id) {
                | Some(&Value::StaticLambda(body)) => Vec::from([Position::Value(body)]),
                | Some(&Value::StaticApplication(head, argument)) => {
                    Vec::from([Position::Value(head), Position::Value(argument)])
                },
                | Some(&Value::Quote(quoted)) => Vec::from([Position::ValueType(quoted)]),
                | _ => Vec::new(),
            },
            | Position::ValueType(id) => match core.value_type(id) {
                | Some(&ValueType::Product(first, second)) => {
                    Vec::from([Position::ValueType(first), Position::ValueType(second)])
                },
                | Some(&ValueType::Element { code, .. }) => Vec::from([Position::Value(code)]),
                | _ => Vec::new(),
            },
        }
    }

    /// Whether `position` is a static redex, and its reduct when it is.
    ///
    /// # Specification
    /// trivial.
    fn redex(
        core: &CoreArena,
        position: Position,
    ) -> Option<(ValueId, ValueId)>
    {
        let Position::Value(id) = position
        else {
            return None;
        };
        let &Value::StaticApplication(head, argument) = core.value(id)?
        else {
            return None;
        };
        let &Value::StaticLambda(body) = core.value(head)?
        else {
            return None;
        };
        Some((body, argument))
    }

    /// Which redex a reference reducer contracts first.
    #[derive(Clone, Copy, Debug)]
    enum Order
    {
        /// The leftmost-outermost: normal order.
        Outermost,
        /// The leftmost-innermost: applicative order.
        Innermost,
    }

    /// The child slot a path step takes below its ancestor, counted from zero.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Slot(usize);

    /// The steps from a root to a node: each ancestor and the child slot taken.
    type Path = Vec<(Position, Slot)>;

    /// The path from `root` to the first redex `order` picks, each step the
    /// ancestor and the child slot taken, or nothing when `root` is normal.
    ///
    /// # Specification
    /// trivial.
    fn first_redex(
        core: &CoreArena,
        root: ValueId,
        order: Order,
    ) -> Option<(Path, ValueId, ValueId)>
    {
        // (position, path to it, children already visited)
        let mut pending: Vec<(Position, Path, bool)> =
            Vec::from([(Position::Value(root), Vec::new(), false)]);
        while let Some((position, path, visited)) = pending.pop() {
            let found = redex(core, position);
            match order {
                | Order::Outermost => {
                    if let Some((body, argument)) = found {
                        return Some((path, body, argument));
                    }
                },
                | Order::Innermost => {
                    if visited {
                        if let Some((body, argument)) = found {
                            return Some((path, body, argument));
                        }
                        continue;
                    }
                    pending.push((position, path.clone(), true));
                },
            }
            let below = children(core, position);
            for (slot, &child) in below.iter().enumerate().rev() {
                let mut deeper = path.clone();
                deeper.push((position, Slot(slot)));
                pending.push((child, deeper, false));
            }
        }
        None
    }

    /// Rebuild the ancestors on `path` over `replacement` at its end.
    ///
    /// # Specification
    /// trivial.
    fn rebuild(
        core: &mut CoreArena,
        path: &[(Position, Slot)],
        replacement: Position,
    ) -> ValueId
    {
        let mut current = replacement;
        for &(ancestor, slot) in path.iter().rev() {
            current = match (ancestor, current) {
                | (Position::Value(id), Position::Value(child)) => {
                    match *core.value(id).expect("an ancestor resolves") {
                        | Value::StaticLambda(_) => {
                            Position::Value(core.value_static_lambda(child))
                        },
                        | Value::StaticApplication(head, argument) => {
                            Position::Value(if slot == Slot(0) {
                                core.value_static_application(child, argument)
                            }
                            else {
                                core.value_static_application(head, child)
                            })
                        },
                        | ref other => panic!("no value child below {other:?}"),
                    }
                },
                | (Position::Value(id), Position::ValueType(child)) => {
                    match *core.value(id).expect("an ancestor resolves") {
                        | Value::Quote(_) => Position::Value(core.value_quote(child)),
                        | ref other => panic!("no type child below {other:?}"),
                    }
                },
                | (Position::ValueType(id), Position::ValueType(child)) => {
                    match *core.value_type(id).expect("an ancestor resolves") {
                        | ValueType::Product(first, second) => {
                            Position::ValueType(if slot == Slot(0) {
                                core.value_type_product(child, second)
                            }
                            else {
                                core.value_type_product(first, child)
                            })
                        },
                        | ref other => panic!("no type child below {other:?}"),
                    }
                },
                | (Position::ValueType(id), Position::Value(child)) => {
                    match *core.value_type(id).expect("an ancestor resolves") {
                        // A decode whose code became a quote reads as the
                        // quoted type, as the readback's decode does.
                        | ValueType::Element { ref target, .. } => {
                            let target = target.clone();
                            Position::ValueType(core.value_type_element(child, target))
                        },
                        | ref other => panic!("no code child below {other:?}"),
                    }
                },
            };
        }
        match current {
            | Position::Value(id) => id,
            | Position::ValueType(_) => panic!("the root is a code"),
        }
    }

    /// Normalize `root` by substitution, contracting redexes in `order`.
    ///
    /// # Specification
    /// trivial.
    fn reduced(
        core: &mut CoreArena,
        root: ValueId,
        order: Order,
    ) -> ValueId
    {
        let mut current = root;
        for _ in 0 .. 100_000_u32 {
            let Some((path, body, argument)) = first_redex(core, current, order)
            else {
                return current;
            };
            let reduct = instantiate_value(core, body, argument);
            current = rebuild(core, &path, Position::Value(reduct));
        }
        panic!("a simply kinded term reaches its normal form well inside the step cap")
    }

    /// Whether two terms agree.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Alike
    {
        /// One term up to node identity.
        Same,
        /// Two terms.
        Different,
    }

    /// Whether two nodes are one term up to node identity.
    ///
    /// # Specification
    /// trivial.
    fn same_term(
        core: &CoreArena,
        left: ValueId,
        right: ValueId,
    ) -> Alike
    {
        let mut pending = Vec::from([(Position::Value(left), Position::Value(right))]);
        while let Some((one, other)) = pending.pop() {
            let alike = match (one, other) {
                | (Position::Value(a), Position::Value(b)) => {
                    match (core.value(a), core.value(b)) {
                        | (Some(&Value::StaticLambda(_)), Some(&Value::StaticLambda(_)))
                        | (
                            Some(&Value::StaticApplication(..)),
                            Some(&Value::StaticApplication(..)),
                        )
                        | (Some(&Value::Quote(_)), Some(&Value::Quote(_))) => true,
                        | (Some(x), Some(y)) => x == y,
                        | _ => false,
                    }
                },
                | (Position::ValueType(a), Position::ValueType(b)) => {
                    match (core.value_type(a), core.value_type(b)) {
                        | (Some(&ValueType::Product(..)), Some(&ValueType::Product(..))) => true,
                        | (
                            Some(&ValueType::Element { target: ref x, .. }),
                            Some(&ValueType::Element { target: ref y, .. }),
                        ) => x == y,
                        | (Some(x), Some(y)) => x == y,
                        | _ => false,
                    }
                },
                | _ => false,
            };
            if !alike {
                return Alike::Different;
            }
            let (ones, others) = (children(core, one), children(core, other));
            if ones.len() != others.len() {
                return Alike::Different;
            }
            pending.extend(ones.into_iter().zip(others));
        }
        Alike::Same
    }

    /// A static classifier of the generated fragment.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Kind
    {
        /// `Type`.
        Star,
        /// `Type → Type`.
        Unary,
        /// `Type → Type → Type`.
        Binary,
        /// `(Type → Type) → Type`.
        Higher,
    }

    impl Kind
    {
        /// The domain and codomain of an arrow kind.
        ///
        /// # Specification
        /// trivial.
        fn arrow(self) -> Option<(Self, Self)>
        {
            match self {
                | Self::Star => None,
                | Self::Unary => Some((Self::Star, Self::Star)),
                | Self::Binary => Some((Self::Star, Self::Unary)),
                | Self::Higher => Some((Self::Unary, Self::Star)),
            }
        }

        /// The arrow kinds whose codomain is this kind.
        ///
        /// # Specification
        /// trivial.
        fn operators(self) -> &'static [Self]
        {
            match self {
                | Self::Star => &[Self::Unary, Self::Higher],
                | Self::Unary => &[Self::Binary],
                | Self::Binary | Self::Higher => &[],
            }
        }
    }

    /// What a generated node is.
    #[derive(Clone, Copy, Debug)]
    enum Shape
    {
        Lambda,
        Apply,
        Variable(u32),
        Rigid,
        Integer,
        Product,
    }

    /// A generated term in pre-order: every child after its parent.
    #[repr(transparent)]
    #[derive(Clone, Debug, Default)]
    struct Tree
    {
        nodes: Vec<(Shape, Vec<usize>)>,
    }

    /// A deterministic xorshift stream.
    #[repr(transparent)]
    struct Stream(u64);

    impl Stream
    {
        /// The next draw among `choices`, or nothing when there are none.
        ///
        /// # Specification
        /// trivial.
        fn pick<'choices, T>(
            &mut self,
            choices: &'choices [T],
        ) -> Option<&'choices T>
        {
            self.0 ^= self.0.wrapping_shl(13);
            self.0 ^= self.0.wrapping_shr(7);
            self.0 ^= self.0.wrapping_shl(17);
            let drawn = self.0.checked_rem(u64::try_from(choices.len()).unwrap())?;
            choices.get(usize::try_from(drawn).unwrap())
        }
    }

    /// How many formers deep a generated term may grow before its leaves.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Depth(u32);

    /// Generate a closed term of `kind`, at most `depth` formers deep before
    /// the leaves.
    ///
    /// # Specification
    /// trivial.
    fn generate(
        stream: &mut Stream,
        kind: Kind,
        depth: Depth,
    ) -> Tree
    {
        let Depth(fuel) = depth;
        let mut tree = Tree::default();
        // (parent, kind, binder kinds outermost first, fuel left)
        let mut pending: Vec<(Option<usize>, Kind, Vec<Kind>, u32)> =
            Vec::from([(None, kind, Vec::new(), fuel)]);
        while let Some((parent, kind, context, fuel)) = pending.pop() {
            let here = tree.nodes.len();
            if let Some(parent) = parent {
                tree.nodes[parent].1.push(here);
            }
            let variables: Vec<u32> = context
                .iter()
                .enumerate()
                .filter(|&(_, &bound)| bound == kind)
                .map(|(level, _)| {
                    let outward = context
                        .len()
                        .checked_sub(1)
                        .unwrap()
                        .checked_sub(level)
                        .unwrap();
                    u32::try_from(outward).unwrap()
                })
                .collect();
            let less = fuel.saturating_sub(1);
            let operators = kind.operators();
            let mut options: Vec<Shape> = Vec::new();
            match kind.arrow() {
                | Some(_) => options.push(Shape::Lambda),
                | None => {
                    options.push(Shape::Integer);
                    options.push(Shape::Rigid);
                    if fuel > 0 {
                        options.push(Shape::Product);
                    }
                },
            }
            if let Some(&index) = stream.pick(&variables) {
                options.push(Shape::Variable(index));
            }
            if fuel > 0 && !operators.is_empty() {
                options.push(Shape::Apply);
                options.push(Shape::Apply);
            }
            let shape = *stream.pick(&options).unwrap();
            let children: Vec<(Kind, Vec<Kind>)> = match shape {
                | Shape::Lambda => {
                    let (domain, codomain) = kind.arrow().unwrap();
                    let mut deeper = context.clone();
                    deeper.push(domain);
                    Vec::from([(codomain, deeper)])
                },
                | Shape::Apply => {
                    let operator = *stream.pick(operators).unwrap();
                    let (domain, _) = operator.arrow().unwrap();
                    Vec::from([(operator, context.clone()), (domain, context.clone())])
                },
                | Shape::Product => {
                    Vec::from([(Kind::Star, context.clone()), (Kind::Star, context.clone())])
                },
                | Shape::Variable(_) | Shape::Rigid | Shape::Integer => Vec::new(),
            };
            tree.nodes.push((shape, Vec::new()));
            for (child, child_context) in children.into_iter().rev() {
                pending.push((Some(here), child, child_context, less));
            }
        }
        tree
    }

    /// Mint `tree` into `core`.
    ///
    /// # Specification
    /// trivial.
    fn build(
        core: &mut CoreArena,
        tree: &Tree,
    ) -> ValueId
    {
        let mut built: Vec<Option<ValueId>> = vec![None; tree.nodes.len()];
        for here in (0 .. tree.nodes.len()).rev() {
            let (shape, ref children) = tree.nodes[here];
            let child = |position: usize| built[children[position]].unwrap();
            let minted = match shape {
                | Shape::Lambda => core.value_static_lambda(child(0)),
                | Shape::Apply => core.value_static_application(child(0), child(1)),
                | Shape::Variable(index) => {
                    core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
                },
                | Shape::Rigid => core.value_constant(ConstantIndex::from(0_usize)),
                | Shape::Integer => {
                    let integer = core.value_type_base(BaseType::Integer);
                    core.value_quote(integer)
                },
                | Shape::Product => {
                    let first = core.value_type_element(child(0), Level::zero());
                    let second = core.value_type_element(child(1), Level::zero());
                    let product = core.value_type_product(first, second);
                    core.value_quote(product)
                },
            };
            built[here] = Some(minted);
        }
        built[0].unwrap()
    }

    #[test]
    fn a_static_redex_normalizes_to_its_ground_type()
    {
        // `Pair := λA. ⌜El A × El A⌝`, read at `Pair (Pair ⌜Integer⌝)`.
        let mut core = CoreArena::new();
        let pair = ConstantIndex::from(0_usize);
        let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = core.value_type_element(bound, Level::zero());
        let doubled = core.value_type_product(decoded, decoded);
        let quote = core.value_quote(doubled);
        let body = core.value_static_lambda(quote);
        let integer = core.value_type_base(BaseType::Integer);
        let integer_code = core.value_quote(integer);
        let head = core.value_constant(pair);
        let inner = core.value_static_application(head, integer_code);
        let outer = core.value_static_application(head, inner);

        let mut definitions = DefinitionChain::new();
        let defined =
            definitions.define(pair, GlobalIndex::from(0_u32), Transparency::Manifest, &[]);
        assert!(defined.is_ok());
        let chain = LoweredChain::lower(definitions, |_| Ok::<_, core::convert::Infallible>(body))
            .unwrap_or_else(|never| match never {});

        let normal = normal_form(&mut core, &chain, outer);
        let mut ground = CoreArena::new();
        let ground_integer = ground.value_type_base(BaseType::Integer);
        let square = ground.value_type_product(ground_integer, ground_integer);
        let fourth = ground.value_type_product(square, square);
        let expected = ground.value_quote(fourth);
        let mut pending = Vec::from([(Position::Value(normal), Position::Value(expected))]);
        while let Some((read, wanted)) = pending.pop() {
            match (read, wanted) {
                | (Position::Value(read), Position::Value(wanted)) => {
                    let (Some(&Value::Quote(read)), Some(&Value::Quote(wanted))) =
                        (core.value(read), ground.value(wanted))
                    else {
                        panic!("the normal form is the ground quote, with no application left");
                    };
                    pending.push((Position::ValueType(read), Position::ValueType(wanted)));
                },
                | (Position::ValueType(read), Position::ValueType(wanted)) => {
                    match (core.value_type(read), ground.value_type(wanted)) {
                        | (Some(&ValueType::Product(a, b)), Some(&ValueType::Product(c, d))) => {
                            pending.push((Position::ValueType(a), Position::ValueType(c)));
                            pending.push((Position::ValueType(b), Position::ValueType(d)));
                        },
                        | (Some(&ValueType::Base(a)), Some(&ValueType::Base(b))) => {
                            assert_eq!(a, b, "every leaf is the instance's ground type");
                        },
                        | (read, wanted) => panic!("{read:?} is not the ground {wanted:?}"),
                    }
                },
                | _ => panic!("the two walks stay in step"),
            }
        }
    }

    #[test]
    fn static_normalization_is_confluent()
    {
        let mut stream = Stream(0x2545_F491_4F6C_DD1D);
        let kinds = [Kind::Star, Kind::Unary, Kind::Binary, Kind::Higher];
        let rounds = 800_usize;
        let mut reducible = 0_usize;
        for round in 0 .. rounds {
            let kind = kinds[round % kinds.len()];
            let tree = generate(&mut stream, kind, Depth(4_u32));
            let mut core = CoreArena::new();
            let term = build(&mut core, &tree);
            if first_redex(&core, term, Order::Outermost).is_some() {
                reducible = reducible.checked_add(1_usize).unwrap();
            }
            let outermost = reduced(&mut core, term, Order::Outermost);
            let innermost = reduced(&mut core, term, Order::Innermost);
            let read = normal_form(&mut core, &LoweredChain::new(), term);
            assert_eq!(
                Alike::Same,
                same_term(&core, outermost, innermost),
                "round {round}: normal order and applicative order reach one normal form for \
                 {tree:?}"
            );
            assert_eq!(
                Alike::Same,
                same_term(&core, outermost, read),
                "round {round}: and the readback reaches it too, for {tree:?}"
            );
        }
        assert!(
            reducible.checked_mul(4_usize).unwrap() >= rounds,
            "the generator reaches redexes in at least a quarter of its terms, so the orders \
             are compared on reductions rather than on terms already normal ({reducible} of \
             {rounds})"
        );
    }

    #[test]
    fn a_deep_static_term_normalizes_inside_a_small_stack()
    {
        let walked = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(|| {
                let mut core = CoreArena::new();
                let integer = core.value_type_base(BaseType::Integer);
                let code = core.value_quote(integer);
                // `id (id (… (id ⌜Integer⌝)))`: every link is a redex.
                let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let identity = core.value_static_lambda(bound);
                let mut redexes = code;
                for _ in 0 .. CHAIN_LINKS {
                    redexes = core.value_static_application(identity, redexes);
                }
                let reduced = normal_form(&mut core, &LoweredChain::new(), redexes);
                let Some(&Value::Quote(quoted)) = core.value(reduced)
                else {
                    panic!("every redex fired, leaving the innermost quote");
                };
                assert_eq!(
                    Some(&ValueType::Base(BaseType::Integer)),
                    core.value_type(quoted),
                    "and the quote carries the innermost type"
                );

                // `F (F (… (F ⌜Integer⌝)))` with `F` rigid: every link stays.
                let family = ConstantIndex::from(0_usize);
                let head = core.value_constant(family);
                let mut stuck = code;
                for _ in 0 .. CHAIN_LINKS {
                    stuck = core.value_static_application(head, stuck);
                }
                let read = normal_form(&mut core, &LoweredChain::new(), stuck);
                let mut links = 0_usize;
                let mut at = read;
                while let Some(&Value::StaticApplication(applied, argument)) = core.value(at) {
                    assert_eq!(
                        Some(&Value::Constant(family)),
                        core.value(applied),
                        "link {links} is the rigid family"
                    );
                    links = links
                        .checked_add(1_usize)
                        .expect("the chain fits a counter");
                    at = argument;
                }
                assert!(
                    matches!(core.value(at), Some(&Value::Quote(_))),
                    "the chain ends at the innermost quote"
                );
                links
            })
            .expect("the small-stack thread spawns")
            .join()
            .expect("evaluation and readback fit the small stack");
        assert_eq!(
            CHAIN_LINKS, walked,
            "every stuck application read back as itself"
        );
    }
}
