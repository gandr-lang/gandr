//! 2-cell faces: a rewrite `lhs ==> rhs` as a pair of open terms in the free
//! structure over a signature.
//!
//! A [`RuleFace`] stores its two [`FreeTerm`]s untyped, with host-side
//! well-formedness ([`check_desc`]) standing in for typing; the encoding
//! stays the same when checking moves into a checker. Each face carries
//! derived [`RuleVarMeta`] per pattern variable, whose [`Variance`] is the
//! constant [`Variance::Producer`] until consumer-argument operations exist.
//!
//! [`check_desc`]: crate::check_desc

use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::RuleVariableLinearity;
use crate::code::Name;
use crate::desc::SurfaceSpan;
use crate::tree::ArgumentCount;
use crate::tree::Children;
use crate::tree::Head;
use crate::tree::Tree;
use crate::tree::TreeRef;
use crate::tree::leaf_image;

/// One node head of a free term.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum TermHead
{
    /// A pattern variable.
    Var(Name),
    /// A constructor application over its argument count.
    Ctor(Name, ArgumentCount),
    /// An operation application over its argument count.
    Op(Name, ArgumentCount),
}

impl Head for TermHead
{
    /// The application's argument count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arity(&self) -> ArgumentCount
    {
        match *self {
            | Self::Var(_) => ArgumentCount::from(0_usize),
            | Self::Ctor(_, arity) | Self::Op(_, arity) => arity,
        }
    }
}

/// A term in the free monad `D⋆(V)` over the description functor with
/// variables `V`: a variable, a constructor application, or an operation
/// application.
///
/// Held as one flat table, so a term of any depth is built, compared, walked
/// and dropped without recursion.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FreeTerm(Tree<TermHead>);

impl FreeTerm
{
    /// A variable term.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn var<N>(name: N) -> Self
    where
        N: Into<Name>,
    {
        Self(Tree::leaf(TermHead::Var(name.into())))
    }

    /// A constructor application `C(t₀, …, tₙ)`; `n = 0` is a nullary
    /// constructor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn ctor<N, A>(
        name: N,
        args: A,
    ) -> Self
    where
        N: Into<Name>,
        A: IntoIterator<Item = Self>,
    {
        let args: Vec<Tree<TermHead>> = args.into_iter().map(|arg| arg.0).collect();
        let arity = ArgumentCount::from(args.len());
        Self(Tree::node(TermHead::Ctor(name.into(), arity), args))
    }

    /// An operation application `f(t₀, …, tₙ)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn op<N, A>(
        name: N,
        args: A,
    ) -> Self
    where
        N: Into<Name>,
        A: IntoIterator<Item = Self>,
    {
        let args: Vec<Tree<TermHead>> = args.into_iter().map(|arg| arg.0).collect();
        let arity = ArgumentCount::from(args.len());
        Self(Tree::node(TermHead::Op(name.into(), arity), args))
    }

    /// The term as a borrowed node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_node(&self) -> TermNode<'_>
    {
        TermNode(self.0.to_ref())
    }

    /// The term's head and arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&self) -> TermView<'_>
    {
        self.to_node().view()
    }

    /// This term's free variables, its variable leaves, in left-to-right
    /// order with repeats.
    ///
    /// # Specification
    /// - ensures: every variable leaf is recorded once per occurrence, in
    ///   left-to-right order, so linearity can be judged by counting.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term with a repeated variable under a nested
    ///   application, and a ground term, pin the count, the order and the empty
    ///   case.
    /// - witness: `rule::tests::free_variables_are_collected_in_order_with_repeats`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref vars| vars.iter().eq(self.to_node().vars()))]
    pub fn collect_vars(&self) -> Vec<Name>
    {
        self.to_node().vars().cloned().collect()
    }

    /// The constructor and operation names the term applies, in pre-order.
    ///
    /// # Specification
    /// - ensures: each applied constructor or operation is yielded once, root
    ///   first and children left to right; variables contribute no name.
    /// - panics: none.
    /// - executable: none — the backend cannot instrument this opaque iterator
    ///   return type, and its full sequence has only a consuming observer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — variable-only, nullary and mixed nested applications
    ///   are observed through exact name sequences; including a variable,
    ///   omitting a nullary head or reversing siblings changes the sequence.
    /// - witness: `rule::tests::inspection_reads_mixed_applications_in_argument_order`
    #[inline]
    pub(crate) fn applied_symbols(&self) -> impl Iterator<Item = &Name>
    {
        self.0.to_ref().preorder().filter_map(|head| match *head {
            | TermHead::Var(_) => None,
            | TermHead::Ctor(ref name, _) | TermHead::Op(ref name, _) => Some(name),
        })
    }

    /// The term with each variable `image` answers for replaced by its image.
    ///
    /// # Specification
    /// - ensures: every variable leaf `image` answers for is replaced by the
    ///   answered term, and every other leaf is kept; applications keep their
    ///   head, kind and argument order.
    /// - panics: none.
    /// - intension: one pass over the table, appending each image whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root and nested variables with present/absent images,
    ///   mixed application kinds and nullary applications are observed as exact
    ///   output terms and callback names. Replacing a head, traversing an image
    ///   again or dropping an unanswered variable changes an observer.
    /// - witness: `rule::tests::variable_replacement_preserves_applications_and_inserts_images_once`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref result| matches!(*self.0.to_ref().head(), TermHead::Var(_))
        || result.0.to_ref().head() == self.0.to_ref().head())]
    pub(crate) fn replace_vars<'image, I>(
        &self,
        mut image: I,
    ) -> Self
    where
        I: FnMut(&Name) -> Maybe<TermNode<'image>, leaf_image::Absent>,
    {
        Self(self.0.to_ref().replace_leaves(|head| match *head {
            | TermHead::Var(ref name) => image(name).map(|replacement| replacement.0),
            | TermHead::Ctor(..) | TermHead::Op(..) => Maybe::Absent(leaf_image::Absent::Kept),
        }))
    }
}

impl fmt::Display for FreeTerm
{
    /// Writes the term in the inspection notation: a variable or a nullary
    /// application as its name, an application as `name(arg, …)`.
    ///
    /// # Specification
    /// - ensures: deterministic text; a constructor and an operation
    ///   application render alike, so two unequal terms can render the same.
    /// - fails: the formatting sink's error when it refuses the rendered text.
    /// - panics: none.
    /// - executable: none — a formatter exposes no readback of the rendered
    ///   text or predicate predicting whether its sink accepts the write.
    /// - intension: one pass over the table in index order, where every node
    ///   follows its arguments' subtrees and its first argument is the most
    ///   recent; rendered arguments wait on a stack.
    ///
    /// # Errors
    /// Propagates a refusal from the formatting sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — variables, nullary and mixed nested applications are
    ///   compared with exact inspection text; a refusing sink pins the error
    ///   boundary. Reordering arguments, adding nullary parentheses or
    ///   discarding a write failure changes the observer.
    /// - witness: `generic::tests::desc_inspection_renders_a_circuit_rule_and_its_telescope`
    /// - witness: `wellformed::tests::a_boundary_mismatched_circuit_rule_is_declined`
    /// - witness: `rule::tests::inspection_reads_mixed_applications_in_argument_order`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let mut rendered: Vec<String> = Vec::new();
        for head in self.0.heads() {
            let (name, arity) = match *head {
                | TermHead::Var(ref name) => (name, 0_usize),
                | TermHead::Ctor(ref name, arity) | TermHead::Op(ref name, arity) => {
                    (name, usize::from(arity))
                },
            };
            if arity == 0 {
                rendered.push(name.to_string());
                continue;
            }
            let mut args: Vec<String> = Vec::with_capacity(arity);
            for _ in 0 .. arity {
                args.push(rendered.pop().unwrap_or_default());
            }
            rendered.push(format!("{name}({})", args.join(", ")));
        }
        f.write_str(&rendered.pop().unwrap_or_default())
    }
}

/// A borrowed node of a [`FreeTerm`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TermNode<'term>(TreeRef<'term, TermHead>);

impl<'term> TermNode<'term>
{
    /// The node's head and arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(self) -> TermView<'term>
    {
        match *self.0.head() {
            | TermHead::Var(ref name) => TermView::Var(name),
            | TermHead::Ctor(ref name, _) => TermView::Ctor {
                name,
                args: TermArgs(self.0.children()),
            },
            | TermHead::Op(ref name, _) => TermView::Op {
                name,
                args: TermArgs(self.0.children()),
            },
        }
    }

    /// The subterm's variable leaves, left to right with repeats.
    ///
    /// # Specification
    /// - ensures: one item per variable leaf, in left-to-right order: pre-order
    ///   visits leaves left to right.
    /// - panics: none.
    /// - executable: none — the backend cannot instrument this opaque iterator
    ///   return type, and observing its sequence consumes the returned value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ground, distinct-leaf and repeated-leaf terms have
    ///   exact variable sequences; reversed siblings, dropped leaves and
    ///   deduplication change those sequences.
    /// - witness: `rule::tests::free_variables_are_collected_in_order_with_repeats`
    #[inline]
    pub fn vars(self) -> impl Iterator<Item = &'term Name>
    {
        self.0.preorder().filter_map(|head| match *head {
            | TermHead::Var(ref name) => Some(name),
            | TermHead::Ctor(..) | TermHead::Op(..) => None,
        })
    }

    /// An owned copy of the subterm.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_term(self) -> FreeTerm
    {
        FreeTerm(self.0.to_tree())
    }
}

/// The head and arguments of one free-term node.
#[derive(Clone, Debug)]
pub enum TermView<'term>
{
    /// A pattern variable `x`.
    Var(&'term Name),
    /// A constructor application.
    Ctor
    {
        /// The constructor's name.
        name: &'term Name,
        /// The arguments, left to right.
        args: TermArgs<'term>,
    },
    /// An operation application.
    Op
    {
        /// The operation's name.
        name: &'term Name,
        /// The arguments, left to right.
        args: TermArgs<'term>,
    },
}

/// The arguments of a free-term application, left to right.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct TermArgs<'term>(Children<'term, TermHead>);

impl<'term> Iterator for TermArgs<'term>
{
    type Item = TermNode<'term>;

    /// The next argument.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.0.next().map(TermNode)
    }

    /// The exact number of remaining arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for TermArgs<'_>
{
}

/// The variance role a rule-face pattern variable occupies.
///
/// The derived variance is the constant [`Variance::Producer`] until
/// consumer-argument operations exist, where a variable would first occupy a
/// [`Variance::Consumer`] position. The variant exists now so rules in
/// `codata` blocks departing from the constant are an update, not a
/// migration.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum Variance
{
    /// A producer-side (introduction) position, the current constant.
    #[default]
    Producer,
    /// A consumer-side (observation) position, first reached by rules in
    /// `codata` blocks once consumer-argument operations exist.
    Consumer,
}

/// Derived metadata for one rule-face pattern variable: its name, variance
/// role and linearity.
///
/// The metadata is derived from the faces ([`derive_cell_var_meta`]); an
/// attribute Σ that tries to declare it is declined by [`check_desc`].
///
/// [`derive_cell_var_meta`]: crate::derive_cell_var_meta
/// [`check_desc`]: crate::check_desc
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RuleVarMeta
{
    /// The pattern variable's name.
    pub var: Name,
    /// The variance role.
    pub variance: Variance,
    /// Whether the variable occurs exactly once on the left-hand side.
    pub linear: RuleVariableLinearity,
}

impl RuleVarMeta
{
    /// Metadata for a variable with an explicit variance and linearity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<N>(
        var: N,
        variance: Variance,
        linear: RuleVariableLinearity,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self {
            var: var.into(),
            variance,
            linear,
        }
    }
}

/// A 2-cell face `lhs ==> rhs`: the surface-to-cell intermediary a cell store
/// elaborates through.
///
/// The two [`FreeTerm`]s are open terms in `D⋆(V)`; `vars` is the derived
/// [`RuleVarMeta`] per left-hand-side pattern variable; `provenance` is the
/// surface span the rule was read from.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RuleFace
{
    /// The rewrite's left-hand side.
    pub lhs: FreeTerm,
    /// The rewrite's right-hand side.
    pub rhs: FreeTerm,
    /// Derived per-variable metadata.
    pub vars: Box<[RuleVarMeta]>,
    /// The surface span this face was read from.
    pub provenance: SurfaceSpan,
}

impl RuleFace
{
    /// A face over two terms with derived variable metadata and a provenance
    /// span.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<V>(
        lhs: FreeTerm,
        rhs: FreeTerm,
        vars: V,
        provenance: SurfaceSpan,
    ) -> Self
    where
        V: Into<Box<[RuleVarMeta]>>,
    {
        Self {
            lhs,
            rhs,
            vars: vars.into(),
            provenance,
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use super::*;

    #[test]
    fn free_variables_are_collected_in_order_with_repeats()
    {
        // `f(x, g(x))` has `x` twice.
        let term = FreeTerm::op("f", [
            FreeTerm::var("x"),
            FreeTerm::ctor("g", [FreeTerm::var("x")]),
        ]);
        assert_eq!(
            vec![Name::from("x"), Name::from("x")],
            term.collect_vars(),
            "each occurrence is counted"
        );
        let ordered = FreeTerm::op("f", [FreeTerm::var("a"), FreeTerm::var("b")]);
        assert_eq!(
            vec![Name::from("a"), Name::from("b")],
            ordered.collect_vars(),
            "the leaves are read left to right"
        );
        let ground = FreeTerm::ctor("Zero", []);
        assert!(
            ground.collect_vars().is_empty(),
            "a ground term has no variables"
        );
    }

    #[test]
    fn variable_replacement_preserves_applications_and_inserts_images_once()
    {
        let image = FreeTerm::ctor("Image", [FreeTerm::var("x")]);
        let source = FreeTerm::op("f", [
            FreeTerm::var("x"),
            FreeTerm::ctor("g", [FreeTerm::var("y")]),
            FreeTerm::ctor("Zero", []),
        ]);
        let mut visited = Vec::new();
        let result = source.replace_vars(|name| {
            visited.push(name.clone());
            if name.as_ref() == "x" {
                Maybe::Present(image.to_node())
            }
            else {
                Maybe::Absent(leaf_image::Absent::Kept)
            }
        });
        visited.sort();
        assert_eq!(visited, [Name::from("x"), Name::from("y")]);
        assert_eq!(
            result,
            FreeTerm::op("f", [
                image.clone(),
                FreeTerm::ctor("g", [FreeTerm::var("y")]),
                FreeTerm::ctor("Zero", [])
            ])
        );
        assert_eq!(
            FreeTerm::var("x").replace_vars(|_| Maybe::Present(image.to_node())),
            image
        );
        assert_eq!(
            FreeTerm::var("y").replace_vars(|_| Maybe::Absent(leaf_image::Absent::Kept)),
            FreeTerm::var("y")
        );
    }

    /// A formatting sink which refuses every write.
    struct RefusingSink;

    impl fmt::Write for RefusingSink
    {
        /// Refuses the supplied text.
        ///
        /// # Specification
        /// - fails: always returns the formatting error.
        /// - panics: none.
        ///
        /// # Errors
        /// Always refuses the write.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — rendering a nonempty application reaches the
        ///   refusing sink; the exact error separates acceptance from refusal.
        /// - witness: `rule::tests::inspection_reads_mixed_applications_in_argument_order`
        #[spec(ensures: |result| result.is_err())]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> fmt::Result
        {
            Err(fmt::Error)
        }
    }

    #[test]
    fn inspection_reads_mixed_applications_in_argument_order()
    {
        let mixed = FreeTerm::op("f", [
            FreeTerm::var("x"),
            FreeTerm::ctor("G", [FreeTerm::ctor("Z", [])]),
            FreeTerm::op("K", []),
        ]);
        assert_eq!(mixed.to_string(), "f(x, G(Z), K)");
        assert_eq!(
            mixed
                .applied_symbols()
                .map(Name::as_ref)
                .collect::<Vec<_>>(),
            ["f", "G", "Z", "K"]
        );
        for term in [
            FreeTerm::var("x"),
            FreeTerm::ctor("x", []),
            FreeTerm::op("x", []),
        ] {
            assert_eq!(term.to_string(), "x");
        }
        assert_eq!(
            FreeTerm::var("x").applied_symbols().collect::<Vec<_>>(),
            Vec::<&Name>::new()
        );
        assert_eq!(
            fmt::write(&mut RefusingSink, format_args!("{mixed}")),
            Err(fmt::Error)
        );
    }
}
