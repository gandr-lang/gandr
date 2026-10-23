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
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::AbstractionDepth;
use crate::boundary::ConditionStatus;
use crate::boundary::InstantiationStatus;
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
    /// A results tuple over its component count.
    Results(ArgumentCount),
    /// A metavariable instantiated at its argument count of terms.
    Inst(Name, ArgumentCount),
    /// An atom abstracted over its one body, `bind a . t`.
    Abs(Name),
    /// An atom named inside an abstraction that binds it, at a port of its
    /// atom sort.
    Atom(Name),
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
            Self::Var(_) | Self::Atom(_) => ArgumentCount::from(0_usize),
            Self::Abs(_) => ArgumentCount::from(1_usize),
            Self::Ctor(_, arity)
            | Self::Op(_, arity)
            | Self::Results(arity)
            | Self::Inst(_, arity) => arity,
        }
    }
}

/// A term in the free monad `D⋆(V)` over the description functor with
/// variables `V`: a variable, a constructor application, an operation
/// application, or a metavariable's instantiation.
///
/// At the root of a rule's right-hand side, a term may also be the results
/// tuple a many-out operation's rule returns ([`FreeTerm::results`]).
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

    /// A results tuple `(t₀, …, tₙ)`: one term per output port of the
    /// operation the rule's left-hand side applies, in port order.
    ///
    /// A many-out operation `(m, n) --> (q, r)` returns its results together,
    /// so its rule's right-hand side is a tuple of them, the product layer of
    /// its arity. The tuple stands only at the root of a right-hand side, and
    /// [`check_desc`](crate::check_desc) refuses it anywhere else; whether its
    /// width is the operation's output count is the cell elaboration's
    /// question, which has the operation's arity in hand.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn results<A>(components: A) -> Self
    where
        A: IntoIterator<Item = Self>,
    {
        let components: Vec<Tree<TermHead>> = components.into_iter().map(|arg| arg.0).collect();
        let arity = ArgumentCount::from(components.len());
        Self(Tree::node(TermHead::Results(arity), components))
    }

    /// The instantiation `t(u₀, …, uₙ)` of the metavariable `t` a binding
    /// port binds on a rule's left-hand side: one argument per variable the
    /// port binds, each standing for that variable in the term `t` names.
    ///
    /// The instantiation is the application of a metavariable, a hole that
    /// takes terms, never an operation of the signature: the first-order
    /// translation reads it as a substitution of the arguments for the bound
    /// variables.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn inst<N, A>(
        name: N,
        args: A,
    ) -> Self
    where
        N: Into<Name>,
        A: IntoIterator<Item = Self>,
    {
        let args: Vec<Tree<TermHead>> = args.into_iter().map(|arg| arg.0).collect();
        let arity = ArgumentCount::from(args.len());
        Self(Tree::node(TermHead::Inst(name.into(), arity), args))
    }

    /// The abstraction `bind a . t` of the atom `a` over `body`, at a port
    /// written `bind (a : N) . T`: the atom is bound in `body`, and two
    /// abstractions that differ by renaming it to an atom fresh for the body
    /// are one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn abs<N>(
        atom: N,
        body: Self,
    ) -> Self
    where
        N: Into<Name>,
    {
        Self(Tree::node(TermHead::Abs(atom.into()), alloc::vec![body.0]))
    }

    /// The atom `a` named inside an abstraction `bind a . t` that binds it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn atom<N>(name: N) -> Self
    where
        N: Into<Name>,
    {
        Self(Tree::leaf(TermHead::Atom(name.into())))
    }

    /// The canonical name of the atom an abstraction `depth` abstractions deep
    /// abstracts: `a0` at the outermost, `a1` under it, and so on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn canonical_atom(depth: AbstractionDepth) -> Name
    {
        Name::from(format!("a{}", usize::from(depth)))
    }

    /// The term with every abstraction's atom re-minted canonically: an
    /// abstraction under `n` others abstracts the canonical atom of depth `n`
    /// ([`Self::canonical_atom`]), and an atom named inside it is renamed
    /// with it. Two terms that differ only in the atoms their abstractions
    /// name re-mint to one term.
    ///
    /// # Specification
    /// - ensures: the term's shape, heads and variables kept, each
    ///   abstraction's atom replaced by the canonical atom of its depth among
    ///   the abstractions above it, and each atom named inside an abstraction
    ///   of it replaced by the innermost such abstraction's canonical atom; an
    ///   atom no abstraction above it binds is kept. The executable predicate
    ///   checks the root, whose head is kept unless it is an abstraction or an
    ///   atom.
    /// - panics: none.
    /// - intension: one worklist pass, each node read once and rebuilt from its
    ///   rebuilt arguments; the abstractions in scope form a tree of links,
    ///   each node naming its innermost, so an atom looks its binder up along
    ///   the abstractions above it alone.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two terms whose nested abstractions name different
    ///   atoms re-mint to one term, an abstraction beside another, rather than
    ///   under it, takes the same level, and an atom named under two
    ///   abstractions takes its own binder's level, not the innermost's.
    /// - witness: `rule::tests::atoms_are_reminted_by_their_depth`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref minted| matches!(*self.0.to_ref().head(), TermHead::Abs(_) | TermHead::Atom(_))
        || minted.0.to_ref().head() == self.0.to_ref().head())]
    pub fn canonical_atoms(&self) -> Self
    {
        /// A step of the rebuild: a node to read at a depth under the
        /// innermost abstraction in scope, or a head to apply to the
        /// arguments rebuilt last.
        enum Mint<'term>
        {
            /// Read a node `usize` abstractions deep.
            Read(TermNode<'term>, usize, Option<usize>),
            /// Rebuild the application of this node's head to its rebuilt
            /// arguments, `usize` abstractions deep.
            Build(TermNode<'term>, usize, Option<usize>),
        }
        // Each abstraction read: its atom, its depth and the link to the
        // abstraction enclosing it.
        let mut scopes: Vec<(&Name, usize, Option<usize>)> = Vec::new();
        let mut pending = alloc::vec![Mint::Read(self.to_node(), 0, None)];
        let mut built: Vec<Self> = Vec::new();
        while let Some(step) = pending.pop() {
            match step {
                Mint::Read(node, depth, scope) => {
                    pending.push(Mint::Build(node, depth, scope));
                    let (args, below, inner) = match node.view() {
                        TermView::Var(_) | TermView::Atom(_) => continue,
                        TermView::Abs { atom, args } => {
                            scopes.push((atom, depth, scope));
                            (
                                args,
                                depth.saturating_add(1),
                                Some(scopes.len().saturating_sub(1)),
                            )
                        },
                        TermView::Ctor { args, .. }
                        | TermView::Op { args, .. }
                        | TermView::Results { args }
                        | TermView::Inst { args, .. } => (args, depth, scope),
                    };
                    let mark = pending.len();
                    pending.extend(args.map(|arg| Mint::Read(arg, below, inner)));
                    if let Some(children) = pending.get_mut(mark ..) {
                        children.reverse();
                    }
                },
                Mint::Build(node, depth, scope) => {
                    let count = match node.view() {
                        TermView::Var(_) | TermView::Atom(_) => 0,
                        TermView::Ctor { args, .. }
                        | TermView::Op { args, .. }
                        | TermView::Results { args }
                        | TermView::Inst { args, .. }
                        | TermView::Abs { args, .. } => args.len(),
                    };
                    let args = built.split_off(built.len().saturating_sub(count));
                    built.push(match node.view() {
                        TermView::Var(name) => Self::var(name.clone()),
                        TermView::Atom(name) => {
                            let mut link = scope;
                            let mut minted = None;
                            while let Some(&(atom, level, outer)) =
                                link.and_then(|at| scopes.get(at))
                            {
                                if atom == name {
                                    minted =
                                        Some(Self::canonical_atom(AbstractionDepth::from(level)));
                                    break;
                                }
                                link = outer;
                            }
                            Self::atom(minted.unwrap_or_else(|| name.clone()))
                        },
                        TermView::Ctor { name, .. } => Self::ctor(name.clone(), args),
                        TermView::Op { name, .. } => Self::op(name.clone(), args),
                        TermView::Results { .. } => Self::results(args),
                        TermView::Inst { name, .. } => Self::inst(name.clone(), args),
                        TermView::Abs { .. } => Self::abs(
                            Self::canonical_atom(AbstractionDepth::from(depth)),
                            args.into_iter().next().unwrap_or_else(|| Self::results([])),
                        ),
                    });
                },
            }
        }
        built.pop().unwrap_or_else(|| self.clone())
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
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the term's variables once, as the check does"
        )
    )]
    #[spec(ensures: |ref vars| vars.iter().eq(self.to_node().vars()))]
    pub fn collect_vars(&self) -> Vec<Name>
    {
        self.to_node().vars().cloned().collect()
    }

    /// The constructor and operation names the term applies, in pre-order.
    ///
    /// # Specification
    /// - ensures: each applied constructor or operation is yielded once, root
    ///   first and children left to right; variables, instantiations and
    ///   results tuples contribute no name.
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
            TermHead::Var(_)
            | TermHead::Results(_)
            | TermHead::Inst(..)
            | TermHead::Abs(_)
            | TermHead::Atom(_) => None,
            TermHead::Ctor(ref name, _) | TermHead::Op(ref name, _) => Some(name),
        })
    }

    /// Whether the term instantiates a metavariable anywhere: a rule whose
    /// right-hand side does is a second-order rule.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn instantiates(&self) -> InstantiationStatus
    {
        InstantiationStatus::from(
            self.0
                .to_ref()
                .preorder()
                .any(|head| matches!(*head, TermHead::Inst(..))),
        )
    }

    /// The width of each results tuple in the term, in pre-order: the root's
    /// first when the root is one.
    ///
    /// # Specification
    /// - ensures: one item per results-tuple node, root first and children left
    ///   to right.
    /// - panics: none.
    /// - executable: none — the backend cannot instrument this opaque iterator
    ///   return type.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a term with no tuple, a tuple at its root and a tuple
    ///   nested under an application are observed through the misplaced-tuple
    ///   diagnostics they earn; skipping the root or a nested tuple changes
    ///   them.
    /// - witness: `wellformed::tests::a_results_tuple_stands_only_at_a_right_hand_root`
    #[inline]
    pub(crate) fn results_widths(&self) -> impl Iterator<Item = ArgumentCount>
    {
        self.0.to_ref().preorder().filter_map(|head| match *head {
            TermHead::Results(width) => Some(width),
            TermHead::Var(_)
            | TermHead::Ctor(..)
            | TermHead::Op(..)
            | TermHead::Inst(..)
            | TermHead::Abs(_)
            | TermHead::Atom(_) => None,
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
            TermHead::Var(ref name) => image(name).map(|replacement| replacement.0),
            TermHead::Ctor(..)
            | TermHead::Op(..)
            | TermHead::Results(_)
            | TermHead::Inst(..)
            | TermHead::Abs(_)
            | TermHead::Atom(_) => Maybe::Absent(leaf_image::Absent::Kept),
        }))
    }
}

impl fmt::Display for FreeTerm
{
    /// Writes the term in the inspection notation: a variable or a nullary
    /// application as its name, an application as `name(arg, …)`, a results
    /// tuple as `(arg, …)`.
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
        let mut args: Vec<String> = Vec::new();
        for head in self.0.heads() {
            let (name, arity) = match *head {
                TermHead::Var(ref name) | TermHead::Atom(ref name) => (Some(name), 0_usize),
                TermHead::Abs(ref atom) => {
                    let body = rendered.pop().unwrap_or_default();
                    rendered.push(format!("bind {atom} . {body}"));
                    continue;
                },
                TermHead::Ctor(ref name, arity)
                | TermHead::Op(ref name, arity)
                | TermHead::Inst(ref name, arity) => (Some(name), usize::from(arity)),
                TermHead::Results(arity) => (None, usize::from(arity)),
            };
            if let (Some(name), 0) = (name, arity) {
                rendered.push(name.to_string());
                continue;
            }
            args.clear();
            for _ in 0 .. arity {
                args.push(rendered.pop().unwrap_or_default());
            }
            let head = name.map_or_else(String::new, alloc::string::ToString::to_string);
            rendered.push(format!("{head}({})", args.join(", ")));
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
            TermHead::Var(ref name) => TermView::Var(name),
            TermHead::Ctor(ref name, _) => TermView::Ctor {
                name,
                args: TermArgs(self.0.children()),
            },
            TermHead::Op(ref name, _) => TermView::Op {
                name,
                args: TermArgs(self.0.children()),
            },
            TermHead::Results(_) => TermView::Results {
                args: TermArgs(self.0.children()),
            },
            TermHead::Inst(ref name, _) => TermView::Inst {
                name,
                args: TermArgs(self.0.children()),
            },
            TermHead::Abs(ref atom) => TermView::Abs {
                atom,
                args: TermArgs(self.0.children()),
            },
            TermHead::Atom(ref name) => TermView::Atom(name),
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
            TermHead::Var(ref name) => Some(name),
            TermHead::Ctor(..)
            | TermHead::Op(..)
            | TermHead::Results(_)
            | TermHead::Inst(..)
            | TermHead::Abs(_)
            | TermHead::Atom(_) => None,
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
    /// A results tuple, the root of a many-out operation rule's right-hand
    /// side.
    Results
    {
        /// The components, in output-port order.
        args: TermArgs<'term>,
    },
    /// A metavariable's instantiation `t(u₀, …, uₙ)`: the variable a binding
    /// port binds on the left-hand side, applied to one term per variable the
    /// port binds.
    Inst
    {
        /// The metavariable's name.
        name: &'term Name,
        /// The terms standing for the variables it binds, in binder order.
        args: TermArgs<'term>,
    },
    /// An atom's abstraction `bind a . t` at a port written
    /// `bind (a : N) . T`: the atom is bound in its one argument, the body.
    Abs
    {
        /// The abstracted atom's name.
        atom: &'term Name,
        /// The body, the one argument.
        args: TermArgs<'term>,
    },
    /// The atom `a` named inside an abstraction `bind a . t` that binds it,
    /// at a port of its atom sort.
    Atom(&'term Name),
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

/// A freshness condition `a # q` on a rule.
///
/// The atom `a`, which an abstraction of the rule names, stands outside the
/// support of the instance of the metavariable `q` (Fernández and Gabbay,
/// _Nominal rewriting_, I&C 2007, § 2).
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the atom and the metavariable as the rule writes them.
/// - executable: none — a data carrier with no invocation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — as [`crate::check_desc`], which refuses a condition
///   naming no abstraction's atom or no metavariable.
/// - witness: `wellformed::tests::a_metavariable_crossing_an_abstraction_names_its_atom_fresh`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Freshness
{
    /// The atom.
    pub atom: Name,
    /// The metavariable the atom is fresh for.
    pub term: Name,
}

impl Freshness
{
    /// The condition `atom # term`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<A, T>(
        atom: A,
        term: T,
    ) -> Self
    where
        A: Into<Name>,
        T: Into<Name>,
    {
        Self {
            atom: atom.into(),
            term: term.into(),
        }
    }
}

/// A 2-cell face `lhs ==> rhs`: the surface-to-cell intermediary a cell store
/// elaborates through.
///
/// The two [`FreeTerm`]s are open terms in `D⋆(V)`; `vars` is the derived
/// [`RuleVarMeta`] per left-hand-side pattern variable; `fresh` the rule's
/// freshness conditions, in written order; `provenance` is the surface span
/// the rule was read from.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct RuleFace
{
    /// The rewrite's left-hand side.
    pub lhs: FreeTerm,
    /// The rewrite's right-hand side.
    pub rhs: FreeTerm,
    /// Derived per-variable metadata.
    pub vars: Box<[RuleVarMeta]>,
    /// The freshness conditions the rule states.
    pub fresh: Box<[Freshness]>,
    /// The surface span this face was read from.
    pub provenance: SurfaceSpan,
}

impl RuleFace
{
    /// A face over two terms with derived variable metadata and a provenance
    /// span, stating no freshness condition.
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
            fresh: Box::default(),
            provenance,
        }
    }

    /// The face stating `fresh` as its freshness conditions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_fresh<F>(
        self,
        fresh: F,
    ) -> Self
    where
        F: Into<Box<[Freshness]>>,
    {
        Self {
            fresh: fresh.into(),
            ..self
        }
    }

    /// The first variable some occurrence of which stands under other
    /// abstractions than its first occurrence on the left side does: on
    /// either side for [`Crossing::Moved`], on the left side alone for
    /// [`Crossing::Split`].
    ///
    /// # Specification
    /// - ensures: the first variable, in pre-order over the left side and then,
    ///   for [`Crossing::Moved`], the right, an instantiated one included,
    ///   whose list of enclosing abstractions' atoms, outermost first, differs
    ///   from the list at its first occurrence on the left side, compared by
    ///   written name and order; [`None`] when every occurrence read agrees.
    /// - panics: none.
    /// - executable: none — the answer is the comparison of the sides' walks,
    ///   which a predicate would walk again.
    /// - intension: one worklist pass over each side read; the abstractions in
    ///   scope form a tree of links, read out at a variable only.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a variable under the same abstraction on both sides
    ///   crosses nothing; one moved under an abstraction and one under two
    ///   abstractions swapped are moved and not split; one standing under an
    ///   abstraction at one left-side occurrence and outside it at another is
    ///   split.
    /// - witness: `rule::tests::a_variable_moved_across_an_abstraction_and_one_split_by_it`
    #[inline]
    #[must_use]
    pub fn crossing(
        &self,
        crossing: Crossing,
    ) -> Option<&Name>
    {
        let mut first: BTreeMap<&Name, Vec<&Name>> = BTreeMap::new();
        let sides: &[(&FreeTerm, bool)] = match crossing {
            Crossing::Moved => &[(&self.lhs, true), (&self.rhs, false)],
            Crossing::Split => &[(&self.lhs, true)],
        };
        let mut scopes: Vec<(&Name, Option<usize>)> = Vec::new();
        let mut pending: Vec<(TermNode<'_>, Option<usize>)> = Vec::new();
        for &(side, left) in sides {
            scopes.clear();
            pending.push((side.to_node(), None));
            while let Some((node, scope)) = pending.pop() {
                let (variable, args) = match node.view() {
                    TermView::Var(name) => (Some(name), None),
                    TermView::Inst { name, args } => (Some(name), Some(args)),
                    TermView::Abs { atom, args } => {
                        scopes.push((atom, scope));
                        let inner = Some(scopes.len().saturating_sub(1));
                        pending.extend(args.map(|body| (body, inner)));
                        continue;
                    },
                    TermView::Op { args, .. }
                    | TermView::Ctor { args, .. }
                    | TermView::Results { args } => (None, Some(args)),
                    TermView::Atom(_) => (None, None),
                };
                if let Some(variable) = variable {
                    let mut enclosing = Vec::new();
                    let mut link = scope;
                    while let Some(&(atom, outer)) = link.and_then(|at| scopes.get(at)) {
                        enclosing.push(atom);
                        link = outer;
                    }
                    enclosing.reverse();
                    match first.get(variable) {
                        Some(known) if *known != enclosing => return Some(variable),
                        None if left => {
                            let _new = first.insert(variable, enclosing);
                        },
                        Some(_) | None => {},
                    }
                }
                if let Some(args) = args {
                    pending.extend(args.map(|arg| (arg, scope)));
                }
            }
        }
        None
    }

    /// Whether the rule states a freshness condition or moves a variable
    /// across an abstraction: where a port takes an atom, it then fires only
    /// where its instance names no atom it may not, and renumbers the atoms
    /// a moved instance names.
    ///
    /// # Specification
    /// - ensures: positive exactly when `fresh` is not empty or
    ///   [`Self::crossing`] at [`Crossing::Moved`] names a variable.
    /// - panics: none.
    /// - executable: none — the body is the predicate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::crossing`]: scope extrusion is
    ///   conditioned, a law under one abstraction on both sides is not.
    /// - witness: `rule::tests::a_variable_moved_across_an_abstraction_and_one_split_by_it`
    #[inline]
    #[must_use]
    pub fn conditioned(&self) -> ConditionStatus
    {
        ConditionStatus::from(!self.fresh.is_empty() || self.crossing(Crossing::Moved).is_some())
    }
}

/// Which occurrences of a variable [`RuleFace::crossing`] compares with its
/// first on the left side.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Crossing
{
    /// Every occurrence, on either side: a variable the rule moves.
    Moved,
    /// The left side's alone: a variable whose instances a match compares
    /// under different abstractions.
    Split,
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use super::*;

    #[test]
    fn a_variable_moved_across_an_abstraction_and_one_split_by_it()
    {
        let span = SurfaceSpan::new(0_usize.into(), 1_usize.into());
        let restricted = |body: FreeTerm| FreeTerm::op("nu", [FreeTerm::abs("a", body)]);
        let par = |p: FreeTerm, q: FreeTerm| FreeTerm::op("par", [p, q]);
        // `par(nu(bind a . p), q) ==> nu(bind a . par(p, q)) where a # q`: `q`
        // moves under `a`, `p` stays under it.
        let scope = RuleFace::new(
            par(restricted(FreeTerm::var("p")), FreeTerm::var("q")),
            restricted(par(FreeTerm::var("p"), FreeTerm::var("q"))),
            Vec::new(),
            span,
        )
        .with_fresh(vec![Freshness::new("a", "q")]);
        assert_eq!(scope.crossing(Crossing::Moved), Some(&Name::from("q")));
        assert_eq!(scope.crossing(Crossing::Split), None);
        assert!(bool::from(scope.conditioned()));
        // `nu(bind a . f(p)) ==> nu(bind a . g(p))` keeps `p` where it was.
        let kept = RuleFace::new(
            restricted(FreeTerm::op("f", [FreeTerm::var("p")])),
            restricted(FreeTerm::op("g", [FreeTerm::var("p")])),
            Vec::new(),
            span,
        );
        assert_eq!(kept.crossing(Crossing::Moved), None);
        assert!(!bool::from(kept.conditioned()));
        // `par(nu(bind a . p), p) ==> p` matches `p` under `a` and beside it.
        let split = RuleFace::new(
            par(restricted(FreeTerm::var("p")), FreeTerm::var("p")),
            FreeTerm::var("p"),
            Vec::new(),
            span,
        );
        assert_eq!(split.crossing(Crossing::Split), Some(&Name::from("p")));
        // `nu2(bind a . bind b . p) ==> nu2(bind b . bind a . p)` swaps the
        // two abstractions over `p`.
        let nu2 = |outer: &str, inner: &str| {
            FreeTerm::op("nu2", [FreeTerm::abs(
                outer,
                FreeTerm::abs(inner, FreeTerm::var("p")),
            )])
        };
        let swapped = RuleFace::new(nu2("a", "b"), nu2("b", "a"), Vec::new(), span);
        assert_eq!(swapped.crossing(Crossing::Moved), Some(&Name::from("p")));
        assert_eq!(swapped.crossing(Crossing::Split), None);
    }

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
    fn atoms_are_reminted_by_their_depth()
    {
        // `par(bind x . bind y . p, bind z . q)` and the same term naming
        // other atoms re-mint to one term: the outer abstractions take `a0`,
        // the inner one `a1`, and the sibling `a0` again.
        let written = |outer: &str, inner: &str, beside: &str| {
            FreeTerm::op("par", [
                FreeTerm::abs(outer, FreeTerm::abs(inner, FreeTerm::var("p"))),
                FreeTerm::abs(beside, FreeTerm::var("q")),
            ])
        };
        let minted = written("x", "y", "z").canonical_atoms();
        assert_eq!(minted, written("a0", "a1", "a0"), "atoms by depth");
        assert_eq!(
            minted,
            written("b", "c", "b").canonical_atoms(),
            "renamed atoms re-mint alike"
        );
        assert_ne!(
            written("x", "y", "z"),
            written("b", "c", "b"),
            "as written the two differ"
        );
        // An occurrence re-mints with the abstraction that binds it: the
        // innermost of its name, and a name no abstraction binds is kept.
        let named = |outer: &str, inner: &str, first: &str, second: &str| {
            FreeTerm::abs(
                outer,
                FreeTerm::abs(
                    inner,
                    FreeTerm::op("out", [FreeTerm::atom(first), FreeTerm::atom(second)]),
                ),
            )
        };
        assert_eq!(
            named("x", "y", "x", "y").canonical_atoms(),
            named("a0", "a1", "a0", "a1"),
            "each occurrence takes its binder's depth"
        );
        assert_eq!(
            named("x", "x", "x", "z").canonical_atoms(),
            named("a0", "a1", "a1", "z"),
            "the inner abstraction shadows the outer, and a free atom is kept"
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
