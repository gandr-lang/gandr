//! Operations and rewrite faces read from declaration members.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_levitation::BridgeArity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::SurfaceSpan;
use gandr_theory_levitation::derive_cell_var_meta;
use quenchant_shape::shape::Maybe;

use super::ArgumentCount;
use super::DescriptionDiagnostic;
use super::DescriptionFault;
use super::Reader;
use super::Run;
use super::Spelling;
use super::written::RuleDirection;
use super::written::RuleOrientation;
use super::written::WrittenFace;
use super::written::WrittenNode;
use super::written::WrittenOperation;
use super::written::WrittenPort;
use super::written::WrittenSort;
use super::written::WrittenTerm;
use super::written::head;
use super::written::member_name;
use super::written::port_name;
use crate::form::Piece;
use crate::form::Placed;

impl Reader<'_, '_>
{
    /// Read an operation's named input and output ports, and where each is
    /// written.
    ///
    /// # Specification
    /// - ensures: the bridge has one monomial per output, each using all
    ///   inputs; the written operation holds the name tile and one port per
    ///   port of the bridge, in order, a lone result sort an unnamed port.
    /// - fails: malformed port syntax is located at its member.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` for missing names, classifiers or delimiters.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-input, two-output declaration distinguishes
    ///   lost ports and wrong bridge maps.
    /// - witness: `description::tests::operations_and_rules_preserve_their_boundaries`
    #[spec(ensures: |result| result.as_ref().map_or(true, |read| read.0.arity.factors.len() == read.0.arity.outputs.len()
        && read.1.inputs.len() == read.0.arity.inputs.len() && read.1.outputs.len() == read.0.arity.outputs.len()))]
    pub(super) fn operation(
        &self,
        run: &mut Run<'_>,
    ) -> Result<(OperDesc, WrittenOperation), DescriptionDiagnostic>
    {
        let named = run.take()?;
        if !run.eat(Spelling("(")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let (inputs, written_inputs) = self.ports(run)?;
        let (outputs, written_outputs) = if run.eat(Spelling("->")).0 {
            if run.eat(Spelling("(")).0 {
                self.ports(run)?
            }
            else {
                let result = run.take()?;
                (vec![SortRef::new("result", self.text(result).0)], vec![
                    WrittenPort {
                        named: Maybe::Absent(port_name::Absent::Unnamed),
                        binders: Vec::new(),
                        sort: WrittenSort {
                            span: result.span,
                            indices: Vec::new(),
                        },
                    },
                ])
            }
        }
        else {
            (Vec::new(), Vec::new())
        };
        let input_count =
            u32::try_from(inputs.len()).map_err(|_error| run.fault(DescriptionFault::Malformed))?;
        let output_count = u32::try_from(outputs.len())
            .map_err(|_error| run.fault(DescriptionFault::Malformed))?;
        let factors = vec![input_count; outputs.len()];
        let source: Vec<_> = (0 .. output_count)
            .flat_map(|_output| 0 .. input_count)
            .collect();
        let dest: Vec<_> = (0 .. output_count).collect();
        let attrs = self.attrs(run)?;
        run.end()?;
        Ok((
            OperDesc::new(
                self.text(named).0,
                BridgeArity::new(inputs, factors, source, dest, outputs),
                attrs,
            ),
            WrittenOperation {
                named: Maybe::Present(named.span),
                inputs: written_inputs,
                outputs: written_outputs,
                formers: Vec::new(),
            },
        ))
    }

    /// Read named typed ports through their closing parenthesis, and where
    /// each is written.
    ///
    /// # Specification
    /// - ensures: preserves port names, sort spellings and source order; one
    ///   written port per port, its name tile and its sort's bytes.
    /// - fails: an incomplete binder is located rather than omitted.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` for an incomplete binder list.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric input and output names distinguish
    ///   reversal and truncation.
    /// - witness: `description::tests::operations_and_rules_preserve_their_boundaries`
    #[spec(captures: before = run.remaining().len(), ensures: |result| result.as_ref().map_or(true, |read| read.0.len() <= before && read.1.len() == read.0.len()))]
    pub(super) fn ports(
        &self,
        run: &mut Run<'_>,
    ) -> Result<(Vec<SortRef>, Vec<WrittenPort>), DescriptionDiagnostic>
    {
        let mut ports = Vec::new();
        let mut written = Vec::new();
        while !run.eat(Spelling(")")).0 {
            let name = run.take()?;
            if !run.eat(Spelling(":")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
            let sort = run.take()?;
            ports.push(SortRef::new(self.text(name).0, self.text(sort).0));
            written.push(WrittenPort {
                named: Maybe::Present(name.span),
                binders: Vec::new(),
                sort: WrittenSort {
                    span: sort.span,
                    indices: Vec::new(),
                },
            });
            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        Ok((ports, written))
    }

    /// Read a written rewrite face, derive its variable metadata, and keep
    /// where each of its sides' nodes is written.
    ///
    /// # Specification
    /// - ensures: the face keeps both terms and the member's exact byte span;
    ///   the written face is anonymous and holds each side's nodes. `<=>`
    ///   states [`RuleOrientation::Unpinned`]; `==>` states
    ///   [`RuleOrientation::Pinned`] left to right.
    /// - fails: only `==>` and `<=>` are written face arrows; `~>` is the
    ///   retired spelling; unsupported terms are located.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` or `RetiredRuleArrow` for unreadable faces.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric rule endpoints distinguish reversal, fresh
    ///   variables and lost nested heads; the equation and the pinned arrow
    ///   state different orientations.
    /// - witness: `description::tests::operations_and_rules_preserve_their_boundaries`
    /// - witness: `description::tests::an_equation_states_no_direction`
    #[spec(ensures: |result| result.as_ref().map_or(true, |read| read.0.provenance.start == usize::from(run.span.start()).into() && read.0.provenance.end == usize::from(run.span.end()).into()))]
    pub(super) fn rule(
        &self,
        run: &mut Run<'_>,
    ) -> Result<(RuleFace, WrittenFace), DescriptionDiagnostic>
    {
        let lhs = run.take()?;
        if run.at(Spelling("~>")).0 {
            let arrow = run.take()?;
            return Err(DescriptionDiagnostic {
                span: arrow.span,
                fault: DescriptionFault::RetiredRuleArrow,
            });
        }
        let orientation = if run.at(Spelling("<=>")).0 {
            RuleOrientation::Unpinned
        }
        else if run.at(Spelling("==>")).0 {
            RuleOrientation::Pinned(RuleDirection::LeftToRight)
        }
        else {
            return Err(run.fault(DescriptionFault::Malformed));
        };
        let arrow = run.take()?.span;
        let rhs = run.take()?;
        run.end()?;
        let (lhs, left) = self.free_term(lhs, &BTreeSet::new())?;
        let (rhs, right) = self.free_term(rhs, &lhs.to_node().vars().collect())?;
        let variables = derive_cell_var_meta(&lhs);
        let span = SurfaceSpan::new(
            usize::from(run.span.start()).into(),
            usize::from(run.span.end()).into(),
        );
        Ok((RuleFace::new(lhs, rhs, variables, span), WrittenFace {
            named: Maybe::Absent(member_name::Absent::Anonymous),
            left,
            right,
            arrow: Maybe::Present(arrow),
            orientation,
        }))
    }

    /// Read free terms iteratively, distinguishing constructors, operations,
    /// instantiations, results tuples and abstractions, and keep where each
    /// node is written.
    ///
    /// # Specification
    /// - ensures: every application preserves its head and ordered argument
    ///   terms; an application whose head is a name of `instantiable` — a
    ///   variable of the rule's left side, read on its right — is that
    ///   variable's instantiation; a parenthesized term is its one component,
    ///   and a parenthesized list of several is a results tuple of them in
    ///   order; `bind a . t` is the abstraction of the atom `a` over `t`, the
    ///   name `a` inside it that atom's occurrence and outside it a variable; a
    ///   variable spelled in a type hole, as a pinned rewrite endpoint is, is a
    ///   variable. The written term holds one node per node of the term, in
    ///   pre-order, each at its own bytes and an application or an abstraction
    ///   with its head's or its atom's.
    /// - fails: forms outside names, applications, parenthesized lists and
    ///   abstractions are located.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` for an unreadable term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — constructor-wrapped operation calls distinguish head
    ///   category and child order; a two-component tuple and a parenthesized
    ///   variable distinguish a results tuple from grouping and a swapped
    ///   component; an atom named inside and beside its abstraction separate
    ///   the abstraction's scope from the term after it: the occurrence inside,
    ///   a variable beside.
    /// - witness: `description::tests::operations_and_rules_preserve_their_boundaries`
    /// - witness: `description::tests::a_parenthesized_result_list_reads_as_a_results_tuple`
    /// - witness: `description::theory::tests::a_pinned_rewrite_endpoint_reads_as_a_variable`
    /// - witness: `described::tests::a_data_rule_answers_each_node_at_its_sort`
    /// - witness: `description::theory::tests::an_applied_left_variable_reads_as_its_instantiation`
    /// - witness: `description::theory::tests::a_rule_term_names_an_atom_inside_its_abstraction`
    #[spec(ensures: |result| result.is_ok() || self.tree.node(at.node).is_some())]
    pub(super) fn free_term(
        &self,
        at: Placed,
        instantiable: &BTreeSet<&Name>,
    ) -> Result<(FreeTerm, WrittenTerm), DescriptionDiagnostic>
    {
        let mut pending = vec![TermFrame::Read(at)];
        // The atoms the enclosing `bind`s abstract, each with how many of them
        // abstract it.
        let mut atoms: BTreeMap<&str, usize> = BTreeMap::new();
        let mut terms = Vec::new();
        let mut written = WrittenTerm::default();
        let leaf = |span| WrittenNode {
            span,
            head: Maybe::Absent(head::Absent::Leaf),
        };
        while let Some(frame) = pending.pop() {
            match frame {
                TermFrame::Read(at) => {
                    let pieces = self.pieces(at)?;
                    if let [Piece::Tile { label, .. }] = *pieces.as_slice() {
                        match label.as_ref() {
                            "identifier" | "type_variable" => {
                                let name = self.text(at).0;
                                if atoms.contains_key(name) {
                                    terms.push(FreeTerm::atom(name));
                                }
                                else {
                                    terms.push(FreeTerm::var(name));
                                }
                                written.nodes.push(leaf(at.span));
                            },
                            "constructor" => {
                                terms.push(FreeTerm::ctor(self.text(at).0, []));
                                written.nodes.push(leaf(at.span));
                            },
                            _ => {
                                return Err(DescriptionDiagnostic {
                                    span: at.span,
                                    fault: DescriptionFault::Malformed,
                                });
                            },
                        }
                        continue;
                    }
                    let mut run = Run::new(&pieces, at.span);
                    if run.eat(Spelling("(")).0 {
                        let mut components = Vec::new();
                        while !run.eat(Spelling(")")).0 {
                            components.push(run.take()?);
                            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                                return Err(run.fault(DescriptionFault::Malformed));
                            }
                        }
                        run.end()?;
                        match <[Placed; 1]>::try_from(components) {
                            Ok([only]) => pending.push(TermFrame::Read(only)),
                            Err(components) if components.is_empty() => {
                                return Err(DescriptionDiagnostic {
                                    span: at.span,
                                    fault: DescriptionFault::Malformed,
                                });
                            },
                            Err(components) => {
                                written.nodes.push(leaf(at.span));
                                pending.push(TermFrame::Gather(ArgumentCount(components.len())));
                                pending.extend(components.into_iter().rev().map(TermFrame::Read));
                            },
                        }
                        continue;
                    }
                    if run.eat(Spelling("bind")).0 {
                        let atom = run.take()?;
                        if !run.eat(Spelling(".")).0 {
                            return Err(run.fault(DescriptionFault::Malformed));
                        }
                        let body = run.take()?;
                        run.end()?;
                        written.nodes.push(WrittenNode {
                            span: at.span,
                            head: Maybe::Present(atom.span),
                        });
                        let spelled = self.text(atom).0;
                        let binds = atoms.entry(spelled).or_insert(0);
                        *binds = binds.saturating_add(1);
                        let atom = Name::from(spelled);
                        pending.push(TermFrame::Abstract(atom));
                        pending.push(TermFrame::Read(body));
                        continue;
                    }
                    let head = run.take()?;
                    if !run.eat(Spelling("(")).0 {
                        return Err(run.fault(DescriptionFault::Malformed));
                    }
                    let mut args = Vec::new();
                    while !run.eat(Spelling(")")).0 {
                        args.push(run.take()?);
                        if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                            return Err(run.fault(DescriptionFault::Malformed));
                        }
                    }
                    written.nodes.push(WrittenNode {
                        span: at.span,
                        head: Maybe::Present(head.span),
                    });
                    let head_pieces = self.pieces(head)?;
                    let name = Name::from(self.text(head).0);
                    let kind = if matches!(head_pieces.as_slice(), [Piece::Tile { label, .. }] if label.as_ref() == "constructor")
                    {
                        TermKind::Constructor
                    }
                    else if instantiable.contains(&name) {
                        TermKind::Instantiation
                    }
                    else {
                        TermKind::Operation
                    };
                    pending.push(TermFrame::Apply(name, ArgumentCount(args.len()), kind));
                    pending.extend(args.into_iter().rev().map(TermFrame::Read));
                },
                TermFrame::Apply(head, count, kind) => {
                    let Some(start) = terms.len().checked_sub(count.0)
                    else {
                        return Err(DescriptionDiagnostic {
                            span: at.span,
                            fault: DescriptionFault::Malformed,
                        });
                    };
                    let args = terms.drain(start ..);
                    let term = match kind {
                        TermKind::Constructor => FreeTerm::ctor(head, args),
                        TermKind::Operation => FreeTerm::op(head, args),
                        TermKind::Instantiation => FreeTerm::inst(head, args),
                    };
                    terms.push(term);
                },
                TermFrame::Gather(count) => {
                    let Some(start) = terms.len().checked_sub(count.0)
                    else {
                        return Err(DescriptionDiagnostic {
                            span: at.span,
                            fault: DescriptionFault::Malformed,
                        });
                    };
                    let components = terms.drain(start ..);
                    let term = FreeTerm::results(components);
                    terms.push(term);
                },
                TermFrame::Abstract(atom) => {
                    if let Some(binds) = atoms.get_mut(atom.as_ref()) {
                        *binds = binds.saturating_sub(1);
                        if *binds == 0 {
                            let _closed = atoms.remove(atom.as_ref());
                        }
                    }
                    let Some(body) = terms.pop()
                    else {
                        return Err(DescriptionDiagnostic {
                            span: at.span,
                            fault: DescriptionFault::Malformed,
                        });
                    };
                    terms.push(FreeTerm::abs(atom, body));
                },
            }
        }
        let term = terms.pop().ok_or(DescriptionDiagnostic {
            span: at.span,
            fault: DescriptionFault::Malformed,
        })?;
        Ok((term, written))
    }
}

/// The category carried by an application head.
enum TermKind
{
    /// A generator application.
    Constructor,
    /// An operation application.
    Operation,
    /// An instantiation of a left-side variable.
    Instantiation,
}

/// A suspended free-term reading.
enum TermFrame
{
    /// Visit one syntax node.
    Read(Placed),
    /// Assemble an ordered argument suffix under its head.
    Apply(Name, ArgumentCount, TermKind),
    /// Assemble an ordered suffix into a results tuple.
    Gather(ArgumentCount),
    /// Abstract the atom over the body read before it, closing its scope.
    Abstract(Name),
}
