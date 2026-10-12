//! Operations and rewrite faces read from declaration members.

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

use super::ArgumentCount;
use super::DescriptionDiagnostic;
use super::DescriptionFault;
use super::Reader;
use super::Run;
use super::Spelling;
use crate::form::Piece;
use crate::form::Placed;

impl Reader<'_, '_>
{
    /// Read an operation's named input and output ports.
    ///
    /// # Specification
    /// - ensures: the bridge has one monomial per output, each using all
    ///   inputs.
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
    #[spec(ensures: |result| result.as_ref().map_or(true, |operation| operation.arity.factors.len() == operation.arity.outputs.len()))]
    pub(super) fn operation(
        &self,
        run: &mut Run<'_>,
    ) -> Result<OperDesc, DescriptionDiagnostic>
    {
        let named = run.take()?;
        if !run.eat(Spelling("(")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let inputs = self.ports(run)?;
        let outputs = if run.eat(Spelling("->")).0 {
            if run.eat(Spelling("(")).0 {
                self.ports(run)?
            }
            else {
                let result = run.take()?;
                vec![SortRef::new("result", self.text(result).0)]
            }
        }
        else {
            Vec::new()
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
        Ok(OperDesc::new(
            self.text(named).0,
            BridgeArity::new(inputs, factors, source, dest, outputs),
            attrs,
        ))
    }

    /// Read named typed ports through their closing parenthesis.
    ///
    /// # Specification
    /// - ensures: preserves port names, sort spellings and source order.
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
    #[spec(captures: before = run.remaining().len(), ensures: |result| result.as_ref().map_or(true, |ports| ports.len() <= before))]
    pub(super) fn ports(
        &self,
        run: &mut Run<'_>,
    ) -> Result<Vec<SortRef>, DescriptionDiagnostic>
    {
        let mut ports = Vec::new();
        while !run.eat(Spelling(")")).0 {
            let name = run.take()?;
            if !run.eat(Spelling(":")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
            let sort = run.take()?;
            ports.push(SortRef::new(self.text(name).0, self.text(sort).0));
            if !run.eat(Spelling(",")).0 && !run.at(Spelling(")")).0 {
                return Err(run.fault(DescriptionFault::Malformed));
            }
        }
        Ok(ports)
    }

    /// Read a written rewrite face and derive its variable metadata.
    ///
    /// # Specification
    /// - ensures: the face keeps both terms and the member's exact byte span.
    /// - fails: only `==>` is a written face arrow; unsupported terms are
    ///   located.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` or `RetiredRuleArrow` for unreadable faces.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric rule endpoints distinguish reversal, fresh
    ///   variables and lost nested heads.
    /// - witness: `description::tests::operations_and_rules_preserve_their_boundaries`
    #[spec(ensures: |result| result.as_ref().map_or(true, |face| face.provenance.start == usize::from(run.span.start()).into() && face.provenance.end == usize::from(run.span.end()).into()))]
    pub(super) fn rule(
        &self,
        run: &mut Run<'_>,
    ) -> Result<RuleFace, DescriptionDiagnostic>
    {
        let lhs = run.take()?;
        if run.at(Spelling("~>")).0 {
            let arrow = run.take()?;
            return Err(DescriptionDiagnostic {
                span: arrow.span,
                fault: DescriptionFault::RetiredRuleArrow,
            });
        }
        if !run.eat(Spelling("==>")).0 {
            return Err(run.fault(DescriptionFault::Malformed));
        }
        let rhs = run.take()?;
        run.end()?;
        let lhs = self.free_term(lhs)?;
        let rhs = self.free_term(rhs)?;
        let variables = derive_cell_var_meta(&lhs);
        let span = SurfaceSpan::new(
            usize::from(run.span.start()).into(),
            usize::from(run.span.end()).into(),
        );
        Ok(RuleFace::new(lhs, rhs, variables, span))
    }

    /// Read free terms iteratively, distinguishing constructors, operations
    /// and results tuples.
    ///
    /// # Specification
    /// - ensures: every application preserves its head and ordered argument
    ///   terms; a parenthesized term is its one component, and a parenthesized
    ///   list of several is a results tuple of them in order.
    /// - fails: forms outside names, applications and parenthesized lists are
    ///   located.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `Malformed` for an unreadable term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — constructor-wrapped operation calls distinguish head
    ///   category and child order; a two-component tuple and a parenthesized
    ///   variable distinguish a results tuple from grouping and a swapped
    ///   component.
    /// - witness: `description::tests::operations_and_rules_preserve_their_boundaries`
    /// - witness: `description::tests::a_parenthesized_result_list_reads_as_a_results_tuple`
    #[spec(ensures: |result| result.is_ok() || self.tree.node(at.node).is_some())]
    pub(super) fn free_term(
        &self,
        at: Placed,
    ) -> Result<FreeTerm, DescriptionDiagnostic>
    {
        let mut pending = vec![TermFrame::Read(at)];
        let mut terms = Vec::new();
        while let Some(frame) = pending.pop() {
            match frame {
                | TermFrame::Read(at) => {
                    let pieces = self.pieces(at)?;
                    if let [Piece::Tile { label, .. }] = *pieces.as_slice() {
                        match label.as_ref() {
                            | "identifier" => terms.push(FreeTerm::var(self.text(at).0)),
                            | "constructor" => terms.push(FreeTerm::ctor(self.text(at).0, [])),
                            | _ => {
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
                            | Ok([only]) => pending.push(TermFrame::Read(only)),
                            | Err(components) if components.is_empty() => {
                                return Err(DescriptionDiagnostic {
                                    span: at.span,
                                    fault: DescriptionFault::Malformed,
                                });
                            },
                            | Err(components) => {
                                pending.push(TermFrame::Gather(ArgumentCount(components.len())));
                                pending.extend(components.into_iter().rev().map(TermFrame::Read));
                            },
                        }
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
                    let head_pieces = self.pieces(head)?;
                    let kind = if matches!(head_pieces.as_slice(), [Piece::Tile { label, .. }] if label.as_ref() == "constructor")
                    {
                        TermKind::Constructor
                    }
                    else {
                        TermKind::Operation
                    };
                    pending.push(TermFrame::Apply(
                        Name::from(self.text(head).0),
                        ArgumentCount(args.len()),
                        kind,
                    ));
                    pending.extend(args.into_iter().rev().map(TermFrame::Read));
                },
                | TermFrame::Apply(head, count, kind) => {
                    let Some(start) = terms.len().checked_sub(count.0)
                    else {
                        return Err(DescriptionDiagnostic {
                            span: at.span,
                            fault: DescriptionFault::Malformed,
                        });
                    };
                    let args = terms.drain(start ..);
                    let term = match kind {
                        | TermKind::Constructor => FreeTerm::ctor(head, args),
                        | TermKind::Operation => FreeTerm::op(head, args),
                    };
                    terms.push(term);
                },
                | TermFrame::Gather(count) => {
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
            }
        }
        terms.pop().ok_or(DescriptionDiagnostic {
            span: at.span,
            fault: DescriptionFault::Malformed,
        })
    }
}

/// The category carried by an application head.
enum TermKind
{
    /// A generator application.
    Constructor,
    /// An operation application.
    Operation,
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
}
