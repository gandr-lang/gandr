# Refusals

What a `gandr-core-checker` refusal records: whose fact it is, and the judgements it was met inside. The crate's [README](../README.md) states the rest of the crate.

<!-- toc -->
- [Whose fact a refusal is](#whose-fact-a-refusal-is)
- [A refused body keeps the judgements it stood inside](#a-refused-body-keeps-the-judgements-it-stood-inside)
<!-- tocstop -->

## Whose fact a refusal is

`CheckRefusal::classify` is a `const`, wildcard-free match that binds no payload. A type mismatch, a shape mismatch, a checking form in synthesis position, an unknown constant, a universe of the wrong sort or level, a bind whose type mentions its binder, a static application past its head's arity or at an argument of the wrong classifier, a static lambda handed to a dynamic parameter and a static Pi over a classifier that holds no codes are malformed source, the author's mistake. A former outside the fragment is unrepresentable. An unbound index, an exhausted allowance, a dangling id, an admission out of order, a machine invariant and an unfolding the normaliser did not certify are engine faults: a producer that resolves binders and positions never hands the checker an unbound index or an out-of-order admission, so either one is the producer's fault, not the author's; the machine invariant reports a miscount of the machine's own frames instead of asserting it. The absence class has no refusal, because obligations come from a declaration's shape. The alternative for the unbound index — classing it as the author's — would hide a resolution bug in the producer behind a source diagnostic; it reverses if a producer ever hands over unresolved author text.

## A refused body keeps the judgements it stood inside

A refusal is one fact about one node; the judgements under way when it was met are why that node was being judged at all, and they are a diagnostic's nested reasons. `check_module` traces each refused body where the run refused it, before the declaration's own type enters the signature table, and `ModuleReport::pending` keeps the trail by position: the value and computation judgements the refusal stood inside, outermost first, each the term and the type it was checked against, or none where it was synthesised. A term judged twice in a row — checked, then synthesised to cross a bridge — is entered once, at its outer judgement. The trace is a third run of the one machine, `Marking::Traced`: it anchors every term goal as a total run does and refuses as a strict run does, so the anchors still standing at its refusal are the trail, and it meets the strict run's refusal because the run is deterministic.

The alternatives were keeping the anchors in every strict run, which charges each accepted judgement for a trail it never reads, and handing the refusal's pending frames back, which names rules rather than terms: most frames carry no enclosing node, so a face could not locate them. `check_declaration` traces nothing, so an incremental caller re-judging one declaration pays for no trail. The reversal is a face that needs the rule each judgement was in, as well as its term — "the argument of this application" rather than "this" — which pairs each anchor with the frame awaiting it.

Witnesses: `judgement::elaboration::tests::a_traced_run_keeps_the_judgements_a_refusal_stood_in`, `module::tests::a_refused_body_keeps_the_judgements_it_was_refused_inside`.
