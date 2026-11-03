# Monoids, and the free one on a type

A monoid is a type with an associative operation and a unit. This file is a literate gandr source: its `gandr` code blocks are the program, and the rest is prose. The Markdown reader keeps each block's position, so a diagnostic lands on the line of this file that holds it.

## The theory

The operation is written `⊕` when typeset. The attribute travels with the name, so every module that imports `Monoid` typesets it the same way.

```gandr
/// An associative operation with a unit.
pub theory Monoid where {
  /// The carrier.
  sort M : Type;
  /// The unit.
  @[format(latex = "\\varepsilon", typst = "epsilon", md = "ε")]
  oper unit : M;
  /// The operation.
  @[format(latex = "\\oplus", typst = "plus.circle", md = "⊕")]
  oper op : (a : M, b : M) --> M;
}
```

## Lists form the free monoid

Concatenation is the operation, and the empty list is the unit. The columns of the two clauses stay aligned when typeset, as the source lays them out.

```gandr
/// Lists under concatenation.
module Lists[a : Type] : Model(Monoid) with { sort M = List(a) } where {
  /// The empty list.
  def unit = [];
  /// The first list, then the second.
  def op(xs : List(a), ys : List(a)) -> List(a) {
    match xs {
      []       => ys,
      [x, ..r] => [x, ..op(r, ys)]
    }
  }
}
```

## Folding a list into any monoid

A fold sends the free monoid to any other. Its doc comment carries a formula in the target's own markup, read by the `#md` reader.

```gandr
/// Folds `xs` into `m`: #md{ $x_1 \oplus \cdots \oplus x_n$ }.
pub def fold[m : Model(Monoid)](xs : List(m.M)) -> m.M {
  match xs {
    []       => m.unit,
    [x, ..r] => m.op(x, fold(r))
  }
}
```
