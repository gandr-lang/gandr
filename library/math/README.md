# math

The mathematical library: definitions for homotopy theory and univalent mathematics, a package built and checked by the same verbs as any other (`gandr check library/math`). `math` builds on `std`, never the reverse (#628). Its first module is `math.path`, the algebra of paths in which naturality and coherence state their composites (#3711).

## The module map

| module | holds | absorbs | status |
| ------ | ----- | ------- | ------ |
| `math.path` | `join` and `ap`, composition and a function's action with their endpoints stated; `apd`, a dependent function's action; the associator `assoc` and the unitors `leftUnit` and `rightUnit`, the groupoid laws of composition, each a definition at its path type (#3711); the whiskers `whiskerLeft` and `whiskerRight`, `ap` of a composition with a fixed path (#3712) | the composite, the action and the associator of `corpus/model/identity/then-units-in-the-kernel.gandr`, which imports it | landed |
| `math.cylinder` | the composites of squares and triangles of paths at dimension 2: `cylinderComposite2`, two squares side by side; `cylinderStack2`, two squares stacked; `coneComposite2`, two triangles over one apex; each the term Catt's built-in prints, written over `math.path` (#3712) | none | landed |
| the rest of #628 | identity's remaining laws, the equivalence formers, the h-level ladder, the circle and its loop space, the directed layer | the HoTT exemplars | reserved |

A module's interface is what its `pub` declarations state; a declaration is private by default. A groupoid law is a definition at its path type, proved by based path induction or by conversion, and the kernel replays it.

## Importing it

A project imports a module of `math` by the relative path to its source, `library/math/src/<module>.gandr`, until a package imports another by name (#533 p3). `math`'s own root imports `std.package` the same way, for the manifest theories its `Package` model is of.
