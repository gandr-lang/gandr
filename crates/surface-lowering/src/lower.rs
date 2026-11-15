//! The lowering itself: [`lower_module`], the [`LoweringBudget`] that bounds
//! it, and the two sweeps over the arena it is made of.
//!
//! # Two sweeps over one arena laid out by form, and no recursion anywhere
//!
//! The molded tree lays its nodes out by form, each form's descendants in
//! level order, so a walk in ascending position order visits every parent
//! before any of its children and a walk in descending order visits every
//! child before its parent. Lowering needs both directions and gets each as a
//! plain loop with no stack of its own.
//!
//! The **ascending sweep classifies**. A node's sort is fixed by its parent —
//! the same identifier is a binder, a type head or a term name depending on
//! where it sits — so the sort and the binder frame flow down. The sweep
//! dispatches every form on its grammar kind, reads its own tiles apart from
//! its operands, resolves every name, parses every literal, and decides every
//! refusal; what it decides for a form is recorded as that form's plan.
//!
//! The **descending sweep mints**. Every child is already lowered when its
//! parent is reached, which is exactly what the core arena's constructor-only
//! minting requires, so the sweep carries out each plan, records an origin,
//! and can fail at nothing. A node whose children did not lower simply does
//! not lower, which is how a refused declaration's subtree costs nothing.
//!
//! # A node's produced sort is a function of its own form
//!
//! The classification never pushes an expected sort into a place that has to
//! re-derive it: `+U` produces a value type and `-F` a computation type, a
//! thunk is a value and a lambda is a computation, and a grouping is whatever
//! it wraps. So a sort mismatch is decided where the node stands rather than
//! where its result is consumed, and every refusal carries the sort its own
//! position demanded.
//!
//! # Eight insertions, by the sort of the position
//!
//! Where the source writes a value and the position reads a computation, or
//! the reverse, the fragment refuses — with eight exceptions, each a site the
//! grammar's own shape names. An application's head reads a computation, and
//! a value standing there is forced; a function's result reads a computation
//! type, and a value type standing there gains a returner; a function's body is
//! a computation where the declaration takes a value, and is thunked; a type
//! standing where a value is read is quoted into its code; a name standing
//! where a type is read, bound at a universe, is decoded out of it; a path
//! type's endpoint, or the point of `here`, reads a value, and a computation
//! standing there is the value it returns, a compound endpoint the checker
//! compares by what it computes; a tail, where a path through a body ends,
//! reads a computation, and a value standing there is returned — the exit its
//! polarity names, as the section on exits below sets out; and every other
//! position that reads a value holds a computation standing there nested, for
//! the checker to suspend or run. Each bridge is decided by the position and
//! the name's binder, never searched for, and its origin is the syntax node
//! that demanded it, marked inserted, so a reader can be shown the cast they
//! did not write. Everywhere else the mismatch stays a refusal: a value written
//! where a computation is read, away from a head and a tail, is the author's
//! to return.
//!
//! The first five in detail: a value standing as an application's head is
//! forced, because a force is the only way from a value to a computation; a
//! value type standing as a function's result gains a returner, so
//! `-> Integer` and `-> -F Integer` mean the same and the returner is never
//! doubled; a function's body, a computation where the declaration takes a
//! value, is thunked; a type standing where a value is read
//! is quoted into its code, a value type by `⌜A⌝` and a computation type by
//! `⌜C⌝`, so `def t : Type ; def t = Integer ;` declares a code, and a type an
//! expression cannot spell bare, a receive `?A >> S` or a labelled sum `+{…}`,
//! is written there as `type(T)`, which reads `T` at the quote's own position
//! and so takes the same quote; and a name
//! standing where a type is read, bound at a universe, is decoded out of it, as
//! a value type when the universe is `Type[+, l]` and a computation type when
//! it is `Type[-, l]`. Each bridge is decided by the position's sort and the
//! written form's, both read off the syntax, so no type is consulted; the
//! decode reads the universe its binder was written at, the binder's own
//! syntax. The inserted node takes the origin of the syntax node that demanded
//! it, marked `Provenance::Inserted` with its `Insertion`, so a reader can be
//! shown the cast the author did not write; the checker judges it like any
//! other node, and the kernel re-derives it on readmission.
//!
//! A type variable is a value variable: `a : Type` binds a value whose type is
//! a universe, and `a` in type position is the decode of that value. The
//! alternative was a separate type-variable binder, a second scope and a second
//! index space; it was declined because the core has one context and dependency
//! on values only, so a type variable would have to become a value variable at
//! the lowering anyway. Reversal: a type-level binder the core gives its own
//! context — a kind layer — moves type variables into it.
//!
//! An elaborator that reads the types in hand is the usual place for these
//! insertions. The first seven need none: the lowering knows every position's
//! sort and every form's, so it writes them. The eighth needs the type: a
//! computation where a value is read is suspended when the position expects
//! a thunk and run before the computation around it otherwise, and only the
//! checker holds the expected type. So the lowering writes the computation
//! as a nested value, `Value::Nested` marked `Insertion::Nested`, and the
//! checker decides it and elaborates the body — a thunk in place, or a bind
//! in written order before the innermost enclosing computation, never out of
//! a thunk or a case arm. A written `run c` where a value is read is the same
//! bridge spelled out, `Value::Run`, which the checker always runs. Every
//! computation in value position was refused before, a lambda there
//! included, with the reversal recorded as the unit that moves this
//! boundary; the expected type the checker now reads is that unit's reason,
//! and the alternatives were a run inserted here wherever the written form is
//! a call, which runs every thunk-typed argument, and keeping the refusal,
//! which makes every non-tail call a statement. Reversal: a position whose
//! sort is not read off the syntax — a head whose classifier only
//! normalisation computes — moves its insertion into the checker beside the
//! eighth.
//!
//! # A parameter a type names binds a dependent arrow
//!
//! A function's declared type is a chain of arrows, one per parameter, and an
//! arrow binds its parameter in the codomain only when it is dependent. A
//! parameter whose name a later parameter's type or the result decodes is
//! recorded on its binder frame as the classification reads that type, so by
//! the time the signature is minted each frame knows whether its arrow binds.
//! A decode's code is the variable counted over the frames between it and its
//! binder that bind in the type: every frame a lambda binds, and a typed
//! parameter's only when its arrow is dependent.
//!
//! Each parameter's type is read under the parameters before it, and the result
//! under all of them, so `def id(a : Type, x : a) -> -F a { return x }`
//! declares `+U (Π (a : Type). a -> -F a)`: a parameter that a later
//! parameter's type or the result names binds a dependent arrow, and every
//! other parameter a plain one. The classification records the naming on the
//! binder's frame as it reads each type, before anything is minted, so the
//! arrow is chosen exactly where it is needed. A decoded name counts the
//! binders between it and its own binder that bind in the type — a dependent
//! arrow's, and every lambda's in a body — so `a` is index zero in both `x`'s
//! type and the result, because `x`'s arrow binds nothing.
//!
//! The alternative was a dependent arrow for every parameter, which is one rule
//! and is correct; it was declined because the core keeps the two arrows
//! distinct nodes so that a codomain's scope is never a payload's question, and
//! an arrow whose binder nothing names should say so. The surface's spelling of
//! the dependent arrow, `(x : A) -> C`, reads by this rule rather than as
//! written (the decision and the choice it reverses are in `lower::arity`).
//!
//! # One order of checks, the same at every form
//!
//! A form is checked in a fixed order, and the first check it fails is its
//! refusal: a kind the fragment has no reading for; a repair the parser made
//! among its children; a former of the wrong family for its position, a term
//! where a type belongs or the reverse; a reserved form; a former that does
//! not produce the sort its position demands; a variant of the form the
//! fragment does not admit, or a number of operands it does not take; and
//! last, the names and literals it holds.
//!
//! # The allowance is what bounds the work
//!
//! Every node visit and every binder frame walked spends one step of a caller's
//! allowance. Without it the binder-chain walk makes lowering quadratic in the
//! depth of a module nothing else bounds; with it the whole lowering is linear
//! in the allowance, and running out is an engine fault rather than a wrong
//! answer.
//!
//! # A form's sort is decided by its own form
//!
//! The sort a position demands flows down from its parent, and the sort a form
//! produces is a function of the form alone: `+U C`, `Type[s, l]` and `A * B`
//! are value types, `-F A` is a computation type, `A -> C` is a computation
//! type except where a value type is read, where it is the box `+U (A -> -F
//! C)`, or a static Pi where its domain classifies codes (§ Type operators are
//! static functions over codes), a thunk, a name, a number, a string, `*{}`, a
//! tuple and a static abstraction `fun (A)
//! { T }` are values, a returner, a force, a lambda, an application and a block
//! are computations, a name in type position is the sort its binder's universe
//! classifies, and a grouping is whatever it wraps. A mismatch is therefore
//! refused where the form stands, carrying the sort its position demanded,
//! except at the five positions the insertions (§ Five insertions, by the sort
//! of the position) name.
//!
//! A form is checked in one order, and the first check it fails is its refusal:
//! a kind the fragment has no reading for; a repair among its children; a term
//! where a type belongs or the reverse; a reserved form; a former that does not
//! produce the demanded sort; a variant the fragment does not admit, or an
//! operand count it does not take; and last, the names and literals it holds.
//!
//! # A function tail is a thunked chain of lambdas
//!
//! `def f(x: A, y: B) -> R { … }` is one form that writes both halves of a
//! declaration: the declared type `+U (A -> B -> R)` and the definition `thunk
//! (λx. λy. …)`, the block lowered under one binder per parameter. An empty
//! parameter list declares `+U R` and defines `thunk …`. The tail is signed
//! when every parameter states its type and the tail states its result; a tail
//! missing any of them writes its definition alone, so the declaration is a
//! bodiless definition whose thunk the checker cannot synthesise, refused there
//! as `NotSynthesisable` and never by the lowering. The declared `+U` takes the
//! declaration's origin and each arrow its parameter's binder, all written;
//! each lambda takes its binder too.
//!
//! A call `f(a, b)` is `f` applied to `a`, then to `b`, curried left to right
//! at the call's origin; `f()` is its head alone. Since a signed tail files one
//! form under both halves, its attributes are filed once, under that form's
//! identity.
//!
//! The alternative was keeping the function tail out of the fragment until a
//! desugaring pass rewrites it into a `def` with a thunk of lambdas, which
//! would put a second tree between the grammar and the lowering. Reversal: when
//! the tail grows a form whose meaning is not a chain of lambdas, that form is
//! lowered by its own plan, and the chain stays the reading of the explicit
//! parameters. A recursive tail is the first such form: one fixpoint over the
//! parameter its matches take apart and the ones after it (the `lower::native`
//! module), the chain kept for the parameters before it.
//!
//! # A block binds each statement over the next
//!
//! A block is a sequence of `let x = c;` and `c;` statements and a last
//! computation. It lowers to a chain of binds, `c₁` bound over the rest of the
//! block with `x` in scope, the last computation innermost, each bind at the
//! origin of its `let` keyword. A discarded statement `c;` binds `c`'s value
//! under a binder no name reaches and splits it with no components, `split u as
//! () in rest`, at the origin of `c`: the split types the value as the unit, so
//! the checker refuses a discarded result of any other type at the statement,
//! and the lowering needs no annotation of its own. A block with no last
//! computation is refused at the block as `Arity` with zero. `let x = recv c;`
//! binds what `recv c` returns as any `let` of a computation does,
//! `let d = fork (c : S) t;` runs `t` beside the rest of the block (the
//! `lower::session` module), `var x = e;` holds `e` for the rest of the block
//! (the `lower::access` module), and `let x at w = v;` opens the handle `v`
//! over it (the `lower::world` module). The statement `unpack` is refused as
//! `Unadmitted`, and `acquire`, `release` and the shared `fork !` as
//! `Reserved`, each named by its form at its keyword; and a `let` binder that
//! is a pattern other than a name, a wildcard or a tuple is refused as
//! `Unadmitted`, at the pattern.
//!
//! The one expression statement admitted is an exit closing its block, `{ let m
//! = f(n); return m; }`: `return v;` or `become c;` written before the closing
//! brace is the block's last computation, as if the semicolon were absent. Any
//! other computation written there, `f(m);`, is still the refused expression
//! statement: a discard closing a block would leave the block without its last
//! computation, and so without an exit. The alternative was admitting every
//! closing statement as the last computation, which would make `{ …; pure 1; }`
//! silently return `1` where the author wrote a discard.
//!
//! The discard's alternatives were a checker-side typed bind, a bind whose
//! binder is stated to be `Unit`, which needs a typed-binder node the core does
//! not have; and admitting `c;` at any type, which drops a result the author
//! may have meant to use. A value of any other type is discarded by the
//! explicit spelling `let _ = c;`: a wildcard binder binds the empty name,
//! which no identifier resolves to, so the rest of the block reads every
//! earlier name one index further out and no split is minted. Reversal: if a
//! dedicated refusal for a non-unit `c;` is wanted, the checker's shape
//! mismatch at the split is the place to name it.
//!
//! A block also stands wherever a computation is read: a match arm that
//! sequences, `| Succ(p) => { let r = f[<] p; return Succ r }`, is a block
//! lowered by the same chain, and a block where a value is read is refused as
//! the wrong sort.
//!
//! `let x = v;` returns `v` once and binds it over the rest of the block, the
//! bind call-by-push-value equates with its `let`. The checker reads that
//! bind's binder as `v`, so a type reading `x` sees `v`, and the value is
//! checked once where it is written, whether or not the name is read. A
//! computation with no stated type, `let n = f(3);`, is returned nested: the
//! checker runs it when it returns and suspends it as a thunk otherwise, so
//! `let g = plus(1);` names a function. A stated type `let x : A = c;` binds
//! `c` at that type: a computation ascribed the returner `-F A`, a value
//! ascribed `A` and returned.
//!
//! # A function exits where its body ends
//!
//! `return v` leaves the nearest enclosing function, lambda or thunk with `v`,
//! and `become c` leaves it by running `c` in tail position, from wherever a
//! path through that body passes: its last computation, and on a path the last
//! computation of a block, every arm of a match, a grouping's operand, the
//! computation of a `let` and `become`'s operand. Every path through a body
//! ends in one, written or inferred. A lambda ending a body answers it through
//! its own body's exits, and a hole passes it on. Any other form where a path
//! ends takes the exit its polarity names, read off the form: a value — a
//! variable, a constructor application, a literal, a thunk, a tuple, an
//! annotation — is returned, so `n` there exits as `return n`; a computation —
//! `pure v`, a call, a force — runs in tail position, so `f(x)` there exits as
//! `become f(x)`. An exit where no path passes — a call's head, a definition's
//! value — is refused as `OutOfFragment` with the `NotInTail` boundary; a
//! block's last computation written as a statement, `c ;`, is refused unless
//! `c` is a written exit, because `;` discards; code after a statement every
//! path of which leaves as `Unreachable`. How an exit lowers, and the
//! alternatives that route was chosen over, are in the crate root's § Early
//! exits leave by a direct cut.
//!
//! An inferred exit is a lowering node, checked as a written one is: a value's
//! is the returner over it, its origin the tail's, marked inserted as
//! `Insertion::Return`; a computation's is the computation itself, as
//! `become`'s is, so `thunk { become f(x) }` and `thunk { f(x) }` lower to one
//! term. Each is recorded at the tail's own bytes in
//! `LoweredModule::inferred_exits`, which a face reads to show the keyword the
//! source left out, and which the `explicit-exits` lint reports.
//!
//! A `become` loop therefore runs in constant continuation however long its
//! input, an early exit inside it included, where a recursion whose call is
//! bound by `let` holds a frame per step: the exit is a cut that passes the
//! function's own continuation on, so no frame is pushed. The dispatcher's
//! `evaluate::tests::a_loop_runs_in_constant_continuation` runs loops past a
//! frame region's worth of jumps without filling it.
//!
//! `pure v` is the computation that does nothing and produces `v`; it stands
//! wherever a computation yields without leaving the function, such as an arm
//! of a bound match. At a tail it is a computation like any other, so it exits
//! as `become pure v`, which returns `v` as `return v` does.
//!
//! The recorded design requires an exit at every tail, so control flow reads at
//! the exit the way a descent claim makes recursion readable at the call. The
//! lowering infers the exit at a tail instead, because there the polarity of
//! the form already names it: a value can only be returned and a computation
//! only run, so the keyword restates the form, while an early exit — one off
//! the last computation — is where the keyword says something, and it stays
//! required there. The required exit is kept as an option, not a rule: the
//! `explicit-exits` lint, off by default and enabled by an `explicit_exits`
//! attribute on a declaration or a top-level module or by the driver's
//! `--lint explicit-exits`, reports every inferred exit with a fix that writes
//! its keyword. Alternatives: the required exit, kept as that lint; and a
//! body's result as its last computation whatever its form, which hides
//! whether a tail runs a call or returns a value — the polarity reading names
//! it. Reversal: a tail whose polarity the syntax does not settle, a form whose
//! sort only its type decides, needs its keyword written, and is refused
//! rather than guessed.
//!
//! # Universes and the fuss-free default
//!
//! `Type[s, l]` lowers to the universe of sort `s` — `+` the value types, `-`
//! the computation types — at level `l`. Whatever is left off is the fuss-free
//! default: `Type` and `Type[+]` are `Type[+, 0]`, `Type[-]` is `Type[-, 0]`,
//! and a binder bound at no universe at all decodes at level zero in the sort
//! its position reads: `Type[-, 0]` where a computation type is read, `Type[+,
//! 0]` everywhere else. The default is the value sort because a type variable
//! most often stands for a value type, and level zero because a program that
//! names no level should never have to; a larger universe admits a smaller type
//! by the lift the checker writes, so the default costs nothing at a use that
//! needs more. A level wider than a level constant is refused as `Unadmitted`
//! at its numeral. In term position the grammar reads `Type` alone, never a
//! bracketed universe, so a sorted or levelled universe is quoted only through
//! a declaration's signature.
//!
//! The alternative was requiring the sort and level on every universe, which
//! the grammar allows; it was declined because every program of this fragment
//! lives at the bottom of the value tower, and a written level there is noise.
//! Reversal: level polymorphism, when a declaration quantifies over a level,
//! makes a bare `Type` in its signature a question the elaborator answers, not
//! a default.
//!
//! # Type operators are static functions over codes
//!
//! `fun (A) { T }` lowers to a static lambda over the code of `T`: the body is
//! read where a value is read, so a type written there is quoted, and `A` binds
//! one more value variable, which a type in the body decodes. An arrow standing
//! where a value type is read — a signature that classifies an operator, an
//! operand of another such arrow — is the static Pi, both sides read as value
//! types; `Type -> Type[-]` classifies the operators from value types to
//! computation types, and a computation type as its codomain is refused as
//! `WrongSort` where it stands, so `def a : Integer -> -F Integer ;` is refused
//! at `-F Integer`. A head a binder or an earlier declaration answers, applied
//! to arguments, is a static application, curried left to right, each argument
//! read where a value is read: where a value is read the application stays one,
//! and where a type is read it is decoded.
//!
//! The decode's universe is the one the operator's written type reaches after
//! one arrow per argument: `raw_rel_monad : (Type -> Type[-]) -> Type -> Type
//! -> Type` applied to three arguments decodes at `Type`, and a binder `t :
//! Type -> Type[-]` applied to one decodes at `Type[-]`. An operator whose
//! written type says nothing — the binder of `fun (A) { T }` — decodes at the
//! default (§ Universes and the fuss-free default) its position reads. The
//! binder of `fun (A) { T }` is written with no type: the declaration's
//! signature classifies the abstraction, and the checker refuses an argument of
//! the wrong sort or level as `SortMismatch`, naming both.
//!
//! The alternatives were a typed binder `\(A : K). T` and a decode always at
//! the fuss-free default. The typed binder was declined because the operators
//! the surface is designed for are each declared under a signature that already
//! classifies them, and a second classifier is a second place to disagree; the
//! fixed default was declined because a carrier `T(A)` with `T : Type ->
//! Type[-]` stands where a computation type is read, which the default would
//! misread as a value type. Reversal: an abstraction written where no signature
//! classifies it takes a typed binder, and when the checker elaborates, the
//! decode's universe is read from the operator's classifier instead of the
//! lowering.
//!
//! A type application's head is a type name or a type variable. A declaration
//! is named by an identifier, which is lowercase, and a lowercase name in type
//! position is a type variable, so an operator one might spell `RawRelMonad` is
//! declared and applied here as `raw_rel_monad`. The alternative was admitting
//! capitalised declaration names, a change to every declaration form the
//! surface has; it was declined because a name's case carries no meaning the
//! core reads. Reversal: when the surface gains a type declaration with
//! capitalised names, an operator declared there applies by that name.
//!
//! # A type variable and a call in a type are decodes
//!
//! A name in type position that a binder answers is the decode of the code the
//! binder holds: a parameter at a universe, and equally a variable `let` binds
//! to a type, so a decoder's arm `let x = el(a); let y = el(b); return (x =>
//! y)` reads `x` and `y` as `El(x)` and `El(y)`. A call of a dynamic function
//! in type position is the decode of the code the call returns, and its
//! arguments are read where a value is read: a capitalised name there is a
//! constructor before it is a type head, so `el(Arrow(NatC, NatC))` applies
//! `el` to a constructor value.
//!
//! This is the recorded design, a Tarski data universe: the codes are an
//! ordinary datatype and the decoder a function written over them, both bound
//! at the value level, and a decode is a type over a code that is a term. The
//! alternative was a large elimination into `Type`, a `match` with types for
//! arms standing in the type language and `Element` erased, declined in #353.
//! The choice reverses for a universe that stops being a data universe, one
//! whose codes are not values a function can case on.
//!
//! # Products, sums, tuples and the box
//!
//! `A * B` is the eager product and `(a, b)` its tuple; `A + B` is the sum,
//! the same core type `+{A, B}` is, and chains as the product does, `A + B +
//! C` one sum of three summands, with `*` binding tighter. An unparenthesized
//! chain is one product: `A * B * C` is one product of three components, while
//! `(A * B) * C` and `A * (B * C)` are products of two whose parenthesized
//! component is a product of its own, as written. A tuple is one node of as
//! many components as it writes, each member read where a value is read, so
//! `(a, b, c)` inhabits `A * B * C` and not `(A * B) * C`. `(a,)` is the tuple
//! of one component, a type distinct from the type of `a`; the one-component
//! product type is `*{A}`. Where a value type is read, `(A1, …, An) -> B` is
//! the box, exactly `+U (A1 -> … -> An -> -F B)`, every former at the arrow's
//! origin, so a program spelled with the box and one spelled with its thunk
//! lower to one core term and one content digest. A computation arrow whose
//! domain is one binder, `(x : A) -> C`, is the dependent arrow `Π (x : A). C`,
//! so the telescope `(x : A, y : B(x)) -> C` where a value type is read is
//! exactly `+U ((x : A) -> (y : B(x)) -> -F C)`. A parenthesised list of types
//! anywhere but before `->` is refused as `MisplacedTile` at its first comma.
//! The lazy product `C & D` is a computation type, the core's `With`.
//!
//! The alternative was a core former for the box, which would give one type
//! two digests by its spelling. It was declined because the box is notation
//! for the thunked arrow, and choosing a spelling is the printer's business,
//! not the core's. Reversal: none planned. The printer restores the box, the
//! infix product and sum and the tuple from the core's shape in its sugared
//! form, `gandr-surface-pretty`'s § Two forms, one walk.
//!
//! # A graded bridge is refused by name
//!
//! `+U[ω] C` is `+U C`: `ω`, the unrestricted grade, is the only one the core's
//! thunk type carries. Any other grade, a numeral or a name, is `GradedBridge`,
//! at the grade and naming it, classed unimplemented. A grade on `-F` is
//! `Unadmitted`, since the returner carries none in any design. The alternative
//! was folding a graded bridge into `OutOfFragment` with the grade as its form;
//! it was declined because the grade is the one bridge parameter a later unit
//! gives meaning to, and naming it lets the corpus pin exactly the sources that
//! unit will admit. Reversal: graded thunk types in the core, which make
//! `+U[r]` lower to the graded former.
//!
//! # Literals mean their decoded value
//!
//! A number whose text is decimal digits lowers to its canonical non-negative
//! magnitude, so `007` and `7` are one literal. A number written with an
//! integer width, `7u32`, `7u64`, `7i32` or `7i64`, lowers to that width's
//! literal when its digits fit the width; digits that do not fit it, or a
//! fraction or an exponent before an integer width, are `MalformedLiteral`. A
//! number written with the `f64` suffix, or annotated `(n : f64)` where it is
//! written, lowers to the IEEE 754 binary64 float nearest its decimal text; the
//! `f32` suffix is not admitted yet (#1109). A string lowers to the text
//! between its quotes with its escapes decoded: `\n`, `\t`, `\r`, `\0`, `\\`,
//! `\"` and `\'` to the character each names, a backslash before a line break
//! elided together with the break, any other escaped character to itself, and a
//! trailing lone backslash dropped. Any other literal whose text is not its
//! form's lexeme is `MalformedLiteral`, which only a hand-built tree carries.
//!
//! Escape decoding preserves unescaped Unicode and drops a backslash-newline
//! continuation as one unit, including CRLF. Unknown escapes retain their
//! escaped character; an unfinished escape contributes nothing. A well-formed
//! decimal fraction or exponent with neither suffix nor annotation states no
//! type, refused as unannotated, distinct from malformed numeric text.
//! Boundary witnesses exercise these lexical decisions independently of the
//! parser’s accepted corpus.
//!
//! **Choice.** A number's type is the one its suffix or annotation writes, and
//! a fraction written bare is refused, naming the ascription it needs; no
//! default type is chosen for it. The alternatives were an exact base type for
//! a fraction (a dyadic or a rational, exact arithmetic and no rounding), and a
//! decimal fixed point, a scaled integer with its scale in its type; the first
//! waits on exact reals, the second is a consumer's encoding rather than a
//! language type, and the host's double is what a program reading
//! probabilities through `exp` needs now. **Reversal:** when exact reals land
//! as another typed number under the same spelling, the default for a bare
//! fraction is ruled then.
//!
//! The alternative was to lower a string to its bytes verbatim. It was dropped
//! because the core literal is the string the source means: two spellings of
//! one string must lower to one core value, so that content identity in the
//! core follows meaning. Reversal: a consumer that needs the written spelling
//! reads it through the literal's origin span.
//!
//! # Two sweeps, no recursion, one allowance
//!
//! The tree is laid out by form, each form's descendants in level order, so
//! ascending position order visits every parent before its children and
//! descending order every child before its parent. The ascending sweep
//! classifies and plans; the descending sweep mints, and can fail at nothing
//! but the allowance, because every decision was made on the way down. It
//! mints each manifest type component's form first, in signature order, so a
//! type head standing for that component adopts a type already minted
//! wherever the head sits. Each is a plain loop: no descent, no
//! frame stack, no depth a module can overflow; nested modules are collected
//! from an explicit stack. Every node visit, every binder frame walked, every
//! module child and every attribute spends one step of the `LoweringBudget`;
//! without it the binder walk would make lowering quadratic in a nesting depth
//! nothing else bounds, and running out is an engine fault rather than a wrong
//! answer.
//!
//! With specification enforcement enabled, predicates check phase-local
//! ownership and scope inheritance, positional bridges, plan families, recorded
//! ranges, minting origins and declaration assembly. The pure literal and
//! cursor readers also check their lexical and consumption boundaries. Adequacy
//! is bounded to the named semantic goldens and adversarial fixtures: it does
//! not assert correctness for every program admitted by the full grammar.
//! Contextual records retain coordinates, not certificates of arena or source
//! ownership; their producers and consumers state the executable relations.
//!
//! # Source holes
//!
//! Source `?` and `?name` lower to core value or computation holes according to
//! their term position. Occurrences have distinct `HoleId`s, each the group
//! of the hole's form and the number of holes the group writes before it. The
//! forms of one declaration, as a signature and its definition, make one
//! group. A hole keeps its name however the text around it is spelled,
//! whatever another declaration writes, and whether another declaration is one
//! form or two; they retain the usual written origins. Witness:
//! `tests::source_holes_keep_their_families_and_distinct_occurrences`.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering_base::lower::Context;
use gandr_surface_lowering_base::lower::Sink;
use gandr_surface_lowering_base::lower::SinkTables;
use gandr_surface_lowering_base::lower::Site;
use gandr_surface_lowering_expression::lower::Expressions;
use gandr_surface_lowering_expression::lower::ExpressionsRef;
use gandr_surface_lowering_expression::lower::Finished;
use gandr_surface_lowering_expression::lower::Resumed;
use gandr_surface_lowering_expression::lower::THROUGH_PRELUDE;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_levitation::THEORY_CONSTRUCTORS;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeTable;
use crate::budget::Fuel;
use crate::budget::LoweringBudget;
use crate::coincide::Decisions;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::form::Shape;
use crate::form::shape_of;
use crate::import::ModuleImports;
use crate::lower::exits::ExitsRef;
use crate::module::Collected;
use crate::module::Container;
use crate::module::FlattenedSlot;
use crate::module::Forgetting;
use crate::module::LoweredModule;
use crate::module::Plicity;
use crate::module::SlotIndex;
use crate::module::begin_collection;
use crate::module::root_pieces;
use crate::module::source_pieces;
use crate::namespace::Recognition;
use crate::origin::OriginTable;
use crate::resolve::SurfaceName;
use crate::unit::SourceIndex;
use crate::unit::Unit;

mod access;

mod arity;

mod boundary;

mod capability;

pub use gandr_surface_lowering_base::lower::cells::refuse_cells;

mod closure;

mod conditional;

pub use closure::CarriedOrigins;
pub use closure::ClosureLowering;
pub use closure::Onto;

mod entry;

pub use gandr_surface_lowering_expression::lower::entry::Arguments;
pub use gandr_surface_lowering_expression::lower::entry::ENTRY;
pub use gandr_surface_lowering_expression::lower::entry::entry_shape;

mod exits;

pub use exits::ElidableExit;
pub use exits::Exit;
pub use exits::Explicitness;
pub use exits::InferredExit;
pub use exits::Returned;

mod families;

mod generic;

mod loops;

mod method;

mod runs;

pub use runs::AskedRuns;
pub use runs::InferredRun;
pub use runs::LinearRun;
pub use runs::NestedSite;
pub use runs::RunOperand;
pub use runs::RunSpelling;

mod identity;

mod implicit;

mod model;

mod native;

mod reader;

mod natural;

mod opening;

mod patched;

mod session;

mod splice;

mod staged;

mod ua;

mod world;

/// A family's view of the lowering: the context it owns.
///
/// Each family of the lowering is a set of inherent methods of this wrapper.
/// A method reads and writes a field of the context as `self.cx.field`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone)]
struct Lowerer<'run, 'source>
{
    /// The context this lowering reads and writes.
    cx: Context<'run, 'source>,
}

/// Lower one source into `arena`, declaring its names over `outermost`: the
/// unit of one source, whose path imports resolve to nothing.
///
/// # Specification
/// - requires: as [`lower_unit`].
/// - ensures: [`lower_unit`] over [`Unit::single`].
/// - provides: the lowering of a source read alone.
/// - fails: as [`lower_unit`].
/// - panics: none.
///
/// # Errors
/// As [`lower_unit`].
///
/// # Adequacy
/// - hypothesis: L3 — every witness of [`lower_unit`] runs through this entry.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |module| {
    usize::from(module.origins().declaration_count()) == module.declarations().iter().len()
}))]
#[inline]
pub fn lower_module<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    arena: &mut CoreArena,
    budget: LoweringBudget,
    outermost: Recognition,
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    lower_unit(
        pbg,
        tree,
        &Unit::single(),
        arena,
        budget,
        outermost,
        &mut Decisions::none(),
    )
}

/// Lower the sources `unit` lays end to end in `tree` into `arena`, declaring
/// their names over `outermost`, each rule block decided through `decisions`.
///
/// # Specification
/// - requires: `tree` was molded under `pbg` over the unit's text, its sources
///   starting where `unit` says; `arena` is the arena the lowered module's ids
///   are read against; `budget` bounds the work; `outermost` holds the seed
///   tables and the shadow policy the module's names are declared against.
/// - ensures: one declaration per distinct declared name, in admission order,
///   each carrying its admission position, the content identity of each of its
///   declaration forms, an origin token, and what its declarations amount to —
///   a completed pair, an uncompleted signature, a bodiless definition, or the
///   declaration's first refusal by arena position; a function tail is a
///   definition, and a signature too when it types every parameter and its
///   result. Every core node the module minted has an origin recorded, terms
///   and types alike, the force, thunk, returner, quote and decode the lowering
///   inserted marked as inserted, and every attribute the module carries is
///   resolved against the registry and filed under the content identity of the
///   declaration form it decorates. Every import is kept in source order, its
///   alias, when it has one, bound in its source's scope, its path resolved as
///   `unit` says. A top-level name is declared in its own source's scope, and a
///   source's name nothing there answers is answered by the sources it imports
///   unqualified (the `import` module). Every declared name is declared over
///   `outermost` in admission order, tagged with its name's bytes, and every
///   lambda, parameter and `let` binder is reported against it; the outermost
///   scope is returned with the module. The sources are lowered one at a time,
///   in the unit's order — a source's collection and every pass over it before
///   the next source's — into the one arena, so what a source lowers to, its
///   declarations and its arena rows, ids included, does not depend on the
///   sources after it.
/// - provides: the whole surface-to-core step, a source at a time over one
///   tree, with one strictness and one verdict per name.
/// - fails: [`LoweringRefusal::GrammarMismatch`] when the tree was molded under
///   another grammar; [`LoweringRefusal::OutOfFragment`] and
///   [`LoweringRefusal::MalformedForm`] when the module's own shape is wrong —
///   a root that is not a module, a root child that is neither a declaration
///   nor an import, a declaration with no name, an import out of shape, or an
///   attribute block decorating nothing; [`LoweringRefusal::UnknownMold`] for a
///   mold `pbg` does not hold; and [`LoweringRefusal::BudgetExceeded`] when the
///   work outruns `budget`. A refusal inside a declaration is carried by that
///   declaration instead — [`LoweringRefusal::ShadowedBuiltin`], a declared
///   name or a binder over a builtin under the reject policy, included — and a
///   second import of one alias by that import,
///   [`LoweringRefusal::DuplicateImportAlias`], so one bad declaration does not
///   hide the rest of the module.
/// - panics: none. Every tree lookup is checked and a position the tree does
///   not hold contributes nothing.
///
/// # Errors
/// [`LoweringRefusal::GrammarMismatch`] for a tree of another grammar,
/// [`LoweringRefusal::OutOfFragment`] and [`LoweringRefusal::MalformedForm`]
/// for a module whose own shape is not a list of declarations and well-formed
/// imports,
/// [`LoweringRefusal::UnknownMold`] for a foreign mold, and
/// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
///
/// # Adequacy
/// - hypothesis: L2 — the listed parser fixtures compare produced core nodes
///   with pinned semantic goldens read from the receiving arena. L3 — the
///   listed malformed forms and budget boundaries distinguish located refusals,
///   declaration isolation and origin coverage. These observations cover those
///   fixtures and finite spelling tables, not every program or arbitrary
///   grammar extensions.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
/// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
/// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
/// - witness: `lower::tests::an_arrow_lowers_under_a_thunk_type`
/// - witness: `lower::tests::every_type_atom_lowers_to_its_core_type`
/// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
/// - witness: `lower::tests::u_and_f_are_names`
/// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
/// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
/// - witness: `lower::tests::the_producer_does_not_admit_a_graded_bridge`
/// - witness: `lower::tests::a_graded_bridge_is_refused_by_name`
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
/// - witness: `lower::tests::the_unit_keyword_lowers_to_the_unit_value`
/// - witness: `lower::tests::the_empty_parentheses_are_never_the_unit`
/// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
/// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
/// - witness: `lower::tests::force_and_application_lower_over_their_children`
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
/// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
/// - witness: `lower::tests::a_self_reference_is_unresolved`
/// - witness: `tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
/// - witness: `lower::tests::an_undefined_term_name_is_refused`
/// - witness: `lower::tests::an_undefined_type_head_is_refused`
/// - witness: `lower::tests::an_applied_nullary_head_is_refused`
/// - witness: `lower::tests::an_applied_head_no_former_answers_is_refused`
/// - witness: `lower::tests::a_lazy_product_is_a_computation_type`
/// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
/// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
/// - witness: `lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
/// - witness: `lower::tests::a_computation_codomain_of_a_box_is_refused`
/// - witness: `lower::tests::a_static_lambda_binds_its_name_over_a_quoted_body`
/// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
/// - witness: `tests::static_operators::the_relative_monad_witness_elaborates_identically_in_both_spellings`
/// - witness: `lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
/// - witness: `lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
/// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
/// - witness: `lower::tests::a_malformed_text_literal_is_refused`
/// - witness: `lower::tests::a_repaired_declaration_is_refused`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
/// - witness: `lower::tests::a_tile_out_of_place_is_refused`
/// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
/// - witness: `lower::tests::a_tree_of_another_grammar_is_refused`
/// - witness: `lower::tests::a_mold_the_grammar_does_not_hold_is_refused`
/// - witness: `lower::tests::an_unknown_attribute_is_refused_with_its_suggestion`
/// - witness: `lower::tests::an_attribute_written_twice_for_one_name_is_refused`
/// - witness: `lower::tests::a_schema_taking_a_payload_refuses_an_absent_one`
/// - witness: `lower::tests::a_non_value_payload_is_refused`
/// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
/// - witness: `lower::tests::a_marker_given_a_payload_is_refused`
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
/// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
/// - witness: `lower::tests::a_module_past_the_allowance_is_refused`
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::an_import_binds_its_alias_and_resolves_no_address`
/// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
/// - witness: `tests::namespace::duplicate_source_import_alias_becomes_a_refusal`
/// - witness: `tests::recognition::a_shadowed_builtin_is_reported_as_a_warning`
/// - witness: `tests::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
/// - witness: `tests::recognition::user_shadowing_is_the_only_observable_delta`
/// - witness: `tests::recognition::a_binder_shadowing_a_builtin_is_rejected_under_policy`
#[spec(
    ensures: |ret| {
        let agrees = tree.grammar() == pbg.fingerprint();
        match ret.as_ref() {
            | Ok(module) => {
                agrees
                    && usize::from(module.origins().declaration_count())
                        == module.declarations().iter().len()
                    && module
                        .declarations()
                        .iter()
                        .zip(module.declarations().iter().skip(1))
                        .all(|(left, right)| left.constant() < right.constant())
                    && module.declarations().iter().all(|declaration| {
                        match module.origins().declaration(declaration.origin()) {
                            | Maybe::Present(origin) => {
                                origin.span() == declaration.span()
                                    && tree.node(origin.node()).is_some()
                            },
                            | Maybe::Absent(_) => false,
                        }
                    })
            },
            | Err(&LoweringRefusal::GrammarMismatch {
                tree: found,
                grammar,
            }) => !agrees && found == tree.grammar() && grammar == pbg.fingerprint(),
            | Err(_) => agrees,
        }
    },
)]
#[inline]
pub fn lower_unit<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    unit: &Unit,
    arena: &mut CoreArena,
    budget: LoweringBudget,
    outermost: Recognition,
    decisions: &mut Decisions,
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    if tree.grammar() != pbg.fingerprint() {
        return Err(LoweringRefusal::GrammarMismatch {
            tree: tree.grammar(),
            grammar: pbg.fingerprint(),
        });
    }
    if rooted(pbg, tree, tree.roots())? == Rooted(false) {
        return Ok(empty_module(outermost));
    }
    let collected = begin_collection(pbg, tree, unit, decisions)?;
    let pieces = root_pieces(pbg, tree)?;
    let mut lowerer = Lowerer::new(pbg, tree, collected, Fuel::new(budget), outermost);
    let mut origins = OriginTable::new();
    let mut sink = Sink::new(arena, &mut origins, SinkTables::new());
    for (source, own) in source_pieces(unit, pieces).into_iter().enumerate() {
        Expressions::new(&mut lowerer).lower_source(SourceIndex::from(source), own, &mut sink)?;
    }

    lowerer.finish(arena, origins, None)
}

/// Whether some root reads as a module's root: a root that is layout lowers
/// to nothing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Rooted(bool);

/// Whether some root of `roots` reads as a module's, refusing a root of any
/// other shape.
///
/// # Specification
/// - requires: `roots` are roots of `tree`, molded under `pbg`.
/// - ensures: `Rooted(true)` when a root reads as a module's root, and
///   `Rooted(false)` when every root is layout or the tree holds none.
/// - fails: [`LoweringRefusal::OutOfFragment`] at the first root that is a
///   form, [`LoweringRefusal::MalformedForm`] at the first that is a repair,
///   and [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold.
/// - panics: none.
///
/// # Errors
/// As the specification's fails clause.
///
/// # Adequacy
/// - hypothesis: L3 — a root that is a form refuses the module, and a document
///   resumed after its closure reads the closure's roots before its own.
/// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
/// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
#[spec(ensures: |ret| ret.is_err() || !roots.is_empty() || matches!(ret, Ok(Rooted(false))))]
fn rooted<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    roots: &[NodeIndex],
) -> Result<Rooted, LoweringRefusal<'source>>
{
    let mut rooted = Rooted(false);
    for &position in roots {
        let Some(root) = tree.node(position)
        else {
            continue;
        };
        match shape_of(pbg, root)? {
            Shape::Root => rooted = Rooted(true),
            Shape::Layout => {},
            Shape::Form { name, .. } => {
                return Err(LoweringRefusal::OutOfFragment {
                    span: root.span(),
                    form: name,
                    sort: FragmentSort::Module,
                    boundary: FragmentBoundary::WrongSort,
                });
            },
            Shape::Repair(repair) => {
                return Err(LoweringRefusal::MalformedForm {
                    span: root.span(),
                    form: FormName::ROOT,
                    fault: FormFault::Repaired(repair),
                });
            },
        }
    }

    Ok(rooted)
}

/// The module of a tree no root of which reads as a module's: nothing
/// declared over `outermost`.
///
/// # Specification
/// trivial.
fn empty_module<'source>(outermost: Recognition) -> LoweredModule<'source>
{
    LoweredModule::new(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        AttributeTable::new(),
        OriginTable::new(),
        ModuleImports::new(),
        outermost,
    )
}

impl<'run, 'source> Lowerer<'run, 'source>
{
    /// A lowering of `tree` whose context is fresh, each cell unread.
    ///
    /// # Specification
    /// trivial.
    fn new(
        pbg: &'run Pbg,
        tree: &'run SyntaxTree<'source>,
        collected: Collected<'source>,
        fuel: Fuel,
        recognition: Recognition,
    ) -> Self
    {
        Self {
            cx: Context::new(pbg, tree, collected, fuel, recognition),
        }
    }

    /// The module every source lowered amounts to: its attributes,
    /// documentation, exits and declarations, assembled over `arena` and
    /// `origins`; after a closure's tables when `resumed` gives them.
    ///
    /// # Specification
    /// - requires: every source of the unit is lowered into `arena`, its
    ///   origins recorded in `origins`; `resumed`, when given, marks where the
    ///   lowering resumed after a closure's ([`ExpressionsRef::resumed`]).
    /// - ensures: the module [`lower_unit`] answers. After a closure, its
    ///   binders in scope, resolutions and nested sites are the closure's
    ///   finished tables followed by those of the entries past the marks, which
    ///   every entry of a later source follows; its tables by declaration
    ///   answer a closure's declaration from the closure's, shared, and any
    ///   other from its own entries past the slot mark; its declarations are
    ///   the closure's, shared, then those of the slots past the mark, whose
    ///   origins `origins` records after the closure's.
    /// - provides: the tail of [`lower_unit`] and of a resumed lowering, the
    ///   latter's scope tables, tables by declaration and declarations built in
    ///   the size of its own sources.
    /// - fails: as the attribute and documentation readings.
    /// - panics: none.
    ///
    /// # Errors
    /// As the specification's fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`lower_unit`]; a document resumed after its
    ///   closure finishes as the whole lowering does.
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_lowers_as_the_whole_1033`
    /// - witness: `tests::namespace::a_document_resumed_after_its_closure_reads_each_table_by_declaration_as_the_whole_3321`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |module| {
        usize::from(module.origins().declaration_count()) == usize::from(module.declaration_count())
    }))]
    fn finish(
        self,
        arena: &CoreArena,
        mut origins: OriginTable,
        resumed: Option<Resumed<'_, 'source>>,
    ) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
    {
        let mut lowerer = self;
        let mut attributes = AttributeTable::new();
        Expressions::new(&mut lowerer).attribute(&mut attributes, arena)?;
        let documentation = Expressions::new(&mut lowerer).document()?;
        let inferred = ExitsRef::new(&lowerer).inferred_exits();
        let elidable = ExitsRef::new(&lowerer).elidable_exits();
        // A document resumed after its closure reads the values recorded after
        // the closure's alone.
        let own_values = origins
            .values()
            .get(resumed.map_or(0, |resumed| resumed.values) ..)
            .unwrap_or_default();
        let nested = ExitsRef::new(&lowerer).nested_sites(own_values);
        let linear = ExitsRef::new(&lowerer).linear_runs(arena, &origins);
        // A document resumed after its closure assembles its own declarations
        // and builds its tables by declaration at them alone: the closure's
        // module's are shared with it.
        let own = SlotIndex::from(resumed.map_or(0, |resumed| resumed.slots));
        let declarations = ExpressionsRef::new(&lowerer).assemble(&mut origins, own);
        let structures = ExpressionsRef::new(&lowerer).structures();
        let in_scope = ExpressionsRef::new(&lowerer).in_scope(resumed);
        // A derived rule's statement is read under its theory's name, `T.r`,
        // and so is a reduct, `T.S`.
        let qualified: BTreeMap<ConstantIndex, SurfaceName<'source>> = lowerer
            .cx
            .collected
            .derived
            .iter()
            .filter_map(|(&slot, derived)| {
                let entry = lowerer.cx.collected.slots.get(usize::from(slot))?;
                (lowerer.cx.collected.owner_of(entry.introduced_by.node) == Maybe::Present(slot))
                    .then(|| (entry.constant, lowerer.cx.name_at(derived.theory)))
            })
            .chain(
                lowerer
                    .cx
                    .collected
                    .reducts
                    .iter()
                    .filter_map(|(&slot, reduct)| {
                        let entry = lowerer.cx.collected.slots.get(usize::from(slot))?;
                        let theory = lowerer.cx.collected.slots.get(usize::from(reduct.source))?;
                        Some((entry.constant, theory.name))
                    }),
            )
            .collect();
        // The row each world requires, as its interfaces named whole mint it.
        let world_rows = core::mem::take(&mut lowerer.cx.world_rows);
        // The row each world requires, as its declaration writes the entries.
        let requirements: BTreeMap<ConstantIndex, Vec<crate::module::Required>> = lowerer
            .cx
            .collected
            .requirements
            .iter()
            .filter_map(|(&slot, entries)| {
                let entry = lowerer.cx.collected.slots.get(usize::from(slot))?;
                let required = entries
                    .iter()
                    .map(|written| crate::module::Required {
                        label: written.label.map(|label| label.span),
                        interface: written.interface.span(),
                        written: written.written,
                    })
                    .collect();
                Some((entry.constant, required))
            })
            .collect();
        // The offer the current source writes, as it writes its entries. An
        // offer is kept only when each label's module is one the source
        // declares, so each label finds its structure.
        let offer = lowerer
            .cx
            .collected
            .offers
            .get(&lowerer.cx.current.source)
            .map_or(
                Maybe::Absent(crate::module::offer::Absent::Unoffered),
                |offer| {
                    Maybe::Present(crate::module::Offered {
                        granted: offer
                            .granted
                            .iter()
                            .map(crate::form::WrittenPath::span)
                            .collect(),
                        answered: offer
                            .answered
                            .iter()
                            .filter_map(|entry| {
                                let structure = *lowerer.cx.collected.modules.get(&(
                                    Container::TopLevel(lowerer.cx.current.source),
                                    lowerer.cx.name_at(entry.module),
                                ))?;
                                Some(crate::module::OfferedLabel {
                                    label: entry.label.span,
                                    module: entry.module.span,
                                    structure,
                                    translation: match entry.translation {
                                        Maybe::Present(
                                            crate::written_import::WrittenTranslation::Via(flow),
                                        ) => {
                                            Maybe::Present(crate::module::OfferedTranslation::Via {
                                                flow: flow.span,
                                                rewritten: entry
                                                    .rewritten
                                                    .iter()
                                                    .map(|member| member.span)
                                                    .collect(),
                                            })
                                        },
                                        Maybe::Present(
                                            crate::written_import::WrittenTranslation::Renaming(
                                                ref pairs,
                                            ),
                                        ) => Maybe::Present(
                                            crate::module::OfferedTranslation::Renaming(
                                                pairs
                                                    .iter()
                                                    .map(|&(read, named)| (read.span, named.span))
                                                    .collect(),
                                            ),
                                        ),
                                        Maybe::Absent(absent) => Maybe::Absent(absent),
                                    },
                                })
                            })
                            .collect(),
                    })
                },
            );
        // The reducts the checker may insert where a model of a theory stands
        // at a model of one it includes.
        let reducts: Vec<ConstantIndex> = lowerer
            .cx
            .collected
            .reducts
            .keys()
            .filter_map(|&slot| lowerer.cx.collected.slots.get(usize::from(slot)))
            .filter(|entry| matches!(entry.refusal, Maybe::Absent(_)))
            .map(|entry| entry.constant)
            .collect();
        // The forgetting maps the checker may insert where a model whose
        // unindexed sorts are manifest stands at its theory's models.
        let forgets: Vec<ConstantIndex> = lowerer
            .cx
            .collected
            .forgets
            .keys()
            .filter_map(|&slot| lowerer.cx.collected.slots.get(usize::from(slot)))
            .filter(|entry| matches!(entry.refusal, Maybe::Absent(_)))
            .map(|entry| entry.constant)
            .collect();
        // The readers the checker may cross a natural literal by where a type
        // other than `Integer` is expected.
        let readers = ExpressionsRef::new(&lowerer).literal_readers();
        // Each minted one as a source writes it: its theory, the theory it
        // returns a model of, and its carriers' sorts.
        let mut forgotten = core::mem::take(&mut lowerer.cx.forgotten);
        let forgettings: Vec<Forgetting> = lowerer
            .cx
            .collected
            .forgets
            .iter()
            .filter_map(|(&slot, forgetting)| {
                let constant = |at: SlotIndex| {
                    lowerer
                        .cx
                        .collected
                        .slots
                        .get(usize::from(at))
                        .map(|entry| entry.constant)
                };
                Some(Forgetting {
                    map: constant(slot)?,
                    theory: constant(forgetting.theory)?,
                    onto: constant(forgetting.onto)?,
                    sorts: forgotten.remove(&slot)?,
                })
            })
            .collect();
        // Each model implicit a telescope writes, by its function's slot and
        // entry, with the number of parameters it binds and, when every
        // sort it fixes minted, how a printed telescope writes it.
        let mut written_slots: BTreeMap<
            SlotIndex,
            BTreeMap<usize, (usize, Option<FlattenedSlot<'source>>)>,
        > = core::mem::take(&mut lowerer.cx.written_slots)
            .split_off(&own)
            .into_iter()
            .map(|(slot, written)| {
                let resolved = written
                    .into_iter()
                    .map(|(entry, spelled)| {
                        let count = spelled.components.len();
                        let fixed: Option<Vec<_>> = spelled
                            .fixed
                            .into_iter()
                            .map(|(name, node)| match lowerer.cx.value_type_at(node) {
                                Maybe::Present(id) => Some((name, id)),
                                Maybe::Absent(_) => None,
                            })
                            .collect();
                        let flattened = fixed.map(|fixed| FlattenedSlot {
                            at: 0,
                            name: spelled.name,
                            named: spelled.named,
                            model: match lowerer.cx.value_type_at(spelled.declared) {
                                Maybe::Present(id) => Maybe::Present(id),
                                Maybe::Absent(_) => {
                                    Maybe::Absent(crate::module::model_type::Absent::Unminted)
                                },
                            },
                            theory: spelled.theory,
                            components: spelled.components,
                            fixed,
                        });
                        (entry, (count, flattened))
                    })
                    .collect();
                (slot, resolved)
            })
            .collect();
        let Context {
            collected,
            recognition,
            data,
            constructors,
            codata,
            mut resolutions,
            shadows,
            stage_bounds,
            supplies,
            handler_laws,
            models,
            mut region_binders,
            ..
        } = lowerer.cx;
        let declared_use = |&(span, slot): &(ByteSpan, SlotIndex)| {
            collected
                .slots
                .get(usize::from(slot))
                .map(|named| (span, crate::Resolution::Declaration(named.constant)))
        };
        let (resolved, declared) =
            resumed.map_or((0, 0), |resumed| (resumed.resolved, resumed.declared));
        resolutions.drain(.. resolved.min(resolutions.len()));
        resolutions.extend(
            collected
                .declared_uses
                .get(declared ..)
                .unwrap_or_default()
                .iter()
                .filter_map(declared_use),
        );
        resolutions.sort_unstable();
        resolutions.dedup();
        let (nested, resolutions) = match resumed {
            Some(resumed) => {
                let mut sites = resumed.finished.nested.clone();
                sites.extend(nested);
                let mut all = Vec::with_capacity(
                    resumed
                        .finished
                        .resolutions
                        .len()
                        .saturating_add(resolutions.len()),
                );
                all.extend_from_slice(&resumed.finished.resolutions);
                all.append(&mut resolutions);
                (sites, all)
            },
            None => (nested, resolutions),
        };
        // A model's theory and a block's include, resolved while collecting,
        // reach the imports of the source declaring what they name.
        let mut collected = collected;
        let crossed: Vec<(SourceIndex, SourceIndex)> = collected
            .declared_uses
            .iter()
            .filter_map(|&(span, slot)| {
                let declared = collected.slots.get(usize::from(slot))?.named.span.start();
                Some((
                    collected.unit.source_at(span.start()),
                    collected.unit.source_at(declared),
                ))
            })
            .filter(|&(using, declaring)| using != declaring)
            .collect();
        for (using, declaring) in crossed {
            collected.reach_source(using, declaring);
        }
        let reached: Vec<ByteSpan> = collected.reached.iter().copied().collect();
        let operation_rules = collected
            .operations
            .range(own ..)
            .map(|(&slot, plan)| (ConstantIndex::from(usize::from(slot)), plan.rules().clone()))
            .collect();
        // Each definition over regions names its binders by ordinal, so a
        // diagnostic spells a type kept at one as the source writes it.
        let region_names: BTreeMap<ConstantIndex, Vec<Option<SurfaceName<'source>>>> =
            region_binders
                .split_off(&own)
                .into_iter()
                .filter_map(|(slot, binders)| {
                    let constant = collected.slots.get(usize::from(slot))?.constant;
                    let mut names = alloc::vec![None; binders.len()];
                    for (name, binder) in binders {
                        if let Some(at) = usize::try_from(u32::from(binder))
                            .ok()
                            .and_then(|at| names.get_mut(at))
                        {
                            *at = Some(name);
                        }
                    }
                    Some((constant, names))
                })
                .collect();
        // Each function whose merged telescope binds an implicit or an
        // instance names it, so a printed call supplies it by name. A model
        // implicit binds one parameter per component, which no single name
        // supplies: each is left unnamed there, and the slot is kept whole
        // beside it.
        let mut implicits: BTreeMap<ConstantIndex, Vec<Option<SurfaceName<'source>>>> =
            BTreeMap::new();
        let mut model_slots: BTreeMap<ConstantIndex, Vec<FlattenedSlot<'source>>> = BTreeMap::new();
        for (&slot, merged) in collected.plicities.range(own ..) {
            let Ok(entries) = merged.as_ref()
            else {
                continue;
            };
            if entries
                .iter()
                .all(|entry| entry.plicity == Plicity::Explicit)
            {
                continue;
            }
            let Some(constant) = collected
                .slots
                .get(usize::from(slot))
                .map(|entry| entry.constant)
            else {
                continue;
            };
            let written = written_slots.remove(&slot).unwrap_or_default();
            let mut names = Vec::with_capacity(entries.len());
            let mut flattened = Vec::new();
            for (at, entry) in entries.iter().enumerate() {
                if let Some(&(count, ref spelled)) = written.get(&at) {
                    if let Some(spelled) = spelled.clone() {
                        flattened.push(FlattenedSlot {
                            at: names.len(),
                            ..spelled
                        });
                    }
                    names.extend(core::iter::repeat_n(None, count));
                    continue;
                }
                names.push(match entry.plicity {
                    Plicity::Implicit | Plicity::Instance => Some(entry.name),
                    Plicity::Explicit => None,
                });
            }
            if !flattened.is_empty() {
                let _first = model_slots.insert(constant, flattened);
            }
            let _first = implicits.insert(constant, names);
        }
        // Each constructor a printer writes by its family's path, by its
        // family's constant: one a source's own shadows, or a module family's.
        let mut shadowed: BTreeMap<ConstantIndex, BTreeSet<String>> = BTreeMap::new();
        for &(family, name) in &collected.shadowed {
            if let Some(entry) = collected.slots.get(usize::from(family)) {
                let _first = shadowed
                    .entry(entry.constant)
                    .or_default()
                    .insert(String::from(name.as_ref()));
            }
        }
        // The code's constructors are bare only in a source that holds a
        // theory block. A reader that names the code through an import
        // writes each of them by the code's path, `Theory.Port`.
        if let Maybe::Present(ref theory) = collected.theory
            && !collected.theory_sources.contains(&collected.unit.last())
            && let Some(entry) = collected.slots.get(usize::from(theory.slot))
        {
            shadowed
                .entry(entry.constant)
                .or_default()
                .extend(THEORY_CONSTRUCTORS.iter().map(|&name| String::from(name)));
        }

        // The prelude's declaration that each comparison calls, found by its
        // native row's name as `through_prelude` finds it, so a printer writes
        // a call of it as the comparison.
        let mut operators: Vec<(ConstantIndex, gandr_core_term::primitive::Operator)> =
            THROUGH_PRELUDE
                .iter()
                .filter_map(|&spelling| {
                    let row = gandr_core_term::primitive::PRELUDE
                        .iter()
                        .find(|primitive| {
                            primitive.operator()
                                == gandr_core_term::primitive::Operator::Infix(spelling)
                        })?;
                    let name = SurfaceName::from(<&'static str>::from(row.name()));
                    let (_, constant) = collected.prelude_declaration(name)?;
                    Some((constant, row.operator()))
                })
                .collect();
        operators.sort_unstable();
        let reads = collected.reads();
        // The faces each record type member of this source names: a closure's
        // members are below `own` and keep theirs.
        let record_faces = collected
            .record_faces
            .split_off(&own)
            .into_values()
            .collect();
        let module = LoweredModule::new(
            declarations,
            data,
            structures,
            attributes,
            origins,
            collected.imports,
            recognition,
        )
        .with_descriptions(
            collected.descriptions,
            collected.description_diagnostics,
            collected.natives,
            collected.cells,
        )
        .with_documentation(documentation.forms, documentation.sources)
        .with_constructors(constructors)
        .with_shadowed(shadowed)
        .with_codata(codata)
        .with_inferred_exits(inferred)
        .with_elidable_exits(elidable)
        .with_linear_runs(linear)
        .with_nested_sites(nested)
        .with_in_scope(in_scope)
        .with_resolutions(resolutions)
        .with_shadows(shadows)
        .with_reached_imports(reached)
        .with_operation_rules(operation_rules)
        .with_stage_bounds(stage_bounds)
        .with_region_names(region_names)
        .with_implicits(implicits)
        .with_model_slots(model_slots)
        .with_supplies(supplies)
        .with_handler_laws(handler_laws)
        .with_models(models)
        .with_qualified(qualified)
        .with_requirements(requirements)
        .with_world_rows(world_rows)
        .with_offer(offer)
        .with_reducts(reducts)
        .with_forgets(forgets)
        .with_readers(readers)
        .with_operators(operators)
        .with_reading(collected.unit, reads)
        .with_forgettings(forgettings)
        .with_record_faces(record_faces);
        Ok(match resumed {
            Some(resumed) => {
                module.after_closure(&resumed.finished.keyed, &resumed.finished.declarations)
            },
            None => module,
        })
    }
}

#[cfg(test)]
use gandr_surface_lowering_base::by_form::At;
#[cfg(test)]
use gandr_surface_lowering_base::lower::Body;
#[cfg(test)]
use gandr_surface_lowering_base::lower::Plan;
#[cfg(test)]
use gandr_surface_lowering_base::lower::Reading;
#[cfg(test)]
use gandr_surface_lowering_base::lower::Stretch;
#[cfg(test)]
use gandr_surface_lowering_base::lower::arguments;
#[cfg(test)]
use gandr_surface_lowering_base::lower::closed;
#[cfg(test)]
use gandr_surface_lowering_base::lower::exhausted;
#[cfg(test)]
use gandr_surface_lowering_base::lower::literal;
#[cfg(test)]
use gandr_surface_lowering_base::lower::lowered;
#[cfg(test)]
use gandr_surface_lowering_base::lower::parse_literal;
#[cfg(test)]
use gandr_surface_lowering_base::lower::stretch;
#[cfg(test)]
use gandr_surface_lowering_base::lower::unread_pattern;
#[cfg(test)]
use gandr_surface_lowering_expression::lower::fractional;
#[cfg(test)]
use gandr_surface_lowering_expression::lower::is_value_form;
#[cfg(test)]
use gandr_surface_lowering_expression::lower::parameter;
#[cfg(test)]
use gandr_surface_lowering_expression::lower::typed_number_literal;

#[cfg(test)]
use crate::form::Cursor;
#[cfg(test)]
use crate::form::Piece;
#[cfg(test)]
use crate::form::Placed;
#[cfg(test)]
use crate::form::TileName;
#[cfg(test)]
use crate::lower::exits::Exits;
#[cfg(test)]
use crate::lower::identity::Identities;
#[cfg(test)]
use crate::resolve::Frame;

#[cfg(test)]
mod tests
{

    #[test]
    fn native_boolean_results_have_the_written_classifier()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def answer : +U (-F Bool) ; def answer = thunk { become 19 < 7 } ;"),
            &mut arena,
        );
        let declared = declared_of(module.declarations().iter().next().unwrap().outcome());
        let Some(&ValueType::Thunk(computation)) = arena.value_type(declared)
        else {
            panic!("thunk classifier");
        };
        let Some(&CompType::Returner {
            result: boolean, ..
        }) = arena.comp_type(computation)
        else {
            panic!("result classifier");
        };
        let Some(held) = arena.value_type(boolean)
        else {
            panic!("canonical boolean sum");
        };
        let ValueType::Sum(ref parts) = *held
        else {
            panic!("canonical boolean sum");
        };
        let [first, second] = **parts
        else {
            panic!("the boolean sum is binary");
        };
        assert_eq!(arena.value_type(first), Some(&ValueType::unit()));
        assert_eq!(arena.value_type(second), Some(&ValueType::unit()));
        assert!(matches!(
            module.origins().value_type(first),
            Maybe::Present(_)
        ));
    }

    /// A linear tail takes each parameter its own list writes once, and an
    /// implicit parameter stays intuitionistic: the body opens a linear lambda
    /// and the signature a linear arrow for each written parameter, where the
    /// plain tail opens intuitionistic ones (#5853).
    #[test]
    fn a_linear_tail_takes_each_written_parameter_once_5853()
    {
        let opened = |source: &'static str| {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            let declaration = module.declarations().iter().next().unwrap();
            let Some(&Value::Thunk(mut body)) = arena.value(body_of(declaration.outcome()))
            else {
                panic!("a function's body is a thunk");
            };
            let mut lambdas = Vec::new();
            while let Some(&(Computation::Lambda(inner) | Computation::LinearLambda(inner))) =
                arena.computation(body)
            {
                lambdas.push(matches!(
                    arena.computation(body),
                    Some(&Computation::LinearLambda(_))
                ));
                body = inner;
            }
            let Some(&ValueType::Thunk(mut arrow)) =
                arena.value_type(declared_of(declaration.outcome()))
            else {
                panic!("a function's signature is a thunk");
            };
            let mut arrows = Vec::new();
            while let Some(
                &(CompType::Arrow { codomain, .. }
                | CompType::Pi { codomain, .. }
                | CompType::LinearArrow { codomain, .. }),
            ) = arena.comp_type(arrow)
            {
                arrows.push(matches!(
                    arena.comp_type(arrow),
                    Some(&CompType::LinearArrow { .. })
                ));
                arrow = codomain;
            }
            (lambdas, arrows)
        };
        assert_eq!(
            opened("def keep[a : Type](x : a, n : Integer) -> a = x ;"),
            (vec![false, false, false], vec![false, false, false]),
            "a plain tail opens an intuitionistic lambda and arrow for each parameter"
        );
        assert_eq!(
            opened("def keep[a : Type](x : a, n : Integer) ⊸ a = x ;"),
            (vec![false, true, true], vec![false, true, true]),
            "a linear tail opens linear ones for its written parameters, and the implicit stays \
             intuitionistic"
        );
    }

    #[test]
    fn native_bindings_keep_generated_origins()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def subtract = sub ;"), &mut arena);
        let value = body_of(module.declarations().iter().next().unwrap().outcome());
        let Some(&Value::Primitive { mut body, .. }) = arena.value(value)
        else {
            panic!("native binding");
        };
        loop {
            assert!(matches!(
                module.origins().computation(body),
                Maybe::Present(_)
            ));
            match arena.computation(body) {
                Some(&Computation::Lambda(inner)) => body = inner,
                Some(&Computation::Primitive { ref arguments, .. }) => {
                    for &argument in arguments.iter() {
                        assert!(matches!(
                            module.origins().value(argument),
                            Maybe::Present(_)
                        ));
                    }
                    break;
                },
                other => panic!("native closure shape: {other:?}"),
            }
        }
    }

    #[test]
    fn native_operator_plans_preserve_order()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def answer = thunk { become 19 - 7 } ;"),
            &mut arena,
        );
        let body = body_of(module.declarations().iter().next().unwrap().outcome());
        let Some(&Value::Thunk(body)) = arena.value(body)
        else {
            panic!("thunk");
        };
        let Some(&Computation::Primitive {
            primitive,
            arguments: gandr_core_term::primitive::Arguments::Binary(arguments),
        }) = arena.computation(body)
        else {
            panic!("native subtraction");
        };
        let operands = arguments.map(|argument| match arena.value(argument) {
            Some(&Value::Literal(Literal::Integer(ref integer))) => integer.magnitude().as_ref(),
            _ => panic!("integer operand"),
        });
        assert_eq!(operands, ["19", "7"]);
        assert_eq!(
            primitive.operator(),
            gandr_core_term::primitive::Operator::Infix("-")
        );
    }

    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_term::CompType;
    use gandr_core_term::CompTypeId;
    use gandr_core_term::Computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Sort;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::CharacterLiteral;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::Float64Literal;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_lowering_expression::lower::Expressions;
    use gandr_surface_lowering_expression::lower::ExpressionsRef;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ClosingClass;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;
    use gandr_surface_syntax::SyntaxTree;
    use quenchant_shape::shape::Maybe;

    use super::is_value_form;
    use super::literal;
    use super::lower_module;
    use super::parse_literal;
    use super::typed_number_literal;
    use crate::attribute::AttributeRegistry;
    use crate::attribute::AttributeSchema;
    use crate::attribute::payload_form;
    use crate::budget::Fuel;
    use crate::budget::LoweringBudget;
    use crate::classify::FailureClass;
    use crate::error::FormFault;
    use crate::error::FragmentBoundary;
    use crate::error::FragmentSort;
    use crate::error::LoweringRefusal;
    use crate::error::refusal_span;
    use crate::fixture::Handmade;
    use crate::fixture::Rule;
    use crate::fixture::Spelled;
    use crate::fixture::grammar;
    use crate::fixture::parsed;
    use crate::fixture::registered;
    use crate::fixture::repaired;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::form::Former;
    use crate::form::Repair;
    use crate::module::DeclarationOutcome;
    use crate::module::LoweredDeclaration;
    use crate::module::LoweredModule;
    use crate::namespace::Recognition;
    use crate::origin::Insertion;
    use crate::origin::OriginCount;
    use crate::origin::Provenance;
    use crate::resolve::HeadArity;
    use crate::resolve::OperandCount;
    use crate::resolve::SurfaceName;
    use crate::unbuilt::Unbuilt;
    use crate::unit::Unit;

    /// The module the parser and the lowering make of `source`, which both
    /// must accept.
    ///
    /// # Specification
    /// - requires: the source parses cleanly and fits the default lowering
    ///   allowance.
    /// - ensures: emitted declaration origins lie within the supplied source,
    ///   in admission order.
    /// - provides: a real parser-to-lowering fixture over the supplied arena.
    /// - fails: none on accepted fixtures.
    /// - panics: if parsing or the lowering engine refuses the fixture.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the listed semantic goldens — complete and one-sided
    ///   declarations retain their independently expected core structure.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
    #[spec(
        ensures: |ret| {
            let spelled: &str = source.as_ref();
            ret.declarations().iter().all(|declaration| {
                let span = declaration.span();
                usize::from(span.start()) <= usize::from(span.end())
                    && usize::from(span.end()) <= spelled.len()
            }) && ret
                .declarations()
                .iter()
                .zip(ret.declarations().iter().skip(1))
                .all(|(left, right)| left.constant() < right.constant())
        },
    )]
    fn lowered<'source>(
        source: SourceText<'source>,
        arena: &mut CoreArena,
    ) -> LoweredModule<'source>
    {
        let pbg = grammar();
        let tree = parsed(&pbg, source);

        lower_module(
            &pbg,
            &tree,
            arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap()
    }

    /// What each declaration of `module` amounts to, in admission order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one outcome per declaration, preserving admission order and
    ///   every refusal payload.
    /// - provides: the semantic outcome sequence used by lowering witnesses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed successful and refused declarations retain
    ///   their individual outcomes rather than truncating at the first refusal.
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[spec(
        ensures: |ret| {
            ret.iter().copied().eq(module
                .declarations()
                .iter()
                .map(LoweredDeclaration::outcome))
        },
    )]
    fn outcomes<'source>(module: &LoweredModule<'source>) -> Vec<DeclarationOutcome<'source>>
    {
        module
            .declarations()
            .iter()
            .map(LoweredDeclaration::outcome)
            .collect()
    }

    /// The refusal the first declaration of `tree` carries.
    ///
    /// # Specification
    /// - requires: the engine accepts the tree and its first declaration is
    ///   refused.
    /// - ensures: the first declaration’s located refusal, rather than an
    ///   engine-wide refusal.
    /// - provides: an exact refusal witness for parsed and deliberately
    ///   malformed trees.
    /// - fails: none on a fixture meeting the precondition.
    /// - panics: if lowering fails or the first declaration is not refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — malformed lexemes and repaired declarations yield
    ///   their specific located refusal through the real lowering entry point.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `lower::tests::a_malformed_text_literal_is_refused`
    /// - witness: `lower::tests::a_repaired_declaration_is_refused`
    #[spec(
        ensures: |ret| matches!(ret.span(), Maybe::Present(_)),
    )]
    fn refusal_in<'source>(
        pbg: &Pbg,
        tree: &SyntaxTree<'source>,
    ) -> LoweringRefusal<'source>
    {
        let mut arena = CoreArena::new();
        let module = lower_module(
            pbg,
            tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        let Some(DeclarationOutcome::Refused(refusal)) = outcomes(&module).first().copied()
        else {
            panic!("the first declaration is refused");
        };

        refusal
    }

    /// The refusal the first declaration of `source` carries, which the
    /// parser must accept cleanly.
    ///
    /// # Specification
    /// - requires: the source parses cleanly and its first declaration is
    ///   refused.
    /// - ensures: a declaration-local refusal whose location lies within the
    ///   source.
    /// - provides: the parsed-source refusal oracle.
    /// - fails: none on a fixture meeting the precondition.
    /// - panics: if parsing or lowering fails, or the first declaration
    ///   succeeds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unresolved term and type names retain their different
    ///   refusal variants and the exact spelling’s span.
    /// - witness: `lower::tests::an_undefined_term_name_is_refused`
    /// - witness: `lower::tests::an_undefined_type_head_is_refused`
    #[spec(
        ensures: |ret| {
            let spelled: &str = source.as_ref();
            matches!(ret.span(), Maybe::Present(span) if usize::from(span.start()) <= usize::from(span.end()) && usize::from(span.end()) <= spelled.len())
        },
    )]
    fn refusal(source: SourceText<'_>) -> LoweringRefusal<'_>
    {
        let pbg = grammar();
        let tree = parsed(&pbg, source);

        refusal_in(&pbg, &tree)
    }

    /// The value `body` of `outcome`, which must lower a body.
    ///
    /// # Specification
    /// - requires: the outcome has a lowered body.
    /// - ensures: the body identifier from a completed or body-only
    ///   declaration.
    /// - provides: a checked extraction for structural core assertions.
    /// - fails: never on the required outcome variants.
    /// - panics: if the declaration has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete and body-only declarations expose their
    ///   actual literal bodies rather than substituting a signature coordinate.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
    #[spec(
        ensures: |ret| matches!(outcome, DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } if ret == body),
    )]
    fn body_of(outcome: DeclarationOutcome<'_>) -> gandr_core_term::ValueId
    {
        match outcome {
            DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => {
                body
            },
            DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_) => {
                panic!("the declaration lowers a body")
            },
        }
    }

    /// The declared type of `outcome`, which must lower a signature.
    ///
    /// # Specification
    /// - requires: the outcome has a lowered signature.
    /// - ensures: the declared type from a completed or signature-only
    ///   declaration.
    /// - provides: a checked extraction for structural type assertions.
    /// - fails: never on the required outcome variants.
    /// - panics: if the declaration has no signature.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete and signature-only declarations retain the
    ///   expected type while distinguishing an absent body.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
    #[spec(
        ensures: |ret| matches!(outcome, DeclarationOutcome::Completed { declared_type, .. } | DeclarationOutcome::Uncompleted { declared_type } if ret == declared_type),
    )]
    fn declared_of(outcome: DeclarationOutcome<'_>) -> gandr_core_term::ValueTypeId
    {
        match outcome {
            DeclarationOutcome::Completed { declared_type, .. }
            | DeclarationOutcome::Uncompleted { declared_type } => declared_type,
            DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_) => {
                panic!("the declaration lowers a signature")
            },
        }
    }

    /// The schema `name` is registered with.
    ///
    /// # Specification
    /// - requires: the name is registered.
    /// - ensures: the schema registered for that name.
    /// - provides: the payload policy expected by refusal witnesses.
    /// - fails: never for a registered name.
    /// - panics: if the name is not registered.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — absent and wrong-form payloads name the schema that
    ///   governs the attribute, not merely any registry entry.
    /// - witness: `lower::tests::a_schema_taking_a_payload_refuses_an_absent_one`
    /// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
    #[spec(
        ensures: |ret| matches!(AttributeRegistry::lookup(name), Maybe::Present((_entry, schema)) if ret == schema),
    )]
    fn schema_of(name: SurfaceName<'_>) -> AttributeSchema
    {
        let Maybe::Present((_entry, schema)) = AttributeRegistry::lookup(name)
        else {
            panic!("the name is registered");
        };

        schema
    }

    /// The integer literal `digits` spell.
    ///
    /// # Specification
    /// - requires: a nonempty sequence of ASCII decimal digits.
    /// - ensures: a nonnegative integer with the canonical unpadded magnitude.
    /// - provides: an independently constructed literal expected by core
    ///   witnesses.
    /// - fails: never on valid decimal text.
    /// - panics: on an empty or nondigit spelling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — padded zero and nonzero spellings distinguish
    ///   magnitude normalization from preserving the input’s padding.
    /// - witness: `lower::tests::an_integer_literal_is_its_canonical_magnitude`
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    #[spec(
        ensures: |ret| {
            let spelled: &str = digits.as_ref();
            let unpadded = spelled.trim_start_matches('0');
            let expected = if unpadded.is_empty() { "0" } else { unpadded };
            matches!(ret, Literal::Integer(ref literal) if literal.sign() == Sign::NonNegative && literal.magnitude().as_ref() == expected)
        },
    )]
    fn integer(digits: SourceFragment<'_>) -> Literal
    {
        let spelled: &str = digits.as_ref();
        let magnitude = Magnitude::from_decimal_text(String::from(spelled)).unwrap();

        Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))
    }

    /// The text literal holding `content`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text literal contains the supplied characters without
    ///   escape decoding or delimiter stripping.
    /// - provides: the expected decoded text for literal witnesses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — escaped source text is compared with the explicitly
    ///   decoded content, distinct from the source spelling.
    /// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
    /// - witness: `lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
    #[spec(
        ensures: |ret| {
            let spelled: &str = content.as_ref();
            matches!(ret, Literal::Text(ref literal) if literal.as_ref() == spelled)
        },
    )]
    fn text(content: SourceFragment<'_>) -> Literal
    {
        let spelled: &str = content.as_ref();

        Literal::Text(StringLiteral::new(String::from(spelled)))
    }

    #[test]
    fn a_completed_declaration_lowers_both_halves()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x : Integer ; def x = 3 ;"),
            &mut arena,
        );
        let [
            DeclarationOutcome::Completed {
                declared_type,
                body,
            },
        ] = outcomes(&module)[..]
        else {
            panic!("a signature and its definition pair into one completed declaration");
        };

        assert_eq!(
            arena.value_type(declared_type),
            Some(&ValueType::Base(BaseType::Integer)),
            "the signature lowers to the declared type"
        );
        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the definition lowers to the body"
        );
    }

    #[test]
    fn an_uncompleted_signature_is_the_obligation_producer()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : Integer ;"), &mut arena);
        let [DeclarationOutcome::Uncompleted { declared_type }] = outcomes(&module)[..]
        else {
            panic!("a signature alone is an uncompleted declaration");
        };

        assert_eq!(
            arena.value_type(declared_type),
            Some(&ValueType::Base(BaseType::Integer)),
            "the obligation carries the declared type"
        );
    }

    #[test]
    fn source_holes_keep_their_families_and_distinct_occurrences()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(r#"def a = ?; def b = ?named; def c() { ?pending }"#),
            &mut arena,
        );
        let [
            DeclarationOutcome::Bodied { body: a },
            DeclarationOutcome::Bodied { body: b },
            DeclarationOutcome::Bodied { body: c },
        ] = outcomes(&module)[..]
        else {
            panic!("each unfinished definition lowers");
        };
        let Some(&Value::Hole(first)) = arena.value(a)
        else {
            panic!("anonymous value hole")
        };
        let Some(&Value::Hole(second)) = arena.value(b)
        else {
            panic!("named value hole")
        };
        assert_ne!(first, second);
        let Some(&Value::Thunk(body)) = arena.value(c)
        else {
            panic!("function thunk")
        };
        assert!(matches!(
            arena.computation(body),
            Some(&Computation::Hole(_))
        ));
    }

    #[test]
    fn a_bodiless_definition_lowers_its_body_alone()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x = 3 ;"), &mut arena);
        let [DeclarationOutcome::Bodied { body }] = outcomes(&module)[..]
        else {
            panic!("a definition alone is a bodiless declaration");
        };

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the body lowers alone"
        );
    }

    #[test]
    fn the_thunk_and_returner_heads_lower_to_their_formers()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : +U (-F Integer) ;"), &mut arena);
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("`+U` lowers to the thunk type");
        };
        let Some(&CompType::Returner {
            result: returned, ..
        }) = arena.comp_type(suspended)
        else {
            panic!("`-F` lowers to the returner type");
        };

        assert_eq!(
            arena.value_type(returned),
            Some(&ValueType::Base(BaseType::Integer)),
            "the returner carries its value type"
        );
    }

    #[test]
    fn the_bridge_tokens_are_compound_and_sum_is_unaffected()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def x : +U(-F Integer) ; def s : Integer + Unit ; def t : Integer +Unit ; \
                 def u : Integer + Unit + String ; def v : (Integer + Unit) + String ; \
                 def w : Integer * Unit + String ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        assert!(
            matches!(
                arena.value_type(declared_of(lowered[0])),
                Some(&ValueType::Thunk(_))
            ),
            "`+U` against a bracket is the bridge"
        );
        let summands = |id| match arena.value_type(id) {
            Some(&ValueType::Sum(ref parts)) => parts
                .iter()
                .map(|&part| spine(&arena, part).join(" "))
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        };
        assert_eq!(
            summands(declared_of(lowered[1])),
            ["Integer", "Unit"],
            "`A + B` is the sum, the same type `+{{A, B}}` is"
        );
        assert!(
            matches!(
                lowered[2],
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedTypeHead {
                    arity: HeadArity::Unary,
                    ..
                })
            ),
            "a sign glued to a word is part of the name, so `Integer +Unit` is no sum: \
             `Integer` applies to the name, and no unary former is named `Integer`: {:?}",
            lowered[2]
        );
        assert_eq!(
            summands(declared_of(lowered[3])),
            ["Integer", "Unit", "String"],
            "an unparenthesized chain is one sum of three summands"
        );
        assert_eq!(
            summands(declared_of(lowered[4])),
            ["+ Integer Unit", "String"],
            "a parenthesized sum stays one summand"
        );
        assert_eq!(
            summands(declared_of(lowered[5])),
            ["* Integer Unit", "String"],
            "the product binds tighter than the sum and stays one summand"
        );
        // A bridge after an operand is no sum (#5326). The thunk opens a form,
        // so `Integer` applies to it, and no unary former is named `Integer`.
        // The returner is a prefix of a looser band, so it is no argument, and
        // the parser repairs the form.
        assert_eq!(
            refusal(SourceText::from("def x : Integer +U Integer ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: span(ByteOffset::from(8_usize), ByteOffset::from(26_usize)),
                head: span(ByteOffset::from(8_usize), ByteOffset::from(15_usize)),
                name: SurfaceName::from("Integer"),
                arity: HeadArity::Unary,
            },
            "`Integer` applies to the thunk type and names no unary former"
        );
        let pbg = grammar();
        let tree = repaired(&pbg, SourceText::from("def x : Integer -F Integer ;"));
        assert!(
            matches!(refusal_in(&pbg, &tree), LoweringRefusal::MalformedForm {
                fault: FormFault::Repaired(_),
                ..
            }),
            "the returner after an operand is no argument, and the parser repairs the form"
        );
    }

    #[test]
    fn an_arrow_lowers_under_a_thunk_type()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g : +U (Integer -> -F Integer) ;"),
            &mut arena,
        );
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("`+U` lowers to the thunk type");
        };
        let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(suspended)
        else {
            panic!("the arrow lowers to the function type");
        };

        assert_eq!(
            arena.value_type(domain),
            Some(&ValueType::Base(BaseType::Integer)),
            "the domain is a value type"
        );
        assert!(
            matches!(arena.comp_type(codomain), Some(&CompType::Returner { .. })),
            "the codomain is a computation type"
        );
    }

    #[test]
    fn every_type_atom_lowers_to_its_core_type()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def u : Unit ; def i : Integer ; def s : String ;"),
            &mut arena,
        );
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| arena.value_type(declared_of(outcome)).cloned())
            .collect();

        assert_eq!(
            lowered,
            [
                Some(ValueType::unit()),
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::String)),
            ],
            "each atom lowers to its own core type"
        );
    }

    #[test]
    fn every_universe_spelling_lowers_to_its_universe()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a : Type ; def b : Type[+] ; def c : Type[-] ; def d : Type[+, 3] ; def e : \
                 Type[-, 1] ;",
            ),
            &mut arena,
        );
        let universe = |sort: GroundSort, level: u64| {
            Some(ValueType::Universe {
                sort: Sort::Ground(sort),
                level: Level::constant(LevelConstant::from(level)),
            })
        };
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| arena.value_type(declared_of(outcome)).cloned())
            .collect();

        assert_eq!(
            lowered,
            [
                universe(GroundSort::Value, 0),
                universe(GroundSort::Value, 0),
                universe(GroundSort::Computation, 0),
                universe(GroundSort::Value, 3),
                universe(GroundSort::Computation, 1),
            ],
            "a universe is the sort and the level written, the value sort and level zero for \
             whichever is left off"
        );
    }

    #[test]
    fn u_and_f_are_names()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (source, name, arity) in [
            ("def x : U ;", "U", HeadArity::Nullary),
            ("def x : F ;", "F", HeadArity::Nullary),
            ("def x : U(Integer) ;", "U", HeadArity::Unary),
            ("def x : F(Integer) ;", "F", HeadArity::Unary),
        ] {
            assert_eq!(
                refusal(SourceText::from(source)),
                LoweringRefusal::UnresolvedTypeHead {
                    span: at(8_usize, source.len().saturating_sub(2_usize)),
                    head: at(8_usize, 9_usize),
                    name: SurfaceName::from(name),
                    arity,
                },
                "the bridges are `+U` and `-F`, so `{source}` names a type nothing declares, \
                 marked over the form that writes it"
            );
        }
    }

    #[test]
    fn a_written_stack_type_lowers_to_its_continuation_type_401()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def k : Stack(-F Integer, -F String) ;"),
            &mut arena,
        );
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Stack { input, output }) = arena.value_type(declared)
        else {
            panic!("`Stack(C, D)` is a continuation's type");
        };
        let returned = |id| match arena.comp_type(id) {
            Some(&CompType::Returner { result, .. }) => arena.value_type(result).cloned(),
            _ => None,
        };

        assert_eq!(
            (returned(input), returned(output)),
            (
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::String))
            ),
            "the computation it runs from is written first, the one it ends as second"
        );
    }

    #[test]
    fn a_bare_type_binder_is_positive_at_the_fuss_free_level()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def id(a : Type, x : a) -> -F a { return x }"),
            &mut arena,
        );
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Pi {
            domain: universe,
            codomain,
        }) = arena.comp_type(suspended)
        else {
            panic!("`a`, which a later type names, binds a dependent arrow");
        };
        let Some(&CompType::Arrow {
            domain,
            codomain: result,
        }) = arena.comp_type(codomain)
        else {
            panic!("`x`, which no type names, binds a plain arrow");
        };
        let Some(&CompType::Returner {
            result: returned, ..
        }) = arena.comp_type(result)
        else {
            panic!("the result is a returner");
        };
        let decoded = |id| match arena.value_type(id) {
            Some(&ValueType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            _ => (None, None),
        };
        let fuss_free = Level::constant(LevelConstant::ZERO);
        let innermost = Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        };

        assert_eq!(
            arena.value_type(universe),
            Some(&ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                level: fuss_free.clone(),
            }),
            "a bare `Type` is the value universe at the fuss-free level"
        );
        assert_eq!(
            decoded(domain),
            (Some(innermost.clone()), Some(fuss_free.clone())),
            "`x : a` decodes `a` out of the universe it was bound at"
        );
        assert_eq!(
            decoded(returned),
            (Some(innermost), Some(fuss_free)),
            "the plain arrow binds nothing, so the result names `a` at the same index"
        );
        assert_eq!(
            module
                .origins()
                .value_type(domain)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Decode)),
            "the decode is the lowering's, not the source's"
        );
    }

    #[test]
    fn a_decode_reads_the_universe_its_code_was_written_at()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def small : Type[+, 1] ; def n : small ; def k(c : (Type[-, 2]), t : +U c) -> c \
                 { become force t }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let decoded = |id| match arena.value_type(id) {
            Some(&ValueType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            _ => (None, None),
        };
        assert_eq!(
            decoded(declared_of(lowered[1])),
            (
                Some(Value::Constant(ConstantIndex::from(0_usize))),
                Some(Level::constant(LevelConstant::from(1_u64)))
            ),
            "a declaration signed at a universe decodes at that universe's level"
        );

        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(lowered[2]))
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Pi { codomain, .. }) = arena.comp_type(suspended)
        else {
            panic!("`c`, which later types name, binds a dependent arrow");
        };
        let Some(&CompType::Arrow {
            domain,
            codomain: result,
        }) = arena.comp_type(codomain)
        else {
            panic!("`t`, which no type names, binds a plain arrow");
        };
        let Some(&ValueType::Thunk(thunked)) = arena.value_type(domain)
        else {
            panic!("`+U c` is a thunk type");
        };
        let comp_decoded = |id| match arena.comp_type(id) {
            Some(&CompType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            _ => (None, None),
        };
        let code = (
            Some(Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            Some(Level::constant(LevelConstant::from(2_u64))),
        );
        assert_eq!(
            comp_decoded(thunked),
            code,
            "a binder written at the computation universe, through a grouping, decodes a \
             computation type at its level"
        );
        assert_eq!(
            comp_decoded(result),
            code,
            "and a result naming it is that computation type, with no returner"
        );
    }

    /// #540: a type a body quotes reads a parameter past one no type names at
    /// its index in the body, where every parameter binds.
    #[test]
    fn a_quote_in_a_body_reads_past_an_unmentioned_parameter()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def endo(a : Type, n : Integer) -> -F Type { return (a -> a) } def lifted(a : \
                 Type, n : Integer) -> -F Type[-] { return (a -> -F a) }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let returned = |arena: &CoreArena, at: usize| {
            let Some(&Value::Thunk(suspended)) = arena.value(body_of(lowered[at]))
            else {
                panic!("the body is a thunk");
            };
            let Some(&Computation::Lambda(over_a)) = arena.computation(suspended)
            else {
                panic!("over `a`");
            };
            let Some(&Computation::Lambda(over_n)) = arena.computation(over_a)
            else {
                panic!("and over `n`");
            };
            let Some(&Computation::Return(quote)) = arena.computation(over_n)
            else {
                panic!("returning the quote");
            };
            quote
        };
        let past_n = Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32),
        };

        let Some(&Value::Quote(quoted)) = arena.value(returned(&arena, 0_usize))
        else {
            panic!("`a => a` is a quoted value type");
        };
        let Some(&ValueType::Thunk(arrow)) = arena.value_type(quoted)
        else {
            panic!("the thunked arrow");
        };
        let Some(&CompType::Arrow { domain, .. }) = arena.comp_type(arrow)
        else {
            panic!("an arrow");
        };
        let Some(&ValueType::Element { code, .. }) = arena.value_type(domain)
        else {
            panic!("whose domain decodes `a`");
        };
        assert_eq!(
            arena.value(code),
            Some(&past_n),
            "`a` is read past `n`, which the body binds though no type names it"
        );

        let Some(&Value::QuoteComputation(quoted)) = arena.value(returned(&arena, 1_usize))
        else {
            panic!("`a -> -F a` is a quoted computation type");
        };
        let Some(&CompType::Arrow { domain, .. }) = arena.comp_type(quoted)
        else {
            panic!("an arrow");
        };
        let Some(&ValueType::Element { code, .. }) = arena.value_type(domain)
        else {
            panic!("whose domain decodes `a`");
        };
        assert_eq!(
            arena.value(code),
            Some(&past_n),
            "and so is a computation type's"
        );
    }

    /// #583: a dependent arrow a body quotes is the Π over its binder when its
    /// codomain names it, though only the quote names it, and the plain arrow
    /// when nothing does.
    #[test]
    fn a_dependent_arrow_a_body_quotes_binds_what_its_codomain_names()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def named(n : Integer) -> -F Type { return (+U ((t : Type) -> -F t)) } def \
                 unnamed(n : Integer) -> -F Type { return (+U ((t : Type) -> -F Integer)) }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let arrow = |arena: &CoreArena, at: usize| {
            let Some(&Value::Thunk(suspended)) = arena.value(body_of(lowered[at]))
            else {
                panic!("the body is a thunk");
            };
            let Some(&Computation::Lambda(over_n)) = arena.computation(suspended)
            else {
                panic!("over `n`");
            };
            let Some(&Computation::Return(quote)) = arena.computation(over_n)
            else {
                panic!("returning the quote");
            };
            let Some(&Value::Quote(quoted)) = arena.value(quote)
            else {
                panic!("a quoted value type");
            };
            let Some(&ValueType::Thunk(arrow)) = arena.value_type(quoted)
            else {
                panic!("the thunked arrow");
            };
            arena.comp_type(arrow).cloned()
        };

        assert!(
            matches!(arrow(&arena, 0_usize), Some(CompType::Pi { .. })),
            "`-F t` names the binder the quote introduces, so the arrow is the Π over it"
        );
        assert!(
            matches!(arrow(&arena, 1_usize), Some(CompType::Arrow { .. })),
            "`-F Integer` names nothing, so the arrow binds nothing"
        );
    }

    /// #1115: a module signature's types are the signature's text, so each
    /// answers for itself: the record it states a nested module at, and the
    /// field it states for a member though that member is refused.
    #[test]
    fn a_signature_s_types_answer_whatever_its_members_1115()
    {
        let text = include_str!(
            "lower/unformatted/a-signature-s-types-answer-whatever-its-members-1115.gandr"
        );
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(text), &mut arena);
        let mut written: Vec<(usize, &str)> = module
            .origins()
            .value_types()
            .iter()
            .filter(|&&(_, origin)| origin.provenance() == Provenance::Written)
            .filter_map(|&(_, origin)| {
                let span = origin.span();
                let start = usize::from(span.start());
                text.get(start .. usize::from(span.end()))
                    .map(|spelled| (start, spelled))
            })
            .collect();
        written.sort_unstable();
        assert_eq!(
            written,
            [
                (26, "*{ answer : Integer }"),
                (38, "Integer"),
                (57, "Integer"),
                (104, "Integer"),
            ],
            "the nested signature, its field, the refused member's field and the nested \
             module's own field, each a written type"
        );
    }

    #[test]
    fn a_run_bound_type_and_a_constructor_argument_stand_in_a_type()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "data U : Type where { | NatC : U | Arrow : (a : U, b : U) --> U } def pick(n : \
                 Integer) -> -F Type { return Integer } def twice(n : Integer) -> -F Type { \
                 let x = pick n; return (x -> x) } def el(u : U) -> -F Type { return Integer \
                 } def one : el(Arrow(NatC, NatC)) ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);

        let Some(&Value::Thunk(suspended)) = arena.value(body_of(lowered[2]))
        else {
            panic!("`twice` is a thunk");
        };
        let Some(&Computation::Lambda(body)) = arena.computation(suspended)
        else {
            panic!("over its parameter");
        };
        let Some(&Computation::Bind(_, continuation)) = arena.computation(body)
        else {
            panic!("`let x = pick(n)` binds the call");
        };
        let Some(&Computation::Return(quote)) = arena.computation(continuation)
        else {
            panic!("and returns");
        };
        let Some(&Value::Quote(quoted)) = arena.value(quote)
        else {
            panic!("a type, quoted where a value is read");
        };
        let Some(&ValueType::Thunk(arrow)) = arena.value_type(quoted)
        else {
            panic!("`x => x` is a thunked arrow");
        };
        let Some(&CompType::Arrow { domain, .. }) = arena.comp_type(arrow)
        else {
            panic!("an arrow");
        };
        let Some(&ValueType::Element { code, .. }) = arena.value_type(domain)
        else {
            panic!("the `let`-bound `x` is a decode");
        };
        assert_eq!(
            arena.value(code),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            "of the variable `let` bound"
        );

        let Some(&ValueType::Element { code, .. }) = arena.value_type(declared_of(lowered[4]))
        else {
            panic!("`el(…)` in a type is a decode");
        };
        let Some(&Value::Returned(call)) = arena.value(code)
        else {
            panic!("of the call's returned code");
        };
        let Some(&Computation::Application(_, argument)) = arena.computation(call)
        else {
            panic!("`el` applied");
        };
        let Some(&Value::Constructor { ref fields, .. }) = arena.value(argument)
        else {
            panic!("to `Arrow(NatC, NatC)`, a constructor value, not a type");
        };
        assert!(
            fields
                .iter()
                .all(|&field| matches!(arena.value(field), Some(&Value::Constructor { .. }))),
            "whose `NatC` arguments are constructors too"
        );
    }

    /// #5208: a telescope written as an operand of a constructor inside a
    /// type reads as a value at a field whose type is no universe, and as a
    /// code at a field whose type is a universe.
    #[test]
    fn a_telescope_operand_of_a_constructor_in_a_type_reads_by_its_field_5208()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "data Box : Type where { | Done : (u : Unit) --> Box | Both : (p : Integer * \
                 Integer) --> Box | Named : (t : Type) --> Box } def holds(b : Box) -> -F Type \
                 { return Integer } def unit : holds(Done(*{})) ; def pair : \
                 holds(Both(*{1, 2})) ; def code : holds(Named(*{})) ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let operand = |arena: &CoreArena, declaration: usize| {
            let Some(&ValueType::Element { code, .. }) =
                arena.value_type(declared_of(lowered[declaration]))
            else {
                panic!("`holds(…)` in a type is a decode");
            };
            let Some(&Value::Returned(call)) = arena.value(code)
            else {
                panic!("of the call's returned code");
            };
            let Some(&Computation::Application(_, argument)) = arena.computation(call)
            else {
                panic!("`holds` applied");
            };
            let Some(&Value::Constructor { ref fields, .. }) = arena.value(argument)
            else {
                panic!("to a constructor value");
            };
            let [field] = **fields
            else {
                panic!("of one field");
            };
            field
        };

        assert!(
            matches!(arena.value(operand(&arena, 2)), Some(&Value::Tuple(ref members)) if members.is_empty()),
            "`*{{}}` at a field of type `Unit` is the unit value"
        );
        let Some(&Value::Tuple(ref members)) = arena.value(operand(&arena, 3))
        else {
            panic!("`*{{1, 2}}` at a field of a product type is a tuple");
        };
        assert!(
            members.len() == 2
                && members
                    .iter()
                    .all(|&member| matches!(arena.value(member), Some(&Value::Literal(_)))),
            "of the two literals"
        );
        assert!(
            matches!(arena.value(operand(&arena, 4)), Some(&Value::Quote(_))),
            "`*{{}}` at a field of type `Type` is the code `Unit`"
        );
    }

    /// #5390: a telescope written as an argument of a call inside a type
    /// reads as a value at a parameter whose type is no universe, and as a
    /// code at a parameter whose type is a universe, in the call's first list
    /// and in a second list that applies its result. A boolean stands in the
    /// tuple as a value.
    #[test]
    fn a_telescope_argument_of_a_call_in_a_type_reads_by_its_parameter_5390()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def pairs(p : Integer * Bool) -> -F Type { return Integer } def codes(t : \
                 Type) -> -F Type { return Integer } def curried(t : Type) -> Integer * Bool \
                 -> Type = return fun (p) { t } ; def pair : pairs(*{3, true}) ; def code : \
                 codes(*{Integer, Bool}) ; def again : curried(Unit)(*{3, false}) ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let argument = |arena: &CoreArena, declaration: usize| {
            let Some(&ValueType::Element { code, .. }) =
                arena.value_type(declared_of(lowered[declaration]))
            else {
                panic!("the call in a type is a decode: {:?}", lowered[declaration]);
            };
            let Some(&Value::Returned(call)) = arena.value(code)
            else {
                panic!("of the call's returned code");
            };
            let Some(&Computation::Application(_, argument)) = arena.computation(call)
            else {
                panic!("the call applied: {:?}", arena.computation(call));
            };
            argument
        };
        let values = |arena: &CoreArena, declaration: usize| match arena
            .value(argument(arena, declaration))
        {
            Some(&Value::Tuple(ref members)) => members
                .iter()
                .map(|&member| arena.value(member).cloned())
                .collect::<Vec<_>>(),
            other => panic!("the argument is a tuple: {other:?}"),
        };

        for (declaration, what) in [
            (3_usize, "a parameter of a product type"),
            (5_usize, "the domain of a function's result"),
        ] {
            let members = values(&arena, declaration);
            assert!(
                matches!(*members.as_slice(), [Some(Value::Literal(_)), Some(ref flag)] if !matches!(flag, Value::Quote(_))),
                "a telescope at {what} is the tuple of a number and a boolean: {members:?}"
            );
        }
        assert!(
            matches!(arena.value(argument(&arena, 4)), Some(&Value::Quote(_))),
            "`*{{Integer, Bool}}` at a parameter of type `Type` is the product's code"
        );
    }

    /// #5500: a telescope written inside parentheses at a constructor's field
    /// or at a call's parameter, and one written as an entry of a telescope
    /// that reads as a tuple, reads as a value where its place's type is no
    /// universe, and as a code where that type is a universe.
    #[test]
    fn a_parenthesised_or_nested_telescope_reads_by_its_place_5500()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "data Box : Type where { | Done : (u : Unit) --> Box | Nested : (p : Unit * \
                 Integer) --> Box | Coded : (p : Type * Integer) --> Box } def holds(b : Box) \
                 -> -F Type { return Integer } def pairs(p : Integer * Bool) -> -F Type { \
                 return Integer } def parenthesised : holds(Done((*{}))) ; def nested : \
                 holds(Nested(*{*{}, 1})) ; def grouped : holds(Nested(*{(*{}), 1})) ; def \
                 coded : holds(Coded(*{*{}, 1})) ; def argued : pairs((*{3, true})) ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let argument = |arena: &CoreArena, declaration: usize| {
            let Some(&ValueType::Element { code, .. }) =
                arena.value_type(declared_of(lowered[declaration]))
            else {
                panic!("the call in a type is a decode: {:?}", lowered[declaration]);
            };
            let Some(&Value::Returned(call)) = arena.value(code)
            else {
                panic!("of the call's returned code");
            };
            let Some(&Computation::Application(_, argument)) = arena.computation(call)
            else {
                panic!("the call applied: {:?}", arena.computation(call));
            };
            argument
        };
        let field = |arena: &CoreArena, declaration: usize| {
            let Some(&Value::Constructor { ref fields, .. }) =
                arena.value(argument(arena, declaration))
            else {
                panic!("`holds` applied to a constructor value");
            };
            let [field] = **fields
            else {
                panic!("of one field");
            };
            field
        };
        let members = |arena: &CoreArena, value| match arena.value(value) {
            Some(&Value::Tuple(ref members)) => members
                .iter()
                .map(|&member| arena.value(member).cloned())
                .collect::<Vec<_>>(),
            other => panic!("the value is a tuple: {other:?}"),
        };

        let parenthesised = members(&arena, field(&arena, 3));
        assert!(
            parenthesised.is_empty(),
            "`(*{{}})` at a field of type `Unit` is the unit value: {parenthesised:?}"
        );
        for (declaration, what) in [(4_usize, "`*{{*{{}}, 1}}`"), (5_usize, "`*{{(*{{}}), 1}}`")] {
            let tuple = members(&arena, field(&arena, declaration));
            assert!(
                matches!(*tuple.as_slice(), [Some(Value::Tuple(ref unit)), Some(Value::Literal(_))] if unit.is_empty()),
                "{what} at a field of type `Unit * Integer` is the unit value and a number: \
                 {tuple:?}"
            );
        }
        let coded = members(&arena, field(&arena, 6));
        assert!(
            matches!(*coded.as_slice(), [
                Some(Value::Quote(_)),
                Some(Value::Literal(_))
            ]),
            "`*{{}}` at a component of type `Type` is the code `Unit`: {coded:?}"
        );
        let argued = members(&arena, argument(&arena, 7));
        assert!(
            matches!(*argued.as_slice(), [Some(Value::Literal(_)), Some(ref flag)] if !matches!(flag, Value::Quote(_))),
            "`(*{{3, true}})` at a parameter of type `Integer * Bool` is a tuple: {argued:?}"
        );
    }

    /// #4520: a list type lowers to the native list where its source lists
    /// `List` from `std.list`, and the same type in a source that lists
    /// nothing is an unresolved head at its name.
    #[test]
    fn a_list_type_resolves_only_through_its_listing_4520()
    {
        let body = "def xs : List(Integer) = #[1, 2] ;";
        let mut arena = CoreArena::new();
        let source = crate::fixture::listing(body);
        let module = crate::fixture::listed(&source, &mut arena);
        let Some(DeclarationOutcome::Completed { declared_type, .. }) =
            outcomes(&module).first().copied()
        else {
            panic!("the listed list type lowers: {:?}", outcomes(&module));
        };
        assert!(
            matches!(arena.value_type(declared_type), Some(&ValueType::List(_))),
            "the listed head is the native list former"
        );
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        assert_eq!(
            refusal(SourceText::from(body)),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(9_usize, 22_usize),
                head: at(9_usize, 13_usize),
                name: SurfaceName::from("List"),
                arity: HeadArity::Unary,
            },
            "an unlisted `List` is no type head"
        );
    }

    /// A list type written through the module path a whole import of
    /// `std.list` binds, or through the alias an import of it binds, lowers to
    /// the native list; a head the module does not home is an unknown member
    /// of the alias.
    #[test]
    fn a_homed_former_reads_through_its_import_s_qualifier_4862()
    {
        for text in [
            include_str!(
                "lower/unformatted/a-homed-former-reads-through-its-import-s-qualifier-4862-2.gandr"
            ),
            include_str!(
                "lower/unformatted/a-homed-former-reads-through-its-import-s-qualifier-4862-1.gandr"
            ),
        ] {
            let mut arena = CoreArena::new();
            let module = crate::fixture::listed(text, &mut arena);
            let Some(DeclarationOutcome::Completed { declared_type, .. }) =
                outcomes(&module).first().copied()
            else {
                panic!(
                    "{text:?}: the qualified list type lowers: {:?}",
                    outcomes(&module)
                );
            };
            assert!(
                matches!(arena.value_type(declared_type), Some(&ValueType::List(_))),
                "{text:?}: the qualified head is the native list former"
            );
        }
        let mut arena = CoreArena::new();
        let module = crate::fixture::listed(
            include_str!(
                "lower/unformatted/a-homed-former-reads-through-its-import-s-qualifier-4862-module.gandr"
            ),
            &mut arena,
        );
        assert_eq!(
            outcomes(&module).first().copied(),
            Some(DeclarationOutcome::Refused(
                LoweringRefusal::UnknownMember {
                    span: span(ByteOffset::from(35_usize), ByteOffset::from(40_usize)),
                    module: SurfaceName::from("l"),
                    member: SurfaceName::from("Lists"),
                }
            )),
            "a head `std.list` does not home is no member of it"
        );
    }

    /// A buffer and a web written where `std.buffer` lists them are the native
    /// atoms, and a buffer written where nothing lists it is an unresolved
    /// head at its name.
    #[test]
    fn a_buffer_type_resolves_only_through_its_listing_4522()
    {
        let mut arena = CoreArena::new();
        let source = include_str!(
            "lower/unformatted/a-buffer-type-resolves-only-through-its-listing-4522.gandr"
        );
        let module = crate::fixture::listed(source, &mut arena);
        let quoted = |declaration: usize| match arena.value(body_of(outcomes(&module)[declaration]))
        {
            Some(&Value::Quote(inner)) => arena.value_type(inner).cloned(),
            _ => None,
        };
        assert_eq!(
            quoted(0_usize),
            Some(ValueType::Buffer),
            "the listed `Buf` is the native buffer"
        );
        assert_eq!(
            quoted(1_usize),
            Some(ValueType::Web),
            "the listed `Web` is the native web"
        );
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        assert_eq!(
            refusal(SourceText::from("def keep(b : Buf) -> Buf { b }")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(13_usize, 16_usize),
                head: at(13_usize, 16_usize),
                name: SurfaceName::from("Buf"),
                arity: HeadArity::Nullary,
            },
            "an unlisted `Buf` is no type head"
        );
    }

    #[test]
    fn a_type_where_a_value_is_read_is_quoted()
    {
        let mut arena = CoreArena::new();
        let source = crate::fixture::listing(
            "def a = Integer ; def b = -F Integer ; def c = Type ; def d = +U (-F Integer) ; def e \
             = Path 1 1 ; def f = List Integer ;",
        );
        let module = crate::fixture::listed(&source, &mut arena);
        let quoted = |declaration: usize| {
            let body = body_of(outcomes(&module)[declaration]);
            let provenance = module
                .origins()
                .value(body)
                .map(|origin| origin.provenance());
            match arena.value(body) {
                Some(&Value::Quote(inner)) => (arena.value_type(inner).cloned(), None, provenance),
                Some(&Value::QuoteComputation(inner)) => {
                    (None, arena.comp_type(inner).cloned(), provenance)
                },
                _ => (None, None, provenance),
            }
        };
        let inserted = Maybe::Present(Provenance::Inserted(Insertion::Quote));

        assert_eq!(
            quoted(0_usize),
            (Some(ValueType::Base(BaseType::Integer)), None, inserted),
            "a type atom where a value is read is its code"
        );
        assert!(
            matches!(quoted(1_usize), (None, Some(CompType::Returner { .. }), _)),
            "a computation type is quoted at its own sort"
        );
        assert_eq!(
            quoted(2_usize).0,
            Some(ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                level: Level::constant(LevelConstant::ZERO),
            }),
            "`Type` where a value is read is the code of the fuss-free universe"
        );
        assert!(
            matches!(quoted(3_usize), (Some(ValueType::Thunk(_)), None, _)),
            "a bridge where a value is read is the code of its thunk type"
        );
        let path = quoted(4_usize);
        assert!(
            matches!(path, (Some(ValueType::Path { carrier, .. }), None, provenance)
                if matches!(arena.value_type(carrier), Some(&ValueType::Element { code, .. })
                    if matches!(arena.value(code), Some(&Value::Hole(_))))
                    && provenance == inserted),
            "a path type written as a call where a value is read is its code (#539), its \
             carrier the hole it nominates: {path:?}"
        );
        let list = quoted(5_usize);
        assert!(
            matches!(list, (Some(ValueType::List(element)), None, provenance)
                if arena.value_type(element) == Some(&ValueType::Base(BaseType::Integer))
                    && provenance == inserted),
            "a unary former written as a call where a value is read is its code (#539): {list:?}"
        );
    }

    #[test]
    fn a_quoted_type_is_the_code_a_bare_type_is()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a = Integer ; def b = type(Integer) ; def c = -F Integer ; \
                 def d = type(-F Integer) ; def e = type(+{Unit}) ;",
            ),
            &mut arena,
        );
        let quoted = |declaration: usize| {
            let body = body_of(outcomes(&module)[declaration]);
            let provenance = module
                .origins()
                .value(body)
                .map(|origin| origin.provenance());
            match arena.value(body) {
                Some(&Value::Quote(inner)) => (arena.value_type(inner).cloned(), None, provenance),
                Some(&Value::QuoteComputation(inner)) => {
                    (None, arena.comp_type(inner).cloned(), provenance)
                },
                _ => (None, None, provenance),
            }
        };

        assert_eq!(
            quoted(1_usize),
            quoted(0_usize),
            "a quoted value type is the code its bare spelling is, inserted the same way"
        );
        assert!(
            matches!(
                quoted(0_usize),
                (Some(ValueType::Base(BaseType::Integer)), None, _)
            ),
            "and that code is the base type's"
        );
        let returned = |declaration: usize| match quoted(declaration) {
            (None, Some(CompType::Returner { result, effects }), provenance) => {
                Some((arena.value_type(result).cloned(), effects, provenance))
            },
            _ => None,
        };
        assert_eq!(
            returned(3_usize),
            returned(2_usize),
            "a quoted computation type is quoted at its own sort, as its bare spelling is"
        );
        assert!(
            matches!(
                returned(2_usize),
                Some((Some(ValueType::Base(BaseType::Integer)), _, _))
            ),
            "and that code returns the base type"
        );
        let sum = quoted(4_usize);
        assert!(
            matches!(&sum, (Some(ValueType::Sum(components)), None, _) if components.len() == 1_usize),
            "a labelled sum no expression reads bare is quoted as the sum's code: {sum:?}"
        );
    }

    /// #1126: a module's type read where a value stands, `M.T`, is the code
    /// of the type it names, as the type written bare there is.
    #[test]
    fn a_qualified_type_argument_is_the_code_its_alias_is_1126()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-qualified-type-argument-is-the-code-its-alias-is-1126-module.gandr"
            )),
            &mut arena,
        );
        let outcomes = outcomes(&module);
        let quoted = |declaration: usize| {
            let body = body_of(outcomes[declaration]);
            match arena.value(body) {
                Some(&Value::Quote(inner)) => arena.value_type(inner).cloned(),
                _ => None,
            }
        };
        let last = outcomes.len().saturating_sub(1);
        assert_eq!(
            quoted(last),
            quoted(last.saturating_sub(1)),
            "a qualified type where a value is read is the code its bare spelling is"
        );
        assert_eq!(
            quoted(last),
            Some(ValueType::Base(BaseType::Integer)),
            "and that code is the type the module states"
        );
    }

    #[test]
    fn the_producer_does_not_admit_a_graded_bridge()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a : +U[ω] (-F Integer) ; def b : +U (-F Integer) ;"),
            &mut arena,
        );
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| {
                let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(outcome))
                else {
                    panic!("the bridge lowers to the thunk type");
                };
                let Some(&CompType::Returner {
                    result: returned, ..
                }) = arena.comp_type(suspended)
                else {
                    panic!("the bridged computation is the returner");
                };
                arena.value_type(returned).cloned()
            })
            .collect();
        assert_eq!(
            lowered,
            [
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::Integer)),
            ],
            "the default grade `ω` is the bridge the core carries, the same as none written"
        );
        assert!(
            matches!(
                refusal(SourceText::from("def c : +U[1] (-F Integer) ;")),
                LoweringRefusal::GradedBridge { .. }
            ),
            "any other grade mints no thunk type"
        );
    }

    #[test]
    fn a_graded_bridge_is_refused_by_name()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (source, grade) in [
            ("def c : +U[1] (-F Integer) ;", "1"),
            ("def c : +U[r] (-F Integer) ;", "r"),
        ] {
            let refused = refusal(SourceText::from(source));
            assert_eq!(
                refused,
                LoweringRefusal::GradedBridge {
                    span: at(11_usize, 12_usize),
                    grade: SurfaceName::from(grade),
                },
                "`{source}` is refused at its grade, naming it"
            );
            assert_eq!(
                refused.classify(),
                FailureClass::Unimplemented(gandr_core_term::TrackingIssue::THUNK_GRADE),
                "a grade names the issue tracking thunk grades"
            );
        }
    }

    #[test]
    fn a_lambda_body_binds_its_own_de_bruijn_index()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x = thunk { fun (y) { return y } } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[0]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Lambda(under)) = arena.computation(suspended)
        else {
            panic!("the lambda lowers to a lambda");
        };
        let Some(&Computation::Return(returned)) = arena.computation(under)
        else {
            panic!("the lambda's body lowers to a returner");
        };

        assert_eq!(
            arena.value(returned),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            "the parameter is the innermost binder"
        );
    }

    /// A lambda's parameter written with its type is the lambda's own binder:
    /// the argument, returned ascribed that type, is bound apart over the body,
    /// so the checker holds the arrow's domain to the written type (#1310), and
    /// the body reads the parameter where a dependent result type does (#3735).
    #[test]
    fn a_typed_parameter_binds_its_argument_ascribed_1310()
    {
        let source =
            include_str!("lower/fixtures/a-typed-parameter-binds-its-argument-ascribed-1310.gandr");
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        let body = body_of(outcomes(&module)[0]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Lambda(under)) = arena.computation(suspended)
        else {
            panic!("the lambda lowers to a lambda");
        };
        let Some(&Computation::Bind(bound, rest)) = arena.computation(under)
        else {
            panic!("the typed parameter is bound over the body");
        };
        let Some(&Computation::Ascribe { body: passed, ty }) = arena.computation(bound)
        else {
            panic!("the argument is ascribed the written type");
        };
        let innermost = Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        };
        assert!(
            matches!(arena.computation(passed), Some(&Computation::Return(argument)) if arena.value(argument) == Some(&innermost)),
            "the argument the lambda binds is the one returned"
        );
        assert!(matches!(
            arena.comp_type(ty),
            Some(&CompType::Returner { result, .. })
                if arena.value_type(result) == Some(&ValueType::Base(BaseType::Integer))
        ));
        let parameter = Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32),
        };
        assert!(
            matches!(arena.computation(rest), Some(&Computation::Return(returned)) if arena.value(returned) == Some(&parameter)),
            "the body reads the parameter as the lambda's own binder, past the bind's"
        );
        let at = source.find("y :").unwrap();
        assert!(
            module.origins().bindings().iter().all(|&(_, binder)| binder
                == span(ByteOffset::from(at), ByteOffset::from(at.saturating_add(1)))),
            "the use is bound at the written parameter: {:?}",
            module.origins().bindings()
        );
        crate::lower::native::tests::assert_accepted(&crate::lower::native::tests::judged(
            &module, &mut arena,
        ));

        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-typed-parameter-binds-its-argument-ascribed-1310-module.gandr"
            )),
            &mut arena,
        );
        let report = crate::lower::native::tests::judged(&module, &mut arena);
        assert!(
            report
                .judged()
                .iter()
                .any(|judged| matches!(judged.verdict(), gandr_core_checker::Verdict::Refused(_))),
            "a written type the arrow's domain does not convert to is refused: {report:?}"
        );
    }

    #[test]
    fn a_variable_keeps_its_binder()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let source = "def k = thunk { fun (y) { fun (y) { fun (z) { return y } } } } ;";
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        let inner = source
            .match_indices("(y)")
            .nth(1)
            .unwrap()
            .0
            .saturating_add(1);
        let [(variable, binder)] = *module.origins().bindings()
        else {
            panic!("one variable is written: {:?}", module.origins().bindings());
        };
        assert_eq!(
            binder,
            at(inner, inner.saturating_add(1)),
            "the use is bound at the inner `y`, which shadows the outer one"
        );
        assert_eq!(
            module.origins().binding(variable),
            Maybe::Present(binder),
            "the lookup answers the recorded binder"
        );
        assert!(
            matches!(arena.value(variable), Some(&Value::Variable { .. })),
            "the recorded node is the variable"
        );
        let unrecorded = arena.value_unit();
        assert_eq!(
            module.origins().binding(unrecorded),
            Maybe::Absent(crate::origin::origin::Absent::Unrecorded),
            "a node the lowering did not mint as a written variable keeps no binder"
        );
    }

    #[test]
    fn an_earlier_declaration_resolves_as_a_constant()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def a = 3 ; def b = a ;"), &mut arena);
        let body = body_of(outcomes(&module)[1]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "a name declared earlier resolves to its admission position"
        );
    }

    #[test]
    fn the_unit_keyword_lowers_to_the_unit_value()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : Unit ; def x = *{} ;"), &mut arena);
        let lowered = outcomes(&module);

        assert_eq!(
            arena.value(body_of(lowered[0])),
            Some(&Value::unit()),
            "`unit` is the unit value"
        );
        assert_eq!(
            spine(&arena, declared_of(lowered[0])),
            ["Unit"],
            "and `Unit` its type"
        );
    }

    /// #815: the printer writes a match on the unit as `unit`; before the
    /// fix the lowering refused that pattern as unadmitted, so the printed
    /// body did not read back.
    #[test]
    fn the_unit_pattern_is_the_empty_products_815()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/the-unit-pattern-is-the-empty-products-815-module.gandr"
            )),
            &mut arena,
        );
        let lowered = outcomes(&module);
        assert_eq!(
            gandr_core_term::equal_certificate_syntax(
                &arena,
                body_of(lowered[0]),
                body_of(lowered[1]),
            ),
            gandr_core_term::CertificateEquality::Equal,
            "the unit pattern is the empty product's"
        );
    }

    #[test]
    fn the_empty_parentheses_are_never_the_unit()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def x = () ;"));

        assert_eq!(
            refused,
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 10_usize),
                form: FormName::UNIT,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::EmptyList,
            },
            "`()` as a value is an empty list"
        );
        assert!(
            alloc::format!("{refused}").contains("`Unit`"),
            "and the refusal names the unit value and its type: {refused}"
        );
        let typed = refusal(SourceText::from("def y : () ;"));
        assert!(
            matches!(typed, LoweringRefusal::OutOfFragment {
                form: FormName::UNIT,
                boundary: FragmentBoundary::EmptyList,
                ..
            }),
            "`()` as a type is the same empty list: {typed:?}"
        );
        assert!(
            alloc::format!("{typed}").contains("`Unit`"),
            "and the refusal names the unit type: {typed}"
        );
    }

    #[test]
    fn a_grouping_lowers_to_what_it_wraps()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x = ( 3 ) ;"), &mut arena);
        let body = body_of(outcomes(&module)[0]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the grouping mints nothing of its own"
        );
        assert_eq!(
            module.origins().value(body).map(|origin| origin.span()),
            Maybe::Present(at(10_usize, 11_usize)),
            "the value's origin is the wrapped form, not the parentheses"
        );
    }

    #[test]
    fn a_text_literal_lowers_with_its_escapes_decoded()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def s = \"a\\nb\" ;"), &mut arena);
        let body = body_of(outcomes(&module)[0]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(text(SourceFragment::from("a\nb")))),
            "the escape is decoded into the character it names"
        );
    }

    /// The append chain the nested `value` mints, its literals quoted, walked
    /// by an explicit stack: each entry a value still to spell or the text
    /// written between them.
    ///
    /// # Specification
    /// trivial.
    fn appended(
        arena: &CoreArena,
        value: gandr_core_term::ValueId,
    ) -> String
    {
        let mut spelled = String::new();
        let mut pending = Vec::from([Ok(value)]);
        while let Some(next) = pending.pop() {
            let value = match next {
                Ok(value) => value,
                Err(between) => {
                    spelled.push_str(between);
                    continue;
                },
            };
            match arena.value(value) {
                Some(&Value::Literal(Literal::Text(ref text))) => {
                    let content: &str = text.as_ref();
                    spelled.push('"');
                    spelled.push_str(content);
                    spelled.push('"');
                },
                Some(&Value::Nested(called)) => match arena.computation(called) {
                    Some(&Computation::Primitive {
                        primitive,
                        ref arguments,
                    }) if primitive.name().as_ref() == "string.append" => {
                        pending.push(Err(")"));
                        for (position, &argument) in arguments.iter().enumerate().rev() {
                            pending.push(Ok(argument));
                            pending.push(Err(if position == 0 { "append(" } else { ", " }));
                        }
                    },
                    _ => spelled.push_str("<not an append>"),
                },
                _ => spelled.push_str("<not a text or an append>"),
            }
        }
        spelled
    }

    #[test]
    fn an_interpolated_string_appends_its_segments_in_order()
    {
        let rows = [
            (
                r#"def s = "a\t${ "b" }c" ;"#,
                "append(append(\"a\t\", \"b\"), \"c\")",
            ),
            (r#"def s = "${ "b" }c" ;"#, r#"append("b", "c")"#),
            (r#"def s = "${ "b" }" ;"#, r#"append("", "b")"#),
            (r#"def s = "${ "a" }${ "b" }" ;"#, r#"append("a", "b")"#),
            // The printer's spellings read back as the appends they were
            // printed from: a nested append on the left, a text right of
            // text, an empty text on the right, an escaped opener.
            (
                r#"def s = "${ "hello ${ "a" }" }!" ;"#,
                r#"append(append("hello ", "a"), "!")"#,
            ),
            (r#"def s = "hello ${ "!" }" ;"#, r#"append("hello ", "!")"#),
            (r#"def s = "${ "a" }${ "" }" ;"#, r#"append("a", "")"#),
            (r#"def s = "a\${${ "b" }" ;"#, r#"append("a${", "b")"#),
        ];
        for (source, expected) in rows {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            let body = body_of(outcomes(&module)[0]);
            assert_eq!(
                appended(&arena, body),
                expected,
                "`{source}` appends its text and interpolations in written order"
            );
        }
    }

    #[test]
    fn force_and_application_lower_over_their_children()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { become (force g) 3 } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[1]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the grouped force lowers to a force");
        };

        assert_eq!(
            arena.value(forced),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "the forced value is the earlier declaration"
        );
        assert_eq!(
            arena.value(argument),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the argument is a value"
        );
    }

    #[test]
    fn an_exit_lowers_where_a_path_passes_and_nowhere_else()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = 3 ; def a = thunk { return g } ; def b = thunk { become (force a) } ; \
                 def c = thunk { { return 4 } } ; def d = thunk { return 5 ; } ; \
                 def e = thunk { become return 6 } ;",
            ),
            &mut arena,
        );
        let suspended = |index: usize| {
            let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[index]))
            else {
                panic!("the thunk lowers to a thunk value");
            };
            suspended
        };
        let Some(&Computation::Return(returned)) = arena.computation(suspended(1_usize))
        else {
            panic!("`return` ending a thunk's body lowers to the returner");
        };
        assert_eq!(
            arena.value(returned),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "the returned value is the earlier declaration"
        );
        assert!(
            matches!(
                arena.computation(suspended(2_usize)),
                Some(&Computation::Force(_))
            ),
            "`become` adopts the computation it runs, minting no frame of its own"
        );
        assert!(
            matches!(
                arena.computation(suspended(3_usize)),
                Some(&Computation::Return(_))
            ),
            "tail position reaches through a block"
        );
        assert!(
            matches!(
                arena.computation(suspended(4_usize)),
                Some(&Computation::Return(_))
            ),
            "an exit written as the block's closing statement ends the body"
        );
        assert!(
            matches!(
                arena.computation(suspended(5_usize)),
                Some(&Computation::Return(_))
            ),
            "`become` passes its body's end to the exit it runs"
        );
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (source, start, end, form) in [
            (
                "def a = thunk { become (return 1) 2 } ;",
                24_usize,
                32_usize,
                "return_expression",
            ),
            (
                "def a = thunk { become (become pure 1) 2 } ;",
                24_usize,
                37_usize,
                "become_expression",
            ),
        ] {
            let refused = refusal(SourceText::from(source));
            assert!(
                matches!(
                    refused,
                    LoweringRefusal::OutOfFragment { span, form: held, boundary: FragmentBoundary::NotInTail, .. }
                        if span == at(start, end) && held == FormName::from(NamedKind(form))
                ),
                "an exit at a call's head, where no path passes, is refused at itself, \
                 inferred exits notwithstanding: `{source}` {refused:?}"
            );
        }
        for (source, start, end) in [
            (
                "def a = thunk { let y = return 1 ; return y } ;",
                35_usize,
                43_usize,
            ),
            (
                "def a = thunk { let y = become pure 1 ; return y } ;",
                40_usize,
                48_usize,
            ),
        ] {
            let refused = refusal(SourceText::from(source));
            assert_eq!(
                refused,
                LoweringRefusal::Unreachable {
                    span: at(start, end)
                },
                "the rest of a block after a statement that always exits is unreachable: \
                 `{source}`"
            );
        }
    }

    #[test]
    fn a_function_tail_lowers_to_a_thunked_lambda_chain()
    {
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(x : Integer, y : String) -> -F Integer { let z = y ; return x }",
            ),
            &mut arena,
        );
        let [declaration] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("the tail declares one name");
        };
        let DeclarationOutcome::Completed {
            declared_type,
            body,
        } = declaration.outcome()
        else {
            panic!("a tail typing every parameter and its result writes both halves");
        };
        assert!(
            matches!(declaration.signature(), Maybe::Present(_))
                && declaration.signature() == declaration.definition(),
            "both halves are the one declaration form"
        );

        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_type)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Arrow {
            domain: first,
            codomain: rest,
        }) = arena.comp_type(suspended)
        else {
            panic!("the first parameter is the outer arrow");
        };
        let Some(&CompType::Arrow {
            domain: second,
            codomain: result,
        }) = arena.comp_type(rest)
        else {
            panic!("the second parameter is the inner arrow");
        };
        let Some(&CompType::Returner {
            result: returned, ..
        }) = arena.comp_type(result)
        else {
            panic!("the result is the written returner");
        };
        assert_eq!(
            [first, second, returned].map(|id| arena.value_type(id).cloned()),
            [
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::String)),
                Some(ValueType::Base(BaseType::Integer)),
            ],
            "the declared type is `+U (Integer -> String -> -F Integer)`"
        );

        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the body is a thunk");
        };
        let Some(&Computation::Lambda(outer)) = arena.computation(suspended)
        else {
            panic!("the first parameter is the outer lambda");
        };
        let Some(&Computation::Lambda(inner)) = arena.computation(outer)
        else {
            panic!("the second parameter is the inner lambda");
        };
        let Some(&Computation::Bind(bound, rest)) = arena.computation(inner)
        else {
            panic!("the statement is a bind");
        };
        let (Some(&Computation::Return(read)), Some(&Computation::Return(last))) =
            (arena.computation(bound), arena.computation(rest))
        else {
            panic!("the bound and the last computation are returners");
        };
        assert_eq!(
            [read, last].map(|id| arena.value(id).cloned()),
            [Some(variable(0_u32)), Some(variable(2_u32))],
            "`y` is innermost before the statement, and `x` sits under `y` and `z` after it"
        );
        assert_eq!(
            module
                .origins()
                .value(body)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Thunk)),
            "the body's thunk is the lowering's, not the source's"
        );
        assert_eq!(
            module
                .origins()
                .value_type(declared_type)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Written),
            "the declared type is the function form's own"
        );
    }

    #[test]
    fn an_empty_parameter_list_lowers_to_a_thunked_computation()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def main() -> -F Integer { return 3 }"),
            &mut arena,
        );
        let [
            DeclarationOutcome::Completed {
                declared_type,
                body,
            },
        ] = outcomes(&module)[..]
        else {
            panic!("a tail of no parameters writes both halves");
        };
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_type)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&Value::Thunk(computation)) = arena.value(body)
        else {
            panic!("the body is a thunk");
        };

        assert!(
            matches!(arena.comp_type(suspended), Some(&CompType::Returner { .. })),
            "no arrow stands between `+U` and the result"
        );
        assert!(
            matches!(
                arena.computation(computation),
                Some(&Computation::Return(_))
            ),
            "no lambda stands between the thunk and the block"
        );
    }

    #[test]
    fn a_tail_missing_a_type_writes_its_definition_alone()
    {
        for source in [
            "def f(x : Integer) { return x }",
            "def f(x, y : Integer) -> -F Integer { return y }",
        ] {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            let [declaration] = *module.declarations().iter().collect::<Vec<_>>()
            else {
                panic!("`{source}` declares one name");
            };

            assert!(
                matches!(declaration.outcome(), DeclarationOutcome::Bodied { .. }),
                "`{source}` lowers its body alone"
            );
            assert!(
                matches!(declaration.signature(), Maybe::Absent(_)),
                "`{source}` writes no signature"
            );
        }
    }

    /// Run every pass of `lowerer` up to and through the mint sweep, minting
    /// into `arena` and recording into `origins`.
    ///
    /// # Specification
    /// trivial.
    fn minted(
        lowerer: &mut super::Lowerer<'_, '_>,
        arena: &mut CoreArena,
        origins: &mut super::OriginTable,
    )
    {
        Expressions::new(lowerer).declare();
        Expressions::new(lowerer).seed().unwrap();
        super::Exits::new(lowerer).survey().unwrap();
        Expressions::new(lowerer).classify().unwrap();
        super::Identities::new(lowerer)
            .refuse_unsynthesised()
            .unwrap();
        Expressions::new(lowerer).propagate_manifests();
        while Expressions::new(lowerer).refuse_unrepresented().0 {
            Expressions::new(lowerer).propagate_manifests();
        }
        let mut sink = super::Sink::new(arena, origins, super::SinkTables::new());
        Expressions::new(lowerer).mint(&mut sink).unwrap();
    }

    #[test]
    fn a_declaration_minting_neither_half_is_refused_by_name_455()
    {
        let pbg = grammar();
        let tree = parsed(
            &pbg,
            SourceText::from("def f(x : Integer) -> -F Integer { return x }"),
        );
        let mut arena = CoreArena::new();
        let mut fuel = Fuel::new(LoweringBudget::DEFAULT);
        let collected = crate::module::collect(&pbg, &tree, &Unit::single(), &mut fuel).unwrap();
        let mut lowerer = super::Lowerer::new(&pbg, &tree, collected, fuel, Recognition::default());
        let mut origins = super::OriginTable::new();
        minted(&mut lowerer, &mut arena, &mut origins);
        let [ref slot] = *lowerer.cx.collected.slots
        else {
            panic!("`f` is the one declared name");
        };
        let Maybe::Present(half) = slot.definition
        else {
            panic!("`f` has a definition half");
        };
        // The two halves of the issue's `windHom`: the function tail's node
        // left unminted, with no refusal filed against the name.
        *lowerer
            .cx
            .lowered
            .get_mut(half.declaration.node)
            .expect("the definition half's node") = Maybe::Absent(super::lowered::Absent::Unminted);
        let declarations =
            ExpressionsRef::new(&lowerer).assemble(&mut origins, super::SlotIndex::from(0_usize));
        let [ref declaration] = *declarations
        else {
            panic!("`f` is assembled, not dropped: {declarations:?}");
        };
        let DeclarationOutcome::Refused(refusal) = declaration.outcome()
        else {
            panic!("`f` is refused: {:?}", declaration.outcome());
        };

        assert!(
            matches!(refusal, LoweringRefusal::Unminted { name, .. } if name == SurfaceName::from("f")),
            "the refusal names `f`: {refusal:?}"
        );
        assert_eq!(refusal.classify(), FailureClass::EngineFault);
    }

    #[test]
    fn a_written_definition_minting_no_body_is_refused_by_name_6113()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def f : Integer ; def f = 1 ;"));
        let mut arena = CoreArena::new();
        let mut fuel = Fuel::new(LoweringBudget::DEFAULT);
        let collected = crate::module::collect(&pbg, &tree, &Unit::single(), &mut fuel).unwrap();
        let mut lowerer = super::Lowerer::new(&pbg, &tree, collected, fuel, Recognition::default());
        let mut origins = super::OriginTable::new();
        minted(&mut lowerer, &mut arena, &mut origins);
        let [ref slot] = *lowerer.cx.collected.slots
        else {
            panic!("`f` is the one declared name");
        };
        let Maybe::Present(crate::module::Half {
            operand: crate::module::Operand::Written(body),
            ..
        }) = slot.definition
        else {
            panic!("`f` has a definition written as a value");
        };
        // The signature mints and the body does not, with no refusal filed
        // against the name: #6113's nested pair at a computed type.
        *lowerer
            .cx
            .lowered
            .get_mut(body.node)
            .expect("the body's node") = Maybe::Absent(super::lowered::Absent::Unminted);
        let declarations =
            ExpressionsRef::new(&lowerer).assemble(&mut origins, super::SlotIndex::from(0_usize));
        let [ref declaration] = *declarations
        else {
            panic!("`f` is assembled, not dropped: {declarations:?}");
        };
        let DeclarationOutcome::Refused(refusal) = declaration.outcome()
        else {
            panic!("`f` is refused, not owed: {:?}", declaration.outcome());
        };

        assert!(
            matches!(refusal, LoweringRefusal::Unminted { name, .. } if name == SurfaceName::from("f")),
            "the refusal names `f`: {refusal:?}"
        );
    }

    #[test]
    fn a_form_s_store_keys_stay_when_another_form_changes_5604()
    {
        // Each key the plans and the answers of `source` hold into a flat
        // store keyed by form, from `def two` on: the offset of the node
        // holding it from `def two`, the store, and the key. An omitted
        // implicit's ordinal counts as a key into `nominated`. The counts of
        // parameters and of operands the whole module pushes follow.
        let later_store_keys = |source: &str| {
            let pbg = grammar();
            let tree = parsed(&pbg, SourceText::from(source));
            let start = source.find("def two").expect("the source writes `def two`");
            let mut fuel = Fuel::new(LoweringBudget::DEFAULT);
            let collected = crate::module::collect(&pbg, &tree, &Unit::single(), &mut fuel)
                .expect("the module collects");
            let mut lowerer =
                super::Lowerer::new(&pbg, &tree, collected, fuel, Recognition::default());
            Expressions::new(&mut lowerer).declare();
            Expressions::new(&mut lowerer)
                .seed()
                .expect("the seed stays within the allowance");
            super::Exits::new(&mut lowerer)
                .survey()
                .expect("the survey stays within the allowance");
            Expressions::new(&mut lowerer)
                .classify()
                .expect("the classification stays within the allowance");
            let after = |node: gandr_surface_syntax::NodeIndex| -> Option<usize> {
                let node = tree.node(node)?;
                usize::from(node.span().start()).checked_sub(start)
            };
            let mut keys = Vec::new();
            for (node, plan) in lowerer.cx.plans.iter() {
                let Some(offset) = after(node)
                else {
                    continue;
                };
                let mut key = |store: &'static str, held: &dyn core::fmt::Debug| {
                    keys.push((offset, store, alloc::format!("{held:?}")));
                };
                if let super::Plan::Function(ref function) = *plan {
                    key("parameters", &function.parameters);
                    key("endpoints", &function.endpoints);
                    match function.body {
                        super::Body::Block(block) => key("statements", &block.statements),
                        super::Body::Clauses(case) => key("cases", &case),
                    }
                }
                if let super::Plan::Block(block)
                | super::Plan::Thunk(block)
                | super::Plan::Lambda(block, _) = *plan
                {
                    key("statements", &block.statements);
                }
                if let super::Plan::Interpolated(_, segments) = *plan {
                    key("segments", &segments);
                }
                if let super::Plan::Telescope(entries, _)
                | super::Plan::DependentArrow(entries, _)
                | super::Plan::Returns(entries)
                | super::Plan::RecordType(_, entries, ..) = *plan
                {
                    key("parameters", &entries);
                }
                if let super::Plan::Case(case) = *plan {
                    key("cases", &case);
                }
                if let super::Plan::Projected(projected) = *plan {
                    key("projected", &projected);
                }
                if let super::Plan::Application(_, held)
                | super::Plan::Tuple(held)
                | super::Plan::List(held)
                | super::Plan::Called(_, held)
                | super::Plan::StaticApplication(_, held)
                | super::Plan::Data(_, held) = *plan
                {
                    key("operands", &held);
                    let positions = ExpressionsRef::new(&lowerer).spread(held);
                    for position in positions.start .. positions.end {
                        if let Some(ordinal) = lowerer.cx.operands.locate(super::At::from(position))
                            && lowerer.cx.nominated.contains_key(&ordinal)
                        {
                            key("nominated", &ordinal);
                        }
                    }
                }
            }
            for (&node, answer) in &lowerer.cx.answers {
                if let (Some(offset), Maybe::Present(arm)) = (after(node), answer.arm) {
                    keys.push((offset, "arms", alloc::format!("{arm:?}")));
                }
            }
            keys.sort();

            let pushed = (
                usize::from(lowerer.cx.parameters.mark()),
                usize::from(lowerer.cx.operands.mark()),
            );
            (keys, pushed)
        };
        let (narrow, narrow_pushed) = later_store_keys(include_str!(
            "lower/unformatted/a-form-s-store-keys-stay-when-another-form-changes-5604-narrow.gandr"
        ));
        let (wide, wide_pushed) = later_store_keys(include_str!(
            "lower/unformatted/a-form-s-store-keys-stay-when-another-form-changes-5604-wide.gandr"
        ));
        assert!(
            wide_pushed.0 > narrow_pushed.0 && wide_pushed.1 > narrow_pushed.1,
            "the wide `one` pushes more parameters and more operands before `two`'s"
        );
        for store in [
            "parameters",
            "statements",
            "segments",
            "cases",
            "arms",
            "projected",
            "operands",
            "nominated",
        ] {
            assert!(
                narrow.iter().any(|&(_, held, _)| held == store),
                "`two` and `three` hold a key into `{store}`: {narrow:?}"
            );
        }
        assert_eq!(
            wide, narrow,
            "more entries in the first form leave every later form's keys where they were"
        );
    }

    #[test]
    fn a_block_binds_each_statement_over_the_next()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { let x = 1 ; let y = x ; return x } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[0]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(first, rest)) = arena.computation(suspended)
        else {
            panic!("the first statement is the outer bind");
        };
        let Some(&Computation::Bind(second, last)) = arena.computation(rest)
        else {
            panic!("the second statement binds over the rest of the block");
        };
        let returned = |id| match arena.computation(id) {
            Some(&Computation::Return(value)) => arena.value(value).cloned(),
            _ => None,
        };

        assert_eq!(
            [returned(first), returned(second), returned(last)],
            [
                Some(Value::Literal(integer(SourceFragment::from("1")))),
                Some(variable(0_u32)),
                Some(variable(1_u32)),
            ],
            "each statement's name binds over everything after it"
        );
        assert_eq!(
            module
                .origins()
                .computation(suspended)
                .map(|origin| origin.span()),
            Maybe::Present(at(16_usize, 19_usize)),
            "a bind's origin is its statement's `let`"
        );
    }

    /// `let` returns a value once and binds it, so the name reads the bind's
    /// binder; a computation it names is returned nested, for the checker to
    /// run when it returns and to suspend otherwise; a stated type ascribes
    /// the value it returns; a pattern splits the value it returns.
    #[test]
    fn a_let_binds_a_value_once_and_a_computation_nested()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(n : Integer) -> -F Integer { return n } \
                 def a = thunk { let x = 1 ; let y = x ; return y } ; \
                 def b = thunk { let m = f 1 ; return m } ; \
                 def c = thunk { let x : Integer = 1 ; return x } ; \
                 def d = thunk { let *{x, y} = *{1, 2} ; return y } ;",
            ),
            &mut arena,
        );
        let suspended = |position: usize| match arena.value(body_of(outcomes(&module)[position])) {
            Some(&Value::Thunk(suspended)) => suspended,
            other => panic!("a thunk lowers to a thunk value, not {other:?}"),
        };
        let returned = |id| match arena.computation(id) {
            Some(&Computation::Return(value)) => arena.value(value).cloned(),
            _ => None,
        };
        let bound = |id| match arena.computation(id) {
            Some(&Computation::Bind(bound, rest)) => (bound, rest),
            other => panic!("a let lowers to a bind, not {other:?}"),
        };
        let one = Value::Literal(integer(SourceFragment::from("1")));
        let binder = Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        };
        let (first, rest) = bound(suspended(1));
        let (second, last) = bound(rest);
        assert_eq!(
            [returned(first), returned(second), returned(last)],
            [
                Some(one.clone()),
                Some(binder.clone()),
                Some(binder.clone())
            ],
            "each value is returned once, and each name reads its bind's binder"
        );
        let (called, rest) = bound(suspended(2));
        assert!(
            matches!(
                returned(called),
                Some(Value::Nested(call))
                    if matches!(arena.computation(call), Some(&Computation::Application(..)))
            ),
            "the call is returned nested, for the checker to run or suspend"
        );
        assert_eq!(
            returned(rest),
            Some(binder.clone()),
            "and the name reads the bind's binder"
        );
        let (stated, rest) = bound(suspended(3));
        let ascribed = |value: Option<Value>| match value {
            Some(Value::Ascribe { value, .. }) => arena.value(value).cloned(),
            _ => None,
        };
        assert_eq!(
            [ascribed(returned(stated)), returned(rest)],
            [Some(one), Some(binder)],
            "the value ascribed its type is returned once, and the name reads the binder"
        );
        let (split, _) = bound(suspended(4));
        assert!(
            matches!(returned(split), Some(Value::Tuple(_))),
            "the tuple is returned to the split"
        );
    }

    #[test]
    fn each_named_binder_records_where_its_name_is_written()
    {
        let text = "def f(n : Integer) -> -F Integer { let m = n ; pure 2 ; return m }";
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(text), &mut arena);
        let Some(&Value::Thunk(lambda)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the function lowers to a thunk");
        };
        let Some(&Computation::Lambda(named)) = arena.computation(lambda)
        else {
            panic!("the parameter lowers to a lambda");
        };
        let Some(&Computation::Bind(_, discarded)) = arena.computation(named)
        else {
            panic!("the named statement is the outer bind");
        };
        let written = |opener| match module.origins().binder(opener) {
            Maybe::Present(origin) => {
                text.get(usize::from(origin.span().start()) .. usize::from(origin.span().end()))
            },
            Maybe::Absent(_) => None,
        };
        assert_eq!(
            written(lambda),
            Some("n"),
            "a parameter's lambda binds its name"
        );
        assert_eq!(
            written(named),
            Some("m"),
            "a named statement's bind binds its name"
        );
        assert_eq!(
            written(discarded),
            None,
            "a discarded statement's bind binds no name"
        );
    }

    /// `c ;` binds its value under a binder no name reaches and splits it as
    /// the unit, so a name bound before it is read one index further out
    /// after it, and the bind's origin is the discarded computation.
    #[test]
    fn a_discarded_statement_splits_its_unit()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { let x = 1 ; pure 2 ; return x } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(_, rest)) = arena.computation(suspended)
        else {
            panic!("the named statement is the outer bind");
        };
        let Some(&Computation::Bind(discarded, split)) = arena.computation(rest)
        else {
            panic!("the discarded statement binds over the rest of the block");
        };
        let Some(&Computation::Split {
            scrutinee,
            arity,
            motive: gandr_core_term::SplitMotive::Ambient,
            body,
        }) = arena.computation(split)
        else {
            panic!("the discarded value is split");
        };
        assert_eq!(arity, gandr_core_term::ComponentCount::default());
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        assert_eq!(arena.value(scrutinee), Some(&variable(0_u32)));
        let returned = |id| match arena.computation(id) {
            Some(&Computation::Return(value)) => arena.value(value).cloned(),
            _ => None,
        };
        assert_eq!(
            [returned(discarded), returned(body)],
            [
                Some(Value::Literal(integer(SourceFragment::from("2")))),
                Some(variable(1_u32)),
            ],
            "the name bound before the discard is read past its binder"
        );
        assert_eq!(
            module
                .origins()
                .computation(rest)
                .map(|origin| origin.span()),
            Maybe::Present(at(28_usize, 34_usize)),
            "a discarded statement's bind has its computation's origin"
        );
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { let x = 1 ; let _ = 2 ; return x } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(_, rest)) = arena.computation(suspended)
        else {
            panic!("the named statement is the outer bind");
        };
        let Some(&Computation::Bind(_, last)) = arena.computation(rest)
        else {
            panic!("the wildcard statement binds over the rest of the block");
        };
        assert!(
            matches!(arena.computation(last), Some(&Computation::Return(value)) if arena.value(value) == Some(&variable(1_u32))),
            "a wildcard binds at any type, with no split, and a name before it is read past it"
        );
    }

    /// A block-like form, a loop, an `if`, a block or an access closing on its
    /// block, followed by another statement needs no `;`, as Rust reads one;
    /// one before the block's `}` is still its last computation.
    #[test]
    fn a_block_like_statement_needs_no_semicolon()
    {
        use crate::lower::native::tests::assert_accepted;
        use crate::lower::native::tests::judged;
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-block-like-statement-needs-no-semicolon-module.gandr"
            )),
            &mut arena,
        );
        assert_accepted(&judged(&module, &mut arena));
    }

    /// `let (q, r) = c ;` binds the tuple under a binder no name reaches and
    /// splits it, the first component outermost, so `q` is read one index
    /// further out than `r`.
    #[test]
    fn a_tuple_binder_splits_the_returned_tuple_in_order()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { let *{q, r} = *{1, 2} ; return *{r, q} } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(_, split)) = arena.computation(suspended)
        else {
            panic!("the statement binds over the rest of the block");
        };
        let Some(&Computation::Split {
            scrutinee,
            arity,
            motive: gandr_core_term::SplitMotive::Ambient,
            body,
        }) = arena.computation(split)
        else {
            panic!("the bound tuple is split");
        };
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        assert_eq!(arity, gandr_core_term::ComponentCount::from(2_usize));
        assert_eq!(arena.value(scrutinee), Some(&variable(0_u32)));
        let Some(&Computation::Return(returned)) = arena.computation(body)
        else {
            panic!("the block's last computation returns");
        };
        let Some(returned) = arena.value(returned)
        else {
            panic!("the returned value is minted");
        };
        let Value::Tuple(ref components) = *returned
        else {
            panic!("a pair is returned");
        };
        assert_eq!(
            components
                .iter()
                .map(|&component| arena.value(component).cloned())
                .collect::<Vec<_>>(),
            [Some(variable(0_u32)), Some(variable(1_u32))],
            "`r` is the innermost binder and `q` the one outside it"
        );
    }

    /// #2181: each component a `let` tuple pattern writes names the binder
    /// its split opens at that place, whether or not the rest of the block
    /// reads it, a wildcard included.
    #[test]
    fn a_tuple_binder_names_each_component_it_writes_2181()
    {
        use crate::origin::ComponentName;
        use crate::origin::SplitComponent;

        let source = SourceText::from("def a = thunk { let *{q, _, r} = *{1, 2, 3} ; return r } ;");
        let mut arena = CoreArena::new();
        let module = lowered(source, &mut arena);
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(_, split)) = arena.computation(suspended)
        else {
            panic!("the statement binds over the rest of the block");
        };
        let named: Vec<Option<&str>> = (0_usize .. 3_usize)
            .map(|component| {
                match module
                    .origins()
                    .component(split, SplitComponent::from(component))
                {
                    Maybe::Present(&ComponentName::Written(origin)) => {
                        source.fragment(origin.span()).ok().map(<&str>::from)
                    },
                    Maybe::Present(&ComponentName::Labelled(_)) | Maybe::Absent(_) => None,
                }
            })
            .collect();
        assert_eq!(
            named,
            [Some("q"), Some("_"), Some("r")],
            "each component is named where the pattern writes it"
        );
    }

    /// `let q : Integer = { pure 1 } ;` binds the block ascribed the pure
    /// returner of the written type, and the rest of the block reads `q` as
    /// the bind's own binder.
    #[test]
    fn a_typed_bind_ascribes_its_computation()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { let q : Integer = { pure 1 } ; return q } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(bound, rest)) = arena.computation(suspended)
        else {
            panic!("the statement binds over the rest of the block");
        };
        let Some(&Computation::Ascribe { body, ty }) = arena.computation(bound)
        else {
            panic!("the bound computation is ascribed");
        };
        assert!(
            matches!(arena.computation(body), Some(&Computation::Return(value)) if arena.value(value) == Some(&Value::Literal(integer(SourceFragment::from("1"))))),
            "the written computation is the one ascribed"
        );
        assert!(
            matches!(arena.comp_type(ty), Some(&CompType::Returner { result, ref effects }) if arena.value_type(result) == Some(&ValueType::Base(BaseType::Integer)) && *effects == gandr_core_term::effect::EffectRow::EMPTY),
            "the ascription is the pure returner of the written type"
        );
        assert!(
            matches!(arena.computation(rest), Some(&Computation::Return(value)) if arena.value(value) == Some(&Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) })),
            "the rest reads the name as the bind's binder"
        );
    }

    /// A tuple pattern written with a type ascribes its bound computation the
    /// pure returner of that type, then splits the tuple it returns into one
    /// name per component (#1543).
    #[test]
    fn a_typed_tuple_binder_ascribes_and_splits_1543()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a = thunk { let *{y, z} : Integer * Integer = *{1, 2} ; return y } ;",
            ),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(bound, rest)) = arena.computation(suspended)
        else {
            panic!("the statement binds over the rest of the block");
        };
        let Some(&Computation::Ascribe { ty, .. }) = arena.computation(bound)
        else {
            panic!("the bound computation is ascribed");
        };
        assert!(
            matches!(arena.comp_type(ty), Some(&CompType::Returner { result, .. }) if matches!(arena.value_type(result), Some(ValueType::Product(components)) if components.len() == 2_usize)),
            "the ascription returns the written product"
        );
        assert!(
            matches!(arena.computation(rest), Some(&Computation::Split { scrutinee, arity, .. }) if arity == gandr_core_term::ComponentCount::from(2_usize) && arena.value(scrutinee) == Some(&Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) })),
            "the rest splits the bound tuple into its two names"
        );
    }

    #[test]
    fn a_block_standing_as_a_computation_binds_its_statements()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { { let x = 1 ; return x } } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(first, last)) = arena.computation(suspended)
        else {
            panic!("the inner block's statement binds over its last computation");
        };
        assert!(
            matches!(arena.computation(first), Some(&Computation::Return(value)) if arena.value(value) == Some(&Value::Literal(integer(SourceFragment::from("1"))))),
            "the statement runs first"
        );
        assert!(
            matches!(arena.computation(last), Some(&Computation::Return(value)) if arena.value(value) == Some(&Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(0_u32) })),
            "the last computation reads the statement's binder"
        );
        let module = lowered(
            SourceText::from("def b = thunk { return { pure 1 } } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Return(returned)) = arena.computation(suspended)
        else {
            panic!("the exit returns its operand");
        };
        assert!(
            matches!(arena.value(returned), Some(&Value::Nested(nested)) if matches!(arena.computation(nested), Some(&Computation::Return(_)))),
            "a block where a value is read stands nested, for the checker to run"
        );
        assert_eq!(
            module
                .origins()
                .value(returned)
                .map(|inserted| (inserted.provenance(), inserted.span())),
            Maybe::Present((
                Provenance::Inserted(Insertion::Nested),
                at(23_usize, 33_usize)
            )),
            "the nesting is the lowering's, at the block whose position demanded it"
        );
    }

    #[test]
    fn a_call_applies_its_arguments_left_to_right()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = thunk { fun (x) { fun (y) { return x } } } ; def h = thunk { become g 1 2 } ; \
                 def k = thunk { become g () } ;",
            ),
            &mut arena,
        );
        let called = |declaration: usize| {
            let Some(&Value::Thunk(suspended)) =
                arena.value(body_of(outcomes(&module)[declaration]))
            else {
                panic!("the thunk lowers to a thunk value");
            };
            suspended
        };
        let Some(&Computation::Application(inner, second)) = arena.computation(called(1_usize))
        else {
            panic!("the last argument is the outer application");
        };
        let Some(&Computation::Application(head, first)) = arena.computation(inner)
        else {
            panic!("the first argument is the inner application");
        };

        assert_eq!(
            [first, second].map(|id| arena.value(id).cloned()),
            [
                Some(Value::Literal(integer(SourceFragment::from("1")))),
                Some(Value::Literal(integer(SourceFragment::from("2")))),
            ],
            "the arguments apply left to right"
        );
        assert!(
            matches!(arena.computation(head), Some(&Computation::Force(_))),
            "the head is applied to the first argument"
        );
        assert!(
            matches!(
                arena.computation(called(2_usize)),
                Some(&Computation::Force(_))
            ),
            "a call of no arguments is its head"
        );
    }

    #[test]
    fn a_call_argument_and_an_inferring_call_lower_4853()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = thunk { fun (x) { fun (y) { return x } } } ; def nested = thunk { become \
                 g (g 1 2) 3 } ; def first[a : Type, b : Type](x : a, y : b) -> -F a { return x } \
                 ; def inferred = thunk { become first 5 7 } ;",
            ),
            &mut arena,
        );
        let outcome = |wanted: &str| {
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .map(LoweredDeclaration::outcome)
        };
        for (name, reason) in [
            ("nested", "a call inside an argument is its own call"),
            (
                "inferred",
                "a juxtaposed call of two arguments infers the implicits it omits",
            ),
        ] {
            assert!(
                matches!(outcome(name), Some(DeclarationOutcome::Bodied { .. })),
                "{reason}: {:?}",
                outcome(name)
            );
        }
    }

    /// #5326: a signature that applies a family by juxtaposition lowers to the
    /// type its call form lowers to, and a returner inside an expression
    /// applies its family the same way.
    #[test]
    fn a_type_applies_its_family_by_juxtaposition_5326()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-type-applies-its-family-by-juxtaposition-5326-module.gandr"
            )),
            &mut arena,
        );
        let outcome = |name: &str| {
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == name)
                .map(LoweredDeclaration::outcome)
        };
        let declared = |name: &str| match outcome(name) {
            Some(DeclarationOutcome::Completed { declared_type, .. }) => declared_type,
            other => panic!("`{name}` lowers its type and its body: {other:?}"),
        };
        assert_eq!(
            gandr_core_term::equal_type_syntax(&arena, declared("juxtaposed"), declared("called")),
            gandr_core_term::CertificateEquality::Equal,
            "`Vec Integer (Succ Zero)` lowers as `Vec(Integer, Succ(Zero))`"
        );
        assert!(
            matches!(outcome("opt"), Some(DeclarationOutcome::Completed { .. })),
            "`-F Maybe A` inside an expression lowers: {:?}",
            outcome("opt")
        );
    }

    #[test]
    fn a_product_binder_splits_as_the_tuple_binder_4853()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def tupled = thunk { let *{q, r} = *{1, 2} ; return r } ; def braced = thunk { \
                 let *{q, r} = *{1, 2} ; return r } ; def three = thunk { let *{a, _, c} = *{1, 2, \
                 3} ; return a } ; def three_braced = thunk { let *{a, _, c} = *{1, 2, 3} ; return \
                 a } ;",
            ),
            &mut arena,
        );
        let body = |wanted: &str| {
            let declaration = module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"));
            let DeclarationOutcome::Bodied { body } = declaration.outcome()
            else {
                panic!("`{wanted}` lowers to a body");
            };
            body
        };
        for (braced, tupled, reason) in [
            ("braced", "tupled", "positional components"),
            ("three_braced", "three", "three components, one a wildcard"),
        ] {
            assert_eq!(
                gandr_core_term::equal_certificate_syntax(&arena, body(braced), body(tupled)),
                gandr_core_term::CertificateEquality::Equal,
                "{reason}"
            );
        }
    }

    #[test]
    fn a_def_head_s_shared_names_are_its_parameters_written_apart_4853()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-def-head-s-shared-names-are-its-parameters-written-apart-4853-module.gandr"
            )),
            &mut arena,
        );
        let completed = |wanted: &str| {
            let declaration = module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"));
            let DeclarationOutcome::Completed {
                declared_type,
                body,
            } = declaration.outcome()
            else {
                panic!("`{wanted}` completes");
            };
            (declared_type, body)
        };
        for (shared, apart, reason) in [
            ("shared", "apart", "two names that share a type"),
            (
                "bound",
                "bound_apart",
                "two names that share a type the head binds",
            ),
            (
                "three",
                "three_apart",
                "three names that share a type after one of their own",
            ),
            (
                "linked",
                "linked_apart",
                "two names that share a type a later type names",
            ),
        ] {
            let ((shared_type, shared_body), (apart_type, apart_body)) =
                (completed(shared), completed(apart));
            let (shared_type, apart_type) = (
                arena.value_quote(shared_type),
                arena.value_quote(apart_type),
            );
            assert_eq!(
                (
                    gandr_core_term::equal_certificate_syntax(&arena, shared_type, apart_type),
                    gandr_core_term::equal_certificate_syntax(&arena, shared_body, apart_body),
                ),
                (
                    gandr_core_term::CertificateEquality::Equal,
                    gandr_core_term::CertificateEquality::Equal
                ),
                "{reason} declare and define what the parameters written apart do"
            );
        }
    }

    #[test]
    fn a_laid_out_body_is_the_braced_body_4853()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-laid-out-body-is-the-braced-body-4853-module.gandr"
            )),
            &mut arena,
        );
        let body = |wanted: &str| {
            let declaration = module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"));
            body_of(declaration.outcome())
        };
        assert_eq!(
            gandr_core_term::equal_certificate_syntax(&arena, body("laid"), body("braced")),
            gandr_core_term::CertificateEquality::Equal,
            "a body in layout, its arms led by bars, is the braced body with its `;` and `,`"
        );
    }

    #[test]
    fn a_call_of_no_arguments_is_the_call_the_source_wrote_364()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        // `g ()` at 52..56 with its head at 52..53; `M.z ()` at 138..144 with
        // its head at 138..141.
        let module = lowered(
            SourceText::from(
                "def g = thunk { return 1 } ; def k = thunk { become g () } ; \
                 module M where { def z() -> -F Integer { return 0 } } \
                 def m = thunk { become M.z () } ;",
            ),
            &mut arena,
        );
        let called = |wanted: &str| {
            let declaration = module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"));
            let Some(&Value::Thunk(suspended)) = arena.value(body_of(declaration.outcome()))
            else {
                panic!("`{wanted}` lowers to a thunk value");
            };
            let Some(&Computation::Force(forced)) = arena.computation(suspended)
            else {
                panic!("`{wanted}`'s call of no arguments forces its head");
            };
            (
                module
                    .origins()
                    .computation(suspended)
                    .map(|origin| (origin.provenance(), origin.span())),
                module.origins().value(forced).map(|origin| origin.span()),
            )
        };
        assert_eq!(
            called("k"),
            (
                Maybe::Present((Provenance::Written, at(52_usize, 56_usize))),
                Maybe::Present(at(52_usize, 53_usize)),
            ),
            "the force is the call the source wrote, and its head stays at the head"
        );
        assert_eq!(
            called("m"),
            (
                Maybe::Present((Provenance::Written, at(138_usize, 144_usize))),
                Maybe::Present(at(138_usize, 141_usize)),
            ),
            "a module member called with no arguments answers at its call too"
        );
    }

    #[test]
    fn a_value_head_is_forced_and_marked_inserted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = thunk { fun (x) { return x } } ; def h = thunk { become g 1 } ;",
            ),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[1]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, _argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the value head is forced");
        };
        let origin = module.origins().computation(head);

        assert_eq!(
            arena.value(forced),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "the force is over the name the source wrote"
        );
        assert_eq!(
            origin.map(|inserted| inserted.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Force)),
            "the force is the lowering's, not the source's"
        );
        assert_eq!(
            origin.map(|inserted| inserted.span()),
            Maybe::Present(at(64_usize, 65_usize)),
            "the inserted force names the head whose position demanded it"
        );
    }

    #[test]
    fn an_author_written_force_is_not_marked_inserted()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { become (force g) 3 } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[1]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, _argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the written force is the head");
        };

        assert!(
            matches!(arena.value(forced), Some(&Value::Constant(_))),
            "a computation head gains no second force"
        );
        assert_eq!(
            module
                .origins()
                .computation(head)
                .map(|written| written.provenance()),
            Maybe::Present(Provenance::Written),
            "the force the source wrote is the source's"
        );
    }

    #[test]
    fn a_positive_result_gains_a_returner_once()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(x : Integer) -> Integer { return x } def g(x : Integer) -> -F Integer { return x }",
            ),
            &mut arena,
        );
        let result = |declaration: usize| {
            let declared = declared_of(outcomes(&module)[declaration]);
            let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
            else {
                panic!("the declared type is a thunk type");
            };
            let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(suspended)
            else {
                panic!("the parameter is an arrow");
            };
            let Some(&CompType::Returner {
                result: returned, ..
            }) = arena.comp_type(codomain)
            else {
                panic!("the result is a returner");
            };
            (
                arena.value_type(returned).cloned(),
                module
                    .origins()
                    .comp_type(codomain)
                    .map(|origin| origin.provenance()),
            )
        };

        assert_eq!(
            result(0_usize),
            (
                Some(ValueType::Base(BaseType::Integer)),
                Maybe::Present(Provenance::Inserted(Insertion::Returner))
            ),
            "a value type at the result gains the lowering's returner"
        );
        assert_eq!(
            result(1_usize),
            (
                Some(ValueType::Base(BaseType::Integer)),
                Maybe::Present(Provenance::Written)
            ),
            "a written returner is the only one, and the source's"
        );
    }

    #[test]
    fn a_self_reference_is_unresolved()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = a ;")),
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("a"),
            },
            "a declaration is not in scope in its own body"
        );
    }

    #[test]
    fn an_undefined_term_name_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = b ;")),
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("b"),
            },
            "a name nothing declares is refused where it stands"
        );
    }

    #[test]
    fn a_dotted_builtin_path_reads_as_its_primitive()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def d = int.div ;\n"), &mut arena);
        assert!(
            matches!(
                arena.value(body_of(outcomes(&module)[0])),
                Some(&Value::Primitive { .. })
            ),
            "`int.div` projects no module: it names the builtin primitive"
        );
    }

    /// A name nothing declares, written inside any former, refuses the
    /// declaration with the refusal of the name itself, located where it is
    /// written: no former around it answers in its place.
    #[test]
    fn a_name_nothing_declares_refuses_through_every_former_around_it()
    {
        let rows = [
            "def a : *{x : Zz} ;",
            "def a : *{x : Integer, y : Zz} ;",
            "def a : Integer * Zz ;",
            "def a : List(Zz) ;",
            "def a : +U (Zz -> -F Integer) ;",
            "def a : +U (Integer -> -F Zz) ;",
            "def a : (x : Zz) -> Integer ;",
            "def a : (x : Integer) -> Zz ;",
            "def a : Zz -> Integer ;",
            "def a : Path[.A = Zz](1, 1) ;",
            "def a = *{1, zz} ;",
            "def a = #[1, zz] ;",
            "def a = thunk { return zz } ;",
            "def a = thunk { let x = zz ; return x } ;",
            "def a = thunk { fun (x) { return zz } } ;",
            "def a = thunk { match 1 { | 1 => return zz | _ => return 0 } } ;",
        ];
        for source in rows {
            // `List` is listed from its home, so only `Zz` goes unresolved.
            let text = crate::fixture::listing(source);
            let module = crate::fixture::listed(&text, &mut CoreArena::new());
            let first = outcomes(&module).first().copied();
            let Some(DeclarationOutcome::Refused(
                LoweringRefusal::UnresolvedName { span, name }
                | LoweringRefusal::UnresolvedTypeHead { span, name, .. },
            )) = first
            else {
                panic!("`{source}` is refused at its name, not {first:?}");
            };
            let spelled = (
                text.get(usize::from(span.start()) .. usize::from(span.end())),
                name,
            );
            assert!(
                matches!(spelled, (Some(written), name) if written.eq_ignore_ascii_case("zz") && name.as_ref() == written),
                "`{source}` names the unresolved name where it is written: {spelled:?}"
            );
        }
    }

    #[test]
    fn an_undefined_type_head_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def a : Intgr ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 13_usize),
                head: at(8_usize, 13_usize),
                name: SurfaceName::from("Intgr"),
                arity: HeadArity::Nullary,
            },
            "a misspelt head is a mistake, not a new nominal type"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an unresolved head is the author's mistake"
        );
    }

    #[test]
    fn an_applied_nullary_head_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Unit Integer ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 20_usize),
                head: at(8_usize, 12_usize),
                name: SurfaceName::from("Unit"),
                arity: HeadArity::Unary,
            },
            "a type a second type follows applies to it (#5326), and no unary former is \
             named `Unit`; the refusal marks the application and names its head"
        );
    }

    #[test]
    fn an_applied_head_no_former_answers_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Foo(Integer) ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 20_usize),
                head: at(8_usize, 11_usize),
                name: SurfaceName::from("Foo"),
                arity: HeadArity::Unary,
            },
            "a head applied to one argument is looked up among the unary formers"
        );
        assert_eq!(
            refusal(SourceText::from("def a : Foo(Integer, String) ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 28_usize),
                head: at(8_usize, 11_usize),
                name: SurfaceName::from("Foo"),
                arity: HeadArity::Polyadic(OperandCount::from(2_usize)),
            },
            "no former takes two arguments, and the refusal says how many were written"
        );
    }

    /// One node of a core type, as [`spine`] walks it.
    ///
    /// # Specification
    /// - requires: identifiers are interpreted in the supplied arena.
    /// - ensures: the pending work retains whether the next node is a value or
    ///   computation type.
    /// - provides: a family-tagged traversal stack for the supported type
    ///   fragment.
    /// - fails: none as a data value.
    /// - panics: none.
    /// - executable: none — the arena and traversal stack are absent; `spine`
    ///   checks the root token and its witnesses observe the ordered structure.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the named semantic goldens — thunk, returner and
    ///   arrow nodes are traversed across both type families.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
    #[derive(Clone, Copy)]
    enum TypeNode
    {
        /// A value type.
        Value(ValueTypeId),
        /// A computation type.
        Computation(CompTypeId),
    }

    /// The type at `root`, in pre-order, one token per former, so two types
    /// minted at different arena positions compare by structure.
    ///
    /// # Specification
    /// - requires: an acyclic type graph rooted in the supplied arena.
    /// - ensures: preorder tokens preserve the supported thunk, returner,
    ///   arrow, product and sum structure; unsupported or absent nodes are
    ///   terminal diagnostic tokens.
    /// - provides: an arena-coordinate-independent comparison for the supported
    ///   type fragment.
    /// - fails: never; this is not a complete serialization of every core type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the supported fragment only — explicit
    ///   thunk/returner and arrow/product spellings yield pinned semantic
    ///   preorder tokens; unsupported nodes are not claimed to have a
    ///   structural encoding.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
    #[spec(
        ensures: |ret| match arena.value_type(root) {
            | Some(&ValueType::Thunk(_)) => ret.first().is_some_and(|token| token == "U"),
            | Some(&ValueType::Product(ref parts)) if parts.is_empty() => ret.first().is_some_and(|token| token == "Unit"),
            | Some(&ValueType::Product(_)) => ret.first().is_some_and(|token| token == "*"),
            | _ => true,
        },
    )]
    fn spine(
        arena: &CoreArena,
        root: ValueTypeId,
    ) -> Vec<String>
    {
        let mut pending = vec![TypeNode::Value(root)];
        let mut tokens = Vec::new();
        while let Some(next) = pending.pop() {
            match next {
                TypeNode::Value(at) => match arena.value_type(at) {
                    Some(&ValueType::Base(base)) => tokens.push(format!("{base:?}")),
                    Some(&ValueType::Product(ref parts)) if parts.is_empty() => {
                        tokens.push(String::from("Unit"));
                    },
                    Some(&ValueType::Thunk(inner)) => {
                        tokens.push(String::from("U"));
                        pending.push(TypeNode::Computation(inner));
                    },
                    Some(&ValueType::Product(ref parts)) => {
                        tokens.push(String::from("*"));
                        pending.extend(parts.iter().rev().map(|&part| TypeNode::Value(part)));
                    },
                    Some(&ValueType::Sum(ref parts)) => {
                        tokens.push(String::from("+"));
                        pending.extend(parts.iter().rev().map(|&part| TypeNode::Value(part)));
                    },
                    other => tokens.push(format!("{other:?}")),
                },
                TypeNode::Computation(at) => match arena.comp_type(at) {
                    Some(&CompType::Returner { result: inner, .. }) => {
                        tokens.push(String::from("F"));
                        pending.push(TypeNode::Value(inner));
                    },
                    Some(&CompType::Arrow { domain, codomain }) => {
                        tokens.push(String::from("->"));
                        pending.push(TypeNode::Computation(codomain));
                        pending.push(TypeNode::Value(domain));
                    },
                    other => tokens.push(format!("{other:?}")),
                },
            }
        }

        tokens
    }

    #[test]
    fn the_alias_is_the_thunked_arrow()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a : Integer -> String ; def b : +U (Integer -> -F String) ; def c : \
                 (Integer, String) -> Unit ; def d : +U (Integer -> String -> -F Unit) ; def e \
                 : Integer -> (Integer -> String) ; def f : +U (Integer -> -F (+U (Integer -> -F \
                 String))) ; def g : () -> String ; def h : +U (-F String) ; def i : Unit -> \
                 String ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let declared = |at: usize| spine(&arena, declared_of(lowered[at]));

        assert_eq!(
            declared(0_usize),
            ["U", "->", "Integer", "F", "String"],
            "`A -> B` lowers to the thunked arrow into the returner"
        );
        assert_eq!(
            declared(0_usize),
            declared(1_usize),
            "and is the same core type the thunked arrow spells"
        );
        assert_eq!(
            declared(2_usize),
            declared(3_usize),
            "a domain list curries left to right under one thunk"
        );
        assert_eq!(
            declared(4_usize),
            declared(5_usize),
            "the box nests to the right, each level its own thunk"
        );
        assert_eq!(
            declared(6_usize),
            ["U", "F", "String"],
            "`() -> C` takes no argument"
        );
        assert_eq!(
            declared(6_usize),
            declared(7_usize),
            "and is the thunked returner itself"
        );
        assert_eq!(
            declared(8_usize),
            ["U", "->", "Unit", "F", "String"],
            "`Unit -> C` takes the unit value, a type of its own"
        );
        assert_eq!(
            refusal(SourceText::from("def z : (Integer, String) ;")),
            LoweringRefusal::MalformedForm {
                span: at(16_usize, 17_usize),
                form: FormName::from(NamedKind("parenthesized_type")),
                fault: FormFault::MisplacedTile,
            },
            "a type list anywhere but before an arrow is refused at its first comma"
        );
        assert_eq!(
            refusal(SourceText::from("def z : Integer -> Integer -> String ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 36_usize),
                form: FormName::from(NamedKind("function_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::ChainedArrow,
            },
            "arrows do not chain: the source writes one group or the output in parentheses"
        );
    }

    #[test]
    fn a_quoted_arrow_is_the_box_its_thunk_spells_4853()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def boxed = thunk { return type(Integer -> String) } ; def thunked = thunk { \
                 return type(+U (Integer -> -F String)) } ; def grouped = thunk { return \
                 type((Integer, String) -> (Integer -> String)) } ; def thunked_grouped = thunk { \
                 return type(+U (Integer -> String -> -F (+U (Integer -> -F String)))) } ; def \
                 computed = thunk { return type(Integer -> -F String) } ;",
            ),
            &mut arena,
        );
        let body = |wanted: &str| {
            let declaration = module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"));
            let DeclarationOutcome::Bodied { body } = declaration.outcome()
            else {
                panic!("`{wanted}` lowers to a body");
            };
            body
        };
        for (arrow, thunked, reason) in [
            (
                "boxed",
                "thunked",
                "a quoted arrow over a value type is the box",
            ),
            (
                "grouped",
                "thunked_grouped",
                "a quoted box of a group whose output is a box",
            ),
        ] {
            assert_eq!(
                gandr_core_term::equal_certificate_syntax(&arena, body(arrow), body(thunked)),
                gandr_core_term::CertificateEquality::Equal,
                "{reason}"
            );
        }
        assert_ne!(
            gandr_core_term::equal_certificate_syntax(&arena, body("computed"), body("boxed")),
            gandr_core_term::CertificateEquality::Equal,
            "a quoted arrow over a returner stays the computation arrow"
        );
    }

    #[test]
    fn a_box_passes_a_lambda_applies_states_a_motive_and_matches_its_columns_4853()
    {
        let source = include_str!(
            "lower/fixtures/a-box-passes-a-lambda-applies-states-a-motive-and-matches-its-columns-4853.gandr"
        );
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        for (name, reason) in [
            (
                "used",
                "a lambda passed for a box is a function value, never a type operator",
            ),
            ("twice", "an implicit box applies as the box"),
            ("moved", "a family a box states is a motive"),
            (
                "plus",
                "a clause definition over a box matches one column per input",
            ),
        ] {
            let outcome = module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == name)
                .map(LoweredDeclaration::outcome);
            assert!(
                matches!(
                    outcome,
                    Some(DeclarationOutcome::Completed { .. } | DeclarationOutcome::Bodied { .. })
                ),
                "{reason}: {outcome:?}"
            );
        }
        crate::lower::native::tests::assert_accepted(&crate::lower::native::tests::judged(
            &module, &mut arena,
        ));
    }

    #[test]
    fn an_arrow_where_a_value_type_is_read_is_a_static_pi()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def t : (Type -> Type[-]) -> Type -> Type ;"),
            &mut arena,
        );
        let universe = |id, sort| {
            arena.value_type(id)
                == Some(&ValueType::Universe {
                    sort: Sort::Ground(sort),
                    level: Level::constant(LevelConstant::ZERO),
                })
        };
        let pi = |id| match arena.value_type(id) {
            Some(&ValueType::StaticPi { domain, codomain }) => Some((domain, codomain)),
            _ => None,
        };
        let Some((family, rest)) = pi(declared_of(outcomes(&module)[0]))
        else {
            panic!("an arrow where a value type is read is a static Pi");
        };
        let Some((family_domain, family_codomain)) = pi(family)
        else {
            panic!("the grouped domain is a static Pi of its own");
        };
        let Some((carrier, result)) = pi(rest)
        else {
            panic!("the codomain nests to the right");
        };
        assert!(
            universe(family_domain, GroundSort::Value)
                && universe(family_codomain, GroundSort::Computation)
                && universe(carrier, GroundSort::Value)
                && universe(result, GroundSort::Value),
            "every operand is the universe it spells"
        );
    }

    #[test]
    fn an_arrow_from_a_universe_to_a_value_type_is_the_box_5203()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def chosen : Type -> Integer ; def operator : Type -> Type ;"),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let universe = |id| {
            matches!(
                arena.value_type(id),
                Some(&ValueType::Universe {
                    sort: Sort::Ground(GroundSort::Value),
                    ..
                })
            )
        };
        let boxed = match arena.value_type(declared_of(lowered[0])) {
            Some(&ValueType::Thunk(arrow)) => match arena.comp_type(arrow) {
                Some(&CompType::Arrow { domain, codomain }) => {
                    universe(domain)
                        && matches!(
                            arena.comp_type(codomain),
                            Some(&CompType::Returner { result, .. })
                                if arena.value_type(result) == Some(&ValueType::Base(BaseType::Integer))
                        )
                },
                _ => false,
            },
            _ => false,
        };
        assert!(
            boxed,
            "an arrow from a universe to a value type is the box `+U (Type -> -F Integer)`"
        );
        assert!(
            matches!(
                arena.value_type(declared_of(lowered[1])),
                Some(&ValueType::StaticPi { domain, codomain }) if universe(domain) && universe(codomain)
            ),
            "an arrow between universes stays the static Pi"
        );
    }

    #[test]
    fn a_lazy_product_is_a_computation_type()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : -F Integer & -F Integer ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 31_usize),
                form: FormName::from(NamedKind("lazy_product_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "the lazy product is no value type: it stands under `+U`"
        );
    }

    #[test]
    fn a_grouped_form_of_the_wrong_sort_is_refused_at_its_parentheses_2341()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let value_as_computation = |span| LoweringRefusal::OutOfFragment {
            span,
            form: FormName::from(NamedKind("number")),
            sort: FragmentSort::Computation,
            boundary: FragmentBoundary::WrongSort,
        };

        assert_eq!(
            refusal(SourceText::from("def b = thunk { return run (1) } ;")),
            value_as_computation(at(27_usize, 30_usize)),
            "the parentheses stand where the computation is read, so they are what is refused"
        );
        assert_eq!(
            refusal(SourceText::from("def b = thunk { return run ((1)) } ;")),
            value_as_computation(at(27_usize, 32_usize)),
            "nested groupings are refused at the outermost"
        );
        assert_eq!(
            refusal(SourceText::from("def a : (-F Integer & -F Integer) ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 33_usize),
                form: FormName::from(NamedKind("lazy_product_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "a grouped computation type where a value type is read is refused at its parentheses"
        );
        assert!(
            matches!(
                refusal(SourceText::from("def b = thunk { return run type(Integer) } ;")),
                LoweringRefusal::OutOfFragment {
                    span,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::WrongSort,
                    ..
                } if span == at(27_usize, 40_usize)
            ),
            "a type quote stands where the computation is read, so it is what is refused"
        );
    }

    #[test]
    fn a_quoted_term_is_refused_at_its_quote_2341()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let block_as_type = |span| LoweringRefusal::OutOfFragment {
            span,
            form: FormName::from(NamedKind("block")),
            sort: FragmentSort::ValueType,
            boundary: FragmentBoundary::WrongSort,
        };

        assert_eq!(
            refusal(SourceText::from("def code = Flow.stay (type({Unit})) ;")),
            block_as_type(at(22_usize, 34_usize)),
            "a labelled sum with its `+` left out quotes a block, refused at the quote, which \
             touches where the `+` stood, not at the statement inside it"
        );
    }

    #[test]
    fn a_computation_codomain_of_a_box_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Integer -> -F Integer ;")),
            LoweringRefusal::OutOfFragment {
                span: at(19_usize, 29_usize),
                form: FormName::from(NamedKind("f_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "an arrow between value types is the box, whose output is a value type"
        );
    }

    #[test]
    fn the_eager_product_and_pair_lower_to_their_formers()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def p : Integer * String ; def q = *{1, \"a\"} ; def r : Integer * Unit * String ; \
                 def s = *{1, *{}, \"a\"} ; def l : (Integer * Unit) * String ; def m : Integer \
                 * (Unit * String) ; def o = *{1,} ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let one = Value::Literal(integer(SourceFragment::from("1")));
        let letter = Value::Literal(text(SourceFragment::from("a")));
        let members = |id| {
            arena
                .value(id)
                .and_then(Value::components)
                .map(|components| {
                    components
                        .iter()
                        .map(|&component| arena.value(component))
                        .collect::<Vec<_>>()
                })
        };
        let parts = |id| match arena.value_type(id) {
            Some(&ValueType::Product(ref parts)) => Some(parts.to_vec()),
            _ => None,
        };
        let spines = |id| {
            parts(id)
                .unwrap_or_default()
                .into_iter()
                .map(|part| spine(&arena, part).join(" "))
                .collect::<Vec<_>>()
        };

        assert_eq!(
            spines(declared_of(lowered[0])),
            ["Integer", "String"],
            "`A * B` lowers to the product of its operands"
        );
        assert_eq!(
            members(body_of(lowered[1])),
            Some(vec![Some(&one), Some(&letter)]),
            "a comma list where a value is read is one tuple holding its members in order"
        );
        assert_eq!(
            spines(declared_of(lowered[2])),
            ["Integer", "Unit", "String"],
            "an unparenthesized chain is one product of three components"
        );
        assert_eq!(
            members(body_of(lowered[3])),
            Some(vec![Some(&one), Some(&Value::unit()), Some(&letter)]),
            "a tuple of three is one node, each member at its place"
        );
        assert_eq!(
            spines(declared_of(lowered[4])),
            ["* Integer Unit", "String"],
            "a parenthesized product on the left stays one component"
        );
        assert_eq!(
            spines(declared_of(lowered[5])),
            ["Integer", "* Unit String"],
            "a parenthesized product on the right stays one component"
        );
        assert_eq!(
            members(body_of(lowered[6])),
            Some(vec![Some(&one)]),
            "`(v,)` is the tuple of one component, not `v`"
        );
        assert_eq!(
            refusal(SourceText::from("def t : +U (Integer * Integer) ;")),
            LoweringRefusal::OutOfFragment {
                span: at(11_usize, 30_usize),
                form: FormName::from(NamedKind("product_type")),
                sort: FragmentSort::CompType,
                boundary: FragmentBoundary::WrongSort,
            },
            "a product is a value type, not a computation type"
        );
        assert_eq!(
            refusal(SourceText::from("def u = thunk { *{1, 2} ; return 0 } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(16_usize, 23_usize),
                form: FormName::from(NamedKind("telescope_expression")),
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::WrongSort,
            },
            "a pair is a value, not a computation: off a tail no exit is inferred for it"
        );
    }

    #[test]
    fn a_list_literal_lowers_to_its_cons_cells_1544()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def e = #[] ; def o = #[1] ; def t = #[1, \"a\", 1,] ;"),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let one = Value::Literal(integer(SourceFragment::from("1")));
        let letter = Value::Literal(text(SourceFragment::from("a")));
        // The heads of the cons chain `id` starts, in order, when it ends in
        // the empty list.
        let cells = |mut id| {
            let mut heads = Vec::new();
            loop {
                match arena.value(id) {
                    Some(&Value::ListCons(head, tail)) => {
                        heads.push(arena.value(head));
                        id = tail;
                    },
                    Some(&Value::ListNil) => return Some(heads),
                    _ => return None,
                }
            }
        };

        assert_eq!(
            cells(body_of(lowered[0])),
            Some(Vec::new()),
            "`#[]` is the empty list"
        );
        assert_eq!(
            cells(body_of(lowered[1])),
            Some(vec![Some(&one)]),
            "`#[v]` is one cell over `v` ending in the empty list"
        );
        assert_eq!(
            cells(body_of(lowered[2])),
            Some(vec![Some(&one), Some(&letter), Some(&one)]),
            "a list of three is three cells over its elements in written order, a comma \
             after the last admitted"
        );
        assert_eq!(
            refusal(SourceText::from("def u = thunk { #[1, 2] ; return 0 } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(16_usize, 23_usize),
                form: FormName::from(NamedKind("list_expression")),
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::WrongSort,
            },
            "a list is a value, not a computation"
        );
    }

    #[test]
    fn a_static_lambda_binds_its_name_over_a_quoted_body()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def k : Type -> Type -> Type ; def k = fun (A) { fun (B) { type(A * B) } } ;",
            ),
            &mut arena,
        );
        let lambda = |id| match arena.value(id) {
            Some(&Value::StaticLambda(body)) => Some(body),
            _ => None,
        };
        let decoded = |id| match arena.value_type(id) {
            Some(&ValueType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            _ => (None, None),
        };
        let variable = |index: u32| {
            (
                Some(Value::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(index),
                }),
                Some(Level::constant(LevelConstant::ZERO)),
            )
        };

        let Some(inner) = lambda(body_of(outcomes(&module)[0])).and_then(lambda)
        else {
            panic!("each `fun` at a static arrow is one static lambda");
        };
        let Some(&Value::Quote(quoted)) = arena.value(inner)
        else {
            panic!("a type written as the body is quoted");
        };
        let Some(held) = arena.value_type(quoted)
        else {
            panic!("the body is the product it spells");
        };
        let ValueType::Product(ref parts) = *held
        else {
            panic!("the body is the product it spells");
        };
        let [first, second] = **parts
        else {
            panic!("the spelled product is binary");
        };
        assert_eq!(
            (decoded(first), decoded(second)),
            (variable(1_u32), variable(0_u32)),
            "each binder decodes at its own index, the fuss-free universe where a value type \
             is read"
        );
        assert_eq!(
            refusal(SourceText::from("def m : fun (A) { A } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 21_usize),
                form: FormName::from(NamedKind("lambda_expression")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "a lambda is a value, not a type"
        );
    }

    #[test]
    fn a_static_application_decodes_where_its_operator_says_or_where_it_stands()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def t : Type -> Type[-, 1] ; def a : +U (t(Integer)) ; def w : Type -> Type[-, 1] ; \
                 def w = fun (X) { t X } ; def k : (Type -> Type[-]) -> Type -> Type ; def k = fun \
                 (G) { fun (A) { type(+U (G(A)) * A) } } ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let constant = Value::Constant(ConstantIndex::from(0_usize));
        let applied = |id| match arena.value(id) {
            Some(&Value::StaticApplication(head, argument)) => {
                Some((arena.value(head).cloned(), arena.value(argument).cloned()))
            },
            _ => None,
        };
        let decoded = |id| match arena.comp_type(id) {
            Some(&CompType::Element { code, ref target }) => Some((code, target.clone())),
            _ => None,
        };
        let lambda = |id| match arena.value(id) {
            Some(&Value::StaticLambda(body)) => Some(body),
            _ => None,
        };

        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(lowered[1]))
        else {
            panic!("`+U` is a thunk type");
        };
        let Some((code, target)) = decoded(suspended)
        else {
            panic!("an operator applied where a computation type is read decodes");
        };
        assert_eq!(
            target,
            Level::constant(LevelConstant::from(1_u64)),
            "at the level of the universe its operator's codomain spells"
        );
        let Some((Some(head), Some(Value::Quote(argument)))) = applied(code)
        else {
            panic!("the code is the operator applied to the quoted argument");
        };
        assert_eq!(
            (head, arena.value_type(argument).cloned()),
            (constant.clone(), Some(ValueType::Base(BaseType::Integer))),
            "the operator is the declaration, and the argument a type's code"
        );

        assert_eq!(
            lambda(body_of(lowered[2])).and_then(applied),
            Some((Some(constant), Some(variable(0_u32)))),
            "where a value is read the application stands as itself, its binder unquoted"
        );

        let Some(inner) = lambda(body_of(lowered[3])).and_then(lambda)
        else {
            panic!("two static lambdas");
        };
        let Some(&Value::Quote(quoted)) = arena.value(inner)
        else {
            panic!("a quoted body");
        };
        let Some(held) = arena.value_type(quoted)
        else {
            panic!("a product body");
        };
        let ValueType::Product(ref parts) = *held
        else {
            panic!("a product body");
        };
        let [left, right] = **parts
        else {
            panic!("the product body is binary");
        };
        let Some(&ValueType::Thunk(family)) = arena.value_type(left)
        else {
            panic!("a thunk type on the left");
        };
        let Some((family_code, family_level)) = decoded(family)
        else {
            panic!("an untyped operator applied where a computation type is read decodes there");
        };
        assert_eq!(
            (applied(family_code), family_level),
            (
                Some((Some(variable(1_u32)), Some(variable(0_u32)))),
                Level::constant(LevelConstant::ZERO)
            ),
            "at the computation types and the fuss-free level"
        );
        assert!(
            matches!(
                arena.value_type(right),
                Some(&ValueType::Element { code, .. })
                    if arena.value(code) == Some(&variable(0_u32))
            ),
            "and an untyped binder where a value type is read decodes at the value types"
        );
    }

    #[test]
    fn a_static_application_its_operator_does_not_fit_decodes_where_it_stands()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def t : Type -> Type[-, 1] ; def u : Type -> Type -> Type[-, 1] ; def a : +U \
                 (t(Integer, Integer)) ; def b : +U (u(Integer)) ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let level = |at: usize| {
            let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(lowered[at]))
            else {
                panic!("`+U` is a thunk type");
            };
            let Some(&CompType::Element { ref target, .. }) = arena.comp_type(suspended)
            else {
                panic!("an operator applied where a computation type is read decodes");
            };
            target.clone()
        };
        assert_eq!(
            (level(2_usize), level(3_usize)),
            (
                Level::constant(LevelConstant::ZERO),
                Level::constant(LevelConstant::ZERO)
            ),
            "an arrow too few or too many leaves the operator's universe unread, so each \
             decodes at the default of where it stands"
        );
    }

    #[test]
    fn a_function_to_a_universe_unquotes_where_a_type_is_read()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def zero = 0 ; def pick(t : Integer) -> -F Type { return Integer } def two : \
                 pick(zero) ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let declared = declared_of(lowered[2]);
        let Some(&ValueType::Element { code, ref target }) = arena.value_type(declared)
        else {
            panic!("a function called where a type is read decodes");
        };
        assert_eq!(
            *target,
            Level::constant(LevelConstant::ZERO),
            "at the universe the position reads"
        );
        let Some(&Value::Returned(called)) = arena.value(code)
        else {
            panic!("the code is what the call returns: {:?}", arena.value(code));
        };
        let Some(&Computation::Application(forced, argument)) = arena.computation(called)
        else {
            panic!("the call applies the function to its argument");
        };
        let Some(&Computation::Force(head)) = arena.computation(forced)
        else {
            panic!("the function is forced");
        };
        assert_eq!(
            (arena.value(head).cloned(), arena.value(argument).cloned()),
            (
                Some(Value::Constant(ConstantIndex::from(1_usize))),
                Some(Value::Constant(ConstantIndex::from(0_usize)))
            ),
            "the function is the declaration, the argument read as a value"
        );
        let provenance =
            |origin: Maybe<crate::Origin, _>| origin.map(|held: crate::Origin| held.provenance());
        assert_eq!(
            (
                provenance(module.origins().value_type(declared)),
                provenance(module.origins().value(code)),
                provenance(module.origins().computation(forced)),
            ),
            (
                Maybe::Present(Provenance::Inserted(Insertion::Decode)),
                Maybe::Present(Provenance::Inserted(Insertion::Endpoint)),
                Maybe::Present(Provenance::Inserted(Insertion::Force)),
            ),
            "the decode, the returned code and the force are the lowering's"
        );
        assert!(
            matches!(
                provenance(module.origins().computation(called)),
                Maybe::Present(Provenance::Written)
            ),
            "the call is the source's"
        );
    }

    /// A function called at the carrier of a path type a body quotes is the
    /// decode of the code its call returns, as it is at a binder's type: the
    /// expression grammar molds it as a call, and it is read as the type
    /// application it spells.
    #[test]
    fn a_call_at_a_quoted_path_carrier_unquotes_as_at_a_binder_3573()
    {
        let mut arena = CoreArena::new();
        let text = "def same(a : Type) -> -F Type { return a } def pathSame(a : Type, x : a) -> \
                    -F Type { return (type(Path[.A = same(a)](x, x))) }";
        let module = lowered(SourceText::from(text), &mut arena);
        let lowered = outcomes(&module);
        assert!(
            !matches!(lowered[1], DeclarationOutcome::Refused(_)),
            "the quoted path type lowers: {:?}",
            lowered[1]
        );
        let at = text.rfind("same(a)").expect("the carrier is written");
        let carrier = module
            .origins()
            .value_types()
            .iter()
            .find(|&&(_, origin)| {
                usize::from(origin.span().start()) == at
                    && origin.provenance() == Provenance::Inserted(Insertion::Decode)
            })
            .map(|&(id, _)| id)
            .expect("the carrier's decode is located at the call");
        let Some(&ValueType::Element { code, .. }) = arena.value_type(carrier)
        else {
            panic!("the carrier is a decode");
        };
        let Some(&Value::Returned(called)) = arena.value(code)
        else {
            panic!("the code is what the call returns: {:?}", arena.value(code));
        };
        let Some(&Computation::Application(forced, _)) = arena.computation(called)
        else {
            panic!("the call applies the function to its argument");
        };
        let Some(&Computation::Force(head)) = arena.computation(forced)
        else {
            panic!("the function is forced");
        };
        assert_eq!(
            arena.value(head).cloned(),
            Some(Value::Constant(ConstantIndex::from(0_usize))),
            "the function is `same`"
        );
    }

    /// #3681: a decoder's descent at the carrier of a path type it quotes,
    /// `Path[.A = el[<](a)](x, y)`, was refused by its sort: the expression
    /// grammar molds it as a call whose head is an instantiation, which no
    /// name resolves. It is the descent the type grammar spells, the decode
    /// of its fixpoint's call, as an unmarked call there is (#3573).
    #[test]
    fn a_descent_at_a_quoted_path_carrier_unquotes_as_in_a_type_3681()
    {
        let mut arena = CoreArena::new();
        let text = "data U : Type where { | NatU : U | PathU : (a : U, x : Integer, y : Integer) --> U } \
                    def rec el(u : U) -> -F Type { match u { | NatU => return Integer | PathU(a, x, \
                    y) => return (type(Path[.A = el[<](a)](x, y))) } }";
        let module = lowered(SourceText::from(text), &mut arena);
        let lowered = outcomes(&module);
        assert!(
            !matches!(lowered[1], DeclarationOutcome::Refused(_)),
            "the decoder lowers: {:?}",
            lowered[1]
        );
        let at = text.find("el[<](a)").expect("the carrier is written");
        let carrier = module
            .origins()
            .value_types()
            .iter()
            .find(|&&(_, origin)| {
                usize::from(origin.span().start()) == at
                    && origin.provenance() == Provenance::Inserted(Insertion::Decode)
            })
            .map(|&(id, _)| id)
            .expect("the carrier's decode is located at the descent");
        assert!(
            matches!(arena.value_type(carrier), Some(&ValueType::Element { .. })),
            "the carrier is a decode: {:?}",
            arena.value_type(carrier)
        );
    }

    #[test]
    fn a_thunk_binder_called_in_a_type_unquotes_its_call()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def pick(t : Type) -> -F Type { return t } def take(g : +U (Integer -> -F \
                 Type), v : g(1), w : pick(g(2))) -> -F Integer { return 1 }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let declared = declared_of(lowered[1]);
        // The domains of the arrows the declared type nests, outermost first:
        // a Π where the rest names its parameter, a plain arrow otherwise.
        let mut domains = Vec::new();
        let mut at = match arena.value_type(declared) {
            Some(&ValueType::Thunk(arrow)) => arrow,
            other => panic!("a function's type is a thunk: {other:?}"),
        };
        while let Some(&CompType::Pi { domain, codomain } | &CompType::Arrow { domain, codomain }) =
            arena.comp_type(at)
        {
            domains.push(domain);
            at = codomain;
        }
        let [_, called, argued] = *domains
        else {
            panic!("three parameters: {domains:?}");
        };
        // The code a decode at `decoded` reads: what a computation returns.
        let returned = |decoded| {
            let Some(&ValueType::Element { code, .. }) = arena.value_type(decoded)
            else {
                panic!("a call where a type is read decodes");
            };
            let Some(&Value::Returned(called)) = arena.value(code)
            else {
                panic!("the code is what the call returns: {:?}", arena.value(code));
            };
            called
        };
        // The forced head and the argument of a call.
        let call = |applied| {
            let Some(&Computation::Application(forced, argument)) = arena.computation(applied)
            else {
                panic!("a call applies its head: {:?}", arena.computation(applied));
            };
            let Some(&Computation::Force(head)) = arena.computation(forced)
            else {
                panic!("the head is forced");
            };
            (arena.value(head).cloned(), arena.value(argument).cloned())
        };
        let variable = |index: u32| {
            Some(Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(index),
            })
        };
        assert_eq!(
            call(returned(called)).0,
            variable(0),
            "the binder's call is the code it returns"
        );
        let (head, argument) = call(returned(argued));
        assert_eq!(
            head,
            Some(Value::Constant(ConstantIndex::from(0_usize))),
            "the outer call forces `pick`"
        );
        let Some(Value::Returned(inner)) = argument
        else {
            panic!("an argument calling the binder is the code it returns: {argument:?}");
        };
        // `v` binds nothing for `w`'s type, a plain arrow's rest, so the binder
        // is the nearest one.
        assert_eq!(
            call(inner).0,
            variable(0),
            "the argument calls the binder in place"
        );
    }

    /// #6787: a call of a dynamic function with no argument, at a family's
    /// argument inside a type, is the expression grammar's `f()`: the force of
    /// its head, which answers at the call. Its value is what that force
    /// returns, in the call form and in the juxtaposed form. A plan of the call
    /// over an empty stretch fails the postcondition of `Plan::Called`. The
    /// juxtaposed form follows a type name: after a variable, `Pair a plus()`
    /// reads `a plus()` as one call until the glued call head of #5752 lands.
    #[test]
    fn a_nullary_call_at_a_family_s_argument_is_its_head_s_force_6787()
    {
        for text in [
            "data Pair(a : Type, b : Type) : Type where { | Mk : (x : a, y : b) --> Pair a b } def \
             plus() -> -F Type { return Integer } def called(a : Type, x : Pair(a, plus())) -> -F \
             Integer { return 1 }",
            "data Pair(a : Type, b : Type) : Type where { | Mk : (x : a, y : b) --> Pair a b } def \
             plus() -> -F Type { return Integer } def called(a : Type, x : Pair Integer plus()) -> \
             -F Integer { return 1 }",
        ] {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(text), &mut arena);
            let lowered = outcomes(&module);
            assert!(
                matches!(lowered[2], DeclarationOutcome::Completed { .. }),
                "`called` lowers, in `{text}`: {:?}",
                lowered[2]
            );
            let declared = declared_of(lowered[2]);
            let arrow = match arena.value_type(declared) {
                Some(&ValueType::Thunk(arrow)) => arrow,
                other => panic!("a function's type is a thunk: {other:?}"),
            };
            // The rest names `a` in the call form, and no type names it in the
            // juxtaposed form.
            let Some(&(CompType::Pi { codomain, .. } | CompType::Arrow { codomain, .. })) =
                arena.comp_type(arrow)
            else {
                panic!("`a` is the first parameter: {:?}", arena.comp_type(arrow));
            };
            let Some(&(CompType::Pi { domain, .. } | CompType::Arrow { domain, .. })) =
                arena.comp_type(codomain)
            else {
                panic!(
                    "`x` is the second parameter: {:?}",
                    arena.comp_type(codomain)
                );
            };
            let Some(ValueType::Data { arguments, .. }) = arena.value_type(domain).cloned()
            else {
                panic!("`x` is held at the family: {:?}", arena.value_type(domain));
            };
            let [_, argument] = *arguments
            else {
                panic!("the family takes two arguments: {arguments:?}");
            };
            let Some(&Value::Returned(forced)) = arena.value(argument)
            else {
                panic!(
                    "the argument is what the call returns: {:?}",
                    arena.value(argument)
                );
            };
            let Some(&Computation::Force(head)) = arena.computation(forced)
            else {
                panic!(
                    "the call is its head's force: {:?}",
                    arena.computation(forced)
                );
            };
            assert_eq!(
                arena.value(head).cloned(),
                Some(Value::Constant(ConstantIndex::from(1_usize))),
                "the head is `plus`, in `{text}`"
            );
            let at = text.rfind("plus()").expect("the call is written");
            let origin = module
                .origins()
                .computation(forced)
                .map(|held: crate::Origin| (held.provenance(), usize::from(held.span().start())));
            assert_eq!(
                origin,
                Maybe::Present((Provenance::Written, at)),
                "the force is the call the source writes, in `{text}`"
            );
        }
    }

    /// A binder whose written type names a type member standing for the
    /// bridge holds a function, so its call where a type is read is the code
    /// the call returns, as a binder written at the bridge is (#522).
    #[test]
    fn a_binder_at_a_family_standing_for_a_function_unquotes_its_call_522()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "type Fam(g : Type) = g -> Type ; def take(g : Type, a : Fam(g), x : g, v : \
                 a(x)) -> -F Integer { return 1 }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let declared = declared_of(*lowered.last().expect("`take` is lowered"));
        let mut domains = Vec::new();
        let mut at = match arena.value_type(declared) {
            Some(&ValueType::Thunk(arrow)) => arrow,
            other => panic!("a function's type is a thunk: {other:?}"),
        };
        while let Some(&CompType::Pi { domain, codomain } | &CompType::Arrow { domain, codomain }) =
            arena.comp_type(at)
        {
            domains.push(domain);
            at = codomain;
        }
        let [_, _, _, applied] = *domains
        else {
            panic!("four parameters: {domains:?}");
        };
        let Some(&ValueType::Element { code, .. }) = arena.value_type(applied)
        else {
            panic!(
                "a call where a type is read decodes: {:?}",
                arena.value_type(applied)
            );
        };
        let Some(&Value::Returned(called)) = arena.value(code)
        else {
            panic!("the code is what the call returns: {:?}", arena.value(code));
        };
        let Some(&Computation::Application(forced, argument)) = arena.computation(called)
        else {
            panic!("a call applies its head: {:?}", arena.computation(called));
        };
        let Some(&Computation::Force(head)) = arena.computation(forced)
        else {
            panic!("the head is forced");
        };
        let variable = |index: u32| {
            Some(Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(index),
            })
        };
        assert_eq!(
            (arena.value(head).cloned(), arena.value(argument).cloned()),
            (variable(1), variable(0)),
            "the binder `a` is called at `x`"
        );
    }

    #[test]
    fn a_lambda_in_value_position_is_nested_and_marked_inserted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = fun (y) { return y } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[0]);
        let Some(&Value::Nested(nested)) = arena.value(body)
        else {
            panic!("the lambda stands nested where a value is read");
        };
        let origin = module.origins().value(body);

        assert!(
            matches!(arena.computation(nested), Some(&Computation::Lambda(_))),
            "the nested computation is the lambda the source wrote"
        );
        assert_eq!(
            origin.map(|inserted| inserted.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Nested)),
            "the nesting is the lowering's, not the source's"
        );
        assert_eq!(
            origin.map(|inserted| inserted.span()),
            Maybe::Present(at(8_usize, 28_usize)),
            "the nesting names the lambda whose position demanded it"
        );
        assert_eq!(
            module
                .origins()
                .computation(nested)
                .map(|written| written.provenance()),
            Maybe::Present(Provenance::Written),
            "the lambda itself is the source's"
        );
    }

    #[test]
    fn a_written_run_lowers_to_a_run_over_its_computation()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { return run (pure 1) } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[0]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Return(returned)) = arena.computation(suspended)
        else {
            panic!("the exit returns its operand");
        };
        let Some(&Value::Run(ran)) = arena.value(returned)
        else {
            panic!("the written run lowers to a run");
        };

        assert!(
            matches!(arena.computation(ran), Some(&Computation::Return(value)) if arena.value(value) == Some(&Value::Literal(integer(SourceFragment::from("1"))))),
            "the run is over the computation the source wrote"
        );
        assert_eq!(
            module
                .origins()
                .value(returned)
                .map(|written| (written.provenance(), written.span())),
            Maybe::Present((Provenance::Written, at(23_usize, 35_usize))),
            "the run is the source's"
        );
        assert_eq!(
            refusal(SourceText::from("def b = thunk { return run 1 } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(27_usize, 28_usize),
                form: FormName::from(NamedKind("number")),
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::WrongSort,
            },
            "a run's operand is a computation, so a value there is refused by sort"
        );
    }

    #[test]
    fn forms_outside_the_fragment_are_unadmitted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let unadmitted =
            |start: usize, end: usize, form: FormName, sort: FragmentSort, feature: Unbuilt| {
                LoweringRefusal::OutOfFragment {
                    span: at(start, end),
                    form,
                    sort,
                    boundary: FragmentBoundary::Unadmitted(feature),
                }
            };
        let rows = [(
            "def a = 1.5f32 ;",
            unadmitted(
                8_usize,
                14_usize,
                FormName::from(NamedKind("typed_number")),
                FragmentSort::Value,
                Unbuilt::TypedNumber,
            ),
        )];
        for (source, expected) in rows {
            let refused = refusal(SourceText::from(source));
            assert_eq!(refused, expected, "`{source}` is outside the fragment");
            assert!(
                matches!(refused.classify(), FailureClass::Unimplemented(_)),
                "`{source}` is unimplemented, not malformed"
            );
        }
    }

    #[test]
    fn a_number_takes_float64_from_its_suffix_or_annotation_1830()
    {
        let float = |source: &'static str| {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            let mut held = body_of(outcomes(&module)[0]);
            // An annotation no form carries ascribes its operand.
            if let Some(&Value::Ascribe { value, .. }) = arena.value(held) {
                held = value;
            }
            match arena.value(held) {
                Some(&Value::Literal(Literal::Float64(float))) => float,
                other => panic!("`{source}` lowers to a float, not {other:?}"),
            }
        };
        assert_eq!(
            float("def a = 0.2f64 ;"),
            Float64Literal::from(0.2_f64),
            "the suffix types the number"
        );
        assert_eq!(
            float("def a = (0.2 : f64) ;"),
            Float64Literal::from(0.2_f64),
            "so does an annotation"
        );
        assert_eq!(
            float("def a = (3 : f64) ;"),
            Float64Literal::from(3.0_f64),
            "an annotation types a number written without a fraction"
        );
        assert_eq!(
            float("def a = 1e3f64 ;"),
            Float64Literal::from(1000.0_f64),
            "an exponent reads as written"
        );
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-number-takes-float64-from-its-suffix-or-annotation-1830-module.gandr"
            )),
            &mut arena,
        );
        assert!(
            matches!(
                outcome_named(&module, "chosen"),
                DeclarationOutcome::Bodied { .. }
            ),
            "`f64` passed where a type is read stands as the type, as `Integer` does: {:?}",
            outcome_named(&module, "chosen")
        );
    }

    /// #4807: a bare fraction or exponent lowers to its exact decimal, its
    /// digits moved across the point by the exponent, and `-d` written on one
    /// to the negative decimal; an exponent past the digits the lowering
    /// holds is a malformed literal.
    #[test]
    fn a_decimal_reads_as_its_exact_value_4807()
    {
        let decimal = |source: &'static str| {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            match arena.value(body_of(outcomes(&module)[0])) {
                Some(&Value::Literal(Literal::Numeric(ref decimal))) => (
                    decimal.sign(),
                    String::from(decimal.integer_part().as_ref()),
                    String::from(decimal.fraction().as_ref()),
                ),
                other => panic!("`{source}` lowers to a decimal, not {other:?}"),
            }
        };
        for (source, sign, whole, fraction) in [
            ("def a = 0.2 ;", Sign::NonNegative, "0", "2"),
            ("def a = 1.250 ;", Sign::NonNegative, "1", "25"),
            ("def a = 1e-3 ;", Sign::NonNegative, "0", "001"),
            ("def a = 1.5e2 ;", Sign::NonNegative, "150", ""),
            ("def a = 12.5E-1 ;", Sign::NonNegative, "1", "25"),
            ("def a = 1e3 ;", Sign::NonNegative, "1000", ""),
            ("def a = - 1.5 ;", Sign::Negative, "1", "5"),
        ] {
            assert_eq!(
                decimal(source),
                (sign, String::from(whole), String::from(fraction)),
                "`{source}` reads as its exact value"
            );
        }
        assert!(
            matches!(
                refusal(SourceText::from("def a = 1e99999999 ;")),
                LoweringRefusal::MalformedLiteral { .. }
            ),
            "an exponent past the digits the lowering holds is malformed"
        );
    }

    #[test]
    fn an_implicit_telescope_on_no_function_is_refused_by_name()
    {
        let refused = refusal(SourceText::from("def f[a : Type] = 1 ;"));
        assert!(
            matches!(refused, LoweringRefusal::ImplicitTelescope { span } if span.start() == ByteOffset::from(0_usize)),
            "a telescope binds a function's parameters, and is refused at any other \
             declaration: {refused:?}"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "the design gives implicits only to a function, so the telescope is the author's error"
        );
    }

    #[test]
    fn a_form_offered_the_wrong_operand_count_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let arity = |start: usize, end: usize, form: FormName, count: usize| {
            LoweringRefusal::OutOfFragment {
                span: at(start, end),
                form,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::Arity(OperandCount::from(count)),
            }
        };
        let rows = [
            (
                "def a = thunk { fun (x, y) { return x } } ;",
                arity(
                    16_usize,
                    39_usize,
                    FormName::from(NamedKind("lambda_expression")),
                    2_usize,
                ),
            ),
            (
                "def a = thunk {} ;",
                arity(14_usize, 16_usize, FormName::BLOCK, 0_usize),
            ),
            (
                "def a = thunk { let x = 1; } ;",
                arity(14_usize, 28_usize, FormName::BLOCK, 0_usize),
            ),
        ];
        for (source, expected) in rows {
            assert_eq!(
                refusal(SourceText::from(source)),
                expected,
                "`{source}` offers its form the wrong number of operands"
            );
        }
    }

    #[test]
    fn a_malformed_integer_literal_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = 3x ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("number.expression"),
            Spelled("number"),
            at(8_usize, 10_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(11_usize, 12_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 12_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.module(at(0_usize, 12_usize), &[declaration]);
        let refused = refusal_in(&pbg, &tree);

        assert_eq!(
            refused,
            LoweringRefusal::MalformedLiteral {
                span: at(8_usize, 10_usize),
                form: FormName::from(NamedKind("number")),
            },
            "a number whose text is not digits is refused"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a malformed literal is the author's mistake"
        );
    }

    #[test]
    fn a_malformed_text_literal_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = \"abc ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("string.expression"),
            Spelled("\""),
            at(8_usize, 12_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(13_usize, 14_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 14_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.module(at(0_usize, 14_usize), &[declaration]);

        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedLiteral {
                span: at(8_usize, 12_usize),
                form: FormName::from(NamedKind("string")),
            },
            "a string missing its closing quote is refused"
        );
    }

    #[test]
    fn a_repaired_declaration_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(&pbg, SourceText::from("def x ;"));
        let refused = refusal_in(&pbg, &tree);

        assert_eq!(
            refused,
            LoweringRefusal::MalformedForm {
                span: at(5_usize, 5_usize),
                form: FormName::DECLARATION,
                fault: FormFault::Repaired(Repair::Unended(crate::form::Ending::Unnamed)),
            },
            "the end the parser appended is reported past the last written tile, naming no \
             tile where the grammar continues with several"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a repaired form is the author's mistake"
        );
    }

    #[test]
    fn a_missing_close_is_reported_at_the_innermost_form()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(
            &pbg,
            SourceText::from(include_str!(
                "../../surface-lowering-base/src/form/tests/unformatted/a-missing-close-is-reported-at-the-innermost-form-tree.gandr"
            )),
        );
        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(74_usize, 74_usize),
                form: FormName::MATCH,
                fault: FormFault::Repaired(Repair::GhostClose(
                    gandr_surface_syntax::ClosingClass::Brace,
                )),
            },
            "the source ends with both the match and the definition open; the refusal names \
             the match at the end of its last arm, not the definition at its opening brace"
        );
    }

    #[test]
    fn a_keyword_in_a_classifier_slot_is_read_with_its_offer_293()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(
            &pbg,
            SourceText::from(include_str!(
                "../../surface-lowering-base/src/form/tests/unformatted/a-keyword-in-a-classifier-slot-is-read-with-its-offer-293-tree.gandr"
            )),
        );
        let LoweringRefusal::MalformedForm { span, fault, .. } = refusal_in(&pbg, &tree)
        else {
            panic!("a keyword in a classifier slot refuses its form");
        };
        assert_eq!(
            span,
            at(32_usize, 36_usize),
            "the refusal stands at the keyword itself"
        );
        let FormFault::Repaired(Repair::Keyword(stray)) = fault
        else {
            panic!("the grout over `type` reads as the keyword, not a missing term: {fault:?}");
        };
        assert_eq!(
            (stray.written, stray.offer),
            (
                crate::form::TileName::TYPE,
                crate::form::Offer::Capitalised(crate::form::TileName::UNIVERSE)
            ),
            "the keyword is named and the universe spelled with a capital is offered"
        );
    }

    /// #6266: a reserved word that the parser read as a name refuses the form
    /// that holds it, at the word and by the word.
    #[test]
    fn a_reserved_word_as_a_name_is_refused_by_name_6266()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        for (source, word) in [
            ("def match(x : Integer) -> Integer = x;", "match"),
            ("def data : Integer = 1;", "data"),
            ("def f(type : Integer) -> Integer = 1;", "type"),
        ] {
            let tree = repaired(&pbg, SourceText::from(source));
            let LoweringRefusal::MalformedForm { span, fault, .. } = refusal_in(&pbg, &tree)
            else {
                panic!("{source}: a reserved word as a name refuses its form");
            };
            let start = source.find(word).unwrap_or_default();
            assert_eq!(
                span,
                at(start, start.saturating_add(word.len())),
                "{source}: the refusal stands at the word itself"
            );
            let FormFault::Repaired(Repair::ReservedName(named)) = fault
            else {
                panic!("{source}: the name reads as the reserved word: {fault:?}");
            };
            assert_eq!(named.as_ref(), word, "{source}: the refusal names the word");
        }
    }

    #[test]
    fn an_unended_form_names_its_missing_tile_where_it_belongs()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        for (source, point, form, tile, why) in [
            (
                include_str!(
                    "../../surface-lowering-base/src/form/tests/unformatted/an-unended-form-names-its-missing-tile-where-it-belongs-1.gandr"
                ),
                27_usize,
                "def_value",
                crate::form::TileName::SEMICOLON,
                "a definition missing its `;` before the next on its line is pointed past its \
                 value",
            ),
            (
                include_str!(
                    "../../surface-lowering-base/src/form/tests/unformatted/an-unended-form-names-its-missing-tile-where-it-belongs-2.gandr"
                ),
                31_usize,
                "string",
                crate::form::TileName::QUOTE,
                "a string never closed is pointed past its text on its own line, not the \
                 definition it swallowed the `;` of",
            ),
        ] {
            let tree = repaired(&pbg, SourceText::from(source));
            assert_eq!(
                refusal_in(&pbg, &tree),
                LoweringRefusal::MalformedForm {
                    span: at(point, point),
                    form: FormName::from(NamedKind(form)),
                    fault: FormFault::Repaired(Repair::Unended(crate::form::Ending::Tile(tile))),
                },
                "{why}"
            );
        }
        let tree = repaired(&pbg, SourceText::from("def a = r."));
        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(10_usize, 10_usize),
                form: FormName::from(NamedKind("projection_expression")),
                fault: FormFault::Repaired(Repair::Unended(crate::form::Ending::Unnamed)),
            },
            "a projection missing its field names no one tile, since a label or an index may \
             end it"
        );
    }

    /// #1829: a form the parser closed at its end is marked where its written
    /// tiles first leave its rule's shape, not at the close.
    #[test]
    fn a_closed_form_is_marked_where_it_first_leaves_its_shape_1829()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(
            &pbg,
            SourceText::from(include_str!(
                "../../surface-lowering-base/src/form/tests/unformatted/a-closed-form-is-marked-where-it-first-leaves-its-shape-1829-tree-1.gandr"
            )),
        );
        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(47_usize, 47_usize),
                form: FormName::from(NamedKind("labelled_sum_expression")),
                fault: FormFault::Repaired(Repair::Diverged(crate::form::Ending::Tile(
                    crate::form::TileName::DOT
                ))),
            },
            "an injection missing its label's `.` is marked at the dot's gap, where an operand \
             follows a tile no hole follows, and names the dot"
        );
        let tree = repaired(&pbg, SourceText::from("def x = ( 1 ;\n"));
        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(11_usize, 11_usize),
                form: FormName::from(NamedKind("parenthesized_expression")),
                fault: FormFault::Repaired(Repair::GhostClose(
                    gandr_surface_syntax::ClosingClass::Paren,
                )),
            },
            "a group left open before a stray `;` is missing its `)` where the `;` stands \
             in its last hole, not at the end of the source"
        );
        let tree = repaired(
            &pbg,
            SourceText::from(include_str!(
                "../../surface-lowering-base/src/form/tests/unformatted/a-closed-form-is-marked-where-it-first-leaves-its-shape-1829-tree-2.gandr"
            )),
        );
        assert!(
            matches!(refusal_in(&pbg, &tree), LoweringRefusal::MalformedForm {
                span,
                fault: FormFault::Repaired(Repair::GhostClose(_)),
                ..
            } if span == at(44_usize, 44_usize)),
            "a module never closed keeps its close at its end: its rule writes its members \
             side by side"
        );
    }

    /// #3812: a group's `)` left out where two places parse is marked over
    /// both places and every byte between them, so the mark touches the place
    /// the source lost it at.
    #[test]
    fn a_closer_owed_at_two_places_is_marked_over_both_3812()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let source = include_str!(
            "../../surface-lowering-base/src/form/tests/unformatted/a-closer-owed-at-two-places-is-marked-over-both-3812.gandr"
        );
        let after = |written: &str| {
            source
                .find(written)
                .map_or(0_usize, |start| start.saturating_add(written.len()))
        };
        let tree = repaired(&pbg, SourceText::from(source));
        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(after("(xs"), after("2 }")),
                form: FormName::from(NamedKind("parenthesized_expression")),
                fault: FormFault::Repaired(Repair::GhostClose(
                    gandr_surface_syntax::ClosingClass::Paren,
                )),
            },
            "the `)` can close the group after `xs` or after the block: the mark spans both, \
             and the place the source lost it at, after `()`, lies between"
        );
    }

    /// #2242: a declaration the parser repaired because a bracket was written
    /// once too often, or left out, is refused at that bracket, as its layout
    /// places it, not where the parser's pairing finally failed.
    #[test]
    fn a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let case = include_str!(
            "lower/unformatted/a-bracket-the-layout-misplaces-is-refused-where-it-was-written-2242-case.gandr"
        );
        let access = include_str!(
            "lower/unformatted/a-bracket-the-layout-misplaces-is-refused-where-it-was-written-2242-access.gandr"
        );
        let handle = include_str!(
            "lower/unformatted/a-bracket-the-layout-misplaces-is-refused-where-it-was-written-2242-handle.gandr"
        );
        let unopened = include_str!(
            "lower/unformatted/a-bracket-the-layout-misplaces-is-refused-where-it-was-written-2242-unopened.gandr"
        );
        let quoted = include_str!(
            "lower/unformatted/a-bracket-the-layout-misplaces-is-refused-where-it-was-written-2242-quoted.gandr"
        );
        let after = |source: &str, written: &str| {
            source
                .find(written)
                .map_or(0_usize, |start| start.saturating_add(written.len()))
        };
        for (source, point, form, fault, why) in [
            (
                case,
                at(after(case, "match n "), after(case, "match n {")),
                "match_expression",
                FormFault::ExtraOpen(ClosingClass::Brace),
                "a doubled `{` is refused at the first of the pair: its line opens two and is \
                 answered once",
            ),
            (
                access,
                at(after(access, "v + 1)"), after(access, "v + 1)")),
                "access_expression",
                FormFault::Repaired(Repair::GhostClose(ClosingClass::Brace)),
                "a block on one line missing its `}` is refused before the line's `;`: the next \
                 line is no deeper",
            ),
            (
                handle,
                at(after(handle, "return n"), after(handle, "return n")),
                "handle_expression",
                FormFault::Repaired(Repair::GhostClose(ClosingClass::Brace)),
                "a block missing its `}` is refused at the end of the line before the one that \
                 comes back to its indentation",
            ),
            (
                unopened,
                at(after(unopened, "if n == 0"), after(unopened, "if n == 0")),
                "if_expression",
                FormFault::MissingOpen(ClosingClass::Brace),
                "a `}` beginning a line deeper than every waiting `{` answers one left out at \
                 the end of the line at its indentation",
            ),
            (
                quoted,
                at(after(quoted, "List"), after(quoted, "List(")),
                "type_application",
                FormFault::ExtraOpen(ClosingClass::Paren),
                "a doubled `(` is refused at the first of the pair",
            ),
        ] {
            let tree = repaired(&pbg, SourceText::from(source));
            assert_eq!(
                refusal_in(&pbg, &tree),
                LoweringRefusal::MalformedForm {
                    span: point,
                    form: FormName::from(NamedKind(form)),
                    fault,
                },
                "{why}"
            );
        }
    }

    #[test]
    fn a_juxtaposed_operand_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        // A type a second type follows applies to it (#5326), and a block-like
        // form ends at its brace, so the operand after it stands apart.
        let refused = refusal(SourceText::from("def f = if true { 1 } else { 2 } 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::MalformedForm {
                span: at(33_usize, 34_usize),
                form: FormName::DECLARATION,
                fault: FormFault::ExtraOperand,
            },
            "a definition's value is one form, and a second operand beside it is refused as \
             the definition's"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a juxtaposition is the author's mistake"
        );
    }

    /// #2259: a keyword misspelt reads as a name, and the form then holds the
    /// name and the operand after it in a hole that takes one. The refusal is
    /// at the word, naming the keyword; a word that misspells none keeps the
    /// refusal at the operand.
    #[test]
    fn a_keyword_misspelt_is_refused_at_the_word_2259()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (written, word) in [
            ("retur", "a last letter left off"),
            ("retrun", "two letters swapped"),
            ("returnn", "one letter too many"),
        ] {
            let source = alloc::format!(
                include_str!(
                    "lower/unformatted/a-keyword-misspelt-is-refused-at-the-word-2259-1.gandr"
                ),
                written = written
            );
            let start = source.find(written).unwrap_or_default();
            assert_eq!(
                refusal(SourceText::from(source.as_str())),
                LoweringRefusal::MalformedForm {
                    span: at(start, start.saturating_add(written.len())),
                    form: FormName::FUNCTION,
                    fault: FormFault::Misspelt(crate::form::TileName::RETURN),
                },
                "`{written}`, {word}, is refused at the word as `return` misspelt"
            );
        }
        let source = include_str!(
            "lower/unformatted/a-keyword-misspelt-is-refused-at-the-word-2259-2.gandr"
        );
        let start = source.find("zebra").unwrap_or_default();
        assert_eq!(
            refusal(SourceText::from(source)),
            LoweringRefusal::UnresolvedName {
                span: at(start, start.saturating_add(5)),
                name: SurfaceName::from("zebra"),
            },
            "a word that misspells no keyword is the call of a name nothing defines"
        );
        let source = include_str!(
            "lower/unformatted/a-keyword-misspelt-is-refused-at-the-word-2259-3.gandr"
        );
        let start = source.find("here").unwrap_or_default();
        assert_eq!(
            refusal(SourceText::from(source)),
            LoweringRefusal::UnresolvedName {
                span: at(start, start.saturating_add(4)),
                name: SurfaceName::from("here"),
            },
            "a word one edit from a keyword that opens no expression is the call of a name nothing \
             defines"
        );
    }

    /// #5301: an operator written twice is a run the operator table does not
    /// hold, so the labeler reads it as one name, and the name stands as an
    /// operand of an application. The refusal is at the run, naming the
    /// operator, and not at a later operand. A word that holds a letter
    /// keeps its refusal.
    #[test]
    fn an_operator_written_twice_is_refused_at_the_run_5301()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (written, operator) in [("∷∷", "∷"), (":::", "::")] {
            let source = alloc::format!(
                include_str!(
                    "lower/unformatted/an-operator-written-twice-is-refused-at-the-run-5301-1.gandr"
                ),
                written = written
            );
            let start = source.find(written).unwrap_or_default();
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source.as_str()), &mut arena);
            let refused = outcome_named(&module, "flipped");
            assert!(
                matches!(
                    refused,
                    DeclarationOutcome::Refused(LoweringRefusal::MalformedForm {
                        span: found,
                        fault: FormFault::MisspeltOperator(misspelt),
                        ..
                    }) if found == at(start, start.saturating_add(written.len()))
                        && misspelt.as_ref() == operator
                ),
                "`{written}` is refused at the run as `{operator}` written twice: {refused:?}"
            );
        }
        let source = include_str!(
            "lower/unformatted/an-operator-written-twice-is-refused-at-the-run-5301-2.gandr"
        );
        let path = source.find("Path.here").unwrap_or_default();
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        let refused = outcome_named(&module, "flipped");
        assert!(
            matches!(
                refused,
                DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { span: found, .. })
                    if found == at(path, path.saturating_add("Path.here".len()))
            ),
            "a declared `∷∷` keeps its reading as the name, and the refusal stays at the path: \
             {refused:?}"
        );
    }

    /// #5512: the parser mints a zero-width repair just before an operator
    /// written with one glyph too many, and the run reads as a name nothing
    /// declares. The repair yields to the run, so the refusal is at the run,
    /// naming the operator.
    #[test]
    fn an_operator_near_miss_behind_a_zero_width_repair_is_refused_at_the_run_5512()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let source = include_str!(
            "lower/unformatted/an-operator-near-miss-behind-a-zero-width-repair-is-refused-at-the-run-5512.gandr"
        );
        let start = source.find("=>>").unwrap_or_default();
        let pbg = grammar();
        let tree = repaired(&pbg, SourceText::from(source));
        let refused = refusal_in(&pbg, &tree);
        assert!(
            matches!(
                refused,
                LoweringRefusal::MalformedForm {
                    span: found,
                    fault: FormFault::MisspeltOperator(misspelt),
                    ..
                } if found == at(start, start.saturating_add(3)) && misspelt.as_ref() == "=>"
            ),
            "`=>>` is refused at the run as `=>`: {refused:?}"
        );
    }

    /// #4944: the bracket of an element index `xs[i]` can parse as no static
    /// argument. Or the form can take no static argument. Then the form is
    /// malformed at the bracket or after it. The refusal is at the bracket,
    /// as a bare index that names `.#[ … ]`. A malformed form after a closed
    /// static bracket keeps its refusal.
    #[test]
    fn a_bare_index_that_parses_as_no_argument_is_refused_at_its_bracket_4944()
    {
        let pbg = grammar();
        for (source, written) in [
            (
                "def passed(xs : Integer, i : Integer) -> -F Integer { let y = xs[i]; pure y }\n",
                "xs[i]",
            ),
            (
                "def summed(xs : Integer, i : Integer) -> -F Integer { xs[i + 1] }\n",
                "xs[i + 1]",
            ),
            (
                "def lent() -> -F Integer { var xs = 0; access shared xs[1] as w { pure w } }\n",
                "xs[1]",
            ),
        ] {
            let tree = gandr_surface_parser::parse(&pbg, SourceText::from(source))
                .expect("the parser reads the source")
                .into_tree();
            let bracket = source
                .find(written)
                .map_or(0_usize, |at| at.saturating_add(2));
            assert!(
                matches!(
                    refusal_in(&pbg, &tree),
                    LoweringRefusal::MalformedForm {
                        span,
                        fault: FormFault::BareIndex,
                        ..
                    } if usize::from(span.start()) == bracket
                        && usize::from(span.end()) == bracket.saturating_add(1)
                ),
                "`{written}` is refused at its bracket: {:?}",
                refusal_in(&pbg, &tree)
            );
        }
        let tree = parsed(
            &pbg,
            SourceText::from(include_str!(
                "lower/unformatted/a-bare-index-that-parses-as-no-argument-is-refused-at-its-bracket-4944-tree.gandr"
            )),
        );
        assert!(
            matches!(refusal_in(&pbg, &tree), LoweringRefusal::UnresolvedName { span, name }
                if span == crate::fixture::span(ByteOffset::from(35_usize), ByteOffset::from(40_usize))
                    && name == SurfaceName::from("zebra")),
            "a static bracket closed before the refusal leaves it where it was: {:?}",
            refusal_in(&pbg, &tree)
        );
    }

    #[test]
    fn a_tile_out_of_place_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def x ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(6_usize, 7_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 7_usize), &[
            keyword, name, close,
        ]);
        let tree = made.module(at(0_usize, 7_usize), &[declaration]);

        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(6_usize, 7_usize),
                form: FormName::DECLARATION,
                fault: FormFault::MisplacedTile,
            },
            "a declaration with no tail closes where its tail should open"
        );
    }

    #[test]
    fn a_root_that_is_not_a_module_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = 3 ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("number.expression"),
            Spelled("number"),
            at(8_usize, 9_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(10_usize, 11_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 11_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.finish(declaration);
        let mut arena = CoreArena::new();

        assert_eq!(
            lower_module(
                &pbg,
                &tree,
                &mut arena,
                LoweringBudget::DEFAULT,
                Recognition::default()
            ),
            Err(LoweringRefusal::OutOfFragment {
                span: at(0_usize, 11_usize),
                form: FormName::DECLARATION,
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
            }),
            "a tree rooted at a declaration is not a module"
        );
    }

    #[test]
    fn a_tree_of_layout_alone_is_an_empty_module_and_a_repaired_root_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let lowered = |tree: &SyntaxTree<'static>| {
            let mut arena = CoreArena::new();
            lower_module(
                &pbg,
                tree,
                &mut arena,
                LoweringBudget::DEFAULT,
                Recognition::default(),
            )
            .map(|module| module.declarations().iter().len())
        };
        let mut made = Handmade::new(&pbg, SourceText::from("  "));
        let space = made.raw(
            gandr_surface_syntax::NodeLabel::Space,
            at(0_usize, 2_usize),
            &[],
        );
        assert_eq!(
            lowered(&made.finish(space)),
            Ok(0_usize),
            "a tree that is only layout lowers to a module of no declarations"
        );
        let mut made = Handmade::new(&pbg, SourceText::from(""));
        let ghost = made.raw(
            gandr_surface_syntax::NodeLabel::GhostClose {
                sort: gandr_surface_syntax::GroutSort::from(0_u16),
                class: gandr_surface_syntax::ClosingClass::Brace,
                reach: gandr_surface_syntax::CloseReach::NONE,
            },
            at(0_usize, 0_usize),
            &[],
        );
        assert_eq!(
            lowered(&made.finish(ghost)),
            Err(LoweringRefusal::MalformedForm {
                span: at(0_usize, 0_usize),
                form: FormName::ROOT,
                fault: FormFault::Repaired(Repair::GhostClose(
                    gandr_surface_syntax::ClosingClass::Brace
                )),
            }),
            "a root the parser had to repair is malformed, not empty"
        );
    }

    #[test]
    fn a_tree_of_another_grammar_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let foreign = GrammarFingerprint::from(0_u64);
        let mut made = Handmade::under(&pbg, SourceText::from("x"), foreign);
        let name = made.tile(
            Rule("identifier.expression"),
            Spelled("identifier"),
            at(0_usize, 1_usize),
        );
        let tree = made.module(at(0_usize, 1_usize), &[name]);
        let mut arena = CoreArena::new();
        let refused = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::GrammarMismatch {
                tree: foreign,
                grammar: pbg.fingerprint(),
            },
            "a tree molded under another grammar is refused before any mold is read"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "the caller paired the wrong tree and grammar"
        );
        assert_eq!(
            refused.span(),
            Maybe::Absent(refusal_span::Absent::Run),
            "the refusal is about the run, not a position in the source"
        );
    }

    #[test]
    fn a_mold_the_grammar_does_not_hold_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let foreign = MoldId::from(u32::MAX);
        let mut made = Handmade::new(&pbg, SourceText::from("x"));
        let stray = made.raw(NodeLabel::Tile(foreign), at(0_usize, 1_usize), &[]);
        let tree = made.module(at(0_usize, 1_usize), &[stray]);
        let mut arena = CoreArena::new();
        let refused = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::UnknownMold {
                span: at(0_usize, 1_usize),
                mold: foreign,
            },
            "a mold outside the grammar's table is refused where it stands"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "a foreign mold is the engine's fault, not the author's"
        );
    }

    #[test]
    fn an_unknown_attribute_is_refused_with_its_suggestion()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ check ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnknownAttribute {
                span: at(3_usize, 8_usize),
                name: SurfaceName::from("check"),
                suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
            },
            "a near miss is refused with the registered name it nearly spells"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an unknown attribute is the author's mistake"
        );
    }

    #[test]
    fn an_attribute_written_twice_for_one_name_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ checks ] @[ checks ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::DuplicateAttribute {
                span: at(15_usize, 21_usize),
                name: SurfaceName::from("checks"),
                first: at(3_usize, 9_usize),
            },
            "the second spelling is refused, naming the first"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a duplicate attribute is the author's mistake"
        );
    }

    #[test]
    fn a_schema_taking_a_payload_refuses_an_absent_one()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::MissingPayload {
                span: at(3_usize, 7_usize),
                name: registered(SurfaceName::from("owes")),
                expected: schema_of(SurfaceName::from("owes")),
            },
            "an attribute whose schema takes a payload is refused without one"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a missing payload is the author's mistake"
        );
    }

    #[test]
    fn a_non_value_payload_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes(pure 1) ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::NonValuePayload {
                span: at(8_usize, 14_usize),
                name: registered(SurfaceName::from("owes")),
                form: FormName::from(NamedKind("pure_expression")),
            },
            "a computation cannot stand as a payload"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a non-value payload is the author's mistake"
        );
    }

    #[test]
    fn a_payload_of_the_wrong_form_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes(\"one\") ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::IllTypedPayload {
                span: at(8_usize, 13_usize),
                name: registered(SurfaceName::from("owes")),
                expected: schema_of(SurfaceName::from("owes")),
                written: payload_form(Former::Text),
            },
            "a payload whose form the schema does not admit is refused at the payload"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an ill-typed payload is the author's mistake"
        );
    }

    #[test]
    fn a_names_payload_holding_other_than_names_is_refused_at_the_payload()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (source, payload) in [
            (
                include_str!(
                    "lower/unformatted/a-names-payload-holding-other-than-names-is-refused-at-the-payload-1.gandr"
                ),
                at(30_usize, 37_usize),
            ),
            (
                include_str!(
                    "lower/unformatted/a-names-payload-holding-other-than-names-is-refused-at-the-payload-2.gandr"
                ),
                at(30_usize, 34_usize),
            ),
        ] {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            assert_eq!(
                outcomes(&module).last().copied(),
                Some(DeclarationOutcome::Refused(
                    LoweringRefusal::IllTypedPayload {
                        span: payload,
                        name: registered(SurfaceName::from("respects")),
                        expected: AttributeSchema::Names,
                        written: crate::attribute::PayloadForm::OtherValue,
                    }
                )),
                "a value that is not a name or a tuple of names is no list of names: {source}"
            );
        }
    }

    #[test]
    fn a_marker_given_a_payload_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("@[ checks(1) ] def a = 3 ;")),
            LoweringRefusal::IllTypedPayload {
                span: at(10_usize, 11_usize),
                name: registered(SurfaceName::from("checks")),
                expected: AttributeSchema::Marker,
                written: payload_form(Former::Number),
            },
            "a marker takes no payload, and one written is refused at the payload"
        );
    }

    /// #492: `form` takes one of its words, read as written: `explicit` is
    /// no declared name, and is filed with no value; a word it does not name
    /// and a text are refused at the payload.
    #[test]
    fn a_form_payload_is_read_as_one_of_its_words()
    {
        use crate::attribute::PayloadForm;
        use crate::attribute::RegisteredAttribute;
        use crate::attribute::payload;

        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("@[ form(explicit) ] def a : Integer ;"),
            &mut arena,
        );
        let [declaration] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("one name is declared");
        };
        assert!(
            !matches!(declaration.outcome(), DeclarationOutcome::Refused(_)),
            "the word is not looked up in scope"
        );
        let Maybe::Present(key) = declaration.signature()
        else {
            panic!("the name has a signature");
        };
        let [ref entry] = *module.attributes().entries(key)
        else {
            panic!("one attribute is filed under the signature");
        };
        assert_eq!(
            (entry.name(), entry.payload()),
            (
                RegisteredAttribute::FORM,
                Maybe::Absent(payload::Absent::Word)
            ),
            "the entry is filed with no value"
        );
        let expected = schema_of(SurfaceName::from("form"));
        assert_eq!(
            refusal(SourceText::from("@[ form(lazy) ] def a = 3 ;")),
            LoweringRefusal::IllTypedPayload {
                span: at(8_usize, 12_usize),
                name: RegisteredAttribute::FORM,
                expected,
                written: PayloadForm::OtherWord,
            },
            "a word `form` does not take is refused at the payload"
        );
        assert_eq!(
            refusal(SourceText::from("@[ form(\"explicit\") ] def a = 3 ;")),
            LoweringRefusal::IllTypedPayload {
                span: at(8_usize, 18_usize),
                name: RegisteredAttribute::FORM,
                expected,
                written: PayloadForm::Text,
            },
            "the word is no text"
        );
    }

    /// #3575: a `builtin` mark gives the declaration it decorates the role
    /// its word names, and an unmarked declaration takes none. A word that
    /// names no role is refused at the payload.
    #[test]
    fn a_builtin_mark_gives_its_declaration_the_role_3575()
    {
        use gandr_kernel_term::Builtin;
        use gandr_kernel_term::builtin_role;

        use crate::attribute::PayloadForm;
        use crate::attribute::RegisteredAttribute;

        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-builtin-mark-gives-its-declaration-the-role-3575-module.gandr"
            )),
            &mut arena,
        );
        let role = |name: &str| {
            let Some(declaration) = module
                .declarations()
                .iter()
                .find(|declaration| declaration.name() == SurfaceName::from(name))
            else {
                panic!("`{name}` is declared");
            };
            module.builtin(declaration)
        };
        assert_eq!(
            role("a"),
            Maybe::Present(Builtin::IrArgs),
            "the mark gives the role its word names"
        );
        assert_eq!(
            role("b"),
            Maybe::Absent(builtin_role::Absent::Unmarked),
            "an unmarked declaration takes no role"
        );
        assert!(
            matches!(
                refusal(SourceText::from("@[ builtin(irElim) ] def a = 3 ;")),
                LoweringRefusal::IllTypedPayload {
                    name: RegisteredAttribute::BUILTIN,
                    written: PayloadForm::OtherWord,
                    ..
                }
            ),
            "a word that names no role is refused at the payload"
        );
    }

    /// #2077: `decomposes` takes one form unquoted, read as its spelling: the
    /// web's node names are no declared names, and the spelling joins a form
    /// written across lines into one. A text is refused at the payload.
    #[test]
    fn a_spelled_payload_is_read_back_where_it_was_filed()
    {
        use crate::attribute::AttributeRegistry;
        use crate::attribute::PayloadForm;
        use crate::attribute::payload;

        let Maybe::Present((decomposes, expected)) =
            AttributeRegistry::lookup(SurfaceName::from("decomposes"))
        else {
            panic!("`decomposes` is registered");
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/unformatted/a-spelled-payload-is-read-back-where-it-was-filed-module.gandr"
            )),
            &mut arena,
        );
        let [declaration, other] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("two names are declared");
        };
        assert!(
            !matches!(declaration.outcome(), DeclarationOutcome::Refused(_)),
            "the web's node names are not looked up in scope: {:?}",
            declaration.outcome()
        );
        let (Maybe::Present(key), Maybe::Present(unspelled)) =
            (declaration.signature(), other.signature())
        else {
            panic!("both names have a signature");
        };
        let [ref entry] = *module.attributes().entries(key)
        else {
            panic!("one attribute is filed under the signature");
        };
        assert_eq!(
            (entry.name(), entry.payload()),
            (decomposes, Maybe::Absent(payload::Absent::Spelled)),
            "the entry is filed with no value"
        );
        assert_eq!(
            module
                .attributes()
                .spelled(key, entry.span())
                .map(String::as_str),
            Some("series (event right 0) (parallel (event left 1) (event right 1))"),
            "the spelling is filed beside the entry, its layout one space"
        );
        assert_eq!(
            module.attributes().spelled(unspelled, entry.span()),
            None,
            "another declaration has no spelling"
        );
        assert_eq!(
            refusal(SourceText::from("@[ decomposes(\"x\") ] def a = 3 ;")),
            LoweringRefusal::IllTypedPayload {
                span: span(ByteOffset::from(14_usize), ByteOffset::from(17_usize)),
                name: decomposes,
                expected,
                written: PayloadForm::Text,
            },
            "the form is unquoted"
        );
    }

    /// #2077: a named payload, `decomposes(primes = 2)`, is spelled with its
    /// name where the spelled schema stands, and is ill-typed from its name
    /// through its value where any other schema stands.
    #[test]
    fn a_named_payload_is_spelled_with_its_name_2077()
    {
        use crate::attribute::AttributeRegistry;
        use crate::attribute::PayloadForm;

        let Maybe::Present((decomposes, _)) =
            AttributeRegistry::lookup(SurfaceName::from("decomposes"))
        else {
            panic!("`decomposes` is registered");
        };
        let Maybe::Present((owes, expected)) = AttributeRegistry::lookup(SurfaceName::from("owes"))
        else {
            panic!("`owes` is registered");
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/unformatted/a-named-payload-is-spelled-with-its-name-2077-module.gandr"
            )),
            &mut arena,
        );
        let [declaration] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("one name is declared");
        };
        let Maybe::Present(key) = declaration.signature()
        else {
            panic!("the name has a signature");
        };
        assert!(
            !matches!(declaration.outcome(), DeclarationOutcome::Refused(_)),
            "the payload's name is not looked up in scope: {:?}",
            declaration.outcome()
        );
        let [ref entry] = *module.attributes().entries(key)
        else {
            panic!("one attribute is filed under the signature");
        };
        assert_eq!(
            (
                entry.name(),
                module
                    .attributes()
                    .spelled(key, entry.span())
                    .map(String::as_str)
            ),
            (decomposes, Some("primes = 2")),
            "the name is spelled before the value"
        );
        assert_eq!(
            refusal(SourceText::from("@[ owes(n = 1) ] def a : Integer ;")),
            LoweringRefusal::IllTypedPayload {
                span: span(ByteOffset::from(8_usize), ByteOffset::from(13_usize)),
                name: owes,
                expected,
                written: PayloadForm::Named,
            },
            "an integer payload takes no name"
        );
    }

    /// #3338: `traces` is written once per channel, and each entry's spelling
    /// is read back by its own span; any other attribute written twice is
    /// refused.
    #[test]
    fn traces_is_written_once_per_channel_3338()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/traces-is-written-once-per-channel-3338-module.gandr"
            )),
            &mut arena,
        );
        let [declaration] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("one name is declared");
        };
        let Maybe::Present(key) = declaration.signature()
        else {
            panic!("the name has a signature");
        };
        let traces = crate::attribute::RegisteredAttribute::TRACES;
        let spelled: Vec<(_, Option<&str>)> = module
            .attributes()
            .entries(key)
            .iter()
            .map(|entry| {
                (
                    entry.name(),
                    module
                        .attributes()
                        .spelled(key, entry.span())
                        .map(String::as_str),
                )
            })
            .collect();
        assert_eq!(
            spelled,
            [
                (traces, Some("decomposes a (event left 0)")),
                (traces, Some("primes b 1")),
            ],
            "each channel's entry is filed with its own spelling, in written order"
        );
        assert!(
            matches!(
                refusal(SourceText::from(
                    "@[ decomposes(event left 0), decomposes(event left 1) ] def a = 3 ;"
                )),
                LoweringRefusal::DuplicateAttribute { name, .. } if name == SurfaceName::from("decomposes")
            ),
            "another spelled attribute is still written once"
        );
    }

    #[test]
    fn an_attribute_is_filed_under_its_declaration_key()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("@[ owes(1) ] def a : Integer ;"),
            &mut arena,
        );
        let [declaration] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("one name is declared");
        };
        let Maybe::Present(key) = declaration.signature()
        else {
            panic!("the name has a signature");
        };
        let [ref entry] = *module.attributes().entries(key)
        else {
            panic!("one attribute is filed under the signature");
        };

        assert_eq!(
            (entry.name(), entry.span()),
            (registered(SurfaceName::from("owes")), at(3_usize, 10_usize)),
            "the entry names the attribute and where it was written"
        );
        let Maybe::Present(payload) = entry.payload()
        else {
            panic!("the entry carries its payload");
        };
        assert_eq!(
            arena.value(payload),
            Some(&Value::Literal(integer(SourceFragment::from("1")))),
            "the payload is the lowered value"
        );
    }

    #[test]
    fn documentation_is_filed_under_the_declaration_key()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/documentation-is-filed-under-the-declaration-key-module.gandr"
            )),
            &mut arena,
        );
        let [square, cube, color, plain] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("four names are declared");
        };
        let key = |declaration: &crate::module::LoweredDeclaration<'_>| {
            let Maybe::Present(key) = declaration.definition()
            else {
                panic!("the name has a definition");
            };
            key
        };
        let text = |key| match module.documentation(key) {
            Maybe::Present(found) => Some(String::from(found.text().as_ref())),
            Maybe::Absent(_) => None,
        };

        assert_eq!(
            text(key(square)).as_deref(),
            Some("Squares, as [cube] cubes.\nTwice."),
            "a `///` run is one text, its link to a later declaration resolving"
        );
        assert!(!matches!(square.outcome(), DeclarationOutcome::Refused(_)));
        assert_eq!(text(key(cube)).as_deref(), Some("Cubes."));
        assert_eq!(text(key(color)).as_deref(), Some("A colour."));
        assert_eq!(text(key(plain)), None, "an undocumented form has none");
        let mut bare_arena = CoreArena::new();
        let bare = lowered(SourceText::from("def square = 1 ;"), &mut bare_arena);
        let [undocumented] = *bare.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("one name is declared");
        };
        assert_eq!(
            key(undocumented),
            key(square),
            "documentation leaves the declaration's identity alone"
        );
    }

    #[test]
    fn each_use_of_a_deprecated_declaration_is_listed()
    {
        let text =
            include_str!("lower/fixtures/each-use-of-a-deprecated-declaration-is-listed.gandr");
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(text), &mut arena);
        let listed: Vec<(&str, String, Option<String>, Option<String>)> = module
            .deprecated_uses(&arena)
            .into_iter()
            .map(|used| {
                (
                    text.get(usize::from(used.span.start()) .. usize::from(used.span.end()))
                        .unwrap_or_default(),
                    alloc::format!("{}", used.name),
                    used.deprecation.since,
                    used.deprecation.note,
                )
            })
            .collect();
        let starts: Vec<usize> = module
            .deprecated_uses(&arena)
            .iter()
            .map(|used| usize::from(used.span.start()))
            .collect();
        let stated = (Some(String::from("0.2")), Some(String::from("use cube")));
        assert_eq!(
            listed,
            [
                (
                    "square",
                    String::from("square"),
                    stated.0.clone(),
                    stated.1.clone()
                ),
                ("old", String::from("old"), None, None),
                ("square", String::from("square"), stated.0, stated.1),
                ("member", String::from("member"), None, None),
            ],
            "each use of a marked declaration is listed with what its attribute states, an \
             attribute on the signature half marking the whole declaration and a module \
             member's use through its dotted path among them; an unmarked use and the \
             declarations' own names are not"
        );
        assert_eq!(
            starts,
            [
                (text.find("= square"), 2_usize),
                (text.find("= old"), 2_usize),
                (text.rfind("= square"), 2_usize),
                (text.rfind(".member"), 1_usize),
            ]
            .map(|(at, past)| at.unwrap_or_default().saturating_add(past)),
            "in source order, at each use, a dotted path's at its last segment"
        );
    }

    #[test]
    fn a_link_to_a_missing_name_is_refused_at_the_link()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/unformatted/a-link-to-a-missing-name-is-refused-at-the-link-module.gandr"
            )),
            &mut arena,
        );
        let [stale, linked] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("two names are declared");
        };

        assert_eq!(
            stale.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedDocLink {
                span: at(9_usize, 13_usize),
                name: SurfaceName::from("gone"),
            }),
            "the refusal stands at the link's name"
        );
        assert!(
            !matches!(linked.outcome(), DeclarationOutcome::Refused(_)),
            "a link to a declared name resolves"
        );
    }

    #[test]
    fn a_respects_attribute_names_its_laws_through_either_form()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def p : Integer ; def q : Integer ; \
                 @[ respects(*{q, p}) ] def r(n : Integer) -> -F Integer { return n } \
                 @[ respects(p) ] def s : +U (Integer -> -F Integer) ; \
                 def s = thunk { fun (n) { return n } } ; \
                 def t(n : Integer) -> -F Integer { return n }",
            ),
            &mut arena,
        );
        let named = |wanted: &str| {
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"))
        };
        let (p, q) = (named("p").constant(), named("q").constant());
        assert_eq!(
            module.laws(named("r")),
            [q, p].as_slice(),
            "a definition names its laws in the order written"
        );
        assert_eq!(
            module.laws(named("s")),
            [p].as_slice(),
            "a signature names its law where its definition names none"
        );
        assert!(
            module.laws(named("t")).is_empty(),
            "an undecorated declaration names none"
        );
    }

    #[test]
    fn a_refused_declarations_attributes_are_filed_under_its_key()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                r#"@[ refuses("UnresolvedName") ] def a = b ; @[ owes(1) ] def c : Intgr ;"#,
            ),
            &mut arena,
        );
        let [defined, signed] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("two names are declared");
        };

        assert_eq!(
            (defined.outcome(), signed.outcome()),
            (
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName {
                    span: at(39_usize, 40_usize),
                    name: SurfaceName::from("b"),
                }),
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedTypeHead {
                    span: at(64_usize, 69_usize),
                    head: at(64_usize, 69_usize),
                    name: SurfaceName::from("Intgr"),
                    arity: HeadArity::Nullary,
                }),
            ),
            "both declarations are refused by their operands"
        );
        let (Maybe::Present(definition), Maybe::Present(signature)) =
            (defined.definition(), signed.signature())
        else {
            panic!("each refused name keeps the key of the form it wrote");
        };
        let [ref refuses] = *module.attributes().entries(definition)
        else {
            panic!("one attribute is filed under the refused definition");
        };
        let [ref owes] = *module.attributes().entries(signature)
        else {
            panic!("one attribute is filed under the refused signature");
        };
        assert_eq!(
            ((refuses.name(), refuses.span()), (owes.name(), owes.span())),
            (
                (
                    registered(SurfaceName::from("refuses")),
                    at(3_usize, 28_usize)
                ),
                (
                    registered(SurfaceName::from("owes")),
                    at(46_usize, 53_usize)
                ),
            ),
            "each entry names its attribute and where it was written"
        );
        let (Maybe::Present(named), Maybe::Present(counted)) = (refuses.payload(), owes.payload())
        else {
            panic!("each entry carries its payload");
        };
        assert_eq!(
            (arena.value(named), arena.value(counted)),
            (
                Some(&Value::Literal(text(SourceFragment::from(
                    "UnresolvedName"
                )))),
                Some(&Value::Literal(integer(SourceFragment::from("1")))),
            ),
            "a refused declaration's payloads are lowered all the same"
        );
    }

    #[test]
    fn a_refused_declarations_compound_payload_is_lowered_to_its_leaves()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def p : Integer ; def q : Integer ; @[ respects(*{q, p}) ] def r(n : Integer) -> \
                 -F Integer { return b }",
            ),
            &mut arena,
        );
        let named = |wanted: &str| {
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name().as_ref() == wanted)
                .unwrap_or_else(|| panic!("`{wanted}` is declared"))
        };
        assert!(
            matches!(named("r").outcome(), DeclarationOutcome::Refused(_)),
            "the body names nothing declared"
        );
        let (p, q) = (named("p").constant(), named("q").constant());
        assert_eq!(
            module.laws(named("r")),
            [q, p].as_slice(),
            "the names inside the payload's tuple are lowered under the refused declaration"
        );
    }

    #[test]
    fn an_unended_form_reports_its_deepest_repair_first_written_among_equals()
    {
        let at = |point: usize| span(ByteOffset::from(point), ByteOffset::from(point));
        let pbg = grammar();
        for (source, point, why) in [
            (
                "def a = (1 + ) * ((2 + ) * 3)",
                22_usize,
                "the deeper hole wins though it is written later",
            ),
            (
                "def a = ((1 + ) * 3) * (2 + )",
                13_usize,
                "the deeper hole wins though it is written earlier",
            ),
            (
                "def a = (1 + ) * (2 + )",
                12_usize,
                "of two holes at one depth the first written wins",
            ),
            (
                "def a = ( * )",
                10_usize,
                "of two holes in one form the first written wins",
            ),
        ] {
            let tree = repaired(&pbg, SourceText::from(source));
            assert_eq!(
                refusal_in(&pbg, &tree),
                LoweringRefusal::MalformedForm {
                    span: at(point),
                    form: FormName::from(NamedKind("binary_expression")),
                    fault: FormFault::Repaired(Repair::Grout(
                        gandr_surface_syntax::GroutShape::Convex,
                    )),
                },
                "{why}: `{source}`"
            );
        }
    }

    /// The outcome of the declaration `wanted` in `module`.
    ///
    /// # Specification
    /// trivial.
    fn outcome_named<'source>(
        module: &crate::module::LoweredModule<'source>,
        wanted: impl AsRef<str>,
    ) -> DeclarationOutcome<'source>
    {
        let wanted = wanted.as_ref();
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name().as_ref() == wanted)
            .unwrap_or_else(|| panic!("`{wanted}` is declared"))
            .outcome()
    }

    #[test]
    fn a_lowered_module_counts_its_names_and_gives_up_its_origins()
    {
        let source = "def f(n : Integer) -> -F Integer { return n } def g = 1 ;";
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source), &mut arena);
        assert_eq!(usize::from(module.declaration_count()), 2_usize);
        let returner = source.find("-F Integer").expect("the returner is written");
        assert!(
            module.origins().comp_types().iter().any(|&(_, origin)| {
                usize::from(origin.span().start()) == returner
                    && usize::from(origin.span().end()) == returner + "-F Integer".len()
            }),
            "the returner type is recorded where it is written"
        );
        assert_eq!(
            module.into_origins().declaration_count(),
            crate::origin::OriginCount::from(2_usize),
            "the table given up holds both declarations"
        );
    }

    #[test]
    fn a_signature_written_after_its_signed_function_is_no_duplicate()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(n : Integer) -> -F Integer { return n } def f : +U (Integer -> -F \
                 Integer) ;",
            ),
            &mut arena,
        );
        assert!(
            matches!(
                outcome_named(&module, "f"),
                DeclarationOutcome::Completed { .. }
            ),
            "the written signature joins the function as it does written first: {:?}",
            outcome_named(&module, "f")
        );
    }

    #[test]
    fn a_module_respects_attribute_files_its_laws_under_the_module()
    {
        let pbg = grammar();
        let source =
            SourceText::from("def p : Integer ; @[ respects(p) ] module M where { def x = 1 ; }");
        let tree = parsed(&pbg, source);
        let mut arena = CoreArena::new();
        let module = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        let [p, _] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("`p` and `x` are declared");
        };
        let filed = tree
            .positions()
            .filter_map(|at| tree.key(at))
            .map(|key| crate::unit::UnitKey::new(crate::unit::SourceIndex::default(), key))
            .filter(|&key| module.attributes().laws(key) == [p.constant()])
            .count();
        assert_eq!(
            filed, 1_usize,
            "the module's form carries the law it names, and no other form does"
        );
    }

    #[test]
    fn a_module_s_documentation_is_filed_under_its_key_1135()
    {
        let pbg = grammar();
        let text = include_str!(
            "lower/fixtures/a-module-s-documentation-is-filed-under-its-key-1135.gandr"
        );
        let source = SourceText::from(text);
        let tree = parsed(&pbg, source);
        let mut arena = CoreArena::new();
        let module = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        let mut filed: Vec<(ByteOffset, String, &str)> = tree
            .positions()
            .filter_map(|at| tree.node(at).map(|node| (at, node)))
            .filter_map(|(at, node)| {
                let key =
                    crate::unit::UnitKey::new(crate::unit::SourceIndex::default(), tree.key(at)?);
                let Maybe::Present(found) = module.documentation(key)
                else {
                    return None;
                };
                let written =
                    text.get(usize::from(node.span().start()) .. usize::from(node.span().end()))?;
                Some((
                    node.span().start(),
                    String::from(found.text().as_ref()),
                    written,
                ))
            })
            .collect();
        filed.sort_unstable_by_key(|&(start, ..)| start);
        let documented: Vec<(&str, bool)> = filed
            .iter()
            .map(|&(_, ref doc, written)| {
                (doc.as_str(), match doc.as_str() {
                    "A module." => written.contains("module A where {"),
                    "A def." => written.contains("def x") && !written.contains("module"),
                    "The inner module." => {
                        written.contains("module B where {") && !written.contains("module A")
                    },
                    _ => written.contains("module C where {") && !written.contains("module A"),
                })
            })
            .collect();
        assert_eq!(
            documented,
            [
                ("A module.", true),
                ("A def.", true),
                ("The inner module.", true),
                ("An attribute decorates this module. See [gone].", true)
            ],
            "a module's, a member's, a nested module's and a decorated module's documentation \
             each stand under their own form, in source order"
        );
        let gone = text.find("gone").expect("the link is written");
        assert_eq!(
            outcome_named(&module, "z"),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedDocLink {
                span: span(ByteOffset::from(gone), ByteOffset::from(gone + 4)),
                name: SurfaceName::from("gone"),
            }),
            "a module's link to a missing name refuses its first member at the link"
        );
        for name in ["x", "y"] {
            assert!(
                !matches!(outcome_named(&module, name), DeclarationOutcome::Refused(_)),
                "`{name}` is refused by nothing: {:?}",
                outcome_named(&module, name)
            );
        }
    }

    #[test]
    fn a_source_s_documentation_is_filed_under_the_source_1365()
    {
        let pbg = grammar();
        let base = include_str!(
            "lower/unformatted/a-source-s-documentation-is-filed-under-the-source-1365-base.gandr"
        );
        let text = format!(
            include_str!(
                "lower/unformatted/a-source-s-documentation-is-filed-under-the-source-1365.gandr"
            ),
            base = base
        );
        let unit = crate::unit::Unit::new(alloc::vec![
            crate::unit::UnitSource::new(ByteOffset::from(0_usize), alloc::vec::Vec::new()),
            crate::unit::UnitSource::new(ByteOffset::from(base.len()), alloc::vec::Vec::new()),
        ])
        .unwrap();
        let tree = parsed(&pbg, SourceText::from(text.as_str()));
        let mut arena = CoreArena::new();
        let module = super::lower_unit(
            &pbg,
            &tree,
            &unit,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
            &mut crate::coincide::Decisions::none(),
        )
        .unwrap();
        let own = |source: usize| match module
            .source_documentation(crate::unit::SourceIndex::from(source))
        {
            Maybe::Present(found) => Some(String::from(found.text().as_ref())),
            Maybe::Absent(_) => None,
        };
        assert_eq!(
            own(0_usize).as_deref(),
            Some("The base.\nSee [b]."),
            "the base's run is the base's own"
        );
        assert_eq!(
            own(1_usize).as_deref(),
            Some("The importer,\nwith two runs. See [gone]."),
            "a source's two runs join in source order, and a `///` run at the root is no source's"
        );
        assert_eq!(
            own(2_usize),
            None,
            "a source the unit does not hold has none"
        );
        let gone = text.find("gone").expect("the link is written");
        assert_eq!(
            outcome_named(&module, "b"),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedDocLink {
                span: span(ByteOffset::from(gone), ByteOffset::from(gone + 4)),
                name: SurfaceName::from("gone"),
            }),
            "a source's link to a missing name refuses its first declaration at the link"
        );
        for name in ["a", "c"] {
            assert!(
                !matches!(outcome_named(&module, name), DeclarationOutcome::Refused(_)),
                "`{name}` is refused by nothing: {:?}",
                outcome_named(&module, name)
            );
        }
    }

    #[test]
    fn a_link_resolves_to_a_module_its_member_or_a_constructor()
    {
        let mut arena = CoreArena::new();
        let source = include_str!(
            "lower/fixtures/a-link-resolves-to-a-module-its-member-or-a-constructor.gandr"
        );
        let module = lowered(SourceText::from(source), &mut arena);
        assert!(
            !matches!(outcome_named(&module, "a"), DeclarationOutcome::Refused(_)),
            "each link names something declared: {:?}",
            outcome_named(&module, "a")
        );
        let gone = source.find("gone").expect("the link is written");
        assert_eq!(
            outcome_named(&module, "b"),
            DeclarationOutcome::Refused(LoweringRefusal::UnresolvedDocLink {
                span: span(ByteOffset::from(gone), ByteOffset::from(gone + 4)),
                name: SurfaceName::from("gone"),
            }),
            "a module beside a missing name does not answer for it"
        );
    }

    /// #4963: a link that names a declaration keeps it, read where the
    /// documentation stands. A link to a module or a constructor keeps none.
    #[test]
    fn a_link_keeps_the_declaration_it_resolves_to_4963()
    {
        let mut arena = CoreArena::new();
        let source =
            include_str!("lower/fixtures/a-link-keeps-the-declaration-it-resolves-to-4963.gandr");
        let module = lowered(SourceText::from(source), &mut arena);
        let declared = module.declarations().iter().collect::<Vec<_>>();
        let [a, b, inner, _, y, ..] = *declared
        else {
            panic!("the names are declared: {declared:?}");
        };
        let targets = |declaration: &crate::module::LoweredDeclaration<'_>| {
            let Maybe::Present(key) = declaration.definition()
            else {
                panic!("the name has a definition");
            };
            let Maybe::Present(found) = module.documentation(key)
            else {
                panic!("the name is documented");
            };
            found
                .targets()
                .iter()
                .map(|target| (String::from(target.name().as_ref()), target.constant()))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            targets(a),
            [
                (String::from("b"), b.constant()),
                (String::from("M.x"), inner.constant()),
                (String::from("y"), y.constant()),
            ],
            "each declaration linked keeps it once; a module and a constructor keep none"
        );
        assert_eq!(
            targets(inner),
            [
                (String::from("x"), inner.constant()),
                (String::from("b"), b.constant()),
            ],
            "a member's link reads its own module before any other"
        );
    }

    #[test]
    fn a_module_attribute_refusal_refuses_its_first_member_alone()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/unformatted/a-module-attribute-refusal-refuses-its-first-member-alone-module.gandr"
            )),
            &mut arena,
        );
        assert_eq!(
            outcome_named(&module, "x"),
            DeclarationOutcome::Refused(LoweringRefusal::UnknownAttribute {
                span: at(3_usize, 9_usize),
                name: SurfaceName::from("checkz"),
                suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
            }),
            "the misspelt attribute is the module's first declaration's refusal"
        );
        assert!(
            !matches!(outcome_named(&module, "y"), DeclarationOutcome::Refused(_)),
            "and the module's neighbour lowers"
        );
    }

    #[test]
    fn an_unknown_capital_where_a_value_is_read_is_unresolved_2653()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def a = Foo ;"));
        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 11_usize),
                name: SurfaceName::from("Foo"),
            },
            "only `Type` is a universe; another unanswered capital names nothing"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a capital naming nothing is the author's mistake, never an unbuilt form"
        );
    }

    /// A pattern the table declines is refused by the feature its row
    /// carries; a form the table reads that stands where a pattern is read is
    /// refused as an unread pattern.
    #[test]
    fn an_unread_pattern_names_its_feature()
    {
        let source =
            "def f(p : Integer * Integer) -> -F Integer { match p { | *{a, ..?} => return 0 } }";
        let refused = refusal(SourceText::from(source));
        assert!(
            matches!(refused, LoweringRefusal::OutOfFragment {
                form,
                boundary: FragmentBoundary::Unadmitted(Unbuilt::RestPattern),
                ..
            } if form == FormName::from(NamedKind("rest_pattern"))),
            "a rest pattern outside a list is declined by its own feature: {refused:?}"
        );
        assert_eq!(
            super::unread_pattern(FormName::from(NamedKind("rest_pattern"))),
            Unbuilt::RestPattern,
            "a declined row's feature names the pattern"
        );
        assert_eq!(
            super::unread_pattern(FormName::from(NamedKind("lambda_expression"))),
            Unbuilt::UnreadPattern,
            "a form the table reads names no feature of its own as a pattern"
        );
        assert_eq!(
            super::unread_pattern(FormName::from(NamedKind("representable_universe_type"))),
            Unbuilt::UnreadPattern,
            "nor does a form the table admits elsewhere"
        );
    }

    #[test]
    fn a_split_of_three_components_lowers()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { let *{x, y, z} = *{1, 2, 3} ; return x } ;"),
            &mut arena,
        );
        assert!(
            !matches!(outcome_named(&module, "a"), DeclarationOutcome::Refused(_)),
            "a tuple pattern takes two components or more: {:?}",
            outcome_named(&module, "a")
        );
    }

    #[test]
    fn a_prefix_operator_takes_its_one_operand()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def f(n : Integer) -> -F Integer { - n }"),
            &mut arena,
        );
        assert!(
            matches!(
                outcome_named(&module, "f"),
                DeclarationOutcome::Completed { .. }
            ),
            "a negation is a tile before one operand: {:?}",
            outcome_named(&module, "f")
        );
    }

    #[test]
    fn a_negated_float_literal_is_float64_negation_1830()
    {
        let negation = |source: &'static str| {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            let body = body_of(module.declarations().iter().next().unwrap().outcome());
            let Some(&Value::Thunk(body)) = arena.value(body)
            else {
                panic!("`{source}` lowers to a thunk");
            };
            match arena.computation(body) {
                Some(&Computation::Primitive {
                    primitive,
                    arguments: gandr_core_term::primitive::Arguments::Unary(operand),
                }) => (
                    String::from(primitive.name().as_ref()),
                    arena.value(operand).cloned(),
                ),
                other => panic!("`{source}` lowers to a negation, not {other:?}"),
            }
        };
        assert_eq!(
            negation("def a = thunk { become - 0.5f64 } ;"),
            (
                String::from("float64.neg"),
                Some(Value::Literal(Literal::Float64(Float64Literal::from(
                    0.5_f64
                ))))
            ),
            "a negated suffixed float is the float's negation"
        );
        assert_eq!(
            negation("def a = thunk { become -(5) } ;").0,
            "neg",
            "a negation of a grouped integer stays the integer's negation"
        );
    }

    /// #4732: `- n` written on a natural literal is one negative literal, a
    /// value with no call, so it stands where a value definition holds it.
    #[test]
    fn a_negated_natural_literal_is_one_negative_literal_4732()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def a : Integer = - 5 ;"), &mut arena);
        let held = body_of(module.declarations().iter().next().unwrap().outcome());
        assert_eq!(
            arena.value(held),
            Some(&Value::Literal(Literal::Integer(IntegerLiteral::new(
                Sign::Negative,
                gandr_kernel_term::Magnitude::from_decimal_text(String::from("5"))
                    .expect("decimal digits"),
            )))),
            "the negation of a natural literal is the negative literal"
        );
        let text = "def a : Integer = - 5 ;";
        let covers = module.origins().covers();
        assert_eq!(covers.len(), 1, "the folded minus records its operand");
        let Some(&(operator, operand)) = covers.first()
        else {
            panic!("the cover is recorded");
        };
        assert_eq!(
            text.get(usize::from(operand.start()) .. usize::from(operand.end())),
            Some("5"),
            "the operand span is the digit"
        );
        assert_eq!(
            text.get(usize::from(operator.start()) .. usize::from(operator.end())),
            Some("- 5"),
            "the operator span is the folded literal"
        );
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def b(x : Integer) -> Integer { -(x) }"),
            &mut arena,
        );
        assert!(
            !matches!(
                module.declarations().iter().next().unwrap().outcome(),
                DeclarationOutcome::Refused(_)
            ),
            "a negated variable still lowers: {:?}",
            module.declarations().iter().next().unwrap().outcome()
        );
    }

    #[test]
    fn a_universe_level_at_or_past_the_greatest_has_none_above_2653()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        assert_eq!(
            refusal(SourceText::from(
                "def d : Type[+, 99999999999999999999999] ;"
            )),
            LoweringRefusal::NoUniverseAbove {
                span: at(16_usize, 39_usize),
                level: SurfaceName::from("99999999999999999999999"),
            },
            "the refusal stands at the level, not the whole universe"
        );
        let greatest = refusal(SourceText::from("def d : Type[+, 18446744073709551615] ;"));
        assert_eq!(
            greatest,
            LoweringRefusal::NoUniverseAbove {
                span: at(16_usize, 36_usize),
                level: SurfaceName::from("18446744073709551615"),
            },
            "the greatest level has no universe above it, so the lowering refuses it too"
        );
        assert_eq!(
            greatest.classify(),
            FailureClass::MalformedSource,
            "the language has no universe above the greatest, so the source asks for none"
        );
    }

    #[test]
    fn a_forward_member_applied_as_a_type_is_refused_at_its_head()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("module M where { def a : f(Integer) ; def f : Type -> Type ; }"),
            &mut arena,
        );
        assert_eq!(
            outcome_named(&module, "a"),
            DeclarationOutcome::Refused(LoweringRefusal::ForwardMemberReference {
                span: at(25_usize, 26_usize),
                name: SurfaceName::from("f"),
                declared: at(42_usize, 43_usize),
            }),
            "the refusal stands at the operator's name, not the whole application"
        );
    }

    #[test]
    fn a_static_lambda_binds_a_lowercase_name()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def t : Type -> Type ; def w : Type -> Type ; def w = fun (x) { t x } ;",
            ),
            &mut arena,
        );
        assert!(
            !matches!(outcome_named(&module, "w"), DeclarationOutcome::Refused(_)),
            "a type variable binds as a type identifier does: {:?}",
            outcome_named(&module, "w")
        );
    }

    /// #4508: one `fun` is a static lambda where its position states a static
    /// arrow — its definition's signature, an operator's parameter — and the
    /// dynamic lambda elsewhere. A static lambda binds one name and its body
    /// is a type, so two parameters and a block of statements are refused.
    #[test]
    fn a_lambda_s_position_decides_its_sort_4508()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def apply : (Type -> Type) -> Type -> Type ; def apply = fun (F) { fun (X) { F X } \
                 } ; def pairs : apply(fun (Y) { type(Y * Y) }, Integer) ; def id : +U (Integer -> \
                 -F Integer) ; def id = thunk { fun (x) { return x } } ; def two : Type -> Type -> \
                 Type ; def two = fun (A, B) { A } ; def held : Type -> Type ; def held = fun (A) { \
                 let x = A ; x } ;",
            ),
            &mut arena,
        );
        let body = |name: &str| arena.value(body_of(outcome_named(&module, name)));
        let Some(&Value::StaticLambda(over_f)) = body("apply")
        else {
            panic!("a definition at a static arrow is a static lambda");
        };
        assert!(
            matches!(arena.value(over_f), Some(&Value::StaticLambda(_))),
            "and so is the lambda its codomain's static arrow types"
        );
        let Some(&ValueType::Element { code, .. }) =
            arena.value_type(declared_of(outcome_named(&module, "pairs")))
        else {
            panic!("the operator applied where a type is read decodes");
        };
        let Some(&Value::StaticApplication(head, _)) = arena.value(code)
        else {
            panic!("the operator applies statically");
        };
        let Some(&Value::StaticApplication(_, argument)) = arena.value(head)
        else {
            panic!("to both its arguments");
        };
        assert!(
            matches!(arena.value(argument), Some(&Value::StaticLambda(_))),
            "an argument at a static arrow's parameter is a static lambda"
        );
        let Some(&Value::Thunk(suspended)) = body("id")
        else {
            panic!("the function is a thunk");
        };
        assert!(
            matches!(arena.computation(suspended), Some(&Computation::Lambda(_))),
            "a thunk's lambda is the dynamic one"
        );
        assert!(
            matches!(
                outcome_named(&module, "two"),
                DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                    boundary: FragmentBoundary::Arity(_),
                    ..
                })
            ),
            "a static lambda binds one name: {:?}",
            outcome_named(&module, "two")
        );
        assert!(
            matches!(
                outcome_named(&module, "held"),
                DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                    boundary: FragmentBoundary::WrongSort,
                    ..
                })
            ),
            "a static lambda's body is a type, not statements: {:?}",
            outcome_named(&module, "held")
        );
    }

    #[test]
    fn the_attribute_diagnostics_fire_on_a_refused_declaration()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let owes = registered(SurfaceName::from("owes"));
        let rows = [
            (
                r#"@[ check ] def a = b ;"#,
                LoweringRefusal::UnknownAttribute {
                    span: at(3_usize, 8_usize),
                    name: SurfaceName::from("check"),
                    suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
                },
            ),
            (
                r#"@[ checks ] @[ checks ] def a = b ;"#,
                LoweringRefusal::DuplicateAttribute {
                    span: at(15_usize, 21_usize),
                    name: SurfaceName::from("checks"),
                    first: at(3_usize, 9_usize),
                },
            ),
            (
                r#"@[ owes ] def a = b ;"#,
                LoweringRefusal::MissingPayload {
                    span: at(3_usize, 7_usize),
                    name: owes,
                    expected: schema_of(SurfaceName::from("owes")),
                },
            ),
            (
                r#"@[ owes(pure 1) ] def a = b ;"#,
                LoweringRefusal::NonValuePayload {
                    span: at(8_usize, 14_usize),
                    name: owes,
                    form: FormName::from(NamedKind("pure_expression")),
                },
            ),
            (
                r#"@[ owes("one") ] def a = b ;"#,
                LoweringRefusal::IllTypedPayload {
                    span: at(8_usize, 13_usize),
                    name: owes,
                    expected: schema_of(SurfaceName::from("owes")),
                    written: payload_form(Former::Text),
                },
            ),
        ];

        for (source, expected) in rows {
            assert_eq!(
                refusal(SourceText::from(source)),
                expected,
                "the attribute's refusal sits before the body's in `{source}` and is the one kept"
            );
        }
    }

    #[test]
    fn every_minted_node_has_an_origin()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x : Integer ; def x = 3 ;"),
            &mut arena,
        );
        let [declaration] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("one name is declared");
        };
        let origins = module.origins();

        assert_eq!(
            origins
                .value_type(declared_of(declaration.outcome()))
                .map(|origin| origin.span()),
            Maybe::Present(at(8_usize, 15_usize)),
            "the declared type's origin is the type it was written as"
        );
        assert_eq!(
            origins
                .value(body_of(declaration.outcome()))
                .map(|origin| origin.span()),
            Maybe::Present(at(26_usize, 27_usize)),
            "the body's origin is the value it was written as"
        );
        assert_eq!(
            origins
                .declaration(declaration.origin())
                .map(|origin| origin.span()),
            Maybe::Present(at(0_usize, 17_usize)),
            "the declaration's origin is the form that introduced the name"
        );
        assert_eq!(
            origins.recorded_count(),
            OriginCount::from(2_usize),
            "exactly the two minted nodes have origins"
        );
    }

    #[test]
    fn a_type_head_answers_at_what_it_stands_for()
    {
        let text = include_str!("lower/fixtures/a-type-head-answers-at-what-it-stands-for.gandr");
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(text), &mut arena);
        let standing: Vec<&str> = module
            .origins()
            .stand_ins()
            .iter()
            .filter_map(|&(ty, origin)| {
                arena.value_type(ty)?;
                text.get(usize::from(origin.span().start()) .. usize::from(origin.span().end()))
            })
            .collect();
        let from = |needle: &str| text.find(needle);
        let heads: Vec<usize> = module
            .origins()
            .stand_ins()
            .iter()
            .map(|&(_, origin)| usize::from(origin.span().start()))
            .collect();
        assert!(
            from("zero : M").is_some_and(|at| heads.contains(&at.saturating_add(7))),
            "a manifest component named in a later one stands for its type: {standing:?}"
        );
        assert!(
            from("zero : T})").is_some_and(|at| heads.contains(&at.saturating_add(7))),
            "a functor parameter's type, renamed to the argument's, stands where the template \
             writes it: {standing:?}"
        );
        assert!(
            standing.contains(&"S.T"),
            "a path to the parameter's type stands for the argument's: {standing:?}"
        );
        let mut grouped_arena = CoreArena::new();
        let grouped = lowered(
            SourceText::from("def a : (Integer) ; def a = 1 ;"),
            &mut grouped_arena,
        );
        assert_eq!(
            grouped.origins().stand_ins(),
            [],
            "a grouping passes its type through and stands for nothing minted elsewhere"
        );
    }

    #[test]
    fn a_refused_declaration_leaves_the_others_lowered()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def a = b ; def c = 3 ;"), &mut arena);
        let [
            DeclarationOutcome::Refused(refused),
            DeclarationOutcome::Bodied { body },
        ] = outcomes(&module)[..]
        else {
            panic!("the first declaration refuses and the second lowers");
        };

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("b"),
            },
            "the first declaration carries its own refusal"
        );
        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the second declaration lowers regardless"
        );
    }

    #[test]
    fn a_duplicate_definition_is_keyed_at_its_form()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x = 1 ; def x = 2 ; def y = 3 ;"),
            &mut arena,
        );
        let [twice, once] = *module.declarations().iter().collect::<Vec<_>>()
        else {
            panic!("two names are declared");
        };
        assert!(
            matches!(
                twice.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::DuplicateDefinition { .. })
            ),
            "the second definition refuses the name: {:?}",
            twice.outcome()
        );
        let (Maybe::Present(first), Maybe::Present(second)) =
            (twice.definition(), twice.refused_form())
        else {
            panic!("the first definition and the repetition are both keyed");
        };
        assert_ne!(first, second, "the repetition is keyed at its own form");
        assert!(
            matches!(once.refused_form(), Maybe::Absent(_)),
            "a name written once keys no repetition"
        );
    }

    /// #2183: a module refused at its header writes no half, so its refusal
    /// is keyed at the module's own form; the member a sound module defines
    /// keys none.
    #[test]
    fn a_module_refused_at_its_header_is_keyed_at_its_form_2183()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(include_str!(
                "lower/fixtures/a-module-refused-at-its-header-is-keyed-at-its-form-2183-module.gandr"
            )),
            &mut arena,
        );
        let refused: Vec<_> = module
            .declarations()
            .iter()
            .filter(|declaration| {
                matches!(
                    declaration.outcome(),
                    DeclarationOutcome::Refused(LoweringRefusal::UnknownMember { .. })
                )
            })
            .collect();
        let [misnamed] = *refused
        else {
            panic!("the module alone is refused: {refused:?}");
        };
        assert_eq!(
            misnamed.refused_form(),
            Maybe::Present(misnamed.introduced()),
            "the refusal is keyed at the module's form"
        );
        assert!(
            module
                .declarations()
                .iter()
                .filter(|declaration| !matches!(
                    declaration.outcome(),
                    DeclarationOutcome::Refused(_)
                ))
                .all(|declaration| matches!(declaration.refused_form(), Maybe::Absent(_))),
            "no sound declaration keys a refused form"
        );
    }

    #[test]
    fn a_module_past_the_allowance_is_refused()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def a = 3 ;"));
        let mut arena = CoreArena::new();
        let budget = LoweringBudget::from(1_usize);
        let refused =
            lower_module(&pbg, &tree, &mut arena, budget, Recognition::default()).unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::BudgetExceeded { budget },
            "a module costing more than the allowance is refused"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "running out of allowance is the engine's fault, not the author's"
        );
    }

    #[test]
    fn only_the_value_forms_can_stand_as_a_payload()
    {
        let values = [
            Former::Name,
            Former::Constructor,
            Former::Number,
            Former::Boolean,
            Former::Text,
            Former::Character,
            Former::Parenthesized,
            Former::Thunk,
            Former::Telescope,
            Former::List,
            Former::PackModel,
            Former::Injection,
        ];
        for former in Former::ALL {
            assert_eq!(
                is_value_form(former).0,
                values.contains(&former),
                "{former:?} can stand as a value exactly when it produces one"
            );
        }
    }

    #[test]
    fn an_integer_literal_is_its_canonical_magnitude()
    {
        assert_eq!(
            parse_literal(Former::Number, SourceFragment::from("007")),
            Maybe::Present(integer(SourceFragment::from("7"))),
            "a padded spelling is the unpadded literal"
        );
        assert_eq!(
            parse_literal(Former::Number, SourceFragment::from("0")),
            Maybe::Present(integer(SourceFragment::from("0"))),
            "zero is a literal"
        );
    }

    #[test]
    fn a_text_literal_is_the_bytes_between_its_quotes()
    {
        let rows = [
            ("\"abc\"", "abc"),
            ("\"\"", ""),
            ("\"a\\tb\\\\c\\q\"", "a\tb\\cq"),
            ("\"a\\\"b\\'c\\0\\r\"", "a\"b'c\0\r"),
            ("\"a\\\nb\"", "ab"),
            ("\"a\\\r\nb\"", "ab"),
            ("\"ab\\\"", "ab"),
        ];
        for (spelled, content) in rows {
            assert_eq!(
                parse_literal(Former::Text, SourceFragment::from(spelled)),
                Maybe::Present(text(SourceFragment::from(content))),
                "`{spelled}` decodes to its content"
            );
        }
    }

    #[test]
    fn a_character_literal_is_the_scalar_between_its_quotes()
    {
        let rows = [
            ("'a'", 'a'),
            ("'\"'", '"'),
            ("'é'", 'é'),
            ("'𐐀'", '𐐀'),
            ("'\\n'", '\n'),
            ("'\\t'", '\t'),
            ("'\\r'", '\r'),
            ("'\\0'", '\0'),
            ("'\\\\'", '\\'),
            ("'\\''", '\''),
            ("'\\q'", 'q'),
        ];
        for (spelled, scalar) in rows {
            assert_eq!(
                parse_literal(Former::Character, SourceFragment::from(spelled)),
                Maybe::Present(Literal::Character(CharacterLiteral::from(scalar))),
                "`{spelled}` decodes to {scalar:?}"
            );
        }
    }

    #[test]
    fn a_typed_number_is_its_value_at_its_width()
    {
        use gandr_kernel_term::FixedInteger;

        let rows = [
            ("0u32", FixedInteger::U32(0)),
            ("007u32", FixedInteger::U32(7)),
            ("4294967295u32", FixedInteger::U32(u32::MAX)),
            ("18446744073709551615u64", FixedInteger::U64(u64::MAX)),
            ("2147483647i32", FixedInteger::I32(i32::MAX)),
            ("9223372036854775807i64", FixedInteger::I64(i64::MAX)),
        ];
        for (spelled, fixed) in rows {
            assert_eq!(
                typed_number_literal(SourceFragment::from(spelled)),
                Maybe::Present(Literal::Fixed(fixed)),
                "`{spelled}` is {fixed:?}"
            );
        }
        let refused = [
            ("4294967296u32", literal::Absent::OutsideWidth),
            ("18446744073709551616u64", literal::Absent::OutsideWidth),
            ("2147483648i32", literal::Absent::OutsideWidth),
            ("9223372036854775808i64", literal::Absent::OutsideWidth),
            ("1.5u32", literal::Absent::OutsideWidth),
            ("1e3i64", literal::Absent::OutsideWidth),
            ("u32", literal::Absent::OutsideWidth),
            ("1.5f32", literal::Absent::Malformed),
            ("2f64", literal::Absent::Malformed),
            ("7u16", literal::Absent::Malformed),
            ("7", literal::Absent::Malformed),
        ];
        for (spelled, reason) in refused {
            assert_eq!(
                typed_number_literal(SourceFragment::from(spelled)),
                Maybe::Absent(reason),
                "`{spelled}` is no width literal"
            );
        }
    }

    #[test]
    fn a_lexeme_of_the_wrong_shape_parses_to_nothing()
    {
        let rows = [
            (Former::Number, "", literal::Absent::Malformed),
            (Former::Number, "3x", literal::Absent::Malformed),
            (Former::Text, "\"abc", literal::Absent::Malformed),
            (Former::Text, "\"", literal::Absent::Malformed),
            (Former::Text, "abc", literal::Absent::Malformed),
            (Former::Character, "'ab'", literal::Absent::Malformed),
            (Former::Character, "''", literal::Absent::Malformed),
            (Former::Character, "'\\\n'", literal::Absent::Malformed),
            (Former::Character, "'a", literal::Absent::Malformed),
            (Former::Character, "\"a\"", literal::Absent::Malformed),
            (Former::Name, "abc", literal::Absent::NotALiteral),
        ];
        for (former, spelled, reason) in rows {
            assert_eq!(
                parse_literal(former, SourceFragment::from(spelled)),
                Maybe::Absent(reason),
                "`{spelled}` is not a {former:?} literal"
            );
        }
    }

    /// Only complete unsigned decimal or exponent spellings are fractional.
    #[test]
    fn fractional_spellings_distinguish_unsupported_numbers_from_malformed_ones()
    {
        for (written, expected) in [
            ("0.0", true),
            ("01e+2", true),
            ("1e-2", true),
            ("1E0", true),
            ("1.2e3", true),
            ("", false),
            ("3", false),
            (".1", false),
            ("1.", false),
            ("1e", false),
            ("1e+", false),
            ("1e--2", false),
            ("1.2.3", false),
            ("1e2e3", false),
            ("-1.0", false),
            ("١.0", false),
            ("1.٢", false),
            ("1.0 ", false),
        ] {
            assert_eq!(super::fractional(SourceFragment::from(written)).0, expected);
        }
    }

    /// Range boundaries keep selected members and never substitute a prefix.
    #[test]
    fn recorded_ranges_keep_valid_members_and_reject_invalid_bounds()
    {
        let entries = [11_u8, 22_u8, 33_u8];
        for (start, end, expected) in [
            (0_usize, 0_usize, [].as_slice()),
            (0_usize, 3_usize, [11_u8, 22_u8, 33_u8].as_slice()),
            (1_usize, 3_usize, [22_u8, 33_u8].as_slice()),
            (2_usize, 1_usize, [].as_slice()),
            (0_usize, 4_usize, [].as_slice()),
            (4_usize, 4_usize, [].as_slice()),
        ] {
            assert_eq!(
                super::stretch(&entries, super::Stretch { start, end }),
                expected
            );
        }
    }

    /// Closing and exhaustion retain the first unexpected position.
    #[test]
    fn closing_and_exhaustion_distinguish_tiles_operands_and_gaps()
    {
        let placed = |index: usize, start: usize, end: usize| super::Placed {
            node: crate::fixture::node(index),
            span: span(ByteOffset::from(start), ByteOffset::from(end)),
        };
        let close = placed(1_usize, 2_usize, 3_usize);
        let operand = placed(2_usize, 5_usize, 6_usize);
        let site = super::Site {
            at: placed(0_usize, 0_usize, 8_usize),
            name: FormName::FUNCTION,
            reading: super::Reading::Function,
        };
        let pieces = [
            super::Piece::Tile {
                label: super::TileName::PAREN_CLOSE,
                at: close,
            },
            super::Piece::Operand(operand),
        ];
        let mut cursor = super::Cursor::new(&pieces, site.at.span);
        let misplaced = LoweringRefusal::MalformedForm {
            span: close.span,
            form: FormName::FUNCTION,
            fault: FormFault::MisplacedTile,
        };
        assert_eq!(super::exhausted(site, &cursor), Err(misplaced));
        assert_eq!(
            super::closed(site, &mut cursor, super::TileName::BRACE_CLOSE),
            Err(misplaced)
        );
        assert_eq!(cursor.peek(), Maybe::Present(pieces[0_usize]));
        assert_eq!(
            super::closed(site, &mut cursor, super::TileName::PAREN_CLOSE),
            Ok(())
        );
        assert_eq!(
            super::exhausted(site, &cursor),
            Err(LoweringRefusal::MalformedForm {
                span: operand.span,
                form: FormName::FUNCTION,
                fault: FormFault::ExtraOperand,
            })
        );
        assert_eq!(
            cursor.read(),
            Maybe::Present(super::Piece::Operand(operand))
        );
        assert_eq!(super::exhausted(site, &cursor), Ok(()));
        assert_eq!(
            super::closed(site, &mut cursor, super::TileName::PAREN_CLOSE),
            Err(LoweringRefusal::MalformedForm {
                span: span(ByteOffset::from(6_usize), ByteOffset::from(6_usize)),
                form: FormName::FUNCTION,
                fault: FormFault::MisplacedTile,
            })
        );
    }

    /// Parameter arities consume the header, its written type included, but
    /// preserve the following body.
    #[test]
    fn parameter_headers_preserve_the_body_and_locate_refusals()
    {
        let placed = |index: usize, start: usize, end: usize| super::Placed {
            node: crate::fixture::node(index),
            span: span(ByteOffset::from(start), ByteOffset::from(end)),
        };
        let lead = super::Piece::Tile {
            label: super::TileName::FUN,
            at: placed(1_usize, 0_usize, 2_usize),
        };
        let open = super::Piece::Tile {
            label: super::TileName::PAREN_OPEN,
            at: placed(2_usize, 3_usize, 4_usize),
        };
        let first = placed(3_usize, 4_usize, 5_usize);
        let identifier = super::Piece::Tile {
            label: super::TileName::IDENTIFIER,
            at: first,
        };
        let comma = super::Piece::Tile {
            label: super::TileName::COMMA,
            at: placed(4_usize, 5_usize, 6_usize),
        };
        let second = super::Piece::Tile {
            label: super::TileName::IDENTIFIER,
            at: placed(5_usize, 6_usize, 7_usize),
        };
        let close = super::Piece::Tile {
            label: super::TileName::PAREN_CLOSE,
            at: placed(6_usize, 7_usize, 8_usize),
        };
        let body = super::Piece::Operand(placed(7_usize, 9_usize, 12_usize));
        let colon = super::Piece::Tile {
            label: super::TileName::COLON,
            at: placed(4_usize, 5_usize, 6_usize),
        };
        let declared = placed(8_usize, 6_usize, 7_usize);
        let typed = super::Piece::Operand(declared);
        let form = FormName::from(NamedKind("lambda_expression"));
        let site = super::Site {
            at: placed(0_usize, 0_usize, 12_usize),
            name: form,
            reading: super::Reading::Computation(super::Frame::Outermost),
        };
        for (pieces, expected, next) in [
            (
                [lead, open, identifier, close, body].as_slice(),
                Ok((first, None)),
                body,
            ),
            (
                [lead, open, close, body].as_slice(),
                Err(LoweringRefusal::OutOfFragment {
                    span: site.at.span,
                    form,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Arity(OperandCount::from(0_usize)),
                }),
                body,
            ),
            (
                [lead, open, identifier, comma, second, close, body].as_slice(),
                Err(LoweringRefusal::OutOfFragment {
                    span: site.at.span,
                    form,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Arity(OperandCount::from(2_usize)),
                }),
                body,
            ),
            (
                [lead, open, identifier, colon, typed, close, body].as_slice(),
                Ok((first, Some(declared))),
                body,
            ),
            (
                [lead, identifier, close, body].as_slice(),
                Err(LoweringRefusal::MalformedForm {
                    span: first.span,
                    form,
                    fault: FormFault::MisplacedTile,
                }),
                identifier,
            ),
        ] {
            let mut cursor = super::Cursor::new(pieces, site.at.span);
            let _lead = cursor.tile(super::TileName::FUN);
            assert_eq!(super::parameter(site, &mut cursor), expected);
            assert_eq!(cursor.peek(), Maybe::Present(next));
        }
    }

    /// Argument failures retain appended operands and identify the first fault.
    #[test]
    fn argument_lists_preserve_prefixes_and_locate_the_first_fault()
    {
        let placed = |index: usize, start: usize, end: usize| super::Placed {
            node: crate::fixture::node(index),
            span: span(ByteOffset::from(start), ByteOffset::from(end)),
        };
        let open = super::Piece::Tile {
            label: super::TileName::PAREN_OPEN,
            at: placed(1_usize, 1_usize, 2_usize),
        };
        let first = placed(2_usize, 2_usize, 3_usize);
        let second = placed(4_usize, 4_usize, 5_usize);
        let comma = super::Piece::Tile {
            label: super::TileName::COMMA,
            at: placed(3_usize, 3_usize, 4_usize),
        };
        let close = super::Piece::Tile {
            label: super::TileName::PAREN_CLOSE,
            at: placed(5_usize, 5_usize, 6_usize),
        };
        let stray = placed(6_usize, 7_usize, 8_usize);
        let site = super::Site {
            at: placed(0_usize, 0_usize, 8_usize),
            name: FormName::FUNCTION,
            reading: super::Reading::Function,
        };
        let previous = crate::fixture::node(99_usize);
        let trailing = super::Piece::Tile {
            label: super::TileName::COMMA,
            at: stray,
        };
        for (pieces, expected, appended) in [
            ([open, close].as_slice(), Ok(()), [].as_slice()),
            (
                [
                    open,
                    super::Piece::Operand(first),
                    comma,
                    super::Piece::Operand(second),
                    close,
                ]
                .as_slice(),
                Ok(()),
                [first.node, second.node].as_slice(),
            ),
            (
                [open, super::Piece::Operand(first), comma, close].as_slice(),
                Ok(()),
                [first.node].as_slice(),
            ),
            (
                [
                    open,
                    super::Piece::Operand(first),
                    close,
                    super::Piece::Operand(stray),
                ]
                .as_slice(),
                Err(LoweringRefusal::MalformedForm {
                    span: stray.span,
                    form: FormName::FUNCTION,
                    fault: FormFault::ExtraOperand,
                }),
                [first.node].as_slice(),
            ),
            (
                [open, super::Piece::Operand(first), close, trailing].as_slice(),
                Err(LoweringRefusal::MalformedForm {
                    span: stray.span,
                    form: FormName::FUNCTION,
                    fault: FormFault::MisplacedTile,
                }),
                [first.node].as_slice(),
            ),
        ] {
            let mut cursor = super::Cursor::new(pieces, site.at.span);
            let mut written = vec![previous];
            assert_eq!(super::arguments(site, &mut cursor, &mut written), expected);
            assert_eq!(written.first(), Some(&previous));
            assert!(written.iter().skip(1_usize).eq(appended.iter()));
        }
    }

    /// #3553: a data or codata family a body quotes reads each argument
    /// naming a parameter at that parameter's index in the body, as a path
    /// type's endpoints do, not past every parameter.
    #[test]
    fn a_family_a_body_quotes_reads_its_parameters_at_their_indices_3553()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "data L(a : Type) : Type where { | N : L(a) } codata S(a : Type) : Type[-] where { head : a; } \
                 def listOf(p : Type) -> -F Type { return (L p) } def firstOf(a : Type, b : \
                 Type) -> -F Type { return (L a) } def secondOf(a : Type, b : Type) -> -F Type { \
                 return (L b) } def streamOf(p : Type) -> -F Type[-] { return (S p) }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        // The value the body returns under its parameters' lambdas.
        let returned = |arena: &CoreArena, at: usize| {
            let Some(&Value::Thunk(mut under)) = arena.value(body_of(lowered[at]))
            else {
                panic!("the body is a thunk");
            };
            while let Some(&Computation::Lambda(body)) = arena.computation(under) {
                under = body;
            }
            let Some(&Computation::Return(value)) = arena.computation(under)
            else {
                panic!("the body returns under its parameters");
            };
            value
        };
        // The one argument of the family the returned quote applies.
        let argument = |arena: &CoreArena, at: usize| {
            let arguments = match arena.value(returned(arena, at)) {
                Some(&Value::Quote(quoted)) => match arena.value_type(quoted) {
                    Some(&ValueType::Data { ref arguments, .. }) => arguments.clone(),
                    _ => panic!("a quoted data family"),
                },
                Some(&Value::QuoteComputation(quoted)) => match arena.comp_type(quoted) {
                    Some(&CompType::Codata { ref arguments, .. }) => arguments.clone(),
                    _ => panic!("a quoted codata family"),
                },
                _ => panic!("a quoted family"),
            };
            let [argument] = *arguments
            else {
                panic!("one argument");
            };
            arena.value(argument).cloned()
        };
        let at = |index: u32| {
            Some(Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(index),
            })
        };

        assert_eq!(
            [2_usize, 3, 4, 5].map(|declaration| argument(&arena, declaration)),
            [at(0), at(1), at(0), at(0)],
            "`L(p)` over one parameter, `L(a)` and `L(b)` over two, and the codata `S(p)`, each \
             argument at its parameter's index in the body"
        );
    }

    /// #3572: a call written as a family's argument, in a type a body quotes,
    /// is the value it returns, as in a binder's type. No run stands under the
    /// quote, and the other argument keeps its parameter's index.
    #[test]
    fn a_call_a_quoted_family_takes_is_the_value_it_returns_3572()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "data Both(a : Type, b : Type) : Type where { | MkBoth : (x : a, y : b) --> Both(a, b) } \
                 def same(a : Type) -> -F Type { return a } def pairSame(a : Type) -> -F Type { \
                 return (Both (same a) a) }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let Some(&Value::Thunk(mut under)) = arena.value(body_of(lowered[2]))
        else {
            panic!("the body is a thunk");
        };
        while let Some(&Computation::Lambda(body)) = arena.computation(under) {
            under = body;
        }
        let Some(&Computation::Return(returned)) = arena.computation(under)
        else {
            panic!("the body returns under its parameter");
        };
        let arguments = match arena.value(returned) {
            Some(&Value::Quote(quoted)) => match arena.value_type(quoted) {
                Some(&ValueType::Data { ref arguments, .. }) => arguments.clone(),
                other => panic!("a quoted data family: {other:?}"),
            },
            other => panic!("a quoted family: {other:?}"),
        };
        let [called, passed] = *arguments
        else {
            panic!("two arguments");
        };
        assert!(
            matches!(arena.value(called), Some(&Value::Returned(_))),
            "`same(a)` as `Both`'s argument is the value it returns: {:?}",
            arena.value(called)
        );
        assert_eq!(
            arena.value(passed).cloned(),
            Some(Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            "`a` as `Both`'s argument stands at its parameter's index"
        );
    }

    /// #3616: a lambda in the argument of a type-valued call, in a signature's
    /// type, makes the arrow binding each variable it reads dependent, and
    /// reads that variable at its index under the lambda, as a lambda in a
    /// family's argument does.
    #[test]
    fn a_lambda_in_a_type_valued_call_reads_outer_variables_at_their_indices_3616()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def idf(d : Type, c : Type, x : d) -> -F d { return x } def fam(d : Type, c : \
                 Type, f : +U (d -> -F d)) -> -F Type { return d } def k10(d : Type, c : Type, w \
                 : d, v : fam(d, c, thunk { fun (a) { idf d c w } })) -> -F Unit { return *{} \
                 } def k11(d : Type, c : Type, w : d, v : fam(d, c, thunk { fun (a) { return w } \
                 })) -> -F Unit { return *{} }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        // Whether each arrow of the declared type is dependent, and the body of
        // the lambda the fourth parameter's call takes last.
        let lambda = |arena: &CoreArena, at: usize| {
            let mut arrow = match arena.value_type(declared_of(lowered[at])) {
                Some(&ValueType::Thunk(arrow)) => arrow,
                other => panic!("a function's type is a thunk: {other:?}"),
            };
            let mut dependent = Vec::new();
            let mut domains = Vec::new();
            while let Some(
                &(CompType::Pi { domain, codomain } | CompType::Arrow { domain, codomain }),
            ) = arena.comp_type(arrow)
            {
                dependent.push(matches!(arena.comp_type(arrow), Some(&CompType::Pi { .. })));
                domains.push(domain);
                arrow = codomain;
            }
            let [_, _, _, decoded] = *domains
            else {
                panic!("four parameters: {domains:?}");
            };
            let Some(&ValueType::Element { code, .. }) = arena.value_type(decoded)
            else {
                panic!("a call where a type is read decodes");
            };
            let Some(&Value::Returned(called)) = arena.value(code)
            else {
                panic!("the code is what the call returns");
            };
            let Some(&Computation::Application(_, argument)) = arena.computation(called)
            else {
                panic!("the call applies the family to its last argument");
            };
            let Some(&Value::Thunk(suspended)) = arena.value(argument)
            else {
                panic!("the last argument is a thunk");
            };
            let Some(&Computation::Lambda(body)) = arena.computation(suspended)
            else {
                panic!("the thunk holds a lambda");
            };
            (dependent, body)
        };
        let index = |arena: &CoreArena, value| match arena.value(value) {
            Some(&Value::Variable { index, .. }) => u32::from(index),
            other => panic!("a variable: {other:?}"),
        };
        // `idf(d, c, w)`: the three values the call applies, first to last.
        let (calling, mut call) = lambda(&arena, 2_usize);
        let mut applied = Vec::new();
        while let Some(&Computation::Application(function, argument)) = arena.computation(call) {
            applied.push(index(&arena, argument));
            call = function;
        }
        applied.reverse();
        let (returning, body) = lambda(&arena, 3_usize);
        let Some(&Computation::Return(returned)) = arena.computation(body)
        else {
            panic!("`return w`");
        };

        assert_eq!(
            ((calling, applied), (returning, index(&arena, returned))),
            (
                (vec![true, true, true, false], vec![3_u32, 2, 1]),
                (vec![true, true, true, false], 1_u32)
            ),
            "`w` is read inside the lambda, so its arrow is dependent; under `d, c, w` and the \
             lambda's own `a`, `idf(d, c, w)` reads `d`, `c` and `w` at 3, 2 and 1, and `return \
             w` reads `w` at 1"
        );
    }

    /// #3562: a recursive function's descent call, under a lambda that a
    /// body's quoted family holds, reads the fixpoint's binder at its index in
    /// the body, with and without a uniform parameter before the staged one,
    /// and not at another binder's.
    #[test]
    fn a_self_call_a_body_quotes_reads_its_fixpoint_at_its_index_3562()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "data Sig(a : Type, b : +U (a -> -F Type)) : Type where { | MkSig : (x : a, y : b(x)) --> Sig(a, b) } data IR(d : Type) : Type[+, 1] where { | Iota : (e : d) --> IR(d) | SigmaC : (a : Type, f : +U (a -> -F IR(d))) --> IR(d) } def rec argsU(c : IR(Unit)) -> \
                 -F Type { match c { | Iota(e) => return Unit | SigmaC(a, f) => return (Sig a (thunk \
                 { fun (y) { argsU[<] (f y) } })) } } def rec argsD(d : Type, c : IR(d)) -> -F Type \
                 { match c { | Iota(e) => return Unit | SigmaC(a, f) => return (Sig a (thunk { fun (y) \
                 { argsD[<] d (f y) } })) } }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        // The head the descent call forces, under the lambda the second arm's
        // quoted `Sig` holds as its second argument.
        let head = |arena: &CoreArena, at: usize| {
            let Some(&Value::Thunk(mut under)) = arena.value(body_of(lowered[at]))
            else {
                panic!("the body is a thunk");
            };
            while let Some(&(Computation::Lambda(body) | Computation::Fixpoint { body, .. })) =
                arena.computation(under)
            {
                under = body;
            }
            let Some(&Computation::DataCase { ref branches, .. }) = arena.computation(under)
            else {
                panic!("the fixpoint matches its code");
            };
            let Some(&(mut arm)) = branches.get(1)
            else {
                panic!("a second arm");
            };
            while let Some(&Computation::Lambda(body)) = arena.computation(arm) {
                arm = body;
            }
            let Some(&Computation::Return(returned)) = arena.computation(arm)
            else {
                panic!("the arm returns");
            };
            let Some(&Value::Quote(quoted)) = arena.value(returned)
            else {
                panic!("a quote");
            };
            let Some(&ValueType::Data { ref arguments, .. }) = arena.value_type(quoted)
            else {
                panic!("a quoted family");
            };
            let Some(&Value::Thunk(family)) = arguments.get(1).and_then(|&held| arena.value(held))
            else {
                panic!("the family's second argument is a thunk");
            };
            let Some(&Computation::Lambda(call)) = arena.computation(family)
            else {
                panic!("under one lambda");
            };
            let Some(&Computation::Application(forced, _)) = arena.computation(call)
            else {
                panic!("a call");
            };
            let Some(&Computation::Force(callee)) = arena.computation(forced)
            else {
                panic!("of a forced head");
            };
            arena.value(callee).cloned()
        };
        let fixpoint = Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(4_u32),
        });

        assert_eq!(
            [2_usize, 3].map(|declaration| head(&arena, declaration)),
            [fixpoint.clone(), fixpoint],
            "under `y`, `f`, `a` and `c`, each head reads its own fixpoint"
        );
    }
}
