//! The lowering itself: [`lower_module`], the [`LoweringBudget`] that bounds
//! it, and the two sweeps over the arena it is made of.
//!
//! # Two sweeps over one level-order arena, and no recursion anywhere
//!
//! The molded tree lays its nodes out in level order, so a walk in ascending
//! position order visits every parent before any of its children and a walk in
//! descending order visits every child before its parent. Lowering needs both
//! directions and gets each as a plain loop with no stack of its own.
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
//! `⌜C⌝`, so `def t : Type ; def t = Integer ;` declares a code; and a name
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
//! produces is a function of the form alone: `+U C`, `Type[s, l]`, `A * B` and
//! `(A1, …, An) => B` are value types, `-F A` is a computation type, `A -> C`
//! is a computation type except where a value type is read, where it is a
//! static Pi (§ Type operators are static functions over codes), a thunk, a
//! name, a number, a string, `unit`, a tuple and a static abstraction `\A. T`
//! are values, a returner, a force, a lambda, an application and a block are
//! computations, a name in type position is the sort its binder's universe
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
//! A block is a sequence of `run x <- c;` and `c;` statements and a last
//! computation. It lowers to a chain of binds, `c₁` bound over the rest of the
//! block with `x` in scope, the last computation innermost, each bind at the
//! origin of its `run` keyword. A discarded statement `c;` binds `c`'s value
//! under a binder no name reaches and splits it with no components, `split u as
//! () in rest`, at the origin of `c`: the split types the value as the unit, so
//! the checker refuses a discarded result of any other type at the statement,
//! and the lowering needs no annotation of its own. A block with no last
//! computation is refused at the block as `Arity` with zero. `recv(c) as x;`
//! binds `x` as `run x <- c;` does, `fork (c : S) t as d;` runs `t` beside
//! the rest of the block (the `lower::session` module), `hold x = e;`
//! holds `e` for the rest of the block (the `lower::access` module), and
//! `leta x = v;` opens the handle `v` over it (the `lower::world` module).
//! The statements `val` and `unpack` are refused as `Unadmitted`, and
//! `acquire`, `release` and the shared `fork !` as `Reserved`, each named by
//! its form at its keyword; and a `run` binder that is annotated or is a
//! pattern other than a name is refused as `Unadmitted`, at the annotation or
//! the pattern.
//!
//! The one expression statement admitted is an exit closing its block, `{ run m
//! <- f(n); return m; }`: `return v;` or `become c;` written before the closing
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
//! explicit spelling `run _ <- c;`: a wildcard binder binds the empty name,
//! which no identifier resolves to, so the rest of the block reads every
//! earlier name one index further out and no split is minted. Reversal: if a
//! dedicated refusal for a non-unit `c;` is wanted, the checker's shape
//! mismatch at the split is the place to name it.
//!
//! A block also stands wherever a computation is read: a match arm that
//! sequences, `Succ(p) => { run r <- f[<](p); return Succ(r) }`, is a block
//! lowered by the same chain, and a block where a value is read is refused as
//! the wrong sort.
//!
//! The alternative was lowering `val x = v;` beside `run`, as the substitution
//! of a value. It was declined because the core has no let and the substitution
//! would duplicate `v` at each occurrence, which the fragment has no sharing to
//! undo. Reversal: when the core gains a let, or the lowering gains sharing,
//! `val` lowers to it.
//!
//! # A function exits where its body ends
//!
//! `return v` leaves the nearest enclosing function, lambda or thunk with `v`,
//! and `become c` leaves it by running `c` in tail position, from wherever a
//! path through that body passes: its last computation, and on a path the last
//! computation of a block, every arm of a match, a grouping's operand, the
//! computation of a `run` and `become`'s operand. Every path through a body
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
//! bound by `run` holds a frame per step: the exit is a cut that passes the
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
//! `\A. T` lowers to a static lambda over the code of `T`: the body is read
//! where a value is read, so a type written there is quoted, and `A` binds one
//! more value variable, which a type in the body decodes. An arrow standing
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
//! written type says nothing — the binder of `\A. T` — decodes at the default
//! (§ Universes and the fuss-free default) its position reads. The binder of
//! `\A. T` is written with no type: the declaration's signature classifies the
//! abstraction, and the checker refuses an argument of the wrong sort or level
//! as `SortMismatch`, naming both.
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
//! binder holds: a parameter at a universe, and equally a variable `run` bound
//! to a type, so a decoder's arm `run x <- el(a); run y <- el(b); return (x =>
//! y)` reads `x` and `y` as `El(x)` and `El(y)`. A call of a dynamic function
//! in type position is the decode of the code the call returns, and its
//! arguments are read where a value is read: a capitalised name there is a
//! constructor before it is a type head, so `el(Arrow(NatC, NatC))` applies
//! `el` to a constructor value.
//!
//! This is the recorded design, a Tarski data universe: the codes are an
//! ordinary datatype and the decoder a function written over them, both bound
//! at the value level, and a decode is a type over a code that is a term. The
//! alternative was a large elimination into `Type`, a `case` with types for
//! arms standing in the type language and `Element` erased, declined in #353.
//! The choice reverses for a universe that stops being a data universe, one
//! whose codes are not values a function can case on.
//!
//! # Products, sums, tuples and the value-function alias
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
//! product type is `#{A}`. `(A1, …, An) => B` is exactly `+U (A1 -> … -> An ->
//! -F B)`, every former at the alias's origin, so a program spelled with the
//! alias and one spelled without it lower to one core term and one content
//! digest. A computation arrow whose domain is one binder, `(x : A) -> C`, is
//! the dependent arrow `Π (x : A). C`, so the telescope `(x : A, y : B(x)) =>
//! C` is exactly `+U ((x : A) -> (y : B(x)) -> -F C)` and has a spelling
//! where the alias cannot stand, an argument among them. A parenthesised list
//! of types anywhere but before `=>` is refused as `MisplacedTile` at its
//! first comma. The lazy product `C & D` is a computation type, the core's
//! `With`.
//!
//! The alternative was a core former for the alias, which would give one type
//! two digests by its spelling. It was declined because `=>` is notation for
//! the thunked arrow, and choosing a spelling is the printer's business, not
//! the core's. Reversal: none planned. The printer restores the alias, the
//! infix product and sum and the tuple from the core's shape in its sugared
//! form, `gandr-surface-pretty`'s § Two forms, one walk.
//!
//! # A graded bridge is refused by name
//!
//! `+U[ω] C` is `+U C`: `ω`, the unrestricted grade, is the only one the core's
//! thunk type carries. Any other grade, a numeral or a name, is `GradedBridge`,
//! at the grade and naming it, classed unrepresentable. A grade on `-F` is
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
//! magnitude, so `007` and `7` are one literal. A string lowers to the text
//! between its quotes with its escapes decoded: `\n`, `\t`, `\r`, `\0`, `\\`,
//! `\"` and `\'` to the character each names, a backslash before a line break
//! elided together with the break, any other escaped character to itself, and a
//! trailing lone backslash dropped. A literal whose text is not its form's
//! lexeme is `MalformedLiteral`, which only a hand-built tree carries.
//!
//! Escape decoding preserves unescaped Unicode and drops a backslash-newline
//! continuation as one unit, including CRLF. Unknown escapes retain their
//! escaped character; an unfinished escape contributes nothing. A well-formed
//! decimal fraction or exponent is recognized as an unsupported number,
//! distinct from malformed numeric text. Boundary witnesses exercise these
//! lexical decisions independently of the parser’s accepted corpus.
//!
//! The alternative was to lower a string to its bytes verbatim. It was dropped
//! because the core literal is the string the source means: two spellings of
//! one string must lower to one core value, so that content identity in the
//! core follows meaning. Reversal: a consumer that needs the written spelling
//! reads it through the literal's origin span.
//!
//! # Two sweeps, no recursion, one allowance
//!
//! The tree is laid out in level order, so ascending position order visits
//! every parent before its children and descending order every child before its
//! parent. The ascending sweep classifies and plans; the descending sweep
//! mints, and can fail at nothing but the allowance, because every decision was
//! made on the way down. It mints each manifest type component's form first, in
//! signature order, so a type head standing for that component adopts a type
//! already minted wherever the head sits. Each is a plain loop: no descent, no
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
//! their term position. Occurrences have distinct `HoleId`s derived from their
//! syntax nodes, and retain the usual written origins. Witness:
//! `tests::source_holes_keep_their_families_and_distinct_occurrences`.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;
use core::ops::ControlFlow;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Renaming;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::identity::Relation;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::SessionAction;
use gandr_core_term::world::WorldForm;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::FormRank;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeEntry;
use crate::attribute::AttributeRegistry;
use crate::attribute::AttributeSchema;
use crate::attribute::AttributeTable;
use crate::attribute::PayloadForm;
use crate::attribute::PayloadVerdict;
use crate::attribute::RegisteredAttribute;
use crate::attribute::names;
use crate::attribute::payload;
use crate::attribute::payload_form;
use crate::attribute::payload_verdict;
use crate::classify::FailureClass;
use crate::doc::Documentation;
use crate::doc::read_doc;
use crate::error::CrossedExit;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::import::ImportBinding;
use crate::import::ImportResolution;
use crate::import::ModuleImports;
use crate::module::Collected;
use crate::module::ComponentScope;
use crate::module::Container;
use crate::module::DataIndex;
use crate::module::DeclarationOutcome;
use crate::module::DeclarationParts;
use crate::module::DeclarationSlot;
use crate::module::DecoratedModule;
use crate::module::FamilyIndex;
use crate::module::Half;
use crate::module::InstanceIndex;
use crate::module::LoweredDeclaration;
use crate::module::LoweredModule;
use crate::module::LoweredStructure;
use crate::module::ManifestComponent;
use crate::module::Member;
use crate::module::Operand;
use crate::module::ParameterForm;
use crate::module::Payload;
use crate::module::Role;
use crate::module::SealedComponent;
use crate::module::Sealing;
use crate::module::SlotIndex;
use crate::module::Stratum;
use crate::module::StructureIndex;
use crate::module::TypeComponent;
use crate::module::TypeMeaning;
use crate::module::ValueComponent;
use crate::module::WrittenAttribute;
use crate::module::begin_collection;
use crate::module::collect_source;
use crate::module::declaration_half;
use crate::module::manifest_type;
use crate::module::root_pieces;
use crate::module::slot_refusal;
use crate::module::source_pieces;
use crate::namespace::Binding;
use crate::namespace::NamePath;
use crate::namespace::PathResolution;
use crate::namespace::Recognition;
use crate::namespace::RecognitionSite;
use crate::namespace::Recognized;
use crate::namespace::Segment;
use crate::namespace::Trie;
use crate::origin::Insertion;
use crate::origin::Label;
use crate::origin::Labelled;
use crate::origin::Origin;
use crate::origin::OriginTable;
use crate::resolve::Bound;
use crate::resolve::Frame;
use crate::resolve::HeadArity;
use crate::resolve::Mentioned;
use crate::resolve::OperandCount;
use crate::resolve::Scope;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::Telescope;
use crate::resolve::TypeAtom;
use crate::resolve::TypeFormer;
use crate::resolve::binder_site;
use crate::resolve::binder_type;
use crate::resolve::type_atom;
use crate::resolve::type_former;
use crate::unit::ImportTarget;
use crate::unit::SourceIndex;
use crate::unit::Unit;
use crate::unit::UnitKey;

mod access;

mod arity;

mod capability;

mod description;

mod exits;

pub use exits::Exit;
pub use exits::Explicitness;
pub use exits::InferredExit;

mod functor;

mod loops;

mod runs;

pub use runs::AskedRuns;
pub use runs::InferredRun;
pub use runs::NestedSite;
pub use runs::RunOperand;
pub use runs::RunSpelling;

mod identity;

mod model;

mod native;

mod sealing;

mod session;

mod ua;

mod world;

quenchant_shape::reason_enum! {
    /// Why a node has no lowered core node.
    pub mod lowered {
        /// The mint sweep produced nothing usable for the node.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node was not minted: unread, refused, or under a refusal.
            Unminted,
            /// The node was minted at another sort than the one asked for.
            OtherSort,
            /// The function tail states no type: a parameter or the result is
            /// untyped.
            Unstated,
            /// The slot belongs to a functor's template, which each
            /// application renames into declarations of its own.
            Templated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a lexeme denotes no literal.
    pub mod literal {
        /// The text is not a lexeme of the literal form asked about.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The text is not the form's lexeme.
            Malformed,
            /// The former is not a literal former at all.
            NotALiteral,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a tile in a block names no statement.
    pub mod statement {
        /// The tile opens none of the statements a block refuses.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The tile is no statement's keyword.
            NotAKeyword,
            /// The tile opens a statement the block reads: `run`, `recv`, or
            /// `fork` without `!`.
            Read,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node sees no manifest type component.
    pub mod scoped {
        /// The node lies in no module signature.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No signature type encloses the node.
            Unscoped,
        }
    }
}

/// The work one lowering may spend before it refuses.
///
/// One step is charged per node visited, per binder frame walked, per module
/// child and per attribute, so the allowance bounds the whole lowering rather
/// than any single sweep.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The limit is shared across the lowering run rather than renewed
///   for each pass.
/// - provides: A nominal bound on charged work, including the zero allowance.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The value has no work history to inspect; `Fuel::new`
///   and `Fuel::spend` check initialization and consumption.
///
/// # Adequacy
/// - hypothesis: L3 — the last allowed charge succeeds, the next charge names
///   the original limit, and a module exceeding its allowance is refused.
/// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
/// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
/// - witness: `lower::tests::a_module_past_the_allowance_is_refused`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LoweringBudget(usize);

impl LoweringBudget
{
    /// The allowance a caller with no reason to bound the walk takes.
    pub const DEFAULT: Self = Self(1_000_000_usize);
}

impl From<usize> for LoweringBudget
{
    /// The allowance of `steps` steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: usize) -> Self
    {
        Self(steps)
    }
}

impl From<LoweringBudget> for usize
{
    /// The number of steps `budget` allows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(budget: LoweringBudget) -> Self
    {
        budget.0
    }
}

impl fmt::Display for LoweringBudget
{
    /// Writes the number of steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// One lowering's remaining allowance.
///
/// # Specification
/// - requires: Instances are created by new and changed only by spend.
/// - ensures: The remaining allowance never exceeds its original budget, and an
///   exhausted tank remains exhausted.
/// - provides: The shared state of all charged passes.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Type-level invariant expansion is unavailable in the
///   enabled specification facade; new and spend carry the executable state
///   relation.
///
/// # Adequacy
/// - hypothesis: L3 — initialization and the last-success/first-refusal
///   boundary distinguish off-by-one charging and preserve the reported
///   allowance.
/// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
/// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fuel
{
    /// How many steps are left.
    remaining: usize,
    /// The allowance the caller set, carried so a refusal can name it.
    budget: LoweringBudget,
}

impl Fuel
{
    /// A full tank at `budget`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the remaining allowance equals the supplied budget, whose
    ///   original value is retained.
    /// - provides: a shared tank for every charged pass.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last permitted charge and first excess charge
    ///   distinguish initialization from an off-by-one allowance.
    /// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
    /// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
    #[spec(
        ensures: |ret| ret.remaining == budget.0 && ret.budget.0 == budget.0,
    )]
    #[inline]
    #[must_use]
    pub const fn new(budget: LoweringBudget) -> Self
    {
        Self {
            remaining: budget.0,
            budget,
        }
    }

    /// Charge one step of work.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the remaining allowance is one lower on success, so a caller
    ///   that charges once per unit of work cannot outrun the allowance by more
    ///   than the unit it was charged for.
    /// - provides: the one place the allowance is spent, so no sweep can walk
    ///   uncharged.
    /// - fails: [`LoweringRefusal::BudgetExceeded`], naming the allowance the
    ///   caller set, once nothing remains; the tank stays empty, so every later
    ///   charge refuses alike.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance is spent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one checked subtraction, separated by the
    ///   boundary pair of the last successful charge and the first refused one
    ///   over an allowance of one, with the exact refusal variant and its
    ///   allowance asserted.
    /// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
    /// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
    #[spec(
        captures: before = (self.remaining, self.budget),
        ensures: |ret| {
            self.budget == before.1
                && self.remaining == before.0.saturating_sub(1)
                && ret
                    == if before.0 == 0 {
                        Err(LoweringRefusal::BudgetExceeded { budget: before.1 })
                    }
                    else {
                        Ok(())
                    }
        },
    )]
    #[inline]
    pub fn spend<'refusal>(&mut self) -> Result<(), LoweringRefusal<'refusal>>
    {
        let Some(remaining) = self.remaining.checked_sub(1_usize)
        else {
            return Err(LoweringRefusal::BudgetExceeded {
                budget: self.budget,
            });
        };
        self.remaining = remaining;

        Ok(())
    }
}

/// How a node's position reads it.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A reading retains its positional sort and, for framed readings,
///   the binder frame used by its children.
/// - provides: The context for classification and insertion decisions.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The tag retains neither its source position nor its
///   scope; sort, family, frame and require specify its projections and
///   interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — lambda binding, forced heads and returner insertion
///   distinguish the framed term and type positions on the listed sources.
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Reading
{
    /// Not read: an own tile, layout, or a node under a form that refused.
    Unread,
    /// Read as a value type, under the binder frame named here.
    ValueType(Frame),
    /// Read as a computation type, under the binder frame named here.
    CompType(Frame),
    /// Read as a value, under the binder frame named here.
    Value(Frame),
    /// Read as a computation, under the binder frame named here.
    Computation(Frame),
    /// Read as an application's head: a computation under the binder frame
    /// named here, which a value standing here reaches by an inserted force.
    Head(Frame),
    /// Read as a function's result: a computation type under the binder frame
    /// named here, which a value type standing here reaches by an inserted
    /// returner.
    Result(Frame),
    /// Read as a function: the declaration form whose tail is one.
    Function,
}

impl Reading
{
    /// The sort a refusal at this position reports.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: unread and function positions report declarations, type
    ///   positions their own type sort, and heads/results the computation sort
    ///   they demand.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — wrong-sort refusals distinguish the expected value,
    ///   computation and type positions; function sites report a declaration.
    /// - witness: `lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
    /// - witness: `lower::tests::a_computation_codomain_of_a_static_pi_is_refused`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (Self::Unread | Self::Function, FragmentSort::Declaration)
                    | (Self::ValueType(_), FragmentSort::ValueType)
                    | (Self::CompType(_) | Self::Result(_), FragmentSort::CompType)
                    | (Self::Value(_), FragmentSort::Value)
                    | (
                        Self::Computation(_) | Self::Head(_),
                        FragmentSort::Computation
                    )
            )
        },
    )]
    const fn sort(self) -> FragmentSort
    {
        match self {
            Self::Unread | Self::Function => FragmentSort::Declaration,
            Self::ValueType(_frame) => FragmentSort::ValueType,
            Self::CompType(_frame) | Self::Result(_frame) => FragmentSort::CompType,
            Self::Value(_frame) => FragmentSort::Value,
            Self::Computation(_frame) | Self::Head(_frame) => FragmentSort::Computation,
        }
    }

    /// The family of formers this reading admits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: type and result readings admit the type family, term and head
    ///   readings the term family, and unread/function readings neither.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — term and type fixtures exercise their reading
    ///   families; a type in value position is quoted rather than rejected as a
    ///   wrong family.
    /// - witness: `lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (Self::Unread | Self::Function, Family::Neither)
                    | (
                        Self::ValueType(_) | Self::CompType(_) | Self::Result(_),
                        Family::Type
                    )
                    | (
                        Self::Value(_) | Self::Computation(_) | Self::Head(_),
                        Family::Term
                    )
            )
        },
    )]
    const fn family(self) -> Family
    {
        match self {
            Self::Unread | Self::Function => Family::Neither,
            Self::ValueType(_frame) | Self::CompType(_frame) | Self::Result(_frame) => Family::Type,
            Self::Value(_frame) | Self::Computation(_frame) | Self::Head(_frame) => Family::Term,
        }
    }

    /// The binder frame this reading is under, the outermost for a reading
    /// that names none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: framed readings retain their frame, while unread and function
    ///   readings use the outermost frame.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda body resolves its binder at the exact index;
    ///   a reading without a binder is interpreted in the outermost scope.
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, ret),
                (
                    Self::Unread
                        | Self::Function
                        | Self::ValueType(Frame::Outermost)
                        | Self::CompType(Frame::Outermost)
                        | Self::Value(Frame::Outermost)
                        | Self::Computation(Frame::Outermost)
                        | Self::Head(Frame::Outermost)
                        | Self::Result(Frame::Outermost),
                    Frame::Outermost
                ) | (
                    Self::ValueType(Frame::Inner(_))
                        | Self::CompType(Frame::Inner(_))
                        | Self::Value(Frame::Inner(_))
                        | Self::Computation(Frame::Inner(_))
                        | Self::Head(Frame::Inner(_))
                        | Self::Result(Frame::Inner(_)),
                    Frame::Inner(_)
                )
            )
        },
    )]
    const fn frame(self) -> Frame
    {
        match self {
            Self::Unread | Self::Function => Frame::Outermost,
            Self::ValueType(frame)
            | Self::CompType(frame)
            | Self::Value(frame)
            | Self::Computation(frame)
            | Self::Head(frame)
            | Self::Result(frame) => frame,
        }
    }

    /// The universe a decode stands at when nothing was written to say, at
    /// the fuss-free level: the computation types where only a computation
    /// type is read, the value types everywhere else — a function's result
    /// included, which takes a value type under an inserted returner.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: only a computation-type reading defaults to the computation
    ///   universe; every other reading defaults to the value universe, all at
    ///   level zero.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — static application decodes at the written universe or
    ///   at the sort demanded by its position when no universe is written.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        ensures: |ret| {
            matches!(ret.level, LevelConstant::ZERO)
                && matches!(
                    (self, ret.sort),
                    (Self::CompType(_), GroundSort::Computation)
                        | (
                            Self::Unread
                                | Self::Function
                                | Self::ValueType(_)
                                | Self::Value(_)
                                | Self::Computation(_)
                                | Self::Head(_)
                                | Self::Result(_),
                            GroundSort::Value
                        )
                )
        },
    )]
    const fn positional_universe(self) -> Universe
    {
        match self {
            Self::CompType(_) => Universe {
                sort: GroundSort::Computation,
                level: LevelConstant::ZERO,
            },
            Self::Unread
            | Self::Function
            | Self::ValueType(_)
            | Self::Value(_)
            | Self::Computation(_)
            | Self::Head(_)
            | Self::Result(_) => Universe::FUSS_FREE,
        }
    }
}

/// Whether a former is a term, a type, or neither.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The family distinguishes term, type and non-expression forms
///   without forbidding the explicitly admitted type-in-value reading.
/// - provides: The coarse family check preceding former-specific admission.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No originating former is retained; `family_of` and
///   `classify_form` check classification and its quoting exception.
///
/// # Adequacy
/// - hypothesis: L3 — a computation in value position is nested, while a type
///   in value position can be quoted or used as a static code.
/// - witness: `lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
/// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Family
{
    /// Values and computations.
    Term,
    /// Value types and computation types.
    Type,
    /// Neither: a declaration or an attribute block.
    Neither,
}

/// How a form standing where a body ends treats that end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the variants partition what a form does at a body's end.
/// - provides: the vocabulary of exit inference.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exit, a match passing its end to its arms and a
///   returner ending a body distinguish the three.
/// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
/// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Ending
{
    /// The form is the exit: `return` or `become`, or a loop's `break` or
    /// `continue`.
    Exit,
    /// The form passes the end on to what ends it — a block's last
    /// computation, a match's arms, a grouping's operand, a lambda's own body,
    /// which answers the function type the end has, a loop's `break`s — or is
    /// a hole, which the author has yet to fill.
    Passes,
    /// The form ends the body without an exit, so the lowering infers the one
    /// its position names: at a body's end, `return` over a value and `become`
    /// over a computation; at a loop body's end, the loop's re-entry.
    Inferred,
}

/// How `former`, standing where a body ends, treats that end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `return`, `become`, `break` and `continue` are the exit; a block,
///   a match, an offer, a copattern block, a grouping, a lambda, a loop and a
///   hole pass the end on; every other former takes an inferred exit.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exits settle, a match ending in exits settles, and a
///   returner or a call ending a body takes an inferred exit at itself.
/// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
/// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
#[spec(ensures: |ret| match former {
    Former::Exit | Former::Become | Former::Break | Former::Continue => ret == Ending::Exit,
    Former::Block | Former::Case | Former::Offer | Former::LazyRecord | Former::Parenthesized | Former::Lambda | Former::Hole | Former::Loop | Former::While | Former::For => ret == Ending::Passes,
    Former::Name | Former::Constructor | Former::Number | Former::Text | Former::Unit | Former::Thunk | Former::Return | Former::Force | Former::Run | Former::Call | Former::Telescope | Former::Injection | Former::Binary | Former::Unary | Former::Projection | Former::TypeHead | Former::TypePath | Former::Universe | Former::TypeApplication | Former::ThunkType | Former::ReturnerType | Former::ArrowType | Former::ProductType | Former::SumType | Former::LazyProductType | Former::TelescopeType | Former::LabelledSumType | Former::LazyRecordType | Former::ValueFunctionType | Former::StaticAbstraction | Former::ParenthesizedType | Former::PathType | Former::RelationType | Former::CapabilityType | Former::AtType | Former::Scope | Former::Declaration | Former::AttributeBlock | Former::Import | Former::Module | Former::Data | Former::Mutual | Former::Instantiation | Former::SessionType | Former::Action | Former::Access | Former::World | Former::WorldDeclaration | Former::Reserved | Former::Unadmitted => ret == Ending::Inferred,
})]
fn ending(former: Former) -> Ending
{
    match former {
        Former::Exit | Former::Become | Former::Break | Former::Continue => Ending::Exit,
        Former::Block
        | Former::Case
        | Former::Offer
        | Former::LazyRecord
        | Former::Parenthesized
        | Former::Lambda
        | Former::Hole
        | Former::Loop
        | Former::While
        | Former::For => Ending::Passes,
        Former::Name
        | Former::Constructor
        | Former::Number
        | Former::Text
        | Former::Unit
        | Former::Thunk
        | Former::Return
        | Former::Force
        | Former::Run
        | Former::Call
        | Former::Telescope
        | Former::Injection
        | Former::Binary
        | Former::Unary
        | Former::Projection
        | Former::Instantiation
        | Former::TypeHead
        | Former::TypePath
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::SumType
        | Former::LazyProductType
        | Former::TelescopeType
        | Former::LabelledSumType
        | Former::LazyRecordType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::PathType
        | Former::RelationType
        | Former::CapabilityType
        | Former::AtType
        | Former::Scope
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Mutual
        | Former::SessionType
        | Former::Action
        | Former::Access
        | Former::World
        | Former::WorldDeclaration
        | Former::Reserved
        | Former::Unadmitted => Ending::Inferred,
    }
}

/// How `former`, standing where a path through a loop's body ends, treats
/// that end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the four exits are the exit; a block, a match, an offer, a
///   grouping and a hole pass the end on; every other former, a nested loop
///   among them, takes the inferred re-entry.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a loop ending in `continue`, in a match whose arms break
///   or end in a call, and in a call each lower and run; one ending in a hole
///   is left to be filled.
/// - witness: `lower::loops::tests::a_loop_body_ends_by_its_exits_or_runs_again`
/// - witness: `lower::loops::tests::a_hole_ending_a_loop_body_is_left_to_be_filled`
#[spec(ensures: |ret| match former {
    Former::Exit | Former::Become | Former::Break | Former::Continue => ret == Ending::Exit,
    Former::Block | Former::Case | Former::Offer | Former::Parenthesized | Former::Hole => ret == Ending::Passes,
    Former::Name | Former::Constructor | Former::Number | Former::Text | Former::Unit | Former::Thunk | Former::Lambda | Former::Return | Former::Loop | Former::While | Former::For | Former::Force | Former::Run | Former::Call | Former::Telescope | Former::Injection | Former::LazyRecord | Former::Binary | Former::Unary | Former::Projection | Former::TypeHead | Former::TypePath | Former::Universe | Former::TypeApplication | Former::ThunkType | Former::ReturnerType | Former::ArrowType | Former::ProductType | Former::SumType | Former::LazyProductType | Former::TelescopeType | Former::LabelledSumType | Former::LazyRecordType | Former::ValueFunctionType | Former::StaticAbstraction | Former::ParenthesizedType | Former::PathType | Former::RelationType | Former::CapabilityType | Former::AtType | Former::Scope | Former::Declaration | Former::AttributeBlock | Former::Import | Former::Module | Former::Data | Former::Mutual | Former::Instantiation | Former::SessionType | Former::Action | Former::Access | Former::World | Former::WorldDeclaration | Former::Reserved | Former::Unadmitted => ret == Ending::Inferred,
})]
fn iterating(former: Former) -> Ending
{
    match ending(former) {
        Ending::Exit => Ending::Exit,
        Ending::Passes
            if matches!(
                former,
                Former::Block | Former::Case | Former::Offer | Former::Parenthesized | Former::Hole
            ) =>
        {
            Ending::Passes
        },
        Ending::Passes | Ending::Inferred => Ending::Inferred,
    }
}

/// The family `former` belongs to.
///
/// # Specification
/// - requires: nothing.
/// - ensures: syntax formers are classified as terms, types or neither
///   independently of the demanded reading; static abstractions and session
///   types belong to the type-former family, session actions and offers to the
///   term family, and a reserved form to neither.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — term and type formers distinguish ordinary interpretation
///   from the positional quote, including a static abstraction.
/// - witness: `lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
/// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
#[spec(
    ensures: |ret| {
        matches!(
            (former, ret),
            (
                Former::Name
                    | Former::Constructor
                    | Former::Hole
                    | Former::Number
                    | Former::Text
                    | Former::Parenthesized
                    | Former::Unit
                    | Former::Thunk
                    | Former::Lambda
                    | Former::Block
                    | Former::Return
                    | Former::Exit
                    | Former::Become
                    | Former::Loop
                    | Former::While
                    | Former::For
                    | Former::Break
                    | Former::Continue
                    | Former::Force
                    | Former::Run
                    | Former::Call
                    | Former::Binary
                    | Former::Unary
                    | Former::Projection
                    | Former::Case
                    | Former::Telescope
                    | Former::Injection
                    | Former::LazyRecord
                    | Former::Instantiation
                    | Former::Scope
                    | Former::Action
                    | Former::Offer
                    | Former::Access
                    | Former::World,
                Family::Term
            ) | (
                Former::TypeHead
                    | Former::TypePath
                    | Former::Universe
                    | Former::TypeApplication
                    | Former::ThunkType
                    | Former::ReturnerType
                    | Former::ArrowType
                    | Former::ProductType
                    | Former::SumType
                    | Former::LazyProductType
                    | Former::TelescopeType
                    | Former::LabelledSumType
                    | Former::LazyRecordType
                    | Former::ValueFunctionType
                    | Former::StaticAbstraction
                    | Former::ParenthesizedType
                    | Former::PathType
                    | Former::RelationType
                    | Former::CapabilityType
                    | Former::AtType
                    | Former::SessionType,
                Family::Type
            ) | (
                Former::Declaration
                    | Former::AttributeBlock
                    | Former::Import
                    | Former::Module
                    | Former::Data
                    | Former::Mutual
                    | Former::Reserved
                    | Former::WorldDeclaration
                    | Former::Unadmitted,
                Family::Neither
            )
        )
    },
)]
const fn family_of(former: Former) -> Family
{
    match former {
        Former::Name
        | Former::Constructor
        | Former::Hole
        | Former::Number
        | Former::Text
        | Former::Parenthesized
        | Former::Unit
        | Former::Thunk
        | Former::Lambda
        | Former::Block
        | Former::Return
        | Former::Exit
        | Former::Become
        | Former::Loop
        | Former::While
        | Former::For
        | Former::Break
        | Former::Continue
        | Former::Force
        | Former::Run
        | Former::Call
        | Former::Binary
        | Former::Unary
        | Former::Projection
        | Former::Case
        | Former::Telescope
        | Former::Injection
        | Former::LazyRecord
        | Former::Instantiation
        | Former::Scope
        | Former::Action
        | Former::Offer
        | Former::Access
        | Former::World => Family::Term,
        Former::TypeHead
        | Former::TypePath
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::SumType
        | Former::LazyProductType
        | Former::TelescopeType
        | Former::LabelledSumType
        | Former::LazyRecordType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::PathType
        | Former::RelationType
        | Former::CapabilityType
        | Former::AtType
        | Former::SessionType => Family::Type,
        Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Mutual
        | Former::Reserved
        | Former::WorldDeclaration
        | Former::Unadmitted => Family::Neither,
    }
}

/// The sort a former produces before positional bridges.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The tag describes the former’s own core family before any
///   positional bridge is inserted.
/// - provides: The input sort to the positional admission relation.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The producing former and demanded reading are not
///   retained; require states the complete admission and insertion relation.
///
/// # Adequacy
/// - hypothesis: L3 — explicit and inserted force remain distinct, and a
///   positive result acquires one returner rather than changing its source
///   type.
/// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Produced
{
    /// A value.
    Value,
    /// A computation.
    Computation,
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
}

/// What the mint sweep writes over a node's own core node.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A bare result is unchanged; an insertion request is interpreted
///   against the lowered child family.
/// - provides: The conversion to apply after the node’s own plan is minted.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The child is not retained on the tag; require selects
///   requests and `Sink::bridge` checks the result family and provenance.
///
/// # Adequacy
/// - hypothesis: L3 — forcing, returner insertion and quotation record the
///   inserted node while preserving the authored child’s origin.
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Bridge
{
    /// Nothing: the node's sort is the sort its position reads.
    Bare,
    /// The bridge from the node's sort to the one its position reads.
    Inserted(Insertion),
}

quenchant_shape::reason_enum! {
    /// Why a function's parameter or result carries no type.
    pub mod stated {
        /// The function tail leaves the type to a signature written apart.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source wrote no `: T` after the binder, or no `-> T` after
            /// the parameter list.
            Unstated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a function tail closes no fixpoint.
    pub mod recursion {
        /// The function names nothing recursively.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration was not written `def rec`.
            Plain,
        }
    }
}

/// A stretch of one of the lowerer's flat stores, which a plan reads its list
/// from rather than owning one.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The endpoints denote a half-open range in a caller-selected flat
///   store; they do not certify order or bounds by themselves.
/// - provides: A borrowed-store coordinate rather than an owned list.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No store is retained, and reversed ranges are admitted
///   inputs to stretch; the accessor checks the borrowed range and empty
///   fallback.
///
/// # Adequacy
/// - hypothesis: L3 — empty, full, interior, reversed and past-end ranges
///   distinguish a valid selection from an invalid range.
/// - witness: `lower::tests::recorded_ranges_keep_valid_members_and_reject_invalid_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Stretch
{
    /// The first entry.
    start: usize,
    /// One past the last entry.
    end: usize,
}

/// What a block statement does with the value its computation returns, or
/// the fork or the hold it is.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum StatementBinding
{
    /// `run x <- c ;` names the value for the rest of the block, and so does
    /// `recv(c) as x ;`; the node is the name's own.
    Named(NodeIndex),
    /// `c ;` discards it, splitting it as the unit under a binder no name
    /// reaches.
    Discarded,
    /// `run (x, y, …) <- c ;` splits the tuple it returns, under a binder no
    /// name reaches, into one named binder per component.
    Split
    {
        /// The tuple's arity.
        arity: gandr_core_term::ComponentCount,
        /// The tuple pattern's own node.
        pattern: NodeIndex,
    },
    /// `run x : A <- c ;` ascribes `c` the returner `-F A`, pure as the
    /// annotation writes no row, and names the value it returns for the rest
    /// of the block, so a computation that returns no `A` refuses.
    Typed
    {
        /// The name's own node.
        name: NodeIndex,
        /// The value type `A` written, read in the statement's own frame.
        annotation: NodeIndex,
    },
    /// `fork (c : S) t as d ;` runs `t`, under `c`'s linear binder, beside
    /// the rest of the block, under `d`'s: the fork's protocol `S` and its
    /// child `t`.
    Forked
    {
        /// The protocol type `S` written for the child's end.
        protocol: NodeIndex,
        /// The child computation.
        child: NodeIndex,
    },
    /// `hold x = e ;` holds the value `e`, under `x`'s linear binder, over the
    /// rest of the block.
    Held
    {
        /// The value held.
        value: NodeIndex,
    },
    /// `leta x = v ;` opens the handle `v`, binding `x`, an intuitionistic
    /// hypothesis located at the handle's world, over the rest of the block.
    Opened
    {
        /// The handle opened.
        value: NodeIndex,
        /// The name's own node.
        name: NodeIndex,
    },
}

/// One `run x <- c ;` or `c ;` statement of a block.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The origin position supplies the bind’s origin while the bound
///   position supplies its computation; the rest says whether the block after
///   the statement is bound once or continues every local end of the
///   computation.
/// - provides: One source-ordered block binding.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Neither the source tree nor the lowered-node table is
///   retained; statement and `mint_block` check the coordinate roles.
///
/// # Adequacy
/// - hypothesis: L3 — consecutive run bindings scope over the following
///   computation and preserve their own source origins.
/// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `lower::tests::a_discarded_statement_splits_its_unit`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::exits::tests::a_bound_match_continues_its_block_at_each_local_arm`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Statement
{
    /// The origin of the bind: the `run` tile, or a discarded statement's
    /// computation.
    origin: NodeIndex,
    /// The computation whose returned value the statement binds.
    bound: NodeIndex,
    /// Whether the rest of the block names the value or discards it.
    binding: StatementBinding,
    /// Where the rest of the block goes.
    rest: exits::Rest,
}

/// A block: its statements, in source order, and its last computation.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The statement range precedes one final computation, which is not
///   replaced by an empty block result.
/// - provides: A block plan over the shared statement store.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The statement store and child results are absent; block
///   and `mint_block` check the range, final computation and bind order.
///
/// # Adequacy
/// - hypothesis: L3 — chained binds preserve order; a block without its final
///   computation is refused at the arity boundary.
/// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Block
{
    /// The block's statements, in the lowerer's statement store.
    statements: Stretch,
    /// The computation the block ends with.
    last: NodeIndex,
}

/// One parameter of a function tail.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The binder’s origin, introduced frame and optional written type
///   remain separate coordinates.
/// - provides: The data used to build a function’s lambda and signature spines.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The source, scope and lowered types are not retained;
///   function, `mint_function` and `mint_signature` interpret those
///   coordinates.
///
/// # Adequacy
/// - hypothesis: L3 — a typed parameter contributes to both spines, while an
///   unstated type does not prevent the function body from lowering.
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Parameter
{
    /// The binder tile, the origin of the parameter's lambda and arrow.
    binder: NodeIndex,
    /// The frame the parameter binds, which says whether a type names it.
    frame: ScopeId,
    /// The parameter's type, when the source wrote one.
    declared: Maybe<NodeIndex, stated::Absent>,
}

/// A label the source writes against an entry, kept while the lowering plans
/// so the label can answer what its entry lowers to.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the label's bytes, the node of the entry it names, and how that
///   entry is read.
/// - executable: none — the record holds neither the tree nor the scope its
///   coordinates are read in.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::labelled`].
/// - witness: `lower::arity::tests::each_label_names_what_it_labels`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LabelSite
{
    /// The label's bytes.
    written: ByteSpan,
    /// The entry the label names.
    held: NodeIndex,
    /// How the entry is read.
    read: LabelRead,
}

/// How the entry a label names is read.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LabelRead
{
    /// As a value type under the frame: the label answers at that type.
    ValueType(Frame),
    /// As a computation type under the frame.
    CompType(Frame),
    /// As a term: the label answers at the term's type.
    Term,
}

/// A universe as the source wrote it: its sort and its level, each defaulted
/// when left off.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The ground sort and nonnegative level are retained independently
///   after explicit or positional defaulting.
/// - provides: The universe at which a source type or code is read.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The spelling and reading position are absent;
///   `universe_of` and `positional_universe` state their distinct defaulting
///   rules.
///
/// # Adequacy
/// - hypothesis: L3 — bare, explicitly sorted and explicitly levelled spellings
///   keep their universes, including the universe of a decoded bound code.
/// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
/// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Universe
{
    /// The sort, `+` for the value types and `-` for the computation types.
    sort: GroundSort,
    /// The level.
    level: LevelConstant,
}

impl Universe
{
    /// The universe a bare `Type` names and an unwritten one defaults to:
    /// the value types at the fuss-free level.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value sort at level zero, not the computation sort.
    /// - provides: the universe of a bare `Type` and the context-free default.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the specification attribute does not accept
    ///   constant items; `universe_of` checks the resulting sort and level.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bare and explicitly sorted universe spellings
    ///   distinguish the value default from a computation universe.
    /// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
    const FUSS_FREE: Self = Self {
        sort: GroundSort::Value,
        level: LevelConstant::ZERO,
    };
}

/// What a path type's carrier is written as.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Carrier
{
    /// A type, the node written at the carrier's place.
    Written(NodeIndex),
    /// A universe spelled by the form's own tiles, `Path(Type, A, B)`: the
    /// endpoints are written as types.
    Universe(Universe),
}

/// The code a decode reads its type from, and the head a static application
/// applies.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A bound code retains the use frame and binder identity until
///   telescope indexing; a constant retains its admission coordinate.
/// - provides: The common head of static applications and decoded types.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The scope and declaration store needed for resolution
///   are absent; `resolve_name`, `static_application` and `mint_code` check
///   their uses.
///
/// # Adequacy
/// - hypothesis: L3 — bound and declared codes decode at their written universe
///   and static applications retain source argument order.
/// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
/// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Code
{
    /// A binder, named from a use site under the frame `from`, whose index is
    /// counted in `telescope` once every type has been read: the signature's,
    /// or a body quote's (#547).
    Bound
    {
        /// The use site's frame.
        from: Frame,
        /// The binder's frame.
        binder: ScopeId,
        /// The telescope the index is counted in.
        telescope: Telescope,
    },
    /// A declaration at this admission position.
    Constant(ConstantIndex),
}

quenchant_shape::reason_enum! {
    /// Why a name resolves to nothing.
    pub mod named {
        /// Neither scope carries the name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No enclosing binder and no earlier declaration is named so.
            Unresolved,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a call's head names no type former.
    pub mod formed {
        /// The head is not a type former's spelling, free.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The head is no capitalised name, spells no former a type
            /// application takes, or names a binder, an earlier declaration
            /// or a stated type that shadows the former.
            Unformed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a `run` statement's binder splits no tuple.
    pub mod untupled {
        /// The binder is a name, a wildcard or another pattern.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The binder is not a tuple pattern.
            OtherPattern,
        }
    }
}

/// What a name resolved to.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A binder retains its bound coordinate; a declaration retains its
///   constant and available written signature.
/// - provides: A resolved name that can become a term or static code.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No name, lookup frame or declaration table is retained;
///   `resolve_name` checks lookup and term checks the projection.
///
/// # Adequacy
/// - hypothesis: L3 — local binders and earlier declarations produce different
///   core references, and self-reference remains unresolved.
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
/// - witness: `lower::tests::a_self_reference_is_unresolved`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Resolved
{
    /// An enclosing binder.
    Binder(Bound),
    /// A declaration strictly earlier than the name's own.
    Declaration
    {
        /// The declaration's admission position.
        constant: ConstantIndex,
        /// The type its signature was written with, when it has one.
        declared: Maybe<NodeIndex, binder_type::Absent>,
    },
}

quenchant_shape::reason_enum! {
    /// Why a path's head reads no aliased import.
    mod alias_member {
        /// The reason the head is no alias.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The head names no alias of a path import of the source.
            Unaliased,
        }
    }
}

impl Resolved
{
    /// The plan of the value the name stands for in term position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a resolved binder becomes a variable plan and a resolved
    ///   declaration a constant plan, retaining the respective index.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — binder uses become de Bruijn variables, while earlier
    ///   declarations become constants with their admission position.
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `tests::modules::a_backward_member_reference_resolves`
    #[spec(
        ensures: |ret| {
            matches!(
                (self, &ret),
                (Self::Binder(_), &Plan::Variable(..))
                    | (Self::Declaration { .. }, &Plan::Constant(_))
            )
        },
    )]
    const fn term(self) -> Plan
    {
        match self {
            Self::Binder(bound) => Plan::Variable(bound.index, bound.binder),
            Self::Declaration { constant, .. } => Plan::Constant(constant),
        }
    }
}

/// A function tail's reading: `(params) -> T? { … }`.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The parameter range, optional result and block are retained
///   separately so an incomplete signature does not discard the body; a
///   recursive tail retains the frame binding its own name.
/// - provides: The two spines of a function tail.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The parameter store and lowered children are not
///   retained; function, `mint_function` and `mint_signature` check the stored
///   ranges and outcomes.
///
/// # Adequacy
/// - hypothesis: L3 — zero and multiple parameters preserve the body and
///   signature distinction, including tails with an unstated type.
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Function
{
    /// The parameters, in the lowerer's parameter store.
    parameters: Stretch,
    /// The result type, when the source wrote one.
    result: Maybe<NodeIndex, stated::Absent>,
    /// The body.
    block: Block,
    /// The frame binding the function's own name, between the staged
    /// parameter and the ones before it, when the tail recurses.
    recursion: Maybe<ScopeId, recursion::Absent>,
}

/// The continuation type's head, resolved after every binder and earlier
/// declaration at two arguments.
const STACK: &str = "Stack";

/// What the mint sweep does for one node, decided by the classification.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The selected former retains the child coordinates and flat-store
///   ranges needed by the later mint sweep; transparent plans adopt their
///   child.
/// - provides: The classification-to-minting boundary without recursive source
///   re-reading.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The source, stores and child results are absent; the
///   readers specify each plan and `mint_plan` checks its output family and
///   transparent case.
///
/// # Adequacy
/// - hypothesis: L3 — the admitted term and type formers retain their concrete
///   core structure, while grouping adds no constructor.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
/// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
/// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
#[derive(Clone, Debug, Eq, PartialEq)]
enum Plan
{
    /// Mint nothing.
    Unplanned,
    /// A value hole at its source occurrence.
    ValueHole(gandr_core_term::hole::HoleId),
    /// A computation hole at its source occurrence.
    CompHole(gandr_core_term::hole::HoleId),
    /// A variable at this index, bound by the binder that entered this frame.
    Variable(DeBruijnIndex, ScopeId),
    /// A constant at this admission position.
    Constant(ConstantIndex),
    /// A table-typed native prelude thunk.
    Primitive(gandr_core_term::primitive::Primitive),
    /// A saturated table operation selected by source operator syntax.
    PrimitiveCall(
        gandr_core_term::primitive::Primitive,
        gandr_core_term::primitive::Arguments<NodeIndex>,
    ),
    /// The unit value.
    Unit,
    /// A literal, already parsed from the node's own text.
    Literal(Literal),
    /// A nullary type atom.
    Atom(TypeAtom),
    /// The atom the abstract type at this admission position declares.
    Sealed(ConstantIndex),
    /// The manifest type an application's instance exports: the type the
    /// functor's body wrote at the node, renamed by the application.
    Instantiated(InstanceIndex, NodeIndex),
    /// A universe.
    Universe(Universe),
    /// The type a code denotes, in the universe it was declared at: the code
    /// is the head applied statically to the arguments in the lowerer's
    /// operand store, none for a bare name.
    Decode(Code, Stretch, Universe),
    /// The type the code a dynamic function returns denotes: the function the
    /// code names — a declaration at its admission position, or a binder
    /// holding a thunk — called on the arguments in the lowerer's operand
    /// store, its returned code decoded in the universe the position reads.
    Unquote(Code, Stretch, Universe),
    /// The call of a dynamic function the code names on the arguments in the
    /// lowerer's operand store, left to right: a type-position call's argument
    /// written as a call, which a value position nests.
    Called(Code, Stretch),
    /// A static application of the head to the arguments in the lowerer's
    /// operand store, left to right.
    StaticApplication(Code, Stretch),
    /// A static lambda over its body.
    StaticLambda(NodeIndex),
    /// A type former over its argument.
    Former(TypeFormer, NodeIndex),
    /// An arrow over its domain and codomain.
    Arrow(NodeIndex, NodeIndex),
    /// A static Pi over its domain and codomain.
    StaticPi(NodeIndex, NodeIndex),
    /// One eager product of the value types in the lowerer's operand store,
    /// in order: an unparenthesized `*` chain is one former, and the
    /// positional telescope type `#{A, …}` another, of any arity.
    Product(Stretch),
    /// The type over labels `#{ l : A, … }`: its fields by label, the binders
    /// of every entry but the last in the lowerer's parameter store, each
    /// over the entries after it, and the last entry's type. The record type
    /// of its fields when no later entry names an earlier label, the
    /// dependent pairs nested to the right otherwise.
    RecordType(BTreeMap<FieldLabel, NodeIndex>, Stretch, NodeIndex),
    /// The sum of the value types in the lowerer's operand store, in order.
    Sum(Stretch),
    /// The lazy record of the computation types in the lowerer's operand
    /// store, in order: the binary lazy product nested to the right.
    With(Stretch),
    /// A case of no arms over a scrutinee stated at no data type and no path
    /// type: the eliminator of the empty sum.
    EmptyCase(NodeIndex),
    /// One tuple of the values in the lowerer's operand store, in order.
    Tuple(Stretch),
    /// The record of the values its labels name: `#{ .l = v, … }`.
    Record(BTreeMap<FieldLabel, NodeIndex>),
    /// The injection of its value into the summand at this index.
    Injection(Summand, NodeIndex),
    /// The copattern block over the computations in the lowerer's operand
    /// store, in order: the binary lazy pair nested to the right.
    Copattern(Stretch),
    /// One entry of the lazy record the thunk at the node holds: the thunk
    /// forced, then observed along the nesting.
    Observe(NodeIndex, arity::Observed),
    /// One entry of the dependent record the name at the node holds:
    /// projected along the nesting.
    Select(NodeIndex, arity::Observed),
    /// The thunked arrow from the domains in the lowerer's operand store to
    /// the returner of the codomain.
    ValueFunction(Stretch, NodeIndex),
    /// The thunked telescope from the entries in the lowerer's parameter
    /// store, each binding the ones after it, to the returner of the
    /// codomain.
    Telescope(Stretch, NodeIndex),
    /// A dependent arrow `(x : A) -> C`: its one binder, in the parameter
    /// store, and its codomain.
    DependentArrow(Stretch, NodeIndex),
    /// Adopt the child's lowered node unchanged.
    Transparent(NodeIndex),
    /// A thunk over its block.
    Thunk(Block),
    /// A returner over its value.
    Return(NodeIndex),
    /// A force over its value.
    Force(NodeIndex),
    /// A run over its computation, standing for the value it returns.
    Run(NodeIndex),
    /// A lambda over its block, and the node its parameter is written at.
    Lambda(Block, NodeIndex),
    /// A block's statements bound over its last computation.
    Block(Block),
    /// A loop's fixpoint over its body.
    Loop(Block),
    /// A conditional loop's fixpoint over the case of its condition: its body
    /// when the condition holds, leaving the loop with unit when it does not.
    While(NodeIndex, Block),
    /// A bare `break`: the returner of unit, leaving the nearest loop.
    Break,
    /// A `continue`: the force of the nearest loop's fixpoint, at this index.
    Reenter(DeBruijnIndex),
    /// An application of its head to its arguments, left to right, in the
    /// lowerer's operand store.
    Application(NodeIndex, Stretch),
    /// A function tail's declared type and body.
    Function(Function),
    /// The nominal family declared at this admission position, over the
    /// arguments in the lowerer's operand store, left to right.
    Data(ConstantIndex, Stretch),
    /// The type family member at this place of the collection's family list,
    /// its type expanded over the arguments in the lowerer's operand store,
    /// left to right.
    Expansion(FamilyIndex, Stretch),
    /// A constructor applied to its fields.
    Constructor(native::Constructed),
    /// A match, compiled to the decision tree at this position of the
    /// lowerer's match store.
    Case(native::CaseIndex),
    /// An element path type over its carrier and its two endpoints.
    Path(Carrier, NodeIndex, NodeIndex),
    /// Reflexivity at its point.
    Here(NodeIndex),
    /// Function extensionality between its two functions.
    Funext(NodeIndex, NodeIndex),
    /// A universe equivalence between its two translators.
    Equiv(NodeIndex, NodeIndex),
    /// Univalence over its record, `ua(e)`.
    Univalence(NodeIndex),
    /// The native product of two universe paths.
    PathProduct(NodeIndex, NodeIndex),
    /// Univalence at a stratum between two descriptions, over its forward
    /// and backward translator records.
    Ua
    {
        /// The degree and catalogue bound written in the head.
        stratum: gandr_core_term::ua::Stratum,
        /// The two descriptions as a stratum reads them.
        sides: Arc<gandr_core_term::ua::Sides>,
        /// Where the two descriptions are named, the source's first.
        named: [Origin; 2],
        /// The forward translator record.
        forward: NodeIndex,
        /// The backward translator record.
        backward: NodeIndex,
    },
    /// The empty native list.
    ListNil,
    /// A native list cell over its head and tail.
    ListCons(NodeIndex, NodeIndex),
    /// Transport along a path, over the static abstraction its motive is
    /// written as, the path, and the transported value.
    Transport(NodeIndex, NodeIndex, NodeIndex),
    /// A directed identity type over its carrier and its two endpoints:
    /// `Flow(A, a, b)`.
    Flow(NodeIndex, NodeIndex, NodeIndex),
    /// A relation between two types written infix, over its two operands:
    /// value types for the equivalence and the quasi-inverse, codes for the
    /// flow.
    Relation(Relation, NodeIndex, NodeIndex),
    /// A first-class continuation's type over the computation types it runs
    /// from and to: `Stack(C, D)`.
    Stack(NodeIndex, NodeIndex),
    /// A session statement, `bisim(A, B)` or `sim(A, B)`, over its two codes.
    SessionRelated(
        gandr_core_term::session::SessionRelation,
        NodeIndex,
        NodeIndex,
    ),
    /// The identity flow at its point.
    Stay(NodeIndex),
    /// The forward flow of its translator.
    Forward(NodeIndex),
    /// The function flow over its domain and codomain flows.
    FunctionFlow(NodeIndex, NodeIndex),
    /// The product of two universe flows.
    FlowProduct(NodeIndex, NodeIndex),
    /// Two flows composed, returned: `f then g` where a flow is answered.
    FlowThen(NodeIndex, NodeIndex),
    /// A recorded run, its moves in order, each payload the node it was
    /// written as.
    Recorded(Arc<[gandr_core_term::session::RecordedMove<NodeIndex>]>),
    /// A ride along a flow, over the static abstraction its motive is written
    /// as, the flow, and the value moved.
    Ride(NodeIndex, NodeIndex, NodeIndex),
    /// `back`, `then` or `cong`, unfolded to the transport it derives
    /// against the path type its position answers.
    Derived(identity::Derived),
    /// The dependent transport over its telescope motive.
    TelescopeTransport(identity::Transported),
    /// A capability type over its authority at its grade, living in its
    /// region.
    Capability(
        capability::Authority,
        gandr_core_term::effect::capability::CapabilityGrade,
        gandr_core_term::effect::capability::Region,
    ),
    /// The returner of the value type at the node, its row holding these
    /// interfaces whole.
    Effectful(BTreeSet<gandr_core_term::effect::EffectName>, NodeIndex),
    /// An operation exercised through a capability.
    Exercise(capability::Exercised),
    /// A capability scope over its subject and clauses.
    Scope(capability::Scoped),
    /// The continuation at the node resumed with the reply the values in the
    /// lowerer's operand store make.
    Resume(NodeIndex, Stretch),
    /// A session type: its protocol over the payload types in the lowerer's
    /// operand store, in slot order, standing at the protocol's root, and
    /// every site the source writes one of its states at.
    Session(Arc<Protocol>, Stretch, Arc<session::Written>),
    /// A session action over the nodes of its payload, its arms and a fork's
    /// protocol and children, with the bytes its endpoint is written at and,
    /// for an offer, each arm's label with the bytes its pattern is written at.
    Action(
        SessionAction<NodeIndex, NodeIndex, NodeIndex>,
        ByteSpan,
        session::ArmLabels,
    ),
    /// A temporary-access form: an access over its body and unwind, or an
    /// eliminator of its view.
    Access(access::Accessed),
    /// A located form or type: a handle type `A at w`, a hold or a
    /// migration.
    World(world::Worlded),
}

/// A node's lowered core node, at the sort its own form produced.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The family tag prevents reading a value as a computation or type;
///   a function can retain a body without a signature.
/// - provides: A family-indexed result for later parents and declaration
///   assembly.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Arena membership cannot be checked from numeric
///   identifiers alone; minting functions and family accessors state the
///   executable result relations.
///
/// # Adequacy
/// - hypothesis: L3 — completed and one-sided declarations preserve their
///   available halves, and function tails keep their body when a type is
///   absent.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
/// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Lowered
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
    /// A function tail: its declared type, when it states one, and its body.
    Function
    {
        /// `+U (A1 -> … -> An -> C)`, from the parameter and result types.
        signature: Maybe<ValueTypeId, lowered::Absent>,
        /// `thunk (λ … λ. block)`.
        body: ValueId,
    },
}

/// Whether a module's own slot holds a half that lowers to a core term.
///
/// # Specification
/// - requires: nothing.
/// - ensures: two distinct answers, so [`Lowerer::outcome`] reads an absent
///   outcome of a slot that owes a declaration as a refusal and of any other
///   slot as the absence it is.
/// - provides: the answer of [`Lowerer::lowers_a_half`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function whose halves the mint left unminted owes a
///   declaration and is refused by name.
/// - witness: `lower::tests::a_declaration_minting_neither_half_is_refused_by_name_455`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Owed
{
    /// A half lowers to a core term, so the slot owes a declaration.
    Owed,
    /// No half lowers to a core term.
    Nothing,
}

/// Whether a form can stand where a value is expected.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag denotes admission to the syntactic value class, not
///   successful name resolution or type checking.
/// - provides: A value-form decision kept distinct from other Boolean
///   decisions.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The tested former is not retained; `is_value_form`
///   specifies the finite membership relation.
///
/// # Adequacy
/// - hypothesis: L3 — the finite former table distinguishes syntactic values
///   from computations and type forms before payload schema checks.
/// - witness: `lower::tests::only_the_value_forms_can_stand_as_a_payload`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ValueForm(bool);

/// Whether a spelling is a numeric lexeme with a fraction or an exponent.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag distinguishes a well-formed but unsupported fractional
///   spelling from a malformed integer spelling.
/// - provides: A lexical refusal decision distinct from numeric evaluation.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — No input text is retained; fractional states the
///   executable numeric-language predicate.
///
/// # Adequacy
/// - hypothesis: L3 — decimal and exponent markers, missing fields, signs and
///   non-ASCII digits separate unsupported numbers from malformed lexemes.
/// - witness: `lower::tests::fractional_spellings_distinguish_unsupported_numbers_from_malformed_ones`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Fractional(bool);

/// Whether a node lies inside an attribute payload, which lowers whatever
/// its declaration's outcome.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The flag marks nodes that remain eligible for minting despite an
///   enclosing declaration’s refusal.
/// - provides: The payload exception to ordinary refusal pruning.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The node and enclosing attributes are absent; seed,
///   `inherit_payload` and `mint_at` check marking and its effect.
///
/// # Adequacy
/// - hypothesis: L3 — an otherwise refused declaration retains its valid
///   attribute payload, and invalid attributes still receive their diagnostics.
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
/// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct InPayload(bool);

/// One form being classified: where it stands, what it is called, and how
/// its position reads it.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: The location, form name and positional reading stay available
///   together when constructing a located refusal.
/// - provides: The source context shared by the form readers.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The grammar and source tree are not retained; readers
///   check admission and one checks the operand-count projection.
///
/// # Adequacy
/// - hypothesis: L3 — misplaced tiles, extra operands and wrong operand counts
///   retain their distinct refusal kinds and source positions.
/// - witness: `lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Site
{
    /// The form.
    at: Placed,
    /// The form's kind, as a diagnostic writes it.
    name: FormName,
    /// How the form's position reads it.
    reading: Reading,
}

impl Site
{
    /// The refusal this form earns for leaving the fragment by `boundary`.
    ///
    /// # Specification
    /// trivial.
    const fn out<'source>(
        self,
        boundary: FragmentBoundary,
    ) -> LoweringRefusal<'source>
    {
        self.folded(self.name, boundary)
    }

    /// The refusal this form earns as the folded form `form`.
    ///
    /// # Specification
    /// - requires: the site identifies the refused source form.
    /// - ensures: the refusal retains the supplied form and boundary at the
    ///   site, with the sort demanded by its reading.
    /// - provides: a positional refusal for a nested former.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declined value, computation and type forms keep the
    ///   position’s sort, distinct from the former’s own family.
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
    #[spec(
        ensures: |ret| {
            matches!(
                (self.reading, ret),
                (
                    Reading::Unread | Reading::Function,
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::Declaration,
                        ..
                    }
                ) | (Reading::ValueType(_), LoweringRefusal::OutOfFragment {
                    sort: FragmentSort::ValueType,
                    ..
                }) | (
                    Reading::CompType(_) | Reading::Result(_),
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::CompType,
                        ..
                    }
                ) | (Reading::Value(_), LoweringRefusal::OutOfFragment {
                    sort: FragmentSort::Value,
                    ..
                }) | (
                    Reading::Computation(_) | Reading::Head(_),
                    LoweringRefusal::OutOfFragment {
                        sort: FragmentSort::Computation,
                        ..
                    }
                )
            )
        },
    )]
    const fn folded<'source>(
        self,
        form: FormName,
        boundary: FragmentBoundary,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::OutOfFragment {
            span: self.at.span,
            form,
            sort: self.reading.sort(),
            boundary,
        }
    }

    /// The refusal this form earns for `fault` at `span`.
    ///
    /// # Specification
    /// trivial.
    const fn fault<'source>(
        self,
        span: ByteSpan,
        fault: FormFault,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::MalformedForm {
            span,
            form: self.name,
            fault,
        }
    }

    /// The operand a one-operand hole holds, or the fault its run earns.
    ///
    /// # Specification
    /// - requires: `run` is a hole of this form.
    /// - ensures: the operand of a one-operand run; an empty run is a missing
    ///   operand at its gap, and a longer run an extra operand at its second.
    /// - provides: the one-hole reading every former shares.
    /// - fails: yields the missing-operand or extra-operand refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a hole not holding one form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — single-operand forms and an overfull hole distinguish
    ///   success from an arity fault at the extra operand.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
    #[spec(
        ensures: |ret| {
            matches!(
                (run, ret),
                (Run::One(_), Ok(_))
                    | (
                        Run::Empty(_),
                        Err(LoweringRefusal::MalformedForm {
                            fault: FormFault::MissingOperand,
                            ..
                        })
                    )
                    | (
                        Run::Several { .. },
                        Err(LoweringRefusal::MalformedForm {
                            fault: FormFault::ExtraOperand,
                            ..
                        })
                    )
            )
        },
    )]
    const fn one<'source>(
        self,
        run: Run,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        match run {
            Run::One(operand) => Ok(operand),
            Run::Empty(gap) => Err(self.fault(gap, FormFault::MissingOperand)),
            Run::Several { extra, .. } => Err(self.fault(extra.span, FormFault::ExtraOperand)),
        }
    }
}

/// The lowering's working state, shared by both sweeps.
///
/// # Specification
/// - requires: The grammar, tree and collected declarations describe one
///   lowering run.
/// - ensures: Per-node tables share the tree’s coordinate space; planned
///   flat-store ranges and declaration ownership are interpreted only in that
///   run.
/// - provides: The state linking collection, classification, minting and
///   assembly.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Type-level invariant expansion is unavailable in the
///   enabled specification facade; new and the phase boundaries carry
///   executable table and state relations.
///
/// # Adequacy
/// - hypothesis: L3 — declaration isolation, manifest dependencies, origins and
///   attribute retention are observed through parsed multi-declaration modules,
///   not inferred from table lengths alone.
/// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
/// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
struct Lowerer<'run, 'source>
{
    /// The grammar the tree was molded under.
    pbg: &'run Pbg,
    /// The tree being lowered.
    tree: &'run SyntaxTree<'source>,
    /// The module's declarations and the slot each node belongs to.
    collected: Collected<'source>,
    /// How each node's position reads it.
    readings: Vec<Reading>,
    /// What the mint sweep does for each node, kept once it is done: a later
    /// source's classification reads an earlier source's plans.
    plans: Vec<Plan>,
    /// Whether the mint sweep has carried out each node's plan, which it does
    /// once.
    taken: Vec<bool>,
    /// What the mint sweep writes over each node's own core node.
    bridges: Vec<Bridge>,
    /// Each node's lowered core node.
    lowered: Vec<Maybe<Lowered, lowered::Absent>>,
    /// Which nodes lie inside an attribute payload.
    payload: Vec<InPayload>,
    /// The manifest type components each node sees, where it lies in a
    /// module signature.
    scopes: Vec<Maybe<ComponentScope, scoped::Absent>>,
    /// Each type head that named a manifest type component, with the held
    /// slot owning that component's type.
    manifests: Vec<(SlotIndex, NodeIndex)>,
    /// Each exported value component's full path, with the member's slot.
    exported: BTreeMap<NamePath, SlotIndex>,
    /// Each exported type component's full path, with what it reads.
    exported_types: BTreeMap<NamePath, TypeComponent<'source>>,
    /// Each witness's body, by slot.
    witnessed: BTreeMap<SlotIndex, ValueId>,
    /// Each abstract slot's declaration, once its kind and representation
    /// lowered.
    sealings: BTreeMap<SlotIndex, Sealing>,
    /// Each kind witness's declared kind and body, the code of the type
    /// member it checks.
    kind_checks: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// Each slot whose signature a model derives, with the type minted for
    /// it.
    modelled: BTreeMap<SlotIndex, ValueTypeId>,
    /// Each slot a check after minting refused: a derived component that
    /// names one that did not lower, or a family whose parameters disagree
    /// with its indices.
    faults: BTreeMap<SlotIndex, LoweringRefusal<'source>>,
    /// The arguments every planned application reads, stretch by stretch.
    operands: Vec<NodeIndex>,
    /// The statements every planned block reads, stretch by stretch.
    statements: Vec<Statement>,
    /// The parameters every planned function reads, stretch by stretch.
    parameters: Vec<Parameter>,
    /// The binder frames the lambdas, the parameters and the statements
    /// extended.
    scope: Scope<'source>,
    /// The outermost scope every declared name is declared in and every
    /// binder is reported against.
    recognition: Recognition,
    /// The remaining allowance.
    fuel: Fuel,
    /// The scratch reading of the form being classified.
    pieces: Pieces,
    /// The scratch reading of a written universe a decode reads its sort and
    /// level from.
    scratch: Pieces,
    /// Each constructor written under an annotation, with the annotation's
    /// type.
    classifiers: BTreeMap<NodeIndex, NodeIndex>,
    /// Each value argument of a data family's application, with its place.
    argued: BTreeMap<NodeIndex, native::Argued>,
    /// Each constructor classified by its place in a data family's
    /// application, not yet minted: its classifier reads the arguments before
    /// it, which the mint sweep reaches after it, so the application mints it.
    awaiting: BTreeSet<NodeIndex>,
    /// Each thunk a definition is, with the answer its signature states for
    /// its body: `C` for `+U C`, `-F B` for `() => B`.
    thunked: BTreeMap<NodeIndex, native::Answer>,
    /// Each node a type classifies without annotating it: a definition whose
    /// signature writes a type no thunk is, and a field of a constructor with
    /// a classifier, with the classifier it takes.
    inherited: BTreeMap<NodeIndex, native::Classifier>,
    /// Each label written against an entry, in the order planned.
    labels: Vec<LabelSite>,
    /// Each type head that stands for a type minted elsewhere: a manifest
    /// component's or a functor instance's, which the head adopts.
    stand_ins: BTreeSet<NodeIndex>,
    /// The type each computation position answers, where a function's result
    /// or a match's answer states it, or the block a statement's local ends
    /// continue answers.
    answers: BTreeMap<NodeIndex, native::Answer>,
    /// Each derived operation standing where no type is answered, its motive
    /// synthesised from its operands: the innermost first once
    /// [`Self::refuse_unsynthesised`] has read them, for the mint sweep.
    synthesised: Vec<Site>,
    /// The terms standing inside a type: a path type's endpoints and every
    /// node under one, whose bound names count only the frames that bind in
    /// the type's telescope and make the arrow binding them dependent.
    in_type: BTreeSet<NodeIndex>,
    /// The nodes of a type a body quotes, the quote included: their binder
    /// reads count in the quote's own telescope, which the quote is carried
    /// out of into the body's context, and never make the signature's arrows
    /// dependent (#547).
    in_quote: BTreeSet<NodeIndex>,
    /// The terms standing at an endpoint: a path type's endpoints,
    /// reflexivity's point and every node under one, where a computation
    /// standing as a value is the value it returns.
    at_endpoint: BTreeSet<NodeIndex>,
    /// What every node's paths do with the body it stands in, surveyed before
    /// the classification reads it.
    leaves: Vec<exits::Leaves>,
    /// The computation positions where a path through a body ends: the last
    /// computation of a function's, a lambda's or a thunk's body, and what
    /// stands in tail position of one — a block's last computation, a match's
    /// arm, a grouping's operand. A form there that is not an exit takes the
    /// one its polarity names.
    exits: BTreeSet<NodeIndex>,
    /// The computation positions a path through a body passes, where an exit
    /// may stand: every position where a path ends, and every statement's
    /// computation in a block on a path, with what stands in tail position of
    /// one.
    exitable: BTreeSet<NodeIndex>,
    /// The computation positions whose local ends continue a block: the
    /// computation of a statement that holds an exit, and what stands in tail
    /// position of one.
    joined: BTreeSet<NodeIndex>,
    /// The exits read: every `return` and `become`, written or inferred, and
    /// every `continue`, whose minted computation the commuting keeps where
    /// it stands.
    leaving: BTreeSet<NodeIndex>,
    /// The computation positions where a path through a loop's body ends: the
    /// body's last computation, and what stands in tail position of one. A
    /// form there that is no exit runs the loop again.
    iterated: BTreeSet<NodeIndex>,
    /// The computation positions a path through a loop's body passes, where
    /// a `break` or a `continue` may stand.
    looping: BTreeSet<NodeIndex>,
    /// The `break`s read, whose minted returner the commuting continues with
    /// what follows their loop.
    breaking: BTreeSet<NodeIndex>,
    /// The loop ends written without an exit, each run again: the index its
    /// loop's fixpoint has under the binder of the result it discards.
    reentered: BTreeMap<NodeIndex, DeBruijnIndex>,
    /// The conditions of `while` loops, read where a computation is: a value
    /// written there is returned, so the loop binds what it tests.
    tested: BTreeSet<NodeIndex>,
    /// The computation positions where a path through a handled subject
    /// ends: the subject's last computation, and what stands in tail position
    /// of one. A value there is returned to the handler's return clause, as
    /// the subject's result; neither it nor a computation there is an exit.
    results: BTreeSet<NodeIndex>,
    /// The computation positions a path through a handled subject passes: a
    /// `return` there leaves its body past every handler frame around it, and
    /// a `become` there is refused.
    framed: BTreeSet<NodeIndex>,
    /// The positions of `framed` whose nearest loop stands outside a
    /// handler's frame: a `break` or a `continue` there is refused.
    looped_past: BTreeSet<NodeIndex>,
    /// The body every position a path passes belongs to, by that body's last
    /// computation.
    bodies: BTreeMap<NodeIndex, NodeIndex>,
    /// The `return`s written at a position of `framed`, each minted as a
    /// capture its body's delimiter discards.
    crossing: BTreeSet<NodeIndex>,
    /// The bodies, by their last computation, that hold a `return` of
    /// `crossing`: each is minted under a delimiter.
    delimited: BTreeSet<NodeIndex>,
    /// The tails the source wrote without an exit, each exited by the one its
    /// polarity names: a value by an inserted `return`, a computation by
    /// running it in tail position.
    inferred: BTreeSet<NodeIndex>,
    /// Every inferred exit the mint sweep minted, with its tail's position.
    elided: Vec<(NodeIndex, Exit)>,
    /// The slots an `explicit_exits` attribute asks written exits of: a
    /// declaration it decorates, and every member of a module it decorates.
    asked: BTreeSet<SlotIndex>,
    /// Which runs an `explicit_runs` attribute asks written of each slot it
    /// reaches: a declaration it decorates, and every member of a module it
    /// decorates, the wider ask where both reach.
    asked_runs: BTreeMap<SlotIndex, AskedRuns>,
    /// The first byte of every statement and tail a block holds that does not
    /// open with `run`: where a `run` written would open a bind instead.
    leading: BTreeSet<ByteOffset>,
    /// Each block's last computation written as a statement, `c ;` before the
    /// closing brace, with the statement's span: admitted only as an exit.
    stated: BTreeMap<NodeIndex, ByteSpan>,
    /// The matches, each compiled to its decision tree.
    cases: Vec<native::CaseForm>,
    /// The position each lowered data declaration's signature takes, by its
    /// position in the collection's data list.
    signatures: BTreeMap<usize, DataIndex>,
    /// The position each words' signature takes, by its position in the
    /// collection's words list.
    worded: BTreeMap<usize, DataIndex>,
    /// The path type at each minted words' point and the family the point
    /// lives in, by its position in the collection's words list: what a later
    /// source's letters and empty words are labelled at.
    word_types: BTreeMap<usize, (ValueTypeId, ValueTypeId)>,
    /// Each loop's binding, the path type at its point and the word of its
    /// one letter, by slot.
    looped: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// Each letter written before a cons, the name an inverse letter applies
    /// `back` to, and the loop a loop arm names, with the words it spells a
    /// letter of: no core node holds it, so it answers at the path type at
    /// the words' point.
    lettered: Vec<(ByteSpan, usize)>,
    /// Each node of a point `here` names when it is the empty word, with the
    /// words at that point: no core node holds it, so it answers at the
    /// words' family.
    pointed: Vec<(ByteSpan, usize)>,
    /// The position each described family's decoded signature takes, by its
    /// slot: a family the native data reading does not own.
    described: BTreeMap<SlotIndex, DataIndex>,
    /// The data declarations' signatures, by [`DataIndex`].
    data: Vec<Arc<DataSignature>>,
    /// The names of each data declaration's constructors in tag order, by
    /// [`DataIndex`].
    constructors: Vec<Vec<String>>,
    /// Each recursive function's own name, by the frame that binds it.
    recursions: BTreeMap<ScopeId, native::Recursion>,
    /// Each recursive function's parameter, by the frame it binds: the
    /// function and the parameter's position, which a match on it stages.
    staged_parameters: BTreeMap<ScopeId, native::Scrutiny>,
    /// Each `run` binder written with no type, by the frame it binds: the
    /// frame its computation reads under and the computation, whose callee's
    /// written result states the binder's type to a match on it.
    ran: BTreeMap<ScopeId, (Frame, Placed)>,
    /// Each node under an arm of a match on a recursive function's
    /// parameter: the innermost such match's function and position.
    scrutinised: BTreeMap<NodeIndex, native::Scrutiny>,
    /// Each recursive call, by its head: the instantiation whose claim checks
    /// it.
    descents: BTreeMap<NodeIndex, native::Descent>,
    /// Each recursive call through a joint fixpoint, by its head: the summand
    /// of the member it calls, which injects its argument.
    injected: BTreeMap<NodeIndex, Summand>,
    /// The reading of the form being classified, or unread between forms: a
    /// value a type reads is filed in [`Self::type_read`].
    reader: Reading,
    /// Every position read as a value by a type — a type-position call's
    /// argument, and its own operands in turn — whose quote stays in the
    /// enclosing type's telescope rather than carried into a term's context.
    type_read: BTreeSet<NodeIndex>,
    /// Each head of a call of no arguments, beside the call: such a call is
    /// its head's force, so the force carries the call's origin.
    nullary: BTreeMap<NodeIndex, NodeIndex>,
    /// Each callable operation's minted type and body, by slot.
    operated: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// Each `theory` block's definition, `S : Theory`, as its minted type and
    /// value, by slot.
    presented: BTreeMap<SlotIndex, (ValueTypeId, ValueId)>,
    /// The frame of every capability a capability scope binds.
    capabilities: BTreeSet<ScopeId>,
    /// The region each capability type written at a scope lives in, by the
    /// capability type's node.
    regions: BTreeMap<NodeIndex, gandr_core_term::effect::capability::RegionDepth>,
    /// Each application's renaming, in source order, or the refusal of the
    /// argument type it could not read: built during the mint sweep, before
    /// the first type written after the application mints.
    renamings: Vec<Result<Renaming, LoweringRefusal<'source>>>,
    /// Each manifest type an instance exports, by its application and the
    /// template's type: that type, renamed by the application.
    instance_types: BTreeMap<(InstanceIndex, NodeIndex), ValueTypeId>,
    /// Each slot of an application — a witness or an image of its functor's
    /// body — with the declaration it amounts to.
    instantiated: BTreeMap<SlotIndex, DeclarationOutcome<'source>>,
    /// The frame of every continuation an operation clause binds.
    resumptions: BTreeSet<ScopeId>,
    /// Every described family decoded so far, by its description's name: a
    /// later description, in its own source or one importing it, reads it.
    described_types:
        BTreeMap<gandr_theory_levitation::Name, gandr_core_term::description::TypeBinding>,
    /// Each node's source: the source its top-level form starts in.
    source_of: Vec<SourceIndex>,
    /// The source the passes are lowering, and where its share of each list
    /// they read begins.
    current: Current,
    /// The current source's own positions, in level order.
    own: Vec<NodeIndex>,
}

/// The source a lowering is at, and where its share of each list the passes
/// read begins. A unit is lowered a source at a time, in its order, each
/// source's collection and every pass over it before the
/// next source's, so what a source lowers to does not depend on the sources
/// after it.
///
/// # Specification
/// - ensures: each mark is the length its list had when the source's collection
///   began.
/// - executable: none — the marks are positions into lists this record does not
///   hold.
///
/// # Adequacy
/// - hypothesis: L3 — a source lowers to the same declarations and the same
///   leading arena rows whether or not another source follows it.
/// - witness: `tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
#[derive(Clone, Copy, Debug, Default)]
struct Current
{
    /// The source.
    source: SourceIndex,
    /// Where its slots begin.
    slots: usize,
    /// Where its modules begin.
    structures: usize,
    /// Where its data declarations begin.
    data: usize,
    /// Where its words begin.
    words: usize,
    /// Where its family members begin.
    families: usize,
    /// Where its functors begin.
    functors: usize,
    /// Where its functor applications begin.
    instances: usize,
    /// Where its mutual blocks begin.
    blocks: usize,
    /// Where its decorated modules begin.
    decorated: usize,
    /// Where its signature scopes begin.
    scopes: usize,
    /// Where its synthesised sites begin.
    synthesised: usize,
    /// Where its labels begin.
    labels: usize,
    /// Where its letters begin.
    lettered: usize,
    /// Where its empty words' points begin.
    pointed: usize,
}

/// Whether a node or a slot belongs to the source being lowered.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Ours(bool);

/// Each node's source: a top-level node's is the source its span starts in,
/// and every other node's is its parent's.
///
/// # Specification
/// - requires: `unit` lays out the text `tree` was parsed from.
/// - ensures: one source per node; the root and every node under a top-level
///   form hold that form's source, the root the first.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a two-source unit's nodes split at the second source's
///   first form.
/// - witness: `tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
#[spec(ensures: |ret| ret.len() == usize::from(tree.node_count()))]
fn sources_of(
    tree: &SyntaxTree<'_>,
    unit: &Unit,
) -> Vec<SourceIndex>
{
    let mut of = Vec::new();
    of.resize(usize::from(tree.node_count()), SourceIndex::default());
    let root = tree.root();
    for position in tree.positions() {
        let own = of.get(usize::from(position)).copied().unwrap_or_default();
        for child in tree.children(position) {
            let source = if position == root {
                tree.node(child)
                    .map_or(own, |node| unit.source_at(node.span().start()))
            }
            else {
                own
            };
            if let Some(held) = of.get_mut(usize::from(child)) {
                *held = source;
            }
        }
    }

    of
}

/// The positions `source_of` gives to `source`, in level order.
///
/// # Specification
/// - ensures: exactly the positions whose source is `source`, ascending.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`sources_of`].
/// - witness: `tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
#[spec(ensures: |ret| ret.is_sorted() && ret.iter().all(|&position| source_of.get(usize::from(position)) == Some(&source)))]
fn own_positions(
    source_of: &[SourceIndex],
    source: SourceIndex,
) -> Vec<NodeIndex>
{
    source_of
        .iter()
        .enumerate()
        .filter(|&(_, &held)| held == source)
        .map(|(position, _)| NodeIndex::from(position))
        .collect()
}

/// Where the mint sweep writes: the arena and the origin table, with the
/// computations the commuting of early exits reads.
///
/// # Specification
/// - requires: The arena and origin table belong to the current minting run;
///   pre-existing arena nodes need not have entries in the new table.
/// - ensures: Minting operations pair newly allocated nodes with written or
///   inserted origins rather than treating an identifier as proof of ownership.
/// - provides: The shared targets of core allocation and provenance recording.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — Allocation history is not a property of the pair of
///   references; value, computation, atom and bridge specify each recording
///   operation.
///
/// # Adequacy
/// - hypothesis: L3 — authored nodes, inserted force and derived function
///   thunks retain distinct provenance on the listed source forms.
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::exits::tests::an_exit_under_nesting_leaves_its_function`
struct Sink<'run>
{
    /// The arena the core nodes are minted into.
    arena: &'run mut CoreArena,
    /// The table every minted node's origin is recorded in.
    origins: &'run mut OriginTable,
    /// Every computation an exit minted, and each copy a match leaf made of
    /// one.
    exits: BTreeSet<ComputationId>,
    /// Every bind whose rest is distributed to its computation's local ends,
    /// and each copy a match leaf made of one, with its statement's origin.
    distributed: BTreeMap<ComputationId, Origin>,
    /// The host's interfaces, once a capability form has minted them.
    host: capability::Host,
    /// Every fixpoint a loop minted, and each copy a match leaf made of one:
    /// the commuting walks into its body.
    loops: BTreeSet<ComputationId>,
    /// Every returner a `break` minted, and each copy a match leaf made of
    /// one: a local end of its loop's position rather than of its body.
    breaks: BTreeSet<ComputationId>,
    /// Every derived operation's transport, with the path type it returns an
    /// element of: what an operation over it reads where no type is answered.
    identities: BTreeMap<ComputationId, identity::Identity>,
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
    usize::from(module.origins().declaration_count()) == module.declarations().len()
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
    lower_unit(pbg, tree, &Unit::single(), arena, budget, outermost)
}

/// Lower the sources `unit` lays end to end in `tree` into `arena`, declaring
/// their names over `outermost`.
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
///   lambda, parameter and `run` binder is reported against it; the outermost
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
///   attribute block decorating nothing;
///   [`LoweringRefusal::DuplicateImportAlias`] when two imports bind one alias;
///   [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold; and
///   [`LoweringRefusal::BudgetExceeded`] when the work outruns `budget`. A
///   refusal inside a declaration is carried by that declaration instead —
///   [`LoweringRefusal::ShadowedBuiltin`], a declared name or a binder over a
///   builtin under the reject policy, included — so one bad declaration does
///   not hide the rest of the module.
/// - panics: none. Every tree lookup is checked and a position the tree does
///   not hold contributes nothing.
///
/// # Errors
/// [`LoweringRefusal::GrammarMismatch`] for a tree of another grammar,
/// [`LoweringRefusal::OutOfFragment`], [`LoweringRefusal::MalformedForm`] and
/// [`LoweringRefusal::DuplicateImportAlias`] for a module whose own shape is
/// not a list of declarations and well-formed imports,
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
/// - witness: `lower::tests::a_computation_codomain_of_a_static_pi_is_refused`
/// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
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
                        == module.declarations().len()
                    && module.declarations().windows(2).all(|pair| match *pair {
                        | [ref left, ref right] => left.constant() < right.constant(),
                        | _ => false,
                    })
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
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    if tree.grammar() != pbg.fingerprint() {
        return Err(LoweringRefusal::GrammarMismatch {
            tree: tree.grammar(),
            grammar: pbg.fingerprint(),
        });
    }
    let empty = |outermost| {
        LoweredModule::new(
            Vec::new(),
            Vec::new(),
            Vec::new(),
            AttributeTable::new(),
            OriginTable::new(),
            ModuleImports::new(),
            outermost,
        )
    };
    let Some(root) = tree.node(tree.root())
    else {
        return Ok(empty(outermost));
    };
    match shape_of(pbg, root)? {
        Shape::Root => {},
        Shape::Layout => return Ok(empty(outermost)),
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
    let fuel = Fuel::new(budget);
    let collected = begin_collection(pbg, tree, unit)?;
    let pieces = root_pieces(pbg, tree)?;
    let mut lowerer = Lowerer::new(pbg, tree, collected, fuel, outermost);
    let mut origins = OriginTable::new();
    let mut sink = Sink {
        arena,
        origins: &mut origins,
        exits: BTreeSet::new(),
        distributed: BTreeMap::new(),
        host: capability::Host::Unminted,
        loops: BTreeSet::new(),
        breaks: BTreeSet::new(),
        identities: BTreeMap::new(),
    };
    for (source, own) in source_pieces(unit, pieces).into_iter().enumerate() {
        lowerer.begin_source(SourceIndex::from(source), own)?;
        lowerer.refuse_imports();
        lowerer.declare();
        lowerer.seed()?;
        lowerer.survey()?;
        lowerer.classify()?;
        lowerer.refuse_unsynthesised()?;
        lowerer.propagate_manifests();
        while lowerer.refuse_unrepresented().0 {
            lowerer.propagate_manifests();
        }
        lowerer.mint(&mut sink)?;
        lowerer.mint_joints(&mut sink);
        lowerer.mint_abstracts(&mut sink);
        lowerer.mint_models(&mut sink);
        lowerer.check_families(&mut sink);
        lowerer.mint_data(&mut sink);
        lowerer.mint_descriptions(&mut sink)?;
        lowerer.mint_presentations(&mut sink)?;
        lowerer.mint_operations(&mut sink);
        lowerer.mint_instances(&mut sink);
    }
    let mut attributes = AttributeTable::new();
    lowerer.attribute(&mut attributes, sink.arena)?;
    let documentation = lowerer.document()?;
    let inferred = lowerer.inferred_exits();
    let nested = lowerer.nested_sites(&origins);
    let declarations = lowerer.assemble(&mut origins);
    let structures = lowerer.structures();
    let in_scope = lowerer.in_scope();
    let Lowerer {
        collected,
        recognition,
        data,
        constructors,
        ..
    } = lowerer;

    Ok(LoweredModule::new(
        declarations,
        data,
        structures,
        attributes,
        origins,
        collected.imports,
        recognition,
    )
    .with_descriptions(
        crate::description::DescriptionReport {
            declarations: collected.descriptions.into_values().collect(),
            diagnostics: collected.description_diagnostics,
            natives: collected.natives,
        },
        collected.cells,
    )
    .with_documentation(documentation)
    .with_constructors(constructors)
    .with_inferred_exits(inferred)
    .with_nested_sites(nested)
    .with_in_scope(in_scope))
}

impl<'run, 'source> Lowerer<'run, 'source>
{
    /// The state for lowering `tree`, everything unread.
    ///
    /// # Specification
    /// - requires: the collected names and ownership positions describe this
    ///   tree.
    /// - ensures: one unread, unplanned, unminted, unbridged and unscoped cell
    ///   is allocated per syntax node; scratch stores and export indexes start
    ///   empty.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty working state is consumed by paired
    ///   declarations, nested modules and attributed refusals without leaking
    ///   prior node state.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `tests::modules::deeply_nested_modules_lower_and_resolve_at_every_depth`
    #[spec(
        ensures: |ret| {
            let count = usize::from(tree.node_count());
            ret.readings.len() == count
                && ret
                    .readings
                    .iter()
                    .all(|reading| matches!(*reading, Reading::Unread))
                && ret.plans.len() == count
                && ret
                    .plans
                    .iter()
                    .all(|plan| matches!(*plan, Plan::Unplanned))
                && ret.bridges.len() == count
                && ret.bridges.iter().all(|bridge| *bridge == Bridge::Bare)
                && ret.lowered.len() == count
                && ret
                    .lowered
                    .iter()
                    .all(|node| matches!(*node, Maybe::Absent(lowered::Absent::Unminted)))
                && ret.payload.len() == count
                && ret.payload.iter().all(|flag| !flag.0)
                && ret.scopes.len() == count
                && ret
                    .scopes
                    .iter()
                    .all(|scope| matches!(*scope, Maybe::Absent(_)))
                && ret.manifests.is_empty()
                && ret.exported.is_empty()
                && ret.witnessed.is_empty()
                && ret.operands.is_empty()
                && ret.statements.is_empty()
                && ret.parameters.is_empty()
                && ret.classifiers.is_empty()
                && ret.thunked.is_empty()
                && ret.inherited.is_empty()
                && ret.answers.is_empty()
                && ret.in_type.is_empty()
                && ret.at_endpoint.is_empty()
                && ret.cases.is_empty()
                && ret.signatures.is_empty()
                && ret.data.is_empty()
                && ret.fuel == fuel
        },
    )]
    fn new(
        pbg: &'run Pbg,
        tree: &'run SyntaxTree<'source>,
        collected: Collected<'source>,
        fuel: Fuel,
        recognition: Recognition,
    ) -> Self
    {
        let count = usize::from(tree.node_count());
        let mut readings = Vec::new();
        readings.resize(count, Reading::Unread);
        let mut plans = Vec::new();
        plans.resize(count, Plan::Unplanned);
        let mut taken = Vec::new();
        taken.resize(count, false);
        let mut bridges = Vec::new();
        bridges.resize(count, Bridge::Bare);
        let mut lowered = Vec::new();
        lowered.resize(count, Maybe::Absent(lowered::Absent::Unminted));
        let mut payload = Vec::new();
        payload.resize(count, InPayload(false));
        let mut scopes = Vec::new();
        scopes.resize(count, Maybe::Absent(scoped::Absent::Unscoped));
        let mut leaves = Vec::new();
        leaves.resize(count, exits::Leaves::Never);
        let source_of = sources_of(tree, &collected.unit);
        let own = own_positions(&source_of, SourceIndex::default());

        Self {
            pbg,
            tree,
            collected,
            readings,
            plans,
            taken,
            bridges,
            lowered,
            payload,
            scopes,
            manifests: Vec::new(),
            exported: BTreeMap::new(),
            exported_types: BTreeMap::new(),
            witnessed: BTreeMap::new(),
            sealings: BTreeMap::new(),
            kind_checks: BTreeMap::new(),
            modelled: BTreeMap::new(),
            faults: BTreeMap::new(),
            operands: Vec::new(),
            statements: Vec::new(),
            parameters: Vec::new(),
            scope: Scope::new(),
            recognition,
            fuel,
            pieces: Pieces::new(),
            scratch: Pieces::new(),
            classifiers: BTreeMap::new(),
            argued: BTreeMap::new(),
            awaiting: BTreeSet::new(),
            thunked: BTreeMap::new(),
            inherited: BTreeMap::new(),
            labels: Vec::new(),
            stand_ins: BTreeSet::new(),
            answers: BTreeMap::new(),
            synthesised: Vec::new(),
            in_type: BTreeSet::new(),
            in_quote: BTreeSet::new(),
            at_endpoint: BTreeSet::new(),
            leaves,
            exits: BTreeSet::new(),
            exitable: BTreeSet::new(),
            joined: BTreeSet::new(),
            leaving: BTreeSet::new(),
            iterated: BTreeSet::new(),
            looping: BTreeSet::new(),
            breaking: BTreeSet::new(),
            reentered: BTreeMap::new(),
            tested: BTreeSet::new(),
            results: BTreeSet::new(),
            framed: BTreeSet::new(),
            looped_past: BTreeSet::new(),
            bodies: BTreeMap::new(),
            crossing: BTreeSet::new(),
            delimited: BTreeSet::new(),
            inferred: BTreeSet::new(),
            elided: Vec::new(),
            asked: BTreeSet::new(),
            asked_runs: BTreeMap::new(),
            leading: BTreeSet::new(),
            stated: BTreeMap::new(),
            cases: Vec::new(),
            signatures: BTreeMap::new(),
            worded: BTreeMap::new(),
            word_types: BTreeMap::new(),
            looped: BTreeMap::new(),
            lettered: Vec::new(),
            pointed: Vec::new(),
            described: BTreeMap::new(),
            data: Vec::new(),
            constructors: Vec::new(),
            recursions: BTreeMap::new(),
            staged_parameters: BTreeMap::new(),
            ran: BTreeMap::new(),
            scrutinised: BTreeMap::new(),
            descents: BTreeMap::new(),
            injected: BTreeMap::new(),
            reader: Reading::Unread,
            type_read: BTreeSet::new(),
            nullary: BTreeMap::new(),
            operated: BTreeMap::new(),
            presented: BTreeMap::new(),
            renamings: Vec::new(),
            instance_types: BTreeMap::new(),
            instantiated: BTreeMap::new(),
            capabilities: BTreeSet::new(),
            regions: BTreeMap::new(),
            resumptions: BTreeSet::new(),
            described_types: BTreeMap::new(),
            source_of,
            current: Current::default(),
            own,
        }
    }

    /// Begin lowering `source`: mark where its share of each list begins and
    /// collect its top-level forms `pieces`.
    ///
    /// # Specification
    /// - requires: every source before `source` is lowered, and `pieces` are
    ///   `source`'s root pieces.
    /// - ensures: the current source is `source`, with its own positions and
    ///   each mark at the length its list had before the collection; the
    ///   source's forms are collected after the earlier sources'.
    /// - provides: the start of each source's lowering.
    /// - fails: as [`collect_source`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`collect_source`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source lowers to the same declarations and the same
    ///   leading arena rows whether or not another source follows it.
    /// - witness: `tests::namespace::a_source_lowers_alike_whatever_follows_it_776`
    #[spec(ensures: |_| self.current.source == source && self.current.slots <= self.collected.slots.len())]
    fn begin_source(
        &mut self,
        source: SourceIndex,
        pieces: Vec<Piece>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        self.own = own_positions(&self.source_of, source);
        self.current = Current {
            source,
            slots: self.collected.slots.len(),
            structures: self.collected.structures.len(),
            data: self.collected.data.len(),
            words: self.collected.words.len(),
            families: self.collected.families.len(),
            functors: self.collected.functors.len(),
            instances: self.collected.instances.len(),
            blocks: self.collected.blocks.len(),
            decorated: self.collected.decorated.len(),
            scopes: self.collected.scopes.len(),
            synthesised: self.synthesised.len(),
            labels: self.labels.len(),
            lettered: self.lettered.len(),
            pointed: self.pointed.len(),
        };
        collect_source(
            (self.pbg, self.tree),
            &mut self.collected,
            &mut self.fuel,
            pieces,
        )
    }

    /// Whether `slot` was admitted while lowering the current source.
    ///
    /// # Specification
    /// trivial.
    fn owns_slot(
        &self,
        slot: SlotIndex,
    ) -> Ours
    {
        Ours(usize::from(slot) >= self.current.slots)
    }

    /// Refuse what a source's imports forbid: every declaration of a source
    /// with an import that resolved to no source, or that is an edge of a
    /// cycle, and every top-level declaration or constructor of a source that
    /// an unqualified import binds again.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: each slot whose name stands in a source with a path import
    ///   resolved to [`ImportTarget::Unresolved`] or [`ImportTarget::Cycle`]
    ///   holds [`LoweringRefusal::ImportUnresolved`] or
    ///   [`LoweringRefusal::ImportCycle`] at its declaration form, naming the
    ///   import; each top-level declared name, and each family whose
    ///   constructor, a source unqualified-imports from another holds
    ///   [`LoweringRefusal::ImportShadows`] at its name, naming the import and
    ///   the imported declaration. The import itself, and every source without
    ///   such an import, is untouched.
    /// - provides: the per-declaration refusal the corpus pins an import's
    ///   failure by.
    /// - fails: never; a refusal is carried by its declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unresolved import, a cycle and a shadowing
    ///   declaration each refuse the importer's declarations by name, in the
    ///   corpus's pathological twins.
    /// - witness: `tests::namespace::an_unresolved_import_refuses_its_source`
    /// - witness: `tests::namespace::a_declaration_an_import_binds_again_is_refused`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: self.collected.slots.len() == before,
    )]
    fn refuse_imports(&mut self)
    {
        let collected = &self.collected;
        let named_at = |slot: SlotIndex| {
            collected
                .slots
                .get(usize::from(slot))
                .map(|found| found.named.span)
        };
        let mut refusals: Vec<(SlotIndex, LoweringRefusal<'source>)> = Vec::new();
        for import in collected.imports.declarations() {
            let source = import.source();
            if source != self.current.source {
                continue;
            }
            let (ImportResolution::Path(target), span) = (import.resolution(), import.span())
            else {
                continue;
            };
            let imported = match target {
                ImportTarget::Source(imported) => imported,
                ImportTarget::Unresolved | ImportTarget::Cycle => {
                    for (index, slot) in collected.slots.iter().enumerate() {
                        if collected.unit.source_at(slot.named.span.start()) != source {
                            continue;
                        }
                        let refused = slot.named.span;
                        refusals.push((SlotIndex::from(index), match target {
                            ImportTarget::Cycle => LoweringRefusal::ImportCycle { span, refused },
                            ImportTarget::Unresolved | ImportTarget::Source(_) => {
                                LoweringRefusal::ImportUnresolved { span, refused }
                            },
                        }));
                    }
                    continue;
                },
            };
            if import.binding() != ImportBinding::Unqualified {
                continue;
            }
            let bound_in_import = |name: SurfaceName<'source>| {
                collected
                    .by_name
                    .get(&(Container::TopLevel(imported), name))
                    .copied()
                    .and_then(named_at)
                    .or_else(|| {
                        collected
                            .constructors
                            .get(&(imported, name))
                            .map(|constructor| constructor.named.span)
                    })
            };
            for (index, slot) in collected.slots.iter().enumerate() {
                if slot.container != Container::TopLevel(source) || slot.role != Role::Declared {
                    continue;
                }
                if let Some(other) = bound_in_import(slot.name) {
                    refusals.push((SlotIndex::from(index), LoweringRefusal::ImportShadows {
                        span: slot.named.span,
                        name: slot.name,
                        import: span,
                        other,
                    }));
                }
            }
            for (&(owner, name), constructor) in &collected.constructors {
                if owner != source {
                    continue;
                }
                if let Some(other) = bound_in_import(name) {
                    refusals.push((constructor.family, LoweringRefusal::ImportShadows {
                        span: constructor.named.span,
                        name,
                        import: span,
                        other,
                    }));
                }
            }
        }
        for (index, refusal) in refusals {
            if let Some(slot) = self.collected.slots.get_mut(usize::from(index)) {
                slot.refuse(slot.introduced_by.node, refusal);
            }
        }
    }

    /// Declare every top-level name over the outermost scope: each top-level
    /// declaration, then each top-level module with the namespace it exports.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: each top-level declaration is declared as a definition, and
    ///   each top-level module as a namespace governing exactly the components
    ///   it exports — a value component as a component, a type component as a
    ///   type, a nested module as a namespace of its own, walked by an explicit
    ///   worklist — each tagged with its name tile's bytes and displacing the
    ///   builtin subtree it lands on; every exported value component's full
    ///   path is recorded with the slot a reference reads — the member, or the
    ///   witness an opaque ascription exports in its place — and every exported
    ///   type component's with what it reads. A declaration the shadow policy
    ///   refuses holds [`LoweringRefusal::ShadowedBuiltin`] at its name,
    ///   offered at its declaration form, and a module so refused files a held
    ///   slot carrying it; the scope keeps the builtin. Module members and
    ///   hidden members are declared nowhere in the outermost scope.
    /// - provides: the outermost half of the module's names, and the governance
    ///   of every module path.
    /// - fails: never; a refusal is carried by its declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration over a builtin under each policy and
    ///   over nothing, asserted as the exact record, outcome and resolution; a
    ///   module exporting a component, hiding a member and exporting a nested
    ///   module, each path asserted as the exact resolution. Every exported
    ///   member is checked here once, after the last module, rather than by
    ///   each module's declaration. A module's member, whatever its name,
    ///   shadows no builtin.
    /// - witness: `tests::recognition::a_shadowed_builtin_is_reported_as_a_warning`
    /// - witness: `tests::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
    /// - witness: `tests::recognition::user_shadowing_is_the_only_observable_delta`
    /// - witness: `tests::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `tests::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
    /// - witness: `tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every slot and every module's exports; the check reads each appended slot and each exported member once"
        )
    )]
    #[spec(
        captures: before = (self.collected.slots.len(), self.collected.structures.len()),
        ensures: |_| {
            self.collected.structures.len() == before.1
                && self.collected.slots.len() >= before.0
                && self.collected.slots.iter().enumerate().skip(before.0).all(
                    |(index, slot)| {
                        slot.role == Role::Held
                            && matches!(slot.container, Container::TopLevel(_))
                            && usize::from(slot.constant) == index
                            && matches!(
                                slot.refusal,
                                Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. }))
                            )
                    },
                )
                && self.exported.values().all(|slot| {
                    self.collected
                        .slots
                        .get(usize::from(*slot))
                        .is_some_and(|entry| matches!(entry.role, Role::Declared | Role::Witness))
                })
        },
    )]
    fn declare(&mut self)
    {
        let (first_slot, first_structure) = (self.current.slots, self.current.structures);
        for slot in self.collected.slots.iter_mut().skip(first_slot) {
            if !matches!(slot.container, Container::TopLevel(_)) || slot.role != Role::Declared {
                continue;
            }
            let site = slot.named.span;
            let mut subtree = Trie::empty();
            let _fresh = subtree.insert(
                &NamePath::root(),
                Binding::new(Recognized::Definition, RecognitionSite::Source(site)),
            );
            let declared =
                self.recognition
                    .declare(Segment::from(slot.name.as_ref()), subtree, site);
            if let Err(_refused) = declared {
                slot.refuse(slot.introduced_by.node, LoweringRefusal::ShadowedBuiltin {
                    span: site,
                    name: slot.name,
                });
            }
        }
        let mut tops: Vec<StructureIndex> = Vec::new();
        let mut shadowing: Vec<StructureIndex> = Vec::new();
        for (position, structure) in self
            .collected
            .structures
            .iter()
            .enumerate()
            .skip(first_structure)
        {
            if !matches!(structure.container, Container::TopLevel(_)) {
                continue;
            }
            match structure.stratum {
                Stratum::Module | Stratum::Instance(_) => {
                    tops.push(StructureIndex::from(position));
                },
                Stratum::Functor(_) => {
                    let mut subtree = Trie::empty();
                    let _fresh = subtree.insert(
                        &NamePath::root(),
                        Binding::new(
                            Recognized::Functor,
                            RecognitionSite::Source(structure.named.span),
                        ),
                    );
                    if let Err(_refused) = self.recognition.declare(
                        Segment::from(structure.name.as_ref()),
                        subtree,
                        structure.named.span,
                    ) {
                        shadowing.push(StructureIndex::from(position));
                    }
                },
                Stratum::Parameter(_) => {},
            }
        }
        for functor in shadowing {
            self.refuse_shadowing(functor);
        }
        for top in tops {
            self.declare_module(top);
        }
    }

    /// Declare the top-level module at `top` with the namespace it exports.
    ///
    /// # Specification
    /// - requires: `top` names a closed top-level module.
    /// - ensures: as [`Self::declare`] for one module.
    /// - provides: the per-module half of [`Self::declare`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — only exported value and type paths enter the module
    ///   namespace, while a hidden member stays absent and nested namespaces
    ///   govern their own paths. The predicate reads only the slot this call
    ///   may append; [`Self::declare`] checks every exported member once, after
    ///   the last module.
    /// - witness: `tests::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `tests::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
    /// - witness: `tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    /// - witness: `tests::modules::a_signed_member_of_a_sealed_module_exports_its_witness`
    #[spec(
        captures: before = (self.exported.len(), self.exported_types.len(), self.collected.slots.len()),
        ensures: |_| {
            self.exported.len() >= before.0
                && self.exported_types.len() >= before.1
                && self.collected.slots.len() >= before.2
                && self.collected.slots.len() <= before.2.saturating_add(1)
                && self.collected.slots.get(before.2 ..).is_some_and(|appended| {
                    appended.iter().all(|slot| {
                        slot.role == Role::Held
                            && matches!(
                                slot.refusal,
                                Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. }))
                            )
                    })
                })
        },
    )]
    fn declare_module(
        &mut self,
        top: StructureIndex,
    )
    {
        let Some(module) = self.collected.structures.get(usize::from(top))
        else {
            return;
        };
        let (name, named) = (module.name, module.named);
        let root = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
        let mut subtree = Trie::empty();
        let _root = subtree.insert(
            &NamePath::root(),
            Binding::new(
                Recognized::ModuleNamespace,
                RecognitionSite::Source(named.span),
            ),
        );
        let mut work = Vec::from([(top, NamePath::root())]);
        while let Some((structure, relative)) = work.pop() {
            let Some(entry) = self.collected.structures.get(usize::from(structure))
            else {
                continue;
            };
            for stated in entry.exported_types() {
                let Some(site) = self
                    .collected
                    .slots
                    .get(usize::from(stated.held))
                    .map(|held| held.named.span)
                else {
                    continue;
                };
                let path = relative.extended(&NamePath::from(Vec::from([Segment::from(
                    stated.name.as_ref(),
                )])));
                let _fresh = subtree.insert(
                    &path,
                    Binding::new(Recognized::ModuleType, RecognitionSite::Source(site)),
                );
                let _replaced = self.exported_types.insert(root.extended(&path), *stated);
            }
            for &export in &entry.exports {
                let (segment, site, recognized) = match export {
                    Member::Slot(slot) => {
                        let Some(member) = self.collected.slots.get(usize::from(slot))
                        else {
                            continue;
                        };
                        (member.name, member.named.span, Recognized::ModuleComponent)
                    },
                    Member::Module(nested) => {
                        let Some(member) = self.collected.structures.get(usize::from(nested))
                        else {
                            continue;
                        };
                        (member.name, member.named.span, Recognized::ModuleNamespace)
                    },
                };
                let path = relative.extended(&NamePath::from(Vec::from([Segment::from(
                    segment.as_ref(),
                )])));
                let _fresh = subtree.insert(
                    &path,
                    Binding::new(recognized, RecognitionSite::Source(site)),
                );
                match export {
                    Member::Slot(slot) => {
                        let read = entry.exported_as.get(&slot).copied().unwrap_or(slot);
                        let _replaced = self.exported.insert(root.extended(&path), read);
                    },
                    Member::Module(nested) => work.push((nested, path)),
                }
            }
        }
        let declared = self
            .recognition
            .declare(Segment::from(name.as_ref()), subtree, named.span);
        if let Err(_refused) = declared {
            self.refuse_shadowing(top);
        }
    }

    /// Refuse the top-level module or functor at `top`, whose name shadows a
    /// builtin the active policy protects, on a held slot of its own.
    ///
    /// # Specification
    /// - requires: `top` names a top-level module of the collection.
    /// - ensures: one held slot at the top level, at the next admission
    ///   position, carries [`LoweringRefusal::ShadowedBuiltin`] at the module's
    ///   name; a `top` the collection does not hold appends nothing.
    /// - provides: the shadowing refusal [`Self::declare`] and
    ///   [`Self::declare_module`] share.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module and a functor named as a builtin under the
    ///   reject policy are each refused at their name.
    /// - witness: `tests::recognition::a_module_or_functor_shadowing_a_builtin_is_rejected_under_policy`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: self.collected.slots.len() <= before.saturating_add(1)
            && self.collected.slots.get(before).is_none_or(|slot| slot.role == Role::Held && matches!(slot.refusal, Maybe::Present((_, LoweringRefusal::ShadowedBuiltin { .. })))),
    )]
    fn refuse_shadowing(
        &mut self,
        top: StructureIndex,
    )
    {
        let Some(module) = self.collected.structures.get(usize::from(top))
        else {
            return;
        };
        let (name, named, declared_by) = (module.name, module.named, module.declared_by);
        let held = SlotIndex::from(self.collected.slots.len());
        let mut slot = DeclarationSlot {
            name,
            container: self.collected.top(named.span.start()),
            role: Role::Held,
            constant: ConstantIndex::from(usize::from(held)),
            introduced_by: declared_by,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Absent(declaration_half::Absent::Unwritten),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        };
        slot.refuse(declared_by.node, LoweringRefusal::ShadowedBuiltin {
            span: named.span,
            name,
        });
        self.collected.slots.push(slot);
    }

    /// Report the binder `binder`, spelling `name`, against the outermost
    /// scope.
    ///
    /// # Specification
    /// - requires: `binder` is a lambda, parameter or `run` binder.
    /// - ensures: a binder over a builtin root is recorded under
    ///   warn-and-allow; the outermost scope is never changed.
    /// - provides: the binder half of the outermost report.
    /// - fails: [`LoweringRefusal::ShadowedBuiltin`] at the binder for a
    ///   builtin root under the reject policy.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ShadowedBuiltin`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda binder over a builtin under each policy,
    ///   asserted as the exact record and outcome.
    /// - witness: `tests::recognition::a_binder_shadowing_a_builtin_is_rejected_under_policy`
    #[spec(
        ensures: |ret| {
            ret == Ok(())
                || ret
                    == Err(LoweringRefusal::ShadowedBuiltin {
                        span: binder.span,
                        name,
                    })
        },
    )]
    fn note_binder(
        &mut self,
        binder: Placed,
        name: SurfaceName<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let noted = self
            .recognition
            .note_binder(Segment::from(name.as_ref()), binder.span);
        match noted {
            Ok(()) => Ok(()),
            Err(_refused) => Err(LoweringRefusal::ShadowedBuiltin {
                span: binder.span,
                name,
            }),
        }
    }

    /// Read every declaration's operands at the sort the declaration demands.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: a signature's type is read as a value type, a definition's
    ///   body as a value in the outermost frame, a function tail's declaration
    ///   form as a function, which reads both halves it wrote at once, a
    ///   manifest type component's and a type member's type and an abstract
    ///   component's written kind as value types, a data declaration's
    ///   parameter types, universe and field types as value types under the
    ///   parameters before them, and an attribute's payload, a declaration's or
    ///   a decorated module's, as a value when its form can stand as one and
    ///   its schema is not a word schema, whose payload is read as written; a
    ///   witness's body, a member rather than a form, is read nowhere. Every
    ///   other node stays unread. Every written payload is marked as one,
    ///   whatever its form, and every signature type's root with the type
    ///   components it sees. A definition both of whose halves are written is
    ///   signed as [`Self::sign_definitions`] signs it.
    /// - provides: the entry points of the ascending sweep.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a payload of a mold the
    ///   grammar does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] for a foreign mold.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signatures and definitions seed different readings;
    ///   manifest types and attribute payloads retain their own roots,
    ///   including attributes of refused declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body visits every slot and each of its attributes; the check reads each attribute's payload flag once"
        )
    )]
    #[spec(
        captures: before = (self.readings.len(), self.payload.len(), self.scopes.len()),
        ensures: |ret| {
            self.readings.len() == before.0
                && self.payload.len() == before.1
                && self.scopes.len() == before.2
                && (ret.is_err()
                    || self
                        .collected
                        .slots
                        .iter()
                        .flat_map(|slot| slot.attributes.iter())
                        .chain(
                            self.collected
                                .decorated
                                .iter()
                                .flat_map(|module| module.attributes.iter()),
                        )
                        .all(|attribute| match attribute.payload {
                            | Payload::Unwritten => true,
                            | Payload::Written(payload) => self
                                .payload
                                .get(usize::from(payload.node))
                                .is_none_or(|flag| flag.0),
                        }))
        },
    )]
    fn seed(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let mut seeds: Vec<(NodeIndex, Reading)> = Vec::new();
        let mut payloads: Vec<NodeIndex> = Vec::new();
        let from = self.current;
        for structure in self.collected.structures.iter().skip(from.structures) {
            for stated in structure.types.iter().chain(&structure.type_members) {
                if let TypeMeaning::Manifest(defined) = stated.meaning {
                    seeds.push((defined.node, Reading::ValueType(Frame::Outermost)));
                }
            }
        }
        for recorded in self
            .collected
            .abstracts
            .range(SlotIndex::from(from.slots) ..)
            .map(|(_, recorded)| recorded)
        {
            if let Maybe::Present(kind) = recorded.kind {
                seeds.push((kind.node, Reading::ValueType(Frame::Outermost)));
            }
        }
        for component in self
            .collected
            .functors
            .iter()
            .skip(from.functors)
            .flat_map(|functor| functor.components.iter())
        {
            if let ParameterForm::Abstract(Maybe::Present(kind)) = component.form {
                seeds.push((kind.node, Reading::ValueType(Frame::Outermost)));
            }
        }
        for &(root, seen) in self.collected.scopes.iter().skip(from.scopes) {
            if let Some(held) = self.scopes.get_mut(usize::from(root)) {
                *held = Maybe::Present(seen);
            }
        }
        for slot in self.collected.slots.iter().skip(from.slots) {
            if let Maybe::Present(half) = slot.signature
                && let Operand::Written(operand) = half.operand
            {
                seeds.push((operand.node, Reading::ValueType(Frame::Outermost)));
            }
            if let Maybe::Present(half) = slot.definition {
                match half.operand {
                    Operand::Written(operand) => {
                        seeds.push((operand.node, Reading::Value(Frame::Outermost)));
                    },
                    Operand::Function => {
                        seeds.push((half.declaration.node, Reading::Function));
                    },
                    Operand::Member(_)
                    | Operand::Data(_)
                    | Operand::Words(_)
                    | Operand::Loop { .. }
                    | Operand::Operation
                    | Operand::Signature
                    | Operand::Presented
                    | Operand::Code
                    | Operand::Model(_)
                    | Operand::World => {},
                }
            }
        }
        let written = self
            .collected
            .slots
            .iter()
            .skip(from.slots)
            .flat_map(|slot| slot.attributes.iter())
            .chain(
                self.collected
                    .decorated
                    .iter()
                    .skip(from.decorated)
                    .flat_map(|module| module.attributes.iter()),
            );
        for attribute in written {
            let Payload::Written(payload) = attribute.payload
            else {
                continue;
            };
            payloads.push(payload.node);
            let worded = matches!(
                AttributeRegistry::lookup(attribute.name),
                Maybe::Present((_, AttributeSchema::Word(_)))
            );
            let (_shape, value) = self.payload_former(payload)?;
            if value.0 && !worded {
                seeds.push((payload.node, Reading::Value(Frame::Outermost)));
            }
        }
        self.seed_data(&mut seeds);
        self.seed_families(&mut seeds);
        self.seed_descriptions(&mut seeds)?;
        self.sign_definitions()?;
        for (position, reading) in seeds {
            self.read(position, reading);
        }
        for position in payloads {
            if let Some(held) = self.payload.get_mut(usize::from(position)) {
                *held = InPayload(true);
            }
        }

        Ok(())
    }

    /// The form a payload is written as, and whether it can stand as a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a known form yields its classification and value-form
    ///   verdict; a missing node yields layout and a negative verdict.
    /// - fails: with an unknown-mold refusal when the grammar cannot classify
    ///   the node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — value and non-value payloads take distinct schema
    ///   paths while every eligible former is covered by the value-form
    ///   classification table.
    /// - witness: `lower::tests::only_the_value_forms_can_stand_as_a_payload`
    /// - witness: `lower::tests::a_non_value_payload_is_refused`
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    #[spec(
        ensures: |ret| {
            ret == self.tree.node(payload.node).map_or(
                Ok((Shape::Layout, ValueForm(false))),
                |node| {
                    shape_of(self.pbg, node).map(|shape| {
                        (shape, match shape {
                            | Shape::Form { former, .. } => is_value_form(former),
                            | Shape::Root | Shape::Repair(_) | Shape::Layout => ValueForm(false),
                        })
                    })
                },
            )
        },
    )]
    fn payload_former(
        &self,
        payload: Placed,
    ) -> Result<(Shape, ValueForm), LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(payload.node)
        else {
            return Ok((Shape::Layout, ValueForm(false)));
        };
        let shape = shape_of(self.pbg, node)?;
        let value = match shape {
            Shape::Form { former, .. } => is_value_form(former),
            Shape::Root | Shape::Repair(_) | Shape::Layout => ValueForm(false),
        };

        Ok((shape, value))
    }

    /// The ascending sweep: classify every read node and plan its mint.
    ///
    /// # Specification
    /// - requires: the seeds have been read.
    /// - ensures: every node carries the reading its parent fixed, the owner
    ///   its parent belongs to and its parent's payload mark, every read form
    ///   has its plan or has offered its refusal to the declaration that owns
    ///   it, and a node under a form that refused stays unread, so a refusal
    ///   costs its subtree nothing.
    /// - provides: everything the mint sweep needs, so the mint sweep decides
    ///   nothing and can fail at nothing.
    /// - fails: every engine fault — [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] — aborts the sweep; every other
    ///   refusal is offered to its declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declaration refusals remain local while grammar and
    ///   budget faults abort the run; classification spends at least one step
    ///   per source node and does not allocate declaration slots.
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `lower::tests::a_tree_of_another_grammar_is_refused`
    /// - witness: `lower::tests::a_module_past_the_allowance_is_refused`
    #[spec(
        captures: before = (
            self.fuel.remaining,
            self.collected.slots.len(),
            self.plans.len(),
        ),
        ensures: |ret| {
            self.collected.slots.len() == before.1
                && self.plans.len() == before.2
                && self.fuel.remaining <= before.0
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err()
                    || self.fuel.remaining
                        <= before.0.saturating_sub(self.own.len()))
        },
    )]
    fn classify(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        for index in 0 .. self.own.len() {
            let Some(&position) = self.own.get(index)
            else {
                continue;
            };
            self.fuel.spend()?;
            self.inherit_owner(position);
            self.inherit_payload(position);
            self.inherit_scope(position);
            self.inherit_type(position);
            self.inherit_scrutiny(position);
            if let Err(refusal) = self.classify_node(position) {
                if refusal.classify() == FailureClass::EngineFault {
                    return Err(refusal);
                }
                self.collected.offer(position, refusal);
            }
        }

        Ok(())
    }

    /// Give every child of `position` the match on a recursive function's
    /// parameter `position` stands under, unless a match of its own records
    /// one.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   record is set when its children are reached; a match records its arm
    ///   bodies when it is classified, after this hands its own record down.
    /// - ensures: every child of a recorded node carries a record, its own when
    ///   it had one and its parent's otherwise; a node under several such
    ///   matches carries the innermost's.
    /// - provides: the scrutiny a claim reads, however deep under its arm.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a claim nested in a call, a constructor and a
    ///   statement under an arm reads its match's record; under two nested
    ///   matches, the inner one's.
    /// - witness: `lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
    /// - witness: `lower::native::tests::claims_under_cases_on_two_parameters_are_refused_by_name`
    #[spec(
        captures: before = self.scrutinised.get(&position).copied(),
        ensures: |_| {
            self.scrutinised.get(&position).copied() == before
                && before.is_none_or(|_| self.tree.children(position).all(|child| self.scrutinised.contains_key(&child)))
        },
    )]
    fn inherit_scrutiny(
        &mut self,
        position: NodeIndex,
    )
    {
        let Some(&seen) = self.scrutinised.get(&position)
        else {
            return;
        };
        for child in self.tree.children(position) {
            let _held = self.scrutinised.entry(child).or_insert(seen);
        }
    }

    /// Give every unowned child of `position` the declaration its parent
    /// belongs to.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   owner is already set when its children are reached.
    /// - ensures: every child of an owned node is owned by the same slot,
    ///   unless the collection pass gave it an owner of its own — a signature
    ///   type written inside a member signature it does not type — so a refusal
    ///   anywhere under a declaration reaches the declaration its type or body
    ///   belongs to.
    /// - provides: the ownership half of the one-refusal-per-declaration rule.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusal and payload nodes remain owned by the correct
    ///   declaration, including payloads lowered after their declaration is
    ///   refused.
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    #[spec(
        captures: before = (
            self.collected.owner.len(),
            self.collected.owner_of(position),
        ),
        ensures: |_| {
            self.collected.owner.len() == before.0
                && self.collected.owner_of(position) == before.1
                && (!matches!(before.1, Maybe::Present(_))
                    || self
                        .tree
                        .children(position)
                        .all(|child| matches!(self.collected.owner_of(child), Maybe::Present(_))))
        },
    )]
    fn inherit_owner(
        &mut self,
        position: NodeIndex,
    )
    {
        let Maybe::Present(slot) = self.collected.owner_of(position)
        else {
            return;
        };
        for child in self.tree.children(position) {
            if let Maybe::Absent(_) = self.collected.owner_of(child) {
                self.collected.own(child, slot);
            }
        }
    }

    /// Give every child of `position` the manifest type components `position`
    /// sees.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   scope is already set when its children are reached.
    /// - ensures: every node under a signature type's root sees that root's
    ///   manifest components, an inner root keeping its own.
    /// - provides: the scope a type head inside a signature resolves against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — manifest names in later component types resolve
    ///   through the enclosing signature prefix rather than ambient source
    ///   declarations.
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    #[spec(
        captures: before = (
            self.scopes.len(),
            self.scopes.get(usize::from(position)).copied(),
        ),
        ensures: |_| {
            self.scopes.len() == before.0
                && self.scopes.get(usize::from(position)).copied() == before.1
                && (!matches!(before.1, Some(Maybe::Present(_)))
                    || self.tree.children(position).all(|child| {
                        self.scopes
                            .get(usize::from(child))
                            .is_none_or(|scope| matches!(*scope, Maybe::Present(_)))
                    }))
        },
    )]
    fn inherit_scope(
        &mut self,
        position: NodeIndex,
    )
    {
        let Some(&Maybe::Present(seen)) = self.scopes.get(usize::from(position))
        else {
            return;
        };
        for child in self.tree.children(position) {
            if let Some(held) = self.scopes.get_mut(usize::from(child))
                && let Maybe::Absent(_) = *held
            {
                *held = Maybe::Present(seen);
            }
        }
    }

    /// Mark every child of `position` as standing inside a type, inside a type
    /// a body quotes, and at an endpoint, when `position` does.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   marks are already set when its children are reached.
    /// - ensures: every node under a path type's endpoint carries both marks,
    ///   and every node under reflexivity's point the endpoint mark, before it
    ///   is classified.
    /// - provides: the context a bound name inside a type resolves in, and the
    ///   one a computation standing as a value is returned in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter named inside a compound endpoint of the
    ///   result type binds dependently and is read at its telescope index, and
    ///   a call nested in an endpoint's argument is returned.
    /// - witness: `lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    #[spec(
        captures: marked = (self.in_type.contains(&position), self.at_endpoint.contains(&position)),
        ensures: |_| {
            self.in_type.contains(&position) == marked.0
                && self.at_endpoint.contains(&position) == marked.1
                && (!marked.0 || self.tree.children(position).all(|child| self.in_type.contains(&child)))
                && (!marked.1 || self.tree.children(position).all(|child| self.at_endpoint.contains(&child)))
        },
    )]
    fn inherit_type(
        &mut self,
        position: NodeIndex,
    )
    {
        if self.in_type.contains(&position) {
            self.in_type.extend(self.tree.children(position));
        }
        if self.in_quote.contains(&position) {
            self.in_quote.extend(self.tree.children(position));
        }
        if self.at_endpoint.contains(&position) {
            self.at_endpoint.extend(self.tree.children(position));
        }
    }

    /// Mark every child of `position` as inside a payload when `position` is.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   mark is already set when its children are reached.
    /// - ensures: every node under a written payload carries the mark, so the
    ///   mint sweep can tell a payload's subtree from the rest of its
    ///   declaration.
    /// - provides: the payload half of what the mint sweep skips.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration still mints its attribute
    ///   payload without minting the refused signature or body, a compound
    ///   payload down to its leaves.
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    /// - witness: `lower::tests::a_refused_declarations_compound_payload_is_lowered_to_its_leaves`
    #[spec(
        captures: before = (self.payload.len(), self.in_payload(position)),
        ensures: |_| {
            self.payload.len() == before.0
                && self.in_payload(position) == before.1
                && (!before.1.0
                    || self.tree.children(position).all(|child| {
                        self.payload
                            .get(usize::from(child))
                            .is_none_or(|flag| flag.0)
                    }))
        },
    )]
    fn inherit_payload(
        &mut self,
        position: NodeIndex,
    )
    {
        if !self.in_payload(position).0 {
            return;
        }
        for child in self.tree.children(position) {
            if let Some(held) = self.payload.get_mut(usize::from(child)) {
                *held = InPayload(true);
            }
        }
    }

    /// Whether `position` lies inside an attribute payload.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored payload flag; an
    ///   out-of-range position is outside every payload.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refused declarations keep payload interpretation
    ///   separate from their signature and body.
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    #[spec(
        ensures: |ret| {
            ret.0
                == self
                    .payload
                    .get(usize::from(position))
                    .is_some_and(|flag| flag.0)
        },
    )]
    fn in_payload(
        &self,
        position: NodeIndex,
    ) -> InPayload
    {
        self.payload
            .get(usize::from(position))
            .copied()
            .unwrap_or(InPayload(false))
    }

    /// Classify one node at the reading its parent fixed.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order.
    /// - ensures: an unread node, an own tile, layout and repairs are skipped;
    ///   a read form is checked in the crate's one order and either planned,
    ///   with its operands read at the sorts it demands, or refused.
    /// - provides: the per-node half of [`Self::classify`].
    /// - fails: yields the form's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's first refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read form gets its own plan or a located refusal;
    ///   unread source and grammar faults are not mistaken for admitted terms.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_mold_the_grammar_does_not_hold_is_refused`
    /// - witness: `lower::tests::a_repaired_declaration_is_refused`
    #[spec(
        captures: active = self.reading(position) != Reading::Unread
            && self
                .tree
                .node(position)
                .is_some_and(|node| matches!(shape_of(self.pbg, node), Ok(Shape::Form { .. }))),
        ensures: |ret| {
            (!active
                || ret.is_err()
                || self
                    .plans
                    .get(usize::from(position))
                    .is_some_and(|plan| *plan != Plan::Unplanned))
                && (self.reading(position) != Reading::Unread || ret.is_ok())
        },
    )]
    fn classify_node(
        &mut self,
        position: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let reading = self.reading(position);
        if reading == Reading::Unread {
            return Ok(());
        }
        let Some(node) = self.tree.node(position)
        else {
            return Ok(());
        };
        let Shape::Form { name, former } = shape_of(self.pbg, node)?
        else {
            return Ok(());
        };
        let site = Site {
            at: Placed::of(position, node),
            name,
            reading,
        };
        if former == Former::Unadmitted {
            return Err(site.out(FragmentBoundary::Unadmitted));
        }
        if former == Former::Reserved {
            return Err(site.out(FragmentBoundary::Reserved));
        }
        let mut pieces = core::mem::take(&mut self.pieces);
        // A value standing inside a type reads its own operands inside it too.
        self.reader = if self.type_read.contains(&position) || self.in_type.contains(&position) {
            Reading::ValueType(reading.frame())
        }
        else {
            reading
        };
        let outcome = read_pieces(self.pbg, self.tree, position, &mut pieces)
            .and_then(|()| self.classify_form(site, former, &pieces));
        self.reader = Reading::Unread;
        self.pieces = pieces;

        outcome
    }

    /// Classify one read form over its pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the form at `site`.
    /// - ensures: a repair refuses the form; a block's last computation written
    ///   as a statement that is not an exit refuses as an unadmitted expression
    ///   statement at the statement's bytes; a former of the wrong family for
    ///   the position refuses as the wrong sort, except a type standing where a
    ///   value is read, which is quoted, and a term name or a capitalised name
    ///   standing where a type is read, which is read as the type head of that
    ///   spelling; a form where a body ends that is neither an exit nor a form
    ///   that passes the end on — a block, a match, a grouping — nor a hole
    ///   takes the exit its polarity names, recorded as inferred and leaving,
    ///   and is handed to its reader; every other former is handed to its own
    ///   reader, a declaration form to the function reader, the one reading of
    ///   the family that seeds one.
    /// - provides: the dispatch on the grammar's named kind.
    /// - fails: yields the form's first refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's first refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repairs take precedence over admission, wrong
    ///   families are refused, a type read as a value is the explicit quoting
    ///   exception, a computation read as a value is nested, and a tail of each
    ///   polarity takes its inferred exit.
    /// - witness: `lower::tests::a_repaired_declaration_is_refused`
    /// - witness: `lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    /// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    #[spec(
        captures: iterated = self.iterated.contains(&site.at.node),
        ensures: |ret| {
            if let Maybe::Present(repaired) = pieces.repair {
                ret == Err(repaired.refusal(site.name))
            }
            else if let Some(&statement) = self.stated.get(&site.at.node)
                && ending(former) != Ending::Exit
                && !iterated
            {
                ret == Err(LoweringRefusal::OutOfFragment {
                    span: statement,
                    form: FormName::EXPRESSION_STATEMENT,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Unadmitted,
                })
            }
            else if family_of(former) != site.reading.family()
                && !(family_of(former) == Family::Type && matches!(site.reading, Reading::Value(_)))
                && !(matches!(former, Former::Name | Former::Constructor) && site.reading.family() == Family::Type)
            {
                ret == Err(site.out(FragmentBoundary::WrongSort))
            }
            else if self.exits.contains(&site.at.node) && ending(former) == Ending::Inferred {
                self.inferred.contains(&site.at.node) && self.leaving.contains(&site.at.node)
                    && (ret.is_err()
                        || self
                            .plans
                            .get(usize::from(site.at.node))
                            .is_some_and(|plan| *plan != Plan::Unplanned))
            }
            else {
                ret.is_err()
                    || self
                        .plans
                        .get(usize::from(site.at.node))
                        .is_some_and(|plan| *plan != Plan::Unplanned)
            }
        },
    )]
    fn classify_form(
        &mut self,
        site: Site,
        former: Former,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(site.name));
        }
        let family = family_of(former);
        if let Some(&statement) = self.stated.get(&site.at.node)
            && ending(former) != Ending::Exit
            && !self.iterated.contains(&site.at.node)
        {
            return Err(LoweringRefusal::OutOfFragment {
                span: statement,
                form: FormName::EXPRESSION_STATEMENT,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::Unadmitted,
            });
        }
        let quoted = family == Family::Type && matches!(site.reading, Reading::Value(_));
        let headed = matches!(former, Former::Name | Former::Constructor)
            && site.reading.family() == Family::Type;
        if family != site.reading.family() && !quoted && !headed {
            return Err(site.out(FragmentBoundary::WrongSort));
        }
        if self.exits.contains(&site.at.node) && ending(former) == Ending::Inferred {
            let _tail = self.inferred.insert(site.at.node);
            let _exit = self.leaving.insert(site.at.node);
        }
        if self.iterated.contains(&site.at.node)
            && ending(former) != Ending::Exit
            && (self.stated.contains_key(&site.at.node) || iterating(former) == Ending::Inferred)
        {
            self.reenter(site)?;
        }
        let cursor = Cursor::new(&pieces.pieces, site.at.span);
        match former {
            Former::Name | Former::Constructor if headed => self.type_head(site),
            Former::Name => self.name(site),
            Former::Constructor => self.constructor(site),
            Former::Hole => {
                let identity = u32::try_from(usize::from(site.at.node)).map_err(|_overflow| {
                    LoweringRefusal::BudgetExceeded {
                        budget: self.fuel.budget,
                    }
                })?;
                let hole = gandr_core_term::hole::HoleId::from(identity);
                let plan = if matches!(site.reading, Reading::Computation(_) | Reading::Head(_)) {
                    let _frame = self.require(site, Produced::Computation)?;
                    Plan::CompHole(hole)
                }
                else {
                    let _frame = self.require(site, Produced::Value)?;
                    Plan::ValueHole(hole)
                };
                self.plan(site, plan);
                Ok(())
            },
            Former::Number => self.number(site),
            Former::Text => self.text(site, pieces),
            Former::Parenthesized => self.parenthesized(site, cursor),
            Former::Unit => {
                let _frame = self.require(site, Produced::Value)?;
                self.plan(site, Plan::Unit);
                Ok(())
            },
            Former::Thunk => self.thunk(site, cursor),
            Former::Lambda => self.lambda(site, cursor),
            Former::Block => self.sequenced(site, cursor),
            Former::Return => self.keyed(site, cursor, TileName::PURE),
            Former::Exit => self.keyed(site, cursor, TileName::RETURN),
            Former::Become => self.tail_call(site, cursor),
            Former::Loop => self.looped(site, cursor),
            Former::While => self.repeated(site, cursor),
            Former::For => Err(LoweringRefusal::ForNeedsListCase { span: site.at.span }),
            Former::Break => self.broken(site, cursor),
            Former::Continue => self.continued(site, cursor),
            Former::Force => self.keyed(site, cursor, TileName::FORCE),
            Former::Run => self.run(site, cursor),
            Former::Call => self.call(site, cursor),
            Former::Case => self.case(site, cursor),
            Former::Telescope => self.telescope(site, cursor),
            Former::Injection => self.injection(site, cursor),
            Former::LazyRecord => self.copattern(site, cursor),
            Former::Binary | Former::Unary => self.operator(site, pieces),
            Former::Projection => self.projection(site, pieces),
            Former::TypeHead => self.type_head(site),
            Former::TypePath => self.type_path(site, pieces),
            Former::Universe => self.universe(site, cursor),
            Former::TypeApplication => self.type_application(site, cursor),
            Former::ThunkType | Former::ReturnerType => self.formed_type(site, cursor),
            Former::ArrowType => self.arrow(site, cursor),
            Former::ProductType => self.chain(site, cursor, Former::ProductType),
            Former::SumType => self.chain(site, cursor, Former::SumType),
            Former::LazyProductType => self.lazy_product(site, cursor),
            Former::TelescopeType => self.telescope_type(site, cursor),
            Former::LabelledSumType => self.labelled_sum_type(site, cursor),
            Former::LazyRecordType => self.lazy_record_type(site, cursor),
            Former::ValueFunctionType => self.value_function(site, cursor),
            Former::StaticAbstraction => self.static_abstraction(site, cursor),
            Former::ParenthesizedType => self.parenthesized_type(site, cursor),
            Former::PathType => self.path_type(site, cursor),
            Former::RelationType => self.relation_type(site, cursor),
            Former::CapabilityType => self.capability_type(site, cursor),
            Former::AtType => self.at_type(site, cursor),
            Former::Scope => self.capability_scope(site, pieces),
            Former::Instantiation => self.instantiation(site, cursor),
            Former::SessionType => self.session_type(site),
            Former::Action | Former::Offer => self.session_action(site, cursor),
            Former::Access => self.access_form(site, pieces),
            Former::World => self.world_form(site, pieces),
            Former::Declaration | Former::Module => self.function(site, cursor),
            Former::AttributeBlock
            | Former::Import
            | Former::Data
            | Former::Mutual
            | Former::Reserved
            | Former::WorldDeclaration
            | Former::Unadmitted => Err(site.out(FragmentBoundary::WrongSort)),
        }
    }

    /// The binder frame of a form whose position demands `produced`, with the
    /// bridge the position writes over it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the frame the position carries when it reads the produced
    ///   sort. An application's head reads a computation and reaches a value by
    ///   a force; a function's result reads a computation type and reaches a
    ///   value type by a returner; a value position reaches a type of either
    ///   sort by a quote, and a computation as the value it returns at an
    ///   endpoint or where a type reads it, and nested everywhere else; a tail,
    ///   where a path through a body ends, reaches a value by the `return` its
    ///   polarity names, recorded as inferred and leaving; a `while` loop's
    ///   condition, and a tail of a handled subject, which is the subject's
    ///   result, reach a value by a `return` recorded as no exit; the bridge is
    ///   recorded for the form's node, and every other match records none.
    /// - provides: the sort check every former takes, and the six insertions
    ///   decided by the sort of a position.
    /// - fails: yields the wrong-sort refusal when the position reads another
    ///   sort no bridge reaches.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each bridge separated from its bare neighbour: a
    ///   value and a computation at a head, a value type and a computation type
    ///   at a result, a value and a type at a value, a computation at an
    ///   endpoint and elsewhere at a value, a value and a computation at a
    ///   tail, each asserted through the lowered node and its origin's
    ///   provenance.
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    /// - witness: `lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
    /// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    /// - witness: `lower::loops::tests::a_while_tests_its_condition_on_every_pass`
    /// - witness: `lower::capability::tests::a_return_in_a_subject_leaves_past_the_handler`
    #[spec(
        ensures: |ret| {
            let expected = match (site.reading, produced) {
                | (Reading::Value(frame), Produced::Value)
                | (Reading::Computation(frame) | Reading::Head(frame), Produced::Computation)
                | (Reading::ValueType(frame), Produced::ValueType)
                | (Reading::CompType(frame) | Reading::Result(frame), Produced::CompType) => {
                    Some((frame, Bridge::Bare))
                },
                | (Reading::Head(frame), Produced::Value) => {
                    Some((frame, Bridge::Inserted(Insertion::Force)))
                },
                | (Reading::Result(frame), Produced::ValueType) => {
                    Some((frame, Bridge::Inserted(Insertion::Returner)))
                },
                | (
                    Reading::Value(frame),
                    Produced::ValueType | Produced::CompType,
                ) => Some((frame, Bridge::Inserted(Insertion::Quote))),
                | (Reading::Value(frame), Produced::Computation)
                    if self.at_endpoint.contains(&site.at.node) || self.type_read.contains(&site.at.node) =>
                {
                    Some((frame, Bridge::Inserted(Insertion::Endpoint)))
                },
                | (Reading::Value(frame), Produced::Computation) => {
                    Some((frame, Bridge::Inserted(Insertion::Nested)))
                },
                | (Reading::Computation(frame), Produced::Value)
                    if self.tested.contains(&site.at.node) || self.results.contains(&site.at.node) =>
                {
                    Some((frame, Bridge::Inserted(Insertion::Return)))
                },
                | (Reading::Computation(frame), Produced::Value)
                    if self.exits.contains(&site.at.node) =>
                {
                    Some((frame, Bridge::Inserted(Insertion::Return)))
                },
                | _ => None,
            };
            match expected {
                | Some((frame, bridge)) => {
                    ret == Ok(frame)
                        && self
                            .bridges
                            .get(usize::from(site.at.node))
                            .is_none_or(|held| *held == bridge)
                        && (bridge != Bridge::Inserted(Insertion::Return)
                            || self.tested.contains(&site.at.node)
                            || self.results.contains(&site.at.node)
                            || (self.inferred.contains(&site.at.node)
                                && self.leaving.contains(&site.at.node)))
                },
                | None => ret == Err(site.out(FragmentBoundary::WrongSort)),
            }
        },
    )]
    fn require(
        &mut self,
        site: Site,
        produced: Produced,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let (frame, bridge) = match (site.reading, produced) {
            (Reading::Value(frame), Produced::Value)
            | (Reading::Computation(frame) | Reading::Head(frame), Produced::Computation)
            | (Reading::ValueType(frame), Produced::ValueType)
            | (Reading::CompType(frame) | Reading::Result(frame), Produced::CompType) => {
                (frame, Bridge::Bare)
            },
            (Reading::Head(frame), Produced::Value) => (frame, Bridge::Inserted(Insertion::Force)),
            (Reading::Result(frame), Produced::ValueType) => {
                (frame, Bridge::Inserted(Insertion::Returner))
            },
            (Reading::Value(frame), Produced::ValueType | Produced::CompType) => {
                (frame, Bridge::Inserted(Insertion::Quote))
            },
            (Reading::Value(frame), Produced::Computation)
                if self.at_endpoint.contains(&site.at.node)
                    || self.type_read.contains(&site.at.node) =>
            {
                (frame, Bridge::Inserted(Insertion::Endpoint))
            },
            (Reading::Value(frame), Produced::Computation) => {
                (frame, Bridge::Inserted(Insertion::Nested))
            },
            (Reading::Computation(frame), Produced::Value)
                if self.tested.contains(&site.at.node) || self.results.contains(&site.at.node) =>
            {
                (frame, Bridge::Inserted(Insertion::Return))
            },
            (Reading::Computation(frame), Produced::Value)
                if self.exits.contains(&site.at.node) =>
            {
                let _tail = self.inferred.insert(site.at.node);
                let _exit = self.leaving.insert(site.at.node);
                (frame, Bridge::Inserted(Insertion::Return))
            },
            _ => return Err(site.out(FragmentBoundary::WrongSort)),
        };
        if let Some(held) = self.bridges.get_mut(usize::from(site.at.node)) {
            *held = bridge;
        }
        // A type a term quotes, where no type reads it, is a body's: its reads
        // count in its own telescope (#547).
        if bridge == Bridge::Inserted(Insertion::Quote)
            && !self.type_read.contains(&site.at.node)
            && !self.in_type.contains(&site.at.node)
        {
            let _quote = self.in_quote.insert(site.at.node);
            self.in_quote.extend(self.tree.children(site.at.node));
        }

        Ok(frame)
    }

    /// What `name`, written at `site` under `frame`, resolves to: the
    /// innermost binder carrying it, else a declaration strictly earlier than
    /// the one `site` belongs to, another member of its mutual block, or that
    /// declaration itself when it is a data declaration, searched from that
    /// declaration's own module outward to the top level.
    ///
    /// # Specification
    /// - requires: `site` is the name's own node.
    /// - ensures: the binder with its index and its written type; else the
    ///   first module, innermost first, whose body declares the name: its
    ///   member when that member's admission position is strictly earlier, and
    ///   the forward-member refusal when it is not; else a top-level
    ///   declaration strictly earlier or another member of the mutual block
    ///   `site` belongs to, with its admission position and its signature's
    ///   written type; the data declaration `site` belongs to, untyped, for its
    ///   own name: a family's self reference, whose positivity the checker
    ///   judges; else a callable operation admitted strictly earlier, untyped;
    ///   the unresolved absence when nothing answers.
    /// - provides: the one resolution term names, capitalised names and type
    ///   heads share.
    /// - fails: [`LoweringRefusal::UnmarkedSelfReference`] for the name a
    ///   recursive function's fixpoint binds, which only a descent claim reads;
    ///   [`LoweringRefusal::ForwardMemberReference`] for a member of an
    ///   enclosing module declared at or after the referring declaration;
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnmarkedSelfReference`],
    /// [`LoweringRefusal::ForwardMemberReference`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member named by an earlier sibling, by a later one,
    ///   by itself, from a nested module and from the top level, each asserted
    ///   as the exact constant or refusal.
    /// - witness: `tests::modules::a_forward_member_reference_is_refused_by_position`
    /// - witness: `tests::modules::a_backward_member_reference_resolves`
    /// - witness: `lower::tests::a_self_reference_is_unresolved`
    /// - witness: `lower::native::tests::a_recursive_family_names_itself_in_its_fields`
    /// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
    /// - witness: `lower::native::tests::an_unmarked_self_reference_is_refused_with_its_claim`
    #[spec(
        captures: before = self.fuel.remaining,
        ensures: |ret| {
            self.fuel.remaining <= before
                && match ret {
                    | Ok(Maybe::Present(Resolved::Declaration { constant, declared })) => {
                        matches!(self.collected.owner_of(site.at.node), Maybe::Present(own) if self.collected.slots.get(usize::from(constant)).is_some_and(|entry| entry.name == name && entry.constant == constant && (usize::from(constant) < usize::from(own) || (usize::from(constant) == usize::from(own) && matches!(entry.definition, Maybe::Present(Half { operand: Operand::Data(_), .. }))) || matches!((self.collected.block_of(SlotIndex::from(usize::from(constant))), self.collected.block_of(own)), (Maybe::Present(held), Maybe::Present(holding)) if held == holding)) && declared == match entry.signature { Maybe::Present(Half { operand: Operand::Written(written), .. }) => Maybe::Present(written.node), Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(binder_type::Absent::Untyped) }))
                    },
                    | Err(
                        LoweringRefusal::ForwardMemberReference {
                            span,
                            name: refused,
                            ..
                        }
                        | LoweringRefusal::UnmarkedSelfReference {
                            span,
                            name: refused,
                        },
                    ) => span == site.at.span && refused == name,
                    | _ => true,
                }
        },
    )]
    fn resolve_name(
        &mut self,
        site: Site,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        if let Maybe::Present(bound) = self.scope.resolve(frame, name, &mut self.fuel)? {
            if self.recursions.contains_key(&bound.binder) {
                return Err(LoweringRefusal::UnmarkedSelfReference {
                    span: site.at.span,
                    name,
                });
            }
            return Ok(Maybe::Present(Resolved::Binder(bound)));
        }
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        let mut container = self.collected.slots.get(usize::from(own)).map_or_else(
            || self.collected.top(site.at.span.start()),
            |slot| slot.container,
        );
        loop {
            self.fuel.spend()?;
            if let Some(&target) = self.collected.by_name.get(&(container, name))
                && let Some(entry) = self.collected.slots.get(usize::from(target))
            {
                let own_family = target == own
                    && matches!(
                        entry.definition,
                        Maybe::Present(Half {
                            operand: Operand::Data(_),
                            ..
                        })
                    );
                // A mutual block's members name one another in any order:
                // the block is admitted as one. A member's own name is the
                // rule above's.
                let one_block = target != own
                    && matches!(
                        (self.collected.block_of(target), self.collected.block_of(own)),
                        (Maybe::Present(held), Maybe::Present(holding)) if held == holding
                    );
                if target < own || own_family || one_block {
                    let declared = match entry.signature {
                        Maybe::Present(Half {
                            operand: Operand::Written(written),
                            ..
                        }) => Maybe::Present(written.node),
                        Maybe::Present(_) | Maybe::Absent(_) => {
                            Maybe::Absent(binder_type::Absent::Untyped)
                        },
                    };
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant: entry.constant,
                        declared,
                    }));
                }
                if let Container::Module(_) = container {
                    return Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name,
                        declared: entry.named.span,
                    });
                }
            }
            let Container::Module(module) = container
            else {
                let source = self.collected.unit.source_at(site.at.span.start());
                if let Some(&target) = self.collected.operation_names.get(&(source, name))
                    && target < own
                    && let Some(entry) = self.collected.slots.get(usize::from(target))
                {
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant: entry.constant,
                        declared: Maybe::Absent(binder_type::Absent::Untyped),
                    }));
                }
                return self.imported(site, source, name);
            };
            container = self
                .collected
                .structures
                .get(usize::from(module))
                .map_or_else(
                    || self.collected.top(site.at.span.start()),
                    |structure| structure.container,
                );
        }
    }

    /// What the sources `source` imports unqualified answer `name`, used at
    /// `site`, with.
    ///
    /// # Specification
    /// - requires: `site` is the name's own node, in `source`.
    /// - ensures: the constant and written signature type of the top-level
    ///   declaration one imported source declares under `name`, or the
    ///   unresolved absence when none does.
    /// - provides: the import fallback of [`Self::resolve_name`].
    /// - fails: [`LoweringRefusal::ImportShadows`] when two imports declare the
    ///   name, naming both; [`LoweringRefusal::UnexportedName`] when the
    ///   declaration has a signature and no definition, which its source does
    ///   not export.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ImportShadows`] and
    /// [`LoweringRefusal::UnexportedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name one import answers, a name two answer and a
    ///   pending declaration, each asserted exactly.
    /// - witness: `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
    /// - witness: `tests::namespace::two_imports_binding_one_name_refuse_its_use`
    /// - witness: `tests::namespace::a_pending_declaration_is_not_exported`
    #[spec(ensures: |ref ret| match *ret {
        Ok(_) => true,
        Err(LoweringRefusal::ImportShadows { name: found, .. } | LoweringRefusal::UnexportedName { name: found, .. }) => {
            found.as_ref() == name.as_ref()
        },
        Err(_) => false,
    })]
    fn imported(
        &self,
        site: Site,
        source: SourceIndex,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        let (target, _import) = match self.collected.imported_slot(source, name) {
            Ok(Maybe::Present(found)) => found,
            Ok(Maybe::Absent(_)) => return Ok(Maybe::Absent(named::Absent::Unresolved)),
            Err(ambiguity) => {
                return Err(LoweringRefusal::ImportShadows {
                    span: site.at.span,
                    name,
                    import: ambiguity.import,
                    other: ambiguity.other,
                });
            },
        };
        self.exported(site, name, target)
    }

    /// The declaration at `target`, which another source exports under
    /// `name`, read at `site`.
    ///
    /// # Specification
    /// - requires: `target` is a top-level declaration of a source the site's
    ///   source imports.
    /// - ensures: its constant and written signature type; the unresolved
    ///   absence for a slot the collection does not hold.
    /// - fails: [`LoweringRefusal::UnexportedName`] for a declaration with a
    ///   signature and no definition.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnexportedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses of [`Self::imported`].
    /// - witness: `tests::namespace::a_pending_declaration_is_not_exported`
    #[spec(ensures: |ref ret| match *ret {
        Ok(Maybe::Present(Resolved::Declaration { constant, .. })) => self
            .collected
            .slots
            .get(usize::from(target))
            .is_some_and(|entry| entry.constant == constant),
        Ok(Maybe::Absent(_)) => self.collected.slots.get(usize::from(target)).is_none(),
        Err(LoweringRefusal::UnexportedName { name: found, .. }) => found.as_ref() == name.as_ref(),
        Ok(Maybe::Present(_)) | Err(_) => false,
    })]
    fn exported(
        &self,
        site: Site,
        name: SurfaceName<'source>,
        target: SlotIndex,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        let Some(entry) = self.collected.slots.get(usize::from(target))
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        if let Maybe::Absent(_) = entry.definition {
            return Err(LoweringRefusal::UnexportedName {
                span: site.at.span,
                name,
                declared: entry.named.span,
            });
        }
        let declared = match entry.signature {
            Maybe::Present(Half {
                operand: Operand::Written(written),
                ..
            }) => Maybe::Present(written.node),
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(binder_type::Absent::Untyped),
        };

        Ok(Maybe::Present(Resolved::Declaration {
            constant: entry.constant,
            declared,
        }))
    }

    /// What `alias.selected`, written at `site`, names when `alias` is the
    /// alias of a path import of the site's source.
    ///
    /// # Specification
    /// - requires: `alias` is the head of the one-link path at `site` and
    ///   `selected` its selected name.
    /// - ensures: the top-level declaration the imported source declares under
    ///   the selected name; the unaliased absence when `alias` is no alias of
    ///   the source or names an import of an address no source of the unit
    ///   answers. A constructor is not selected through an alias: a selected
    ///   name is lowercase, so a qualified constructor does not parse.
    /// - provides: the qualified reading of an aliased import.
    /// - fails: [`LoweringRefusal::UnknownMember`] for a name the imported
    ///   source does not declare; [`LoweringRefusal::UnexportedName`] for one
    ///   it declares without a definition.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMember`] and
    /// [`LoweringRefusal::UnexportedName`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an aliased family and value each read from the
    ///   imported source, an undeclared member refused by name, and a pending
    ///   member refused at the member.
    /// - witness: `tests::namespace::an_aliased_import_qualifies_its_source_s_names`
    /// - witness: `tests::namespace::a_pending_member_read_through_an_alias_is_refused_at_the_member`
    #[spec(ensures: |ref ret| matches!(
        *ret,
        Ok(_) | Err(LoweringRefusal::UnknownMember { .. } | LoweringRefusal::UnexportedName { .. })
    ))]
    fn aliased_member(
        &self,
        site: Site,
        alias: Placed,
        selected: Placed,
    ) -> Result<Maybe<Resolved, alias_member::Absent>, LoweringRefusal<'source>>
    {
        let source = self.collected.unit.source_at(site.at.span.start());
        let module = self.name_at(alias);
        let Maybe::Present(import) = self.collected.imports.aliased(source, module)
        else {
            return Ok(Maybe::Absent(alias_member::Absent::Unaliased));
        };
        let ImportResolution::Path(ImportTarget::Source(target)) = import.resolution()
        else {
            return Ok(Maybe::Absent(alias_member::Absent::Unaliased));
        };
        let member = self.name_at(selected);
        let unknown = LoweringRefusal::UnknownMember {
            span: selected.span,
            module,
            member,
        };
        let Some(&slot) = self
            .collected
            .by_name
            .get(&(Container::TopLevel(target), member))
        else {
            return Err(unknown);
        };
        let read = Site {
            at: selected,
            ..site
        };
        match self.exported(read, member, slot)? {
            Maybe::Present(resolved) => Ok(Maybe::Present(resolved)),
            Maybe::Absent(_) => Err(unknown),
        }
    }

    /// Classify a term name.
    ///
    /// # Specification
    /// - requires: `site` is an identifier in term position.
    /// - ensures: a name standing as a value resolves against the binder frame
    ///   first and the declarations strictly earlier than its own second, and
    ///   is planned as the variable or constant it resolved to; a binder named
    ///   inside a type is planned as [`Self::resolved_term`] plans it.
    /// - provides: the term-name half of resolution.
    /// - fails: yields the wrong-sort refusal for a name in computation
    ///   position, and the unresolved-name refusal when no scope answers;
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — local binders and earlier declarations resolve to
    ///   their own variable or constant, while an undefined name keeps its
    ///   source span.
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `lower::tests::an_undefined_term_name_is_refused`
    /// - witness: `tests::modules::a_backward_member_reference_resolves`
    /// - witness: `lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Variable(..) | Plan::Constant(_) | Plan::Primitive(_) | Plan::StaticApplication(..) | Plan::ListNil))
                )
        },
    )]
    fn name(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let name = self.name_at(site.at);
        match self.resolve_name(site, frame, name)? {
            Maybe::Present(resolved) => {
                let plan = self.resolved_term(site, frame, resolved);
                self.plan(site, plan);
                Ok(())
            },
            Maybe::Absent(_) => {
                if name.as_ref() == identity::NIL {
                    self.plan(site, Plan::ListNil);
                    return Ok(());
                }
                let path = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
                if let PathResolution::Complete(Recognized::BuiltinPrimitive {
                    primitive, ..
                }) = self.recognition.resolve_path(&path)
                {
                    self.plan(site, Plan::Primitive(primitive));
                    Ok(())
                }
                else {
                    Err(LoweringRefusal::UnresolvedName {
                        span: site.at.span,
                        name,
                    })
                }
            },
        }
    }

    /// Classify a capitalised name in term position.
    ///
    /// # Specification
    /// - requires: `site` is a constructor in term position.
    /// - ensures: a constructor of a data family declared strictly earlier
    ///   stands as that constructor applied to no fields; otherwise a data
    ///   family an earlier declaration answers stands as its type, which a
    ///   value position quotes, and any other name a binder or an earlier
    ///   declaration answers stands as the value it resolved to; otherwise a
    ///   type component or type member the name states, read as
    ///   [`Self::stated_type`] reads it, or a type atom, or `Type` for the
    ///   value universe at the fuss-free level, stands as a type, which a value
    ///   position quotes.
    /// - provides: the term-position spelling of a type, of a nullary
    ///   constructor, and of a declaration named with a capital.
    /// - fails: yields the wrong-sort refusal for a resolved name or a type
    ///   where its position reads neither; a constructor's own refusals; the
    ///   arity refusal for a family of parameters named alone; a name nothing
    ///   answers is unadmitted.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration, a type atom, the universe and an
    ///   unanswered constructor each written where a value is read, asserted as
    ///   the exact core node or refusal; an unknown constructor unadmitted.
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_data_family_named_where_a_value_is_read_is_quoted`
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `lower::tests::an_unknown_constructor_where_a_value_is_read_is_unadmitted`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(
                        &(Plan::Variable(..)
                            | Plan::StaticApplication(..)
                            | Plan::Constant(_)
                            | Plan::Atom(_)
                            | Plan::Universe(_)
                            | Plan::Constructor(_)
                            | Plan::Data(..)
                            | Plan::Transparent(_)
                            | Plan::Sealed(_)
                            | Plan::Instantiated(..))
                    )
                )
        },
    )]
    fn constructor(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let name = self.name_at(site.at);
        if let Maybe::Present(constructor) = self.constructor_named(site, name) {
            let none = Stretch {
                start: self.operands.len(),
                end: self.operands.len(),
            };
            return self.construct(site, constructor, none);
        }
        if let Maybe::Present(resolved) = self.resolve_name(site, site.reading.frame(), name)? {
            if let Resolved::Declaration { constant, .. } = resolved
                && let Maybe::Present(arity) = self.data_family(constant)
            {
                let none = Stretch {
                    start: self.operands.len(),
                    end: self.operands.len(),
                };
                return self.family(site, constant, arity, none);
            }
            let frame = self.require(site, Produced::Value)?;
            let plan = self.resolved_term(site, frame, resolved);
            self.plan(site, plan);
            return Ok(());
        }
        if let Maybe::Present(stated) = self.stated_named(site, name)? {
            return self.stated_type(site, stated);
        }
        let quoted = match type_atom(name) {
            Maybe::Present(atom) => Plan::Atom(atom),
            Maybe::Absent(_) if name.as_ref() == TileName::UNIVERSE.as_ref() => {
                Plan::Universe(Universe::FUSS_FREE)
            },
            Maybe::Absent(_) => return Err(site.out(FragmentBoundary::Unadmitted)),
        };
        let _frame = self.require(site, Produced::ValueType)?;
        self.plan(site, quoted);

        Ok(())
    }

    /// The plan a name that resolved to `resolved` stands as, read as a value
    /// at `site` under `frame`.
    ///
    /// # Specification
    /// - requires: `resolved` is what the name at `site` resolves to.
    /// - ensures: a binder named inside a type is mentioned, so the arrow that
    ///   binds it is dependent, and planned as the bare code it names, minted
    ///   at its telescope index; any other resolution is the variable or the
    ///   constant it names.
    /// - provides: the one place a term name inside a type reads the type's
    ///   telescope rather than the term context.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter named in a result type's compound
    ///   endpoint, and one named in a body, each checked.
    /// - witness: `lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    #[spec(
        ensures: |ret| match (resolved, self.in_type.contains(&site.at.node)) {
            | (Resolved::Binder(bound), true) => {
                matches!(ret, Plan::StaticApplication(Code::Bound { binder, .. }, arguments) if binder == bound.binder && arguments.start == arguments.end)
                    && (bool::from(self.scope.mentioned(bound.binder)) || self.in_quote.contains(&site.at.node))
            },
            | _ => ret == resolved.term(),
        },
    )]
    fn resolved_term(
        &mut self,
        site: Site,
        frame: Frame,
        resolved: Resolved,
    ) -> Plan
    {
        match resolved {
            Resolved::Binder(bound) if self.in_type.contains(&site.at.node) => {
                let telescope = self.name_in_type(site.at.node, bound.binder);
                let none = Stretch {
                    start: self.operands.len(),
                    end: self.operands.len(),
                };
                Plan::StaticApplication(
                    Code::Bound {
                        from: frame,
                        binder: bound.binder,
                        telescope,
                    },
                    none,
                )
            },
            Resolved::Binder(_) | Resolved::Declaration { .. } => resolved.term(),
        }
    }

    /// Record that a type position at `node` names `binder`, and answer the
    /// telescope its index counts in: a type a body quotes counts in its own,
    /// leaving the signature's arrows as they are, and any other type in the
    /// signature's, whose arrow binding `binder` becomes dependent (#547).
    ///
    /// # Specification
    /// - requires: `node` is a type position naming `binder`.
    /// - ensures: [`Telescope::Quote`] with `binder` quoted when `node` lies in
    ///   a body quote; [`Telescope::Signature`] with `binder` mentioned
    ///   otherwise.
    /// - provides: the one place a binder read inside a type chooses its
    ///   telescope.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter only a body quote names leaves its arrow
    ///   independent and the quote reads it; one a signature type names makes
    ///   it dependent.
    /// - witness: `lower::tests::a_quote_in_a_body_reads_past_an_unmentioned_parameter`
    #[spec(ensures: |ret| if self.in_quote.contains(&node) {
        ret == Telescope::Quote
    } else {
        ret == Telescope::Signature && bool::from(self.scope.mentioned(binder))
    })]
    fn name_in_type(
        &mut self,
        node: NodeIndex,
        binder: ScopeId,
    ) -> Telescope
    {
        if self.in_quote.contains(&node) {
            self.scope.quote(binder);
            Telescope::Quote
        }
        else {
            self.scope.mention(binder);
            Telescope::Signature
        }
    }

    /// Whether the type at `node`, which introduces `binder`, names it: in the
    /// telescope [`Self::name_in_type`] counted the type's reads in, so a type
    /// a body quotes depends on a binder its own reads name, and any other
    /// type on one a signature type names (#583).
    ///
    /// # Specification
    /// - requires: `node` is the type introducing `binder`, or a node inside
    ///   it; every read of the type has been recorded.
    /// - ensures: whether `binder` binds in [`Telescope::Quote`] when `node`
    ///   lies in a body quote, and in [`Telescope::Signature`] otherwise.
    /// - provides: the Π-or-arrow and Σ-or-product decision, in step with the
    ///   indices the type's reads were minted at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent arrow a body quotes, whose codomain names
    ///   its binder, is the Π over it; one whose codomain does not is the plain
    ///   arrow.
    /// - witness: `lower::tests::a_dependent_arrow_a_body_quotes_binds_what_its_codomain_names`
    #[spec(ensures: |ret| ret == self.scope.binds(binder, self.telescope_at(node)))]
    fn names_own_binder(
        &self,
        node: NodeIndex,
        binder: ScopeId,
    ) -> Mentioned
    {
        self.scope.binds(binder, self.telescope_at(node))
    }

    /// The telescope a type at `node` counts its binders in: a body quote's
    /// own when `node` lies in a body quote, the signature's otherwise (#547).
    ///
    /// # Specification
    /// - requires: the classification has reached `node`.
    /// - ensures: [`Telescope::Quote`] exactly when `node` lies in a body
    ///   quote.
    /// - provides: the one choice of telescope every reading of a type's
    ///   binders shares: its indices, its arrows' dependency (#583) and the
    ///   names it is spelled with (#590).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type a body quotes answers the quote's telescope
    ///   and a signature type the signature's: the arrow minted from each, and
    ///   the label spelled for each, tell the two apart.
    /// - witness: `lower::tests::a_dependent_arrow_a_body_quotes_binds_what_its_codomain_names`
    /// - witness: `resolve::tests::a_quoted_binder_binds_only_in_a_body_quote_s_telescope`
    #[spec(ensures: |ret| (ret == Telescope::Quote) == self.in_quote.contains(&node))]
    fn telescope_at(
        &self,
        node: NodeIndex,
    ) -> Telescope
    {
        if self.in_quote.contains(&node) {
            Telescope::Quote
        }
        else {
            Telescope::Signature
        }
    }

    /// Classify a number literal.
    ///
    /// # Specification
    /// - requires: `site` is a number.
    /// - ensures: a number standing as a value whose lexeme is decimal digits
    ///   is planned as its canonical integer.
    /// - provides: the integer half of the literal reading.
    /// - fails: yields the wrong-sort refusal outside value position; a
    ///   fraction or an exponent is a number the fragment does not admit; any
    ///   other text is a malformed literal.
    /// - panics: none.
    ///
    /// # Errors
    /// The number's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — canonical integer magnitudes, fractional syntax and
    ///   malformed lexemes separate successful literal plans from their
    ///   refusals.
    /// - witness: `lower::tests::an_integer_literal_is_its_canonical_magnitude`
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Literal(Literal::Integer(_)))
                )
        },
    )]
    fn number(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let text = self.text_at(site.at);
        if let Maybe::Present(literal) = parse_literal(Former::Number, text) {
            self.plan(site, Plan::Literal(literal));
            return Ok(());
        }
        if fractional(text).0 {
            return Err(site.out(FragmentBoundary::Unadmitted));
        }

        Err(LoweringRefusal::MalformedLiteral {
            span: site.at.span,
            form: site.name,
        })
    }

    /// Classify a string literal.
    ///
    /// # Specification
    /// - requires: `site` is a string; `pieces` is its reading.
    /// - ensures: a string standing as a value with no interpolation is planned
    ///   as its decoded text.
    /// - provides: the text half of the literal reading.
    /// - fails: yields the wrong-sort refusal outside value position; an
    ///   interpolation is a form the fragment does not admit; a string missing
    ///   a delimiter is a malformed literal.
    /// - panics: none.
    ///
    /// # Errors
    /// The string's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quoted strings decode their escapes; interpolation
    ///   and malformed text retain their distinct located refusals.
    /// - witness: `lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
    /// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_malformed_text_literal_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Literal(Literal::Text(_)))
                )
        },
    )]
    fn text(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let interpolated = pieces.pieces.iter().any(
            |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::INTERPOLATION),
        );
        if interpolated {
            return Err(site.folded(FormName::INTERPOLATION, FragmentBoundary::Unadmitted));
        }
        let Maybe::Present(literal) = parse_literal(Former::Text, self.text_at(site.at))
        else {
            return Err(LoweringRefusal::MalformedLiteral {
                span: site.at.span,
                form: site.name,
            });
        };

        self.plan(site, Plan::Literal(literal));

        Ok(())
    }

    /// Classify a parenthesised expression: a grouping, a pair or an
    /// annotation.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised expression in term position.
    /// - ensures: `(e)` reads its operand at its own reading and adopts it, the
    ///   answer its position states passed on; a comma list is read as a pair;
    ///   `(C… : T)` over a constructor standing as a value reads `T` as a value
    ///   type under the same frame, records it as the constructor's classifier
    ///   and adopts the constructor.
    /// - provides: the reading of every form the grammar folds into
    ///   parentheses.
    /// - fails: yields the pair's own refusal, the unadmitted refusal for an
    ///   annotation over anything but a constructor standing as a value, the
    ///   empty-list refusal for `()`, which is never the unit, and the
    ///   extra-operand refusal for a juxtaposition.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — grouping preserves its operand while a
    ///   comma-separated tuple plans one tuple rather than treating the commas
    ///   as grouping.
    /// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::the_empty_parentheses_are_never_the_unit`
    /// - witness: `lower::native::tests::a_parameterized_constructor_needs_its_classifier`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Transparent(_) | Plan::Tuple(_)))
                )
        },
    )]
    fn parenthesized(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let list = cursor.clone();
        let _open = cursor.tile(TileName::PAREN_OPEN);
        let run = cursor.operands();
        if let Maybe::Present(_) = cursor.at(TileName::COMMA) {
            return self.pair(site, list);
        }
        if let Maybe::Present(_) = cursor.at(TileName::COLON) {
            return self.annotated(site, run, cursor);
        }
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        if let Run::Empty(_) = run {
            let unit = Site {
                name: FormName::UNIT,
                ..site
            };
            return Err(unit.out(FragmentBoundary::EmptyList));
        }
        let inner = site.one(run)?;
        self.read(inner.node, site.reading);
        if let Some(&answer) = self.answers.get(&site.at.node) {
            let _passed = self.answers.insert(inner.node, answer);
        }
        if let Some(&inherited) = self.inherited.get(&site.at.node) {
            let _passed = self.inherited.insert(inner.node, inherited);
        }
        self.pass_paths(site.at.node, inner.node);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// Classify a tuple, `(v1, …, vn)`, the one-element `(v,)` included.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the `(` of a parenthesised expression
    ///   whose first member a comma follows.
    /// - ensures: the tuple stands as a value, reads every member as a value
    ///   under its own frame, and is planned over them as one tuple, as one `*`
    ///   chain is one product.
    /// - provides: the introduction of the eager product.
    /// - fails: yields the wrong-sort refusal where no value is read, and the
    ///   list's refusal for a member out of shape, both naming the tuple.
    /// - panics: none.
    ///
    /// # Errors
    /// The tuple's refusal.
    ///
    /// # Termination
    /// The member loop runs once per entry of the finite member stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of one, of two and of three, and a tuple
    ///   where a computation is read, each asserted as the exact core node read
    ///   back out of the arena or the exact refusal.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Tuple(members)) if members.end.saturating_sub(members.start) >= 1_usize
                )
        },
    )]
    fn pair(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let tuple = Site {
            name: FormName::TUPLE,
            ..site
        };
        let frame = self.require(tuple, Produced::Value)?;
        let start = self.operands.len();
        if let Err(refusal) = arguments(tuple, &mut cursor, &mut self.operands) {
            self.operands.truncate(start);
            return Err(refusal);
        }
        let members = Stretch {
            start,
            end: self.operands.len(),
        };
        for position in members.start .. members.end {
            if let Some(&member) = self.operands.get(position) {
                self.read(member, Reading::Value(frame));
            }
        }

        self.plan(site, Plan::Tuple(members));

        Ok(())
    }

    /// Classify a thunk, `thunk { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk in term position.
    /// - ensures: a thunk standing as a value reads its block in its own frame
    ///   as a body a path runs through, answering the type the signature of the
    ///   definition it is states for its body, and is planned over it.
    /// - provides: the value former that suspends a computation.
    /// - fails: yields the wrong-sort refusal outside value position, the
    ///   unadmitted refusal for a grade, the block's own refusal, and the
    ///   unreachable refusal for statements after one every path of which
    ///   exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The thunk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk keeps its block computation under suspension;
    ///   an authored force reads that value before forcing its computation.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Thunk(Block { statements, .. })) if statements.start <= statements.end && statements.end <= self.statements.len())
        },
    )]
    fn thunk(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let _keyword = cursor.tile(TileName::THUNK);
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(FormName::GRADE, FragmentBoundary::Unadmitted));
        }
        let body = self.block(site, &mut cursor, frame)?;
        let answer = match self.thunked.get(&site.at.node) {
            Some(&answer) => {
                let _passed = self.answers.insert(body.last, answer);
                Maybe::Present(answer)
            },
            None => Maybe::Absent(native::answered::Absent::Unstated),
        };
        self.open_body(site, body, answer)?;

        self.plan(site, Plan::Thunk(body));

        Ok(())
    }

    /// Classify a lambda, `fn (x) { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a lambda in term position.
    /// - ensures: a lambda standing as a computation binds its one parameter in
    ///   a frame extending its own, reads its block under that frame as a body
    ///   a path runs through, and is planned over it. Where its position
    ///   answers a written arrow `A -> C`, parentheses stripped, the binder is
    ///   typed `A` as a parameter's written type types it, and the body answers
    ///   `C`, each under the frame the arrow was read under.
    /// - provides: the binder of the fragment.
    /// - fails: yields the wrong-sort refusal where no bridge reaches a
    ///   computation; the unadmitted refusal for a type abstraction or a typed
    ///   parameter; the arity refusal for any parameter count but one; the
    ///   block's own refusal; and the unreachable refusal for statements after
    ///   one every path of which exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The lambda's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda body uses its newly introduced binder and a
    ///   lambda offered directly in value position is nested.
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    /// - witness: `lower::tests::a_lambda_in_value_position_is_nested_and_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Lambda(Block { statements, .. }, _)) if statements.start <= statements.end && statements.end <= self.statements.len())
        },
    )]
    fn lambda(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let _keyword = cursor.tile(TileName::FN);
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(FormName::TYPE_ABSTRACTION, FragmentBoundary::Unadmitted));
        }
        let binder = parameter(site, &mut cursor)?;
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        let arrow = self.answered_arrow(site)?;
        let extended = match arrow {
            Some((domain, _)) => {
                self.scope
                    .extend_typed(frame, name, domain, Maybe::Present(binder.span))
            },
            None => self.scope.extend(frame, name, Maybe::Present(binder.span)),
        };
        let body = self.block(site, &mut cursor, Frame::Inner(extended))?;
        let answer = match arrow {
            Some((_, codomain)) => {
                let _passed = self.answers.insert(body.last, codomain);
                Maybe::Present(codomain)
            },
            None => Maybe::Absent(native::answered::Absent::Unstated),
        };
        self.open_body(site, body, answer)?;

        self.plan(site, Plan::Lambda(body, binder.node));

        Ok(())
    }

    /// The domain and the answered codomain of the arrow the lambda at `site`
    /// answers: a written arrow `A -> C`, parentheses stripped, or the next
    /// arrow a value function space `(A1, …, An) => B` stands for. A binder
    /// the arrow or the space names, `(x : A)`, answers its type `A`.
    ///
    /// # Specification
    /// - requires: `site` is a lambda in term position.
    /// - ensures: for a position answering a written type that unwraps to an
    ///   arrow of two operands, the domain's node — the type a dependent
    ///   arrow's binder declares — and the codomain answered under the arrow's
    ///   frame; for a position answering an alias's arrows past `t` domains,
    ///   its domain `t + 1` — the type a telescope's entry `t + 1` declares —
    ///   and, under the same frame, the arrows past `t + 1` domains, or `B`
    ///   returning past the last; nothing for an unanswered position, an answer
    ///   over a loop or a returner, an alias with no domain left and any other
    ///   type.
    /// - fails: as [`Self::unwrapped`] and [`Self::alias_domains`].
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda signed `+U (Empty -> -F Integer)` matches no
    ///   arm on its binder, as a parameter of the same type does, and a lambda
    ///   signed `Empty => Integer`, `(Empty, Integer) => Integer` or the
    ///   telescope `(a : One) => Path(One, a, a)` lowers as under the thunked
    ///   arrows the alias stands for.
    /// - witness: `lower::native::tests::a_match_of_no_arms_switches_on_a_lambda_binder_its_arrow_types`
    /// - witness: `lower::native::tests::a_lambda_under_a_value_function_alias_lowers_as_under_its_thunked_arrow_808`
    /// - witness: `lower::native::tests::a_lambda_under_a_telescope_alias_lowers_as_under_its_dependent_arrows_815`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |arrow| arrow.is_none_or(|(_, codomain)| matches!(codomain.over, native::Over::Written | native::Over::Returning | native::Over::Valued { .. }))))]
    fn answered_arrow(
        &mut self,
        site: Site,
    ) -> Result<Option<(NodeIndex, native::Answer)>, LoweringRefusal<'source>>
    {
        let Some(&answer) = self.answers.get(&site.at.node)
        else {
            return Ok(None);
        };
        let taken = match answer.over {
            native::Over::Written => None,
            native::Over::Valued { taken } => Some(taken),
            native::Over::Loop { .. } | native::Over::Returning => return Ok(None),
        };
        let unwrapped = self.unwrapped(answer.node)?;
        let Maybe::Present(native::Unwrapped {
            former,
            ref operands,
            ..
        }) = unwrapped
        else {
            return Ok(None);
        };
        let &[domain, codomain] = operands.as_slice()
        else {
            return Ok(None);
        };
        let Some(taken) = taken
        else {
            if former != Former::ArrowType {
                return Ok(None);
            }
            let bound = self.binder_type(domain, answer.frame)?.unwrap_or(domain);
            return Ok(Some((bound, native::Answer {
                node: codomain,
                ..answer
            })));
        };
        if former != Former::ValueFunctionType {
            return Ok(None);
        }
        let Some(domains) = self.alias_domains(domain, answer.frame)?
        else {
            return Ok(None);
        };
        let Some(&bound) = domains.get(taken)
        else {
            return Ok(None);
        };
        let next = taken.saturating_add(1_usize);
        let rest = if next < domains.len() {
            native::Answer {
                over: native::Over::Valued { taken: next },
                ..answer
            }
        }
        else {
            native::Answer {
                node: codomain,
                frame: answer.frame,
                over: native::Over::Returning,
            }
        };

        Ok(Some((bound, rest)))
    }

    /// Classify a block standing as a computation, `{ run x <- c ; … c }`.
    ///
    /// # Specification
    /// - requires: `site` is a block in term position.
    /// - ensures: a block standing as a computation reads its statements and
    ///   its last computation as a thunk's or a lambda's block does, under its
    ///   own frame, passes the answer its position states and the paths through
    ///   its position to its last computation, runs the paths on to its
    ///   statements when a path passes it, and is planned over them.
    /// - provides: sequencing where one computation is read, a match arm's body
    ///   among them.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   block's own refusal, and the unreachable refusal for statements after
    ///   one every path of which exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block arm binds its statement over its last
    ///   computation, and a block where a value is read is refused.
    /// - witness: `lower::tests::a_block_standing_as_a_computation_binds_its_statements`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Block(Block { statements, .. })) if statements.start <= statements.end && statements.end <= self.statements.len())
        },
    )]
    fn sequenced(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let body = self.block(site, &mut cursor, frame)?;
        let answer = match self.answers.get(&site.at.node) {
            Some(&answer) => {
                let _passed = self.answers.insert(body.last, answer);
                Maybe::Present(answer)
            },
            None => Maybe::Absent(native::answered::Absent::Unstated),
        };
        self.pass_paths(site.at.node, body.last);
        if self.exitable.contains(&site.at.node) {
            self.paths_through(site, body, answer)?;
        }

        self.plan(site, Plan::Block(body));

        Ok(())
    }

    /// Classify a function tail, `def f(x: A, …) -> B { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a declaration form read as a function, whose tail
    ///   opens on `(`.
    /// - ensures: each parameter binds in a frame extending the one before it,
    ///   left to right, with its type, when written, read as a value type under
    ///   the frame before it and recorded on the binder; a recursive tail
    ///   stages the parameter [`Self::staged_by_body`] reads off its body and
    ///   binds its own name in one more frame, between that parameter and the
    ///   ones before it, typed by the declaration form so no telescope counts
    ///   it, records the parameters before it as the ones every recursive call
    ///   passes unchanged, and records each parameter's position as the one a
    ///   match on it scrutinises; the result, when written, is read at the
    ///   result position under the last parameter's frame, as the block is, and
    ///   recorded as the answer of the block's last computation and of every
    ///   statement whose local ends continue the block; the block is read as a
    ///   body a path runs through; the form is planned as the function's
    ///   declared type and body.
    /// - provides: the function tail, lowered once at the declaration form for
    ///   both halves it writes.
    /// - fails: yields the unadmitted refusal for a parameter spelled as a type
    ///   or a type variable, and, as a recursive tail, for one with no
    ///   parameter to descend on; a fault naming the function form for a
    ///   parameter list, a type or a result out of shape; a form fault reading
    ///   a recursive tail's body ahead; the block's own refusal; and the
    ///   unreachable refusal for statements after one every path of which
    ///   exits.
    /// - panics: none.
    ///
    /// # Errors
    /// The function's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parameter count is separated by none and two,
    ///   each lowered tail asserted as the exact core node read back out of the
    ///   arena, and the refusals by a type-spelled parameter and a juxtaposed
    ///   parameter type, each asserted as the exact variant.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
    /// - witness: `lower::native::tests::a_match_takes_its_answer_from_the_function_result`
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `lower::native::tests::a_definition_descends_on_the_parameter_its_cases_scrutinise`
    #[spec(
        captures: parameters = self.parameters.len(),
        ensures: |ret| {
            ret.is_err()
                || self
                    .plans
                    .get(usize::from(site.at.node))
                    .is_some_and(|plan| match *plan {
                        | Plan::Function(ref function) => {
                            function.parameters.start == parameters
                                && function.parameters.end == self.parameters.len()
                                && function.block.statements.start <= function.block.statements.end
                                && function.block.statements.end <= self.statements.len()
                        },
                        | _ => false,
                    })
        },
    )]
    fn function(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let function = Site {
            name: FormName::FUNCTION,
            ..site
        };
        loop {
            match cursor.read() {
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::DEF => break,
                Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) => {},
                Maybe::Absent(_) => {
                    return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
        }
        let recursive = cursor.tile(TileName::REC);
        let named = cursor.tile(TileName::IDENTIFIER);
        closed(function, &mut cursor, TileName::PAREN_OPEN)?;
        let start = self.parameters.len();
        let mut frame = Frame::Outermost;
        let mut recursion = Maybe::Absent(recursion::Absent::Plain);
        // A recursive tail stages the parameter its body's matches take
        // apart, read off the syntax ahead before anything binds.
        let staged = match (recursive, named) {
            (Maybe::Present(_), Maybe::Present(own)) => {
                let mut ahead = cursor.clone();
                let mut names = Vec::new();
                let mut roots = Vec::new();
                let mut listed = true;
                while let Maybe::Present(piece) = ahead.read() {
                    match piece {
                        Piece::Tile { label, at } if listed && label == TileName::IDENTIFIER => {
                            names.push(self.name_at(at));
                        },
                        Piece::Tile { label, .. } if label == TileName::PAREN_CLOSE => {
                            listed = false;
                        },
                        Piece::Operand(operand) if !listed => roots.push(operand.node),
                        Piece::Tile { .. } | Piece::Operand(_) => {},
                    }
                }
                let own = self.name_at(own);
                Some(self.staged_by_body(own, &names, &roots)?)
            },
            _ => None,
        };
        loop {
            let binder = match cursor.peek() {
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_CLOSE => {
                    let _close = cursor.tile(TileName::PAREN_CLOSE);
                    break;
                },
                Maybe::Present(Piece::Tile { label, at }) if label == TileName::IDENTIFIER => at,
                Maybe::Present(Piece::Tile { label, at }) if TileName::BINDERS.contains(&label) => {
                    let parameter = Site {
                        at,
                        name: FormName::PARAMETER,
                        ..function
                    };
                    return Err(parameter.out(FragmentBoundary::Unadmitted));
                },
                Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                    return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
                },
            };
            let _binder = cursor.tile(TileName::IDENTIFIER);
            let declared = match cursor.tile(TileName::COLON) {
                Maybe::Present(_) => {
                    let declared = function.one(cursor.operands())?;
                    self.read(declared.node, Reading::ValueType(frame));
                    Maybe::Present(declared.node)
                },
                Maybe::Absent(_) => Maybe::Absent(stated::Absent::Unstated),
            };
            let name = self.name_at(binder);
            self.note_binder(binder, name)?;
            if let (Maybe::Present(own), Some(staged)) = (named, staged)
                && self.parameters.len().saturating_sub(start) == staged.0
            {
                let own_site = Maybe::Present(own.span);
                let named = own.node;
                let own = self.name_at(own);
                let bound = self.scope.extend_typed(frame, own, site.at.node, own_site);
                let _first = self.recursions.insert(bound, native::Recursion {
                    parameters: Stretch { start, end: start },
                    uniform: Stretch {
                        start,
                        end: self.parameters.len(),
                    },
                    claimed: native::Claimed(false),
                    named,
                });
                recursion = Maybe::Present(bound);
                frame = Frame::Inner(bound);
            }
            let written = Maybe::Present(binder.span);
            let bound = match declared {
                Maybe::Present(declared) => self.scope.extend_typed(frame, name, declared, written),
                Maybe::Absent(_) => self.scope.extend(frame, name, written),
            };
            self.parameters.push(Parameter {
                binder: binder.node,
                frame: bound,
                declared,
            });
            frame = Frame::Inner(bound);
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
            {
                return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
            }
        }
        if let (Maybe::Present(_), Maybe::Absent(_)) = (recursive, recursion) {
            let recursive = Site {
                name: FormName::RECURSIVE,
                ..site
            };
            return Err(recursive.out(FragmentBoundary::Unadmitted));
        }
        let parameters = Stretch {
            start,
            end: self.parameters.len(),
        };
        if let Maybe::Present(own) = recursion
            && let Some(held) = self.recursions.get_mut(&own)
        {
            held.parameters = parameters;
            for (position, parameter) in stretch(&self.parameters, parameters).iter().enumerate() {
                let scrutiny = native::Scrutiny {
                    recursion: own,
                    position: native::ParameterAt(position),
                };
                let _first = self.staged_parameters.insert(parameter.frame, scrutiny);
            }
        }
        let result = match cursor.tile(TileName::ARROW) {
            Maybe::Present(_) => {
                let result = function.one(cursor.operands())?;
                self.read(result.node, Reading::Result(frame));
                Maybe::Present(result.node)
            },
            Maybe::Absent(_) => Maybe::Absent(stated::Absent::Unstated),
        };
        let block = self.block(function, &mut cursor, frame)?;
        let answer = match result {
            Maybe::Present(node) => {
                let answer = native::Answer {
                    node,
                    frame,
                    over: native::Over::Written,
                };
                let _first = self.answers.insert(block.last, answer);
                Maybe::Present(answer)
            },
            Maybe::Absent(_) => Maybe::Absent(native::answered::Absent::Unstated),
        };
        self.open_body(function, block, answer)?;

        self.plan(
            site,
            Plan::Function(Function {
                parameters,
                result,
                block,
                recursion,
            }),
        );

        Ok(())
    }

    /// Read a block, `{ s… c }`, whose first statement reads under `frame`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the block's `{`, which the form's last
    ///   piece closes.
    /// - ensures: each `run x <- c ;` statement reads its computation under the
    ///   frame the statements before it extended and binds `x` in a frame
    ///   extending that one; `recv(c) as x ;` binds `x` the same way, and `fork
    ///   (c : S) t as d ;` binds `d` and `hold x = e ;` binds `x` linearly over
    ///   the rest of the block; the last computation, written bare or as a
    ///   statement `c ;` before the closing `}` and then recorded as stated,
    ///   reads under the frame every statement extended; the statements and the
    ///   last computation are returned, with the cursor past the closing `}`
    ///   and nothing after it.
    /// - provides: the body reading of thunks, lambdas and function tails.
    /// - fails: yields the unadmitted or the reserved refusal for a statement
    ///   the fragment does not read, by the statement's own name; the
    ///   unadmitted refusal for a fork or a hold in a block whose ends continue
    ///   an enclosing one past an early exit; the arity refusal, as a block,
    ///   for a block with no last computation; and each statement's and hole's
    ///   own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the statement count is separated by none and two, the
    ///   second binding over the first, each asserted as the exact bind chain
    ///   read back out of the arena; the residue by one witness row per refused
    ///   statement form, asserted as the exact refusal.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
    /// - witness: `lower::session::tests::a_fork_an_exit_would_continue_is_declined`
    /// - witness: `lower::access::tests::an_exit_inside_an_access_is_refused`
    /// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
    #[spec(
        captures: before = (self.statements.len(), frame),
        ensures: |ret| {
            ret.as_ref().map_or(true, |block| {
                block.statements.start == before.0
                    && block.statements.end == self.statements.len()
                    && matches!(self.reading(block.last), Reading::Computation(_))
                    && (block.statements.start != block.statements.end
                        || self.reading(block.last) == Reading::Computation(before.1))
                    && matches!(cursor.peek(), Maybe::Absent(_))
            })
        },
    )]
    fn block(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Block, LoweringRefusal<'source>>
    {
        let Maybe::Present(open) = cursor.tile(TileName::BRACE_OPEN)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let start = self.statements.len();
        let mut frame = frame;
        loop {
            match cursor.peek() {
                Maybe::Present(Piece::Operand(_)) => {
                    let run = cursor.operands();
                    if let Maybe::Present(semicolon) = cursor.at(TileName::SEMICOLON) {
                        let first = match run {
                            Run::One(written) | Run::Several { first: written, .. } => written.span,
                            Run::Empty(gap) => gap,
                        };
                        let span = first.join(semicolon.span);
                        let mut ahead = cursor.clone();
                        let _semicolon = ahead.tile(TileName::SEMICOLON);
                        if let (Run::One(written), Maybe::Present(_)) =
                            (run, ahead.at(TileName::BRACE_CLOSE))
                        {
                            let _semicolon = cursor.tile(TileName::SEMICOLON);
                            let _first = self.stated.insert(written.node, span);
                            let _leads = self.leading.insert(written.span.start());
                            closed(site, cursor, TileName::BRACE_CLOSE)?;
                            exhausted(site, cursor)?;
                            self.read(written.node, Reading::Computation(frame));
                            return Ok(Block {
                                statements: Stretch {
                                    start,
                                    end: self.statements.len(),
                                },
                                last: written.node,
                            });
                        }
                        let discarded = site.one(run)?;
                        let _semicolon = cursor.tile(TileName::SEMICOLON);
                        self.read(discarded.node, Reading::Computation(frame));
                        let _leads = self.leading.insert(discarded.span.start());
                        self.statements.push(Statement {
                            origin: discarded.node,
                            bound: discarded.node,
                            binding: StatementBinding::Discarded,
                            rest: exits::Rest::Bound,
                        });
                        frame = Frame::Inner(self.scope.extend(
                            frame,
                            SurfaceName::from(""),
                            Maybe::Absent(binder_site::Absent::Unwritten),
                        ));
                        continue;
                    }
                    let last = site.one(run)?;
                    closed(site, cursor, TileName::BRACE_CLOSE)?;
                    exhausted(site, cursor)?;
                    self.read(last.node, Reading::Computation(frame));
                    let _leads = self.leading.insert(last.span.start());
                    return Ok(Block {
                        statements: Stretch {
                            start,
                            end: self.statements.len(),
                        },
                        last: last.node,
                    });
                },
                Maybe::Present(Piece::Tile { label, .. }) if label == TileName::BRACE_CLOSE => {
                    let braced = ByteSpan::new(open.span.start(), site.at.span.end())
                        .unwrap_or(site.at.span);
                    let as_block = Site {
                        at: Placed {
                            node: site.at.node,
                            span: braced,
                        },
                        name: FormName::BLOCK,
                        reading: Reading::Computation(frame),
                    };
                    return Err(as_block.out(FragmentBoundary::Arity(OperandCount::from(0_usize))));
                },
                Maybe::Present(Piece::Tile { label, at }) => {
                    match statement_form(label, cursor) {
                        Maybe::Present((form, boundary)) => {
                            return Err(LoweringRefusal::OutOfFragment {
                                span: at.span,
                                form,
                                sort: FragmentSort::Computation,
                                boundary,
                            });
                        },
                        Maybe::Absent(statement::Absent::NotAKeyword) => {
                            return Err(site.fault(at.span, FormFault::MisplacedTile));
                        },
                        Maybe::Absent(statement::Absent::Read) => {},
                    }
                    let _keyword = cursor.read();
                    frame = if label == TileName::RUN {
                        self.statement(cursor, at, frame)?
                    }
                    else if label == TileName::RECV {
                        self.receive(cursor, at, frame)?
                    }
                    else if label == TileName::LETA {
                        self.leta(cursor, at, frame)?
                    }
                    else if self.joined.contains(&site.at.node) {
                        return Err(LoweringRefusal::OutOfFragment {
                            span: at.span,
                            form: if label == TileName::HOLD {
                                FormName::HOLD_STATEMENT
                            }
                            else {
                                FormName::FORK_STATEMENT
                            },
                            sort: FragmentSort::Computation,
                            boundary: FragmentBoundary::Unadmitted,
                        });
                    }
                    else if label == TileName::HOLD {
                        self.hold(cursor, at, frame)?
                    }
                    else {
                        self.fork(cursor, at, frame)?
                    };
                },
                Maybe::Absent(_) => {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
        }
    }

    /// Read one `run p <- c ;` statement, its `run` tile already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's `run` tile `run`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: the statement's computation is read under `frame` and the
    ///   statement recorded with its `run` tile; the frame binding the
    ///   statement's name over `frame`, which the rest of the block reads
    ///   under, is returned. A tuple pattern `(x, y, …)` binds the returned
    ///   tuple under a nameless binder and each component's name over it, in
    ///   order, and the statement is recorded as that split. A name annotated
    ///   `x : A` reads `A` in `frame` and binds the name over it, and the
    ///   statement is recorded as the bind of `c` ascribed `-F A`. A name
    ///   written with no type is recorded with `frame` and `c`, which
    ///   [`Self::ran_type`] reads its type off.
    /// - provides: the one statement the fragment reads.
    /// - fails: yields the unadmitted refusal for an annotated tuple pattern
    ///   and for a binder pattern other than a name, a wildcard or a tuple of
    ///   those, and a fault naming the bind statement for a hole or a tile out
    ///   of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each run statement reads its bound computation in the
    ///   previous frame and introduces its names only for subsequent
    ///   computations; a two-component tuple binds both names in order, so a
    ///   swapped binding reads the other component; an annotated name checks
    ///   the bound computation against its type before binding it.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::a_tuple_binder_splits_the_returned_tuple_in_order`
    /// - witness: `lower::tests::a_typed_bind_ascribes_its_computation`
    #[spec(
        captures: before = self.statements.len(),
        ensures: |ret| match ret {
            | Ok(Frame::Inner(_)) => {
                self.statements.len() == before.saturating_add(1_usize)
                    && self.statements.last().is_some_and(|last| {
                        last.origin == run.node
                            && matches!(last.binding, StatementBinding::Named(_) | StatementBinding::Split { .. } | StatementBinding::Typed { .. })
                            && self.reading(last.bound) == Reading::Computation(frame)
                    })
            },
            | Ok(Frame::Outermost) => false,
            | Err(_) => self.statements.len() == before,
        },
    )]
    fn statement(
        &mut self,
        cursor: &mut Cursor<'_>,
        run: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: run,
            name: FormName::BIND_STATEMENT,
            reading: Reading::Computation(frame),
        };
        let binder = statement.one(cursor.operands())?;
        let annotation = if let Maybe::Present(colon) = cursor.tile(TileName::COLON) {
            Some((colon, statement.one(cursor.operands())?))
        }
        else {
            None
        };
        closed(statement, cursor, TileName::BIND)?;
        let bound = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::SEMICOLON)?;
        if let Maybe::Present(components) = self.tuple_binders(statement, binder)? {
            if let Some((colon, _)) = annotation {
                return Err(LoweringRefusal::OutOfFragment {
                    span: colon.span,
                    form: FormName::ANNOTATION,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Unadmitted,
                });
            }
            let mut names = Vec::with_capacity(components.len());
            for &component in &components {
                let name = self.binder_name(statement, component)?;
                self.note_binder(component, name)?;
                names.push((name, component.span));
            }
            self.read(bound.node, Reading::Computation(frame));
            self.statements.push(Statement {
                origin: run.node,
                bound: bound.node,
                binding: StatementBinding::Split {
                    arity: gandr_core_term::ComponentCount::from(names.len()),
                    pattern: binder.node,
                },
                rest: exits::Rest::Bound,
            });
            let mut inner = self.scope.extend(
                frame,
                SurfaceName::from(""),
                Maybe::Absent(binder_site::Absent::Unwritten),
            );
            for (name, written) in names {
                inner = self
                    .scope
                    .extend(Frame::Inner(inner), name, Maybe::Present(written));
            }
            return Ok(Frame::Inner(inner));
        }
        let name = self.binder_name(statement, binder)?;
        self.note_binder(binder, name)?;
        if let Some((_, annotation)) = annotation {
            self.read(bound.node, Reading::Computation(frame));
            self.read(annotation.node, Reading::ValueType(frame));
            self.statements.push(Statement {
                origin: run.node,
                bound: bound.node,
                binding: StatementBinding::Typed {
                    name: binder.node,
                    annotation: annotation.node,
                },
                rest: exits::Rest::Bound,
            });
            return Ok(Frame::Inner(self.scope.extend(
                frame,
                name,
                Maybe::Present(binder.span),
            )));
        }
        self.read(bound.node, Reading::Computation(frame));
        self.statements.push(Statement {
            origin: run.node,
            bound: bound.node,
            binding: StatementBinding::Named(binder.node),
            rest: exits::Rest::Bound,
        });
        let bound_at = self.scope.extend(frame, name, Maybe::Present(binder.span));
        let _first = self.ran.insert(bound_at, (frame, bound));

        Ok(Frame::Inner(bound_at))
    }

    /// The component patterns of a tuple pattern standing as a `run`
    /// statement's binder, in order.
    ///
    /// # Specification
    /// - requires: `binder` is the pattern operand of the statement at
    ///   `statement`.
    /// - ensures: each component operand of a tuple pattern, in order; absent
    ///   for any other pattern.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a foreign mold, and a
    ///   fault naming the bind statement for a repaired pattern or a tile out
    ///   of place among the components.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-component tuple binds both names in order, and
    ///   three components bind all three, and a name pattern reads as no tuple.
    /// - witness: `lower::tests::a_tuple_binder_splits_the_returned_tuple_in_order`
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::a_split_of_three_components_lowers`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |components| match *components { Maybe::Present(ref parts) => parts.len() >= 2, Maybe::Absent(_) => true }))]
    fn tuple_binders(
        &self,
        statement: Site,
        binder: Placed,
    ) -> Result<Maybe<Vec<Placed>, untupled::Absent>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(binder.node)
        else {
            return Ok(Maybe::Absent(untupled::Absent::OtherPattern));
        };
        let Shape::Form { name, .. } = shape_of(self.pbg, node)?
        else {
            return Ok(Maybe::Absent(untupled::Absent::OtherPattern));
        };
        if name != FormName::TUPLE_PATTERN {
            return Ok(Maybe::Absent(untupled::Absent::OtherPattern));
        }
        let mut pieces = Pieces::new();
        read_pieces(self.pbg, self.tree, binder.node, &mut pieces)?;
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(repaired.refusal(FormName::TUPLE_PATTERN));
        }
        let mut cursor = Cursor::new(&pieces.pieces, binder.span);
        closed(statement, &mut cursor, TileName::PAREN_OPEN)?;
        let mut components = Vec::new();
        loop {
            components.push(statement.one(cursor.operands())?);
            if let Maybe::Present(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
            {
                continue;
            }
            closed(statement, &mut cursor, TileName::PAREN_CLOSE)?;
            break;
        }
        if components.len() < 2 {
            return Err(statement.fault(binder.span, FormFault::MisplacedTile));
        }
        Ok(Maybe::Present(components))
    }

    /// The name a `run` statement's pattern binds.
    ///
    /// # Specification
    /// - requires: `binder` is the pattern operand of the statement at
    ///   `statement`.
    /// - ensures: the name an identifier pattern spells; the empty name, which
    ///   no identifier resolves to, for a wildcard, so `run _ <- c;` discards
    ///   `c`'s value at any type.
    /// - provides: the binder reading of the bind statement.
    /// - fails: yields the unadmitted refusal, at pattern sort and by the
    ///   pattern's own name, for every other pattern;
    ///   [`LoweringRefusal::UnknownMold`] for a foreign mold.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary run binders introduce the spelled name, a
    ///   wildcard binds a name nothing reads, and other patterns are refused
    ///   rather than becoming ordinary names. The predicate asks for the
    ///   binder's own source bytes, by address and length, rather than reading
    ///   the name.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::a_discarded_statement_splits_its_unit`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |name| {
                self.tree.node(binder.node).is_some_and(|node| {
                    match shape_of(self.pbg, node) {
                        | Ok(Shape::Form {
                            former: Former::Name,
                            ..
                        }) => core::ptr::eq(
                            core::ptr::from_ref::<str>(name.as_ref()),
                            core::ptr::from_ref::<str>(self.name_at(binder).as_ref()),
                        ),
                        | Ok(Shape::Form { name: form, .. }) => {
                            form == FormName::WILDCARD && name.as_ref().is_empty()
                        },
                        | _ => false,
                    }
                })
            })
        },
    )]
    fn binder_name(
        &self,
        statement: Site,
        binder: Placed,
    ) -> Result<SurfaceName<'source>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(binder.node)
        else {
            return Err(statement.fault(binder.span, FormFault::MisplacedTile));
        };
        match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::Name,
                ..
            } => Ok(self.name_at(binder)),
            Shape::Form { name, .. } if name == FormName::WILDCARD => Ok(SurfaceName::from("")),
            Shape::Form { name, .. } => Err(LoweringRefusal::OutOfFragment {
                span: binder.span,
                form: name,
                sort: FragmentSort::Pattern,
                boundary: FragmentBoundary::Unadmitted,
            }),
            Shape::Repair(repair) => Err(statement.fault(binder.span, FormFault::Repaired(repair))),
            Shape::Root | Shape::Layout => {
                Err(statement.fault(binder.span, FormFault::MisplacedTile))
            },
        }
    }

    /// Classify a keyword form of one value operand: `ret v`, `return v` or
    /// `force v`.
    ///
    /// # Specification
    /// - requires: `site` is a returner, a return or a force in term position,
    ///   whose keyword tile is `keyword`.
    /// - ensures: the form standing as a computation reads its one operand as a
    ///   value in its own frame and is planned over it; a return is planned as
    ///   the returner and recorded as an exit, which leaves the function
    ///   because the commuting puts every exit where the function's body ends.
    ///   A return in a handled subject is recorded as crossing its handlers'
    ///   frames, and the body around the scope as delimited: it leaves that
    ///   body past every frame, no return clause run. The operand of a `pure`
    ///   where a body ends, and of a return, is classified by the type the body
    ///   answers.
    /// - provides: the computation formers over a value, and the exit that
    ///   leaves a function with a value.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   not-in-tail refusal for a return that stands where no path through a
    ///   function's, a lambda's or a thunk's body passes, a scope's subject
    ///   included, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — force and return plan their own former over a value
    ///   operand, and an author-written force is not marked as inserted; a
    ///   return on a path lowers as the returner and one in a call's head is
    ///   refused.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    /// - witness: `lower::capability::tests::a_return_in_a_subject_leaves_past_the_handler`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::Force(operand)) => {
                        keyword == TileName::FORCE
                            && self.reading(operand) == Reading::Value(site.reading.frame())
                    },
                    | Some(&Plan::Return(operand)) => {
                        keyword != TileName::FORCE
                            && (keyword != TileName::RETURN
                                || (self.exitable.contains(&site.at.node)
                                    && self.leaving.contains(&site.at.node)
                                    && self.framed.contains(&site.at.node)
                                        == self.crossing.contains(&site.at.node)))
                            && self.reading(operand) == Reading::Value(site.reading.frame())
                    },
                    | _ => false,
                }
        },
    )]
    fn keyed(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        keyword: TileName,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if keyword == TileName::RETURN {
            if !self.exitable.contains(&site.at.node) {
                return Err(site.out(FragmentBoundary::NotInTail));
            }
            if self.framed.contains(&site.at.node) {
                let Some(&body) = self.bodies.get(&site.at.node)
                else {
                    return Err(site.out(FragmentBoundary::NotInTail));
                };
                let _crossing = self.crossing.insert(site.at.node);
                let _delimited = self.delimited.insert(body);
            }
            let _exit = self.leaving.insert(site.at.node);
        }
        let _keyword = cursor.tile(keyword);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(operand.node, Reading::Value(frame));
        // The value a tail's `pure` or a `return` returns is the one the body
        // answers.
        let answer = if keyword == TileName::PURE && self.exits.contains(&site.at.node) {
            self.answers.get(&site.at.node)
        }
        else if keyword == TileName::RETURN {
            self.bodies
                .get(&site.at.node)
                .and_then(|body| self.answers.get(body))
        }
        else {
            None
        };
        if let Some(&answer) = answer {
            let _first = self
                .inherited
                .insert(operand.node, native::Classifier::Answered { answer, frame });
        }
        let plan = if keyword == TileName::FORCE {
            Plan::Force(operand.node)
        }
        else {
            Plan::Return(operand.node)
        };

        self.plan(site, plan);

        Ok(())
    }

    /// Classify a run written where a value is read, `run c`.
    ///
    /// # Specification
    /// - requires: `site` is a run in term position.
    /// - ensures: the form standing as a value reads its one operand as a
    ///   computation in its own frame and is planned as the run over it; the
    ///   checker's elaboration binds the computation before the computation
    ///   around it.
    /// - provides: the written form of the bridge a computation in value
    ///   position otherwise takes inferred.
    /// - fails: yields the wrong-sort refusal where no bridge reaches a value,
    ///   and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written run plans the run over its computation
    ///   operand, marked written rather than inserted, and its operand is read
    ///   as a computation, so a value operand is refused by sort.
    /// - witness: `lower::tests::a_written_run_lowers_to_a_run_over_its_computation`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Run(operand))
                    if self.reading(operand) == Reading::Computation(site.reading.frame()))
        },
    )]
    fn run(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let _keyword = cursor.tile(TileName::RUN);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(operand.node, Reading::Computation(frame));
        self.plan(site, Plan::Run(operand.node));

        Ok(())
    }

    /// Classify a tail call, `become c`.
    ///
    /// # Specification
    /// - requires: `site` is a `become` in term position.
    /// - ensures: the form standing as a computation where a path through a
    ///   function's, a lambda's or a thunk's body passes reads its one operand
    ///   as a computation in its own frame, the answer its position states
    ///   passed on, is recorded as an exit and adopts the operand: the operand
    ///   runs under the caller's continuation, so the exit adds the guarantee,
    ///   not a frame. The operand is not itself where the body ends: `become`
    ///   is the exit, so the operand needs none; a path passes it, so an exit
    ///   inside it leaves the function too.
    /// - provides: the exit that leaves a function by running a computation.
    /// - fails: yields the wrong-sort refusal outside computation position, the
    ///   not-in-tail refusal for a `become` where no path passes,
    ///   [`LoweringRefusal::AcrossHandler`] for one in a handled subject, which
    ///   would run its operand in place of a live handler's frame, and the
    ///   hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `become` ending a body lowers as its operand, one
    ///   in a bound computation leaves the function, and one in a call's head
    ///   is refused.
    /// - witness: `lower::tests::an_exit_lowers_where_a_path_passes_and_nowhere_else`
    /// - witness: `lower::capability::tests::an_exit_that_would_run_in_a_live_frame_is_refused`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Transparent(operand))
                    if self.exitable.contains(&site.at.node) && self.leaving.contains(&site.at.node)
                        && !self.exits.contains(&operand) && self.exitable.contains(&operand)
                        && self.reading(operand) == Reading::Computation(site.reading.frame()))
        },
    )]
    fn tail_call(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        if !self.exitable.contains(&site.at.node) {
            return Err(site.out(FragmentBoundary::NotInTail));
        }
        if self.framed.contains(&site.at.node) {
            return Err(LoweringRefusal::AcrossHandler {
                span: site.at.span,
                exit: CrossedExit::Become,
            });
        }
        let _exit = self.leaving.insert(site.at.node);
        let _keyword = cursor.tile(TileName::BECOME);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(operand.node, Reading::Computation(frame));
        if let Some(&answer) = self.answers.get(&site.at.node) {
            let _passed = self.answers.insert(operand.node, answer);
        }
        let _path = self.exitable.insert(operand.node);
        if let Some(&body) = self.bodies.get(&site.at.node) {
            let _owner = self.bodies.insert(operand.node, body);
        }
        self.plan(site, Plan::Transparent(operand.node));

        Ok(())
    }

    /// Classify an application, `c(v, …)`.
    ///
    /// # Specification
    /// - requires: `site` is a call in term position.
    /// - ensures: a call whose head is a constructor of a data family declared
    ///   strictly earlier is that constructor applied to the arguments as its
    ///   fields; a call whose head is `here`, `back` or `cong`, a name no
    ///   binder and no earlier declaration carries, is that identity operation
    ///   over the arguments; a call whose head selects an operation off a
    ///   capability is that exercise, and one whose head is an operation
    ///   clause's continuation resumes it, as [`Self::exercise`] and
    ///   [`Self::resumption`] read them; a call standing where a value is read
    ///   whose head is a type former's name, free — `Path` over three
    ///   arguments, `List(A)`, `Flow`, `Stack`, `Run` — is the type it spells,
    ///   as [`Self::applied_head`] plans it, quoted; any other call standing as
    ///   a computation reads its head at the head position and each argument as
    ///   a value, all in its own frame, and is planned as the head applied to
    ///   the arguments left to right; a call whose head is an instantiation, a
    ///   recursive call, records every argument for the head's claim to check
    ///   and reads and applies those from the staged parameter's on, the ones
    ///   its fixpoint takes; a call of no arguments is its head, whose force
    ///   [`Self::mint_at`] marks as the call the source wrote.
    /// - provides: the elimination of a lambda, curried over any argument
    ///   count.
    /// - fails: yields the wrong-sort refusal outside computation position, and
    ///   the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the argument count is separated by none, one and two,
    ///   each asserted as the exact application chain read back out of the
    ///   arena. The predicate reads only the operands this call appended.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    /// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    /// - witness: `lower::identity::tests::a_bound_name_shadows_an_identity_operation`
    /// - witness: `lower::capability::tests::an_exercise_is_checked_against_the_authority_it_was_attenuated_to`
    /// - witness: `lower::capability::tests::a_scope_handles_its_capability_and_resumes`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::Application(head, arguments)) => {
                        let end = self.operands.len();
                        let descends = self.descents.get(&head).is_some_and(|descent| {
                            descent.arguments == Stretch { start, end } && descent.call == site
                        });
                        (arguments.start == start || (descends && arguments.start >= start))
                            && arguments.end == end
                            && self.reading(head) == Reading::Head(site.reading.frame())
                            && self.operands.get(arguments.start ..).is_some_and(|appended| {
                                appended.iter().all(|&argument| {
                                    self.reading(argument) == Reading::Value(site.reading.frame())
                                })
                            })
                    },
                    | Some(&Plan::Constructor(constructed)) => {
                        constructed.fields.start == start
                            && constructed.fields.end == self.operands.len()
                    },
                    | Some(&(Plan::Here(_) | Plan::Funext(..) | Plan::Equiv(..) | Plan::Univalence(_) | Plan::PathProduct(..) | Plan::Ua { .. } | Plan::ListCons(..) | Plan::Transport(..) | Plan::TelescopeTransport(_) | Plan::Derived(_) | Plan::Exercise(_) | Plan::Resume(..) | Plan::SessionRelated(..) | Plan::Stay(_) | Plan::Forward(_) | Plan::FunctionFlow(..) | Plan::FlowProduct(..) | Plan::Recorded(_) | Plan::Ride(..))) => true,
                    | Some(&(Plan::Path(..) | Plan::Flow(..) | Plan::Stack(..) | Plan::Former(..))) => {
                        matches!(site.reading, Reading::Value(_))
                    },
                    | _ => false,
                }
        },
    )]
    fn call(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(constructor) = self.constructor_head(site, head)?
        {
            let _head = cursor.operands();
            let start = self.operands.len();
            arguments(site, &mut cursor, &mut self.operands)?;
            let fields = Stretch {
                start,
                end: self.operands.len(),
            };
            return self.construct(site, constructor, fields);
        }
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(operation) = self.identity_head(site, head)?
        {
            let _head = cursor.operands();
            return self.identity_call(site, operation, cursor);
        }
        if let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(stratum) = self.ua_head(site, head)?
        {
            let _head = cursor.operands();
            return self.ua_call(site, stratum, cursor);
        }
        if let Reading::Value(_) = site.reading
            && let Run::One(head) = cursor.clone().operands()
            && let Maybe::Present(name) = self.former_head(site, head)?
        {
            let _head = cursor.operands();
            let start = self.operands.len();
            arguments(site, &mut cursor, &mut self.operands)?;
            let written = Stretch {
                start,
                end: self.operands.len(),
            };
            return self.applied_head(site, head, name, written);
        }
        if self.exercise(site, &cursor)? == arity::Planned(true) {
            return Ok(());
        }
        if self.resumption(site, &cursor)? == arity::Planned(true) {
            return Ok(());
        }
        let frame = self.require(site, Produced::Computation)?;
        let head = site.one(cursor.operands())?;
        let start = self.operands.len();
        arguments(site, &mut cursor, &mut self.operands)?;
        let written = Stretch {
            start,
            end: self.operands.len(),
        };
        let descends = self.tree.node(head.node).is_some_and(|node| {
            matches!(
                shape_of(self.pbg, node),
                Ok(Shape::Form {
                    former: Former::Instantiation,
                    ..
                })
            )
        });
        let applied = if descends {
            let _first = self.descents.insert(head.node, native::Descent {
                call: site,
                arguments: written,
            });
            let leading = self.leading_parameters(frame, head)?.0;
            Stretch {
                start: written.start.saturating_add(leading).min(written.end),
                end: written.end,
            }
        }
        else {
            written
        };
        if applied.start == applied.end {
            let _first = self.nullary.insert(head.node, site.at.node);
        }
        self.read(head.node, Reading::Head(frame));
        for position in applied.start .. applied.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(site, Plan::Application(head.node, applied));

        Ok(())
    }

    /// Lower native prefix and infix syntax using the shared vocabulary.
    ///
    /// # Specification
    /// - ensures: the table row selected by the operator receives value
    ///   operands in source order; the infix `then` is the composite of two
    ///   paths, or of two flows where a flow is answered, as [`Self::derive`]
    ///   plans it; the cons `g ∷ p` is a word, as [`Self::cons`] plans it.
    /// - fails: malformed tiles or operators outside the admitted vocabulary
    ///   are refused; `then` refuses as [`Self::derive`] does, and the cons as
    ///   [`Self::cons`] does.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the form or fragment refusal at the source operator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric operands separate order and operator
    ///   choice; unsupported operators are rejected; a prefix operator takes
    ///   its one operand.
    /// - witness: `lower::tests::native_operator_plans_preserve_order`
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    /// - witness: `lower::tests::a_prefix_operator_takes_its_one_operand`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(Plan::PrimitiveCall(..) | Plan::Derived(_) | Plan::FlowThen(..) | Plan::Constructor(_))))]
    fn operator(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        use gandr_core_term::primitive::Arguments;
        use gandr_core_term::primitive::Operator;
        use gandr_core_term::primitive::PRELUDE;
        if let &[
            Piece::Operand(letter),
            Piece::Tile { label, .. },
            Piece::Operand(rest),
        ] = pieces.pieces.as_slice()
            && label == TileName::CONS
        {
            return self.cons(site, letter, rest);
        }
        let frame = self.require(site, Produced::Computation)?;
        let (label, arguments) = match *pieces.pieces.as_slice() {
            [Piece::Tile { label, .. }, Piece::Operand(argument)] => {
                (label, Arguments::Unary(argument.node))
            },
            [
                Piece::Operand(first),
                Piece::Tile { label, .. },
                Piece::Operand(second),
            ] => (label, Arguments::Binary([first.node, second.node])),
            _ => return Err(site.fault(site.at.span, FormFault::MisplacedTile)),
        };
        if label == TileName::THEN
            && let Arguments::Binary([first, second]) = arguments
        {
            return self.derive(site, frame, identity::Derivation::Then { first, second });
        }
        let Some(&primitive) =
            PRELUDE
                .iter()
                .find(|primitive| match (primitive.operator(), arguments) {
                    (Operator::Prefix(spelling), Arguments::Unary(_))
                    | (Operator::Infix(spelling), Arguments::Binary(_)) => {
                        spelling == label.as_ref()
                    },
                    _ => false,
                })
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        for argument in arguments.iter() {
            self.read(*argument, Reading::Value(frame));
        }
        self.plan(site, Plan::PrimitiveCall(primitive, arguments));
        Ok(())
    }

    /// Classify a selection `e.name` or `e.0`.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: a selection by position projects the pair its operand is, as
    ///   [`Self::positional`] reads it; a selection read as a computation off a
    ///   name whose written type is a thunked lazy record over labels observes
    ///   the entry its label names; a selection off a name whose written type
    ///   is a type over labels projects the entry its label names, as
    ///   [`Self::selection`] reads it. A chain of selections whose head is a
    ///   capitalised name is a path: inside a functor whose parameter the head
    ///   names, a one-link path is that parameter's value component, as
    ///   [`Self::parameter_value`] reads it; otherwise it is resolved through
    ///   the outermost scope at the depth that binds it: a path ending at an
    ///   exported value component stands as that member's constant when the
    ///   member is declared strictly before the declaration the path is written
    ///   in. The chain is walked by an explicit loop, and its links are left
    ///   unread.
    /// - provides: the governed reading of a module path.
    /// - fails: yields [`LoweringRefusal::UnknownMember`], naming the module as
    ///   the path spells it and the member, for a selection a governing module
    ///   or a parameter does not export; the forward-member refusal for a
    ///   member declared at or after the referring declaration;
    ///   [`LoweringRefusal::ProjectionFromApplication`] for a chain whose head
    ///   is an application of a functor; the wrong-sort refusal for a path
    ///   ending at a module, which is not a value; the wrong-sort refusal
    ///   outside value position; and the unadmitted refusal for a selection no
    ///   module governs, a record projection the fragment does not admit.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path to an exported component at depth two and at
    ///   depth nine, to a hidden member, to an absent member at each depth, to
    ///   a module, to a member declared later, and a selection off a free name,
    ///   each asserted as the exact constant or refusal; a path past a
    ///   parameter's value, refused at that link.
    /// - witness: `tests::modules::a_user_module_selection_is_governed_and_a_free_target_still_projects`
    /// - witness: `tests::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `tests::modules::a_deep_module_path_is_governed_at_the_depth_that_binds_it`
    /// - witness: `tests::modules::a_module_namespace_is_not_a_projectable_record`
    /// - witness: `tests::modules::a_hidden_or_absent_user_module_component_is_declined_as_a_hole`
    /// - witness: `lower::arity::tests::an_observation_projects_along_the_nesting`
    /// - witness: `lower::arity::tests::a_selection_projects_a_dependent_record_along_its_nesting`
    /// - witness: `tests::modules::functors::a_parameter_is_read_only_inside_its_functor`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Constant(_) | Plan::Primitive(_) | Plan::Observe(..) | Plan::Select(..)))
                )
        },
    )]
    fn projection(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if self.positional(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        if self.observation(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        if self.selection(site, pieces)? == arity::Planned(true) {
            return Ok(());
        }
        let (head, selected) = Self::link(site, &pieces.pieces, site.at.span)?;
        let named = match self.tree.node(head.node) {
            Some(node) => matches!(shape_of(self.pbg, node)?, Shape::Form {
                former: Former::Name,
                ..
            }),
            None => false,
        };
        if named && let Maybe::Present(resolved) = self.aliased_member(site, head, selected)? {
            let none = Stretch {
                start: self.operands.len(),
                end: self.operands.len(),
            };
            if let Resolved::Declaration { constant, .. } = resolved
                && let Maybe::Present(arity) = self.data_family(constant)
            {
                return self.family(site, constant, arity, none);
            }
            let frame = self.require(site, Produced::Value)?;
            let plan = self.resolved_term(site, frame, resolved);
            self.plan(site, plan);
            return Ok(());
        }
        let _frame = self.require(site, Produced::Value)?;
        let mut links: Vec<(Placed, Placed)> = Vec::new();
        let (mut target, member) = Self::link(site, &pieces.pieces, site.at.span)?;
        links.push((target, member));
        let mut chain = Pieces::new();
        let head = loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(target.node)
            else {
                return Err(site.out(FragmentBoundary::Unadmitted));
            };
            match shape_of(self.pbg, node)? {
                Shape::Form {
                    former: Former::Projection,
                    ..
                } => {
                    read_pieces(self.pbg, self.tree, target.node, &mut chain)?;
                    if let Maybe::Present(repaired) = chain.repair {
                        return Err(repaired.refusal(site.name));
                    }
                    let (inner, selected) = Self::link(site, &chain.pieces, target.span)?;
                    links.push((inner, selected));
                    target = inner;
                },
                Shape::Form {
                    former: Former::Constructor | Former::Name,
                    ..
                } => break target,
                Shape::Form {
                    former: Former::Call,
                    ..
                } => {
                    self.refuse_applied(target, &mut chain)?;
                    return Err(site.out(FragmentBoundary::Unadmitted));
                },
                Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                },
            }
        };
        if let Some(&(_, first)) = links.last()
            && self.parameter_value(site, head, first, functor::Deeper(links.len() > 1_usize))?
                == functor::Read::Planned
        {
            return Ok(());
        }
        let mut segments = Vec::with_capacity(links.len().saturating_add(1_usize));
        segments.push(Segment::from(self.text_at(head).as_ref()));
        for &(_prefix, selected) in links.iter().rev() {
            segments.push(Segment::from(self.text_at(selected).as_ref()));
        }
        let path = NamePath::from(segments);
        match self.recognition.resolve_path(&path) {
            PathResolution::Complete(Recognized::BuiltinPrimitive { primitive, .. }) => {
                self.plan(site, Plan::Primitive(primitive));
                Ok(())
            },
            PathResolution::Complete(Recognized::ModuleComponent) => {
                let Some(&exported) = self.exported.get(&path)
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                self.select(site, exported)
            },
            PathResolution::Complete(Recognized::ModuleNamespace) => {
                Err(site.out(FragmentBoundary::WrongSort))
            },
            PathResolution::UnknownMember { depth, .. } => {
                let Some(&(prefix, selected)) = links
                    .len()
                    .checked_sub(usize::from(depth))
                    .and_then(|link| links.get(link))
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                Err(LoweringRefusal::UnknownMember {
                    span: selected.span,
                    module: self.name_at(prefix),
                    member: self.name_at(selected),
                })
            },
            PathResolution::Complete(_) | PathResolution::Ungoverned => {
                Err(site.out(FragmentBoundary::Unadmitted))
            },
        }
    }

    /// The target and the selected name of one selection, read from its
    /// pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of a projection covering `span`.
    /// - ensures: the operand the selection is taken from and the name tile
    ///   after its dot.
    /// - provides: the one-link half of [`Self::projection`].
    /// - fails: yields the misplaced-tile refusal when the pieces are not an
    ///   operand, a dot and a name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a malformed selection.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — single and deeply nested selections preserve their
    ///   target and own member positions, which locate an unknown member at its
    ///   depth.
    /// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
    /// - witness: `tests::modules::a_deep_module_path_is_governed_at_the_depth_that_binds_it`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |&(target, selected)| {
                pieces.first() == Some(&Piece::Operand(target))
                    && matches!(
                        pieces.get(1),
                        Some(&Piece::Tile {
                            label: TileName::DOT,
                            ..
                        })
                    )
                    && pieces.get(2)
                        == Some(&Piece::Tile {
                            label: TileName::IDENTIFIER,
                            at: selected,
                        })
            })
        },
    )]
    fn link(
        site: Site,
        pieces: &[Piece],
        span: ByteSpan,
    ) -> Result<(Placed, Placed), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(pieces, span);
        let Maybe::Present(Piece::Operand(target)) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let (Maybe::Present(_dot), Maybe::Present(selected)) = (
            cursor.tile(TileName::DOT),
            cursor.tile(TileName::IDENTIFIER),
        )
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };

        Ok((target, selected))
    }

    /// Plan the selection at `site` as the exported member at `target`.
    ///
    /// # Specification
    /// - requires: `target` is the member an exported path resolved to.
    /// - ensures: the member's constant, when the member is declared strictly
    ///   before the declaration `site` belongs to.
    /// - provides: the position rule for a path.
    /// - fails: yields [`LoweringRefusal::ForwardMemberReference`] for a member
    ///   declared at or after it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ForwardMemberReference`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a backward member becomes its declared constant while
    ///   a forward member is refused at the use, with the declaration retained.
    /// - witness: `tests::modules::a_backward_member_reference_resolves`
    /// - witness: `tests::modules::a_forward_member_reference_is_refused_by_position`
    #[spec(
        ensures: |ret| match self.collected.slots.get(usize::from(target)) {
            | None => ret == Err(site.out(FragmentBoundary::Unadmitted)),
            | Some(entry) => {
                if matches!(self.collected.owner_of(site.at.node), Maybe::Present(own) if target >= own)
                {
                    ret == Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name: entry.name,
                        declared: entry.named.span,
                    })
                }
                else {
                    ret.is_ok()
                        && matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Constant(constant)) if constant == entry.constant)
                }
            },
        },
    )]
    fn select(
        &mut self,
        site: Site,
        target: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(entry) = self.collected.slots.get(usize::from(target))
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        let (constant, name, declared) = (entry.constant, entry.name, entry.named.span);
        if let Maybe::Present(own) = self.collected.owner_of(site.at.node)
            && target >= own
        {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: site.at.span,
                name,
                declared,
            });
        }
        self.plan(site, Plan::Constant(constant));

        Ok(())
    }

    /// Classify a bare type head.
    ///
    /// # Specification
    /// - requires: `site` is a primitive type, a type identifier or a type
    ///   variable in type position, or a term name or a capitalised name where
    ///   a type is read.
    /// - ensures: a head standing where a value is read — an argument of a
    ///   type-position call — that names a constructor of a data family
    ///   declared strictly earlier stands as that constructor applied to no
    ///   fields, as [`Self::constructor`] reads it in term position. Otherwise,
    ///   inside a module signature, a head naming a type component written
    ///   before the head's own component stands for what that component reads:
    ///   the type a manifest component names, adopted as it lowered, or the
    ///   atom a sealed component's abstract type declares. Otherwise a head a
    ///   binder answers is that code; past the binders, a head naming a type
    ///   member written before it in its own module or an enclosing one stands
    ///   for that member's type; then a head an earlier declaration answers is
    ///   that code, read as the static application of it to no arguments. Any
    ///   other head resolves against the nullary table and is planned as its
    ///   atom.
    /// - provides: the type-head half of resolution, the expansion of a
    ///   manifest type component and a type member, the atom of a sealed one,
    ///   and the decode of a value name in type position.
    /// - fails: yields the wrong-sort refusal for a head whose sort does not
    ///   suit the position and the unresolved-head refusal for a head nothing
    ///   answers.
    /// - panics: none.
    ///
    /// # Errors
    /// The head's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at the bare universe, a binder
    ///   written at a sorted and levelled one, a binder a `run` bound to a
    ///   type, a declaration, an atom, a constructor where a value is read, a
    ///   manifest component, a sealed one and a type member, each asserted as
    ///   the exact core type read back out of the arena.
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::a_run_bound_type_and_a_constructor_argument_stand_in_a_type`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::every_type_atom_lowers_to_its_core_type`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_type_member_is_named_only_after_it_is_written`
    #[spec(
        captures: before = self.manifests.len(),
        ensures: |ret| {
            self.manifests.len() >= before
                && self.manifests.len() <= before.saturating_add(1_usize)
                && (ret.is_err()
                    || matches!(
                        self.plans.get(usize::from(site.at.node)),
                        Some(
                            &(Plan::Transparent(_)
                                | Plan::Sealed(_)
                                | Plan::Instantiated(..)
                                | Plan::Atom(_)
                                | Plan::Decode(_, _, _)
                                | Plan::StaticApplication(_, _)
                                | Plan::Data(_, _)
                                | Plan::Constructor(_))
                        )
                    ))
        },
    )]
    fn type_head(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let name = self.name_at(site.at);
        if let Reading::Value(_) = site.reading
            && let Maybe::Present(constructor) = self.constructor_named(site, name)
        {
            let none = Stretch {
                start: self.operands.len(),
                end: self.operands.len(),
            };
            return self.construct(site, constructor, none);
        }
        if let Maybe::Present(stated) = self.stated_named(site, name)? {
            return self.stated_type(site, stated);
        }
        let from = site.reading.frame();
        if let Maybe::Present(resolved) = self.resolve_name(site, from, name)? {
            let none = Stretch {
                start: self.operands.len(),
                end: self.operands.len(),
            };
            return self.static_application(site, resolved, none);
        }
        let _frame = self.require(site, Produced::ValueType)?;
        let Maybe::Present(atom) = type_atom(name)
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: site.at.span,
                name,
                arity: HeadArity::Nullary,
            });
        };

        self.plan(site, Plan::Atom(atom));

        Ok(())
    }

    /// Plan the type head at `site` as what the stated type `stated` reads.
    ///
    /// # Specification
    /// - requires: `stated` is a type component or a type member the head
    ///   names.
    /// - ensures: the head is planned as the type a manifest meaning names,
    ///   adopted as it lowered, as the atom a sealed component's abstract slot
    ///   declares, or as an instance's manifest type, its template's renamed by
    ///   the application; either way the reference is recorded against the slot
    ///   carrying the stated type's refusal, so a refusal there reaches the
    ///   declaration the head belongs to.
    /// - provides: the one reading of a stated type, whether named bare or by a
    ///   path.
    /// - fails: yields the wrong-sort refusal where the position reads no value
    ///   type, and [`LoweringRefusal::ForwardMemberReference`] for an atom or
    ///   an instance's type the referring declaration does not follow.
    /// - panics: none.
    ///
    /// # Errors
    /// The head's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest component, a type member and a sealed
    ///   component each plan their exact reading, and a sealed one named by a
    ///   declaration before its module is refused by position.
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    #[spec(
        captures: before = self.manifests.len(),
        ensures: |ret| {
            ret.is_err()
                || (self.manifests.len() == before.saturating_add(1_usize)
                    && self.manifests.last() == Some(&(stated.held, site.at.node))
                    && match stated.meaning {
                        | TypeMeaning::Manifest(defined) => matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Transparent(node)) if node == defined.node),
                        | TypeMeaning::Sealed => matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Sealed(atom)) if usize::from(atom) == usize::from(stated.held)),
                        | TypeMeaning::Instantiated { defined, instance } => matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Instantiated(read, node)) if read == instance && node == defined.node),
                        | TypeMeaning::Family(_) => false,
                    })
        },
    )]
    fn stated_type(
        &mut self,
        site: Site,
        stated: TypeComponent<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::ValueType)?;
        let plan = match stated.meaning {
            TypeMeaning::Manifest(defined) => Plan::Transparent(defined.node),
            TypeMeaning::Sealed | TypeMeaning::Instantiated { .. } => {
                let Some(atom) = self.collected.slots.get(usize::from(stated.held))
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                if let Maybe::Present(own) = self.collected.owner_of(site.at.node)
                    && own <= stated.held
                {
                    return Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name: atom.name,
                        declared: atom.named.span,
                    });
                }
                match stated.meaning {
                    TypeMeaning::Instantiated { defined, instance } => {
                        Plan::Instantiated(instance, defined.node)
                    },
                    TypeMeaning::Sealed | TypeMeaning::Manifest(_) | TypeMeaning::Family(_) => {
                        Plan::Sealed(atom.constant)
                    },
                }
            },
            TypeMeaning::Family(_) => {
                return Err(site.out(FragmentBoundary::Arity(OperandCount::from(0_usize))));
            },
        };
        self.manifests.push((stated.held, site.at.node));
        if matches!(plan, Plan::Transparent(_) | Plan::Instantiated(..)) {
            let _fresh = self.stand_ins.insert(site.at.node);
        }
        self.plan(site, plan);

        Ok(())
    }

    /// The type component or type member `name` names at `site`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: inside a signature type, the latest of the type components
    ///   written before the type's own component that bears the name, and
    ///   nothing else; elsewhere, nothing where a binder answers the name, and
    ///   otherwise the type member [`Self::type_member_named`] answers.
    /// - provides: the one scope a stated type is named in, bare or applied.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when a walk outruns the
    ///   allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a component named in a signature, a member named in a
    ///   body and a binder shadowing a member each resolve as stated.
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `tests::modules::a_type_member_is_named_only_after_it_is_written`
    /// - witness: `tests::modules::models::a_derived_signature_states_what_the_written_one_does`
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(stated)) => stated.name == name,
            | Ok(Maybe::Absent(_)) | Err(_) => true,
        },
    )]
    fn stated_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<TypeComponent<'source>, named::Absent>, LoweringRefusal<'source>>
    {
        let unresolved = Maybe::Absent(named::Absent::Unresolved);
        if let Some(&Maybe::Present(seen)) = self.scopes.get(usize::from(site.at.node)) {
            return Ok(self
                .collected
                .structures
                .get(usize::from(seen.structure))
                .and_then(|structure| structure.types.get(.. seen.before))
                .and_then(|visible| visible.iter().rev().find(|stated| stated.name == name))
                .copied()
                .map_or(unresolved, Maybe::Present));
        }
        if let Maybe::Present(_) = self
            .scope
            .resolve(site.reading.frame(), name, &mut self.fuel)?
        {
            return Ok(unresolved);
        }

        self.type_member_named(site, name)
    }

    /// The type member `name` names at `site`: one written before it in the
    /// module its declaration belongs to, or in an enclosing one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the nearest module outward from the container of the
    ///   declaration owning `site` whose body declares a type member of the
    ///   name, written wholly before `site`, answers it; a site no declaration
    ///   owns, or a name no such member has, answers nothing.
    /// - provides: the body scope of a type member.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member's signature naming an earlier type member of
    ///   its own module, and one naming a member it precedes, separate the
    ///   scope from the module's whole body.
    /// - witness: `tests::modules::a_type_member_is_named_only_after_it_is_written`
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(member)) => member.name == name
                && self.collected.slots.get(usize::from(member.held)).is_some_and(|held| held.introduced_by.span.end() <= site.at.span.start()),
            | Ok(Maybe::Absent(_)) | Err(_) => true,
        },
    )]
    fn type_member_named(
        &mut self,
        site: Site,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<TypeComponent<'source>, named::Absent>, LoweringRefusal<'source>>
    {
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        let mut container = self.collected.slots.get(usize::from(own)).map_or_else(
            || self.collected.top(site.at.span.start()),
            |slot| slot.container,
        );
        while let Container::Module(module) = container
            && let Some(structure) = self.collected.structures.get(usize::from(module))
        {
            self.fuel.spend()?;
            let written = structure.type_members.iter().rev().find(|member| {
                member.name == name
                    && self
                        .collected
                        .slots
                        .get(usize::from(member.held))
                        .is_some_and(|held| held.introduced_by.span.end() <= site.at.span.start())
            });
            if let Some(&member) = written {
                return Ok(Maybe::Present(member));
            }
            container = structure.container;
        }

        Ok(Maybe::Absent(named::Absent::Unresolved))
    }

    /// Classify a qualified type reference `M.T`.
    ///
    /// # Specification
    /// - requires: `site` is a type path; `pieces` is its reading.
    /// - ensures: a chain of type paths whose head is a bare type name is one
    ///   path: inside a functor whose parameter the head names, a one-link path
    ///   is that parameter's type component, as [`Self::parameter_type`] reads
    ///   it; otherwise it is resolved through the outermost scope at the depth
    ///   that binds it: a path ending at an exported type component stands for
    ///   what the component reads — the type a manifest component or a type
    ///   member names, the type member a transparently ascribed abstract
    ///   component reads, the atom an opaquely ascribed one's abstract type
    ///   declares, or an instance's manifest type. The chain is walked by an
    ///   explicit loop, and its links are left unread. A one-link path whose
    ///   head is the alias of a path import reads the type the imported source
    ///   declares under the member, as a static application of it.
    /// - provides: the governed reading of a type path.
    /// - fails: yields [`LoweringRefusal::UnknownMember`], naming the module as
    ///   the path spells it and the member, for a type a governing module or a
    ///   parameter does not export; [`LoweringRefusal::UnresolvedTypeHead`]
    ///   naming the head for a path no module governs;
    ///   [`LoweringRefusal::ProjectionFromApplication`] for a chain whose head
    ///   is an application of a functor; the wrong-sort refusal for a path
    ///   ending at a value component or a module, and outside value-type
    ///   position; the forward-member refusal for a type component declared at
    ///   or after the referring declaration, so a type always lowers before its
    ///   readers.
    /// - panics: none.
    ///
    /// # Errors
    /// The path's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path to a sealed component, to a manifest one, to a
    ///   body type member, to a nested module's type, to an absent member, to a
    ///   value component and from an unbound head, each asserted as the exact
    ///   type or refusal; a path past a parameter's type, refused at that link.
    /// - witness: `tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    /// - witness: `tests::modules::an_unbound_type_path_is_refused_by_name`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::functors::a_parameter_is_read_only_inside_its_functor`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Transparent(_) | Plan::Sealed(_) | Plan::Instantiated(..) | Plan::Decode(..) | Plan::Unquote(..) | Plan::Data(..)))
                )
        },
    )]
    fn type_path(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut links: Vec<(Placed, Placed)> = Vec::new();
        let (mut target, member) = Self::type_link(site, &pieces.pieces, site.at.span)?;
        links.push((target, member));
        let headed = match self.tree.node(target.node) {
            Some(node) => matches!(shape_of(self.pbg, node)?, Shape::Form {
                former: Former::TypeHead,
                ..
            }),
            None => false,
        };
        if headed && let Maybe::Present(resolved) = self.aliased_member(site, target, member)? {
            let none = Stretch {
                start: self.operands.len(),
                end: self.operands.len(),
            };
            return self.static_application(site, resolved, none);
        }
        let mut chain = Pieces::new();
        let head = loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(target.node)
            else {
                return Err(site.out(FragmentBoundary::Unadmitted));
            };
            match shape_of(self.pbg, node)? {
                Shape::Form {
                    former: Former::TypePath,
                    ..
                } => {
                    read_pieces(self.pbg, self.tree, target.node, &mut chain)?;
                    if let Maybe::Present(repaired) = chain.repair {
                        return Err(repaired.refusal(site.name));
                    }
                    let (inner, selected) = Self::type_link(site, &chain.pieces, target.span)?;
                    links.push((inner, selected));
                    target = inner;
                },
                Shape::Form {
                    former: Former::TypeHead,
                    ..
                } => break target,
                Shape::Form {
                    former: Former::TypeApplication,
                    ..
                } => {
                    self.refuse_applied(target, &mut chain)?;
                    return Err(site.out(FragmentBoundary::Unadmitted));
                },
                Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                },
            }
        };
        if let Some(&(_, first)) = links.last()
            && self.parameter_type(site, head, first, functor::Deeper(links.len() > 1_usize))?
                == functor::Read::Planned
        {
            return Ok(());
        }
        let mut segments = Vec::with_capacity(links.len().saturating_add(1_usize));
        segments.push(Segment::from(self.text_at(head).as_ref()));
        for &(_prefix, selected) in links.iter().rev() {
            segments.push(Segment::from(self.text_at(selected).as_ref()));
        }
        let path = NamePath::from(segments);
        match self.recognition.resolve_path(&path) {
            PathResolution::Complete(Recognized::ModuleType) => {
                let Some(&stated) = self.exported_types.get(&path)
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                if let Maybe::Present(own) = self.collected.owner_of(site.at.node)
                    && own <= stated.held
                    && let Some(held) = self.collected.slots.get(usize::from(stated.held))
                {
                    return Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name: self.name_at(member),
                        declared: held.named.span,
                    });
                }
                self.stated_type(site, stated)
            },
            PathResolution::UnknownMember { depth, .. } => {
                let Some(&(prefix, selected)) = links
                    .len()
                    .checked_sub(usize::from(depth))
                    .and_then(|link| links.get(link))
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                Err(LoweringRefusal::UnknownMember {
                    span: selected.span,
                    module: self.name_at(prefix),
                    member: self.name_at(selected),
                })
            },
            PathResolution::Ungoverned => Err(LoweringRefusal::UnresolvedTypeHead {
                span: head.span,
                name: self.name_at(head),
                arity: HeadArity::Nullary,
            }),
            PathResolution::Complete(_) => Err(site.out(FragmentBoundary::WrongSort)),
        }
    }

    /// The target and the selected type name of one link of a type path,
    /// read from its pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of a type path covering `span`.
    /// - ensures: the operand the type is selected from and the type name tile
    ///   after its dot.
    /// - provides: the one-link half of [`Self::type_path`].
    /// - fails: yields the misplaced-tile refusal when the pieces are not an
    ///   operand, a dot and a type name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a malformed link.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a one-link and a two-link path preserve their targets
    ///   and selected names.
    /// - witness: `tests::modules::a_qualified_type_reference_resolves_through_the_namespace`
    #[spec(
        ensures: |ret| {
            ret.as_ref().map_or(true, |&(target, selected)| {
                pieces.first() == Some(&Piece::Operand(target))
                    && matches!(pieces.get(1), Some(&Piece::Tile { label: TileName::DOT, .. }))
                    && pieces.get(2)
                        == Some(&Piece::Tile {
                            label: TileName::TYPE_IDENTIFIER,
                            at: selected,
                        })
            })
        },
    )]
    fn type_link(
        site: Site,
        pieces: &[Piece],
        span: ByteSpan,
    ) -> Result<(Placed, Placed), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(pieces, span);
        let Maybe::Present(Piece::Operand(target)) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let (Maybe::Present(_dot), Maybe::Present(selected)) = (
            cursor.tile(TileName::DOT),
            cursor.tile(TileName::TYPE_IDENTIFIER),
        )
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };

        Ok((target, selected))
    }

    /// Classify a universe, `Type[s, l]`.
    ///
    /// # Specification
    /// - requires: `site` is a universe in type position, or in value position
    ///   where it is quoted.
    /// - ensures: a universe standing as a value type is planned at the sort
    ///   and level written, the value sort and the fuss-free level supplied for
    ///   whichever is left off.
    /// - provides: the universe former of the fragment.
    /// - fails: yields the wrong-sort refusal where its position reads no value
    ///   type, a misplaced-tile fault for a bracket out of shape, and the
    ///   unadmitted refusal for a level beyond the core's level width.
    /// - panics: none.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the bare spelling, a sort alone and a sort with a
    ///   level at each sort, each asserted as the exact core universe.
    /// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Universe(_))
                )
        },
    )]
    fn universe(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::ValueType)?;
        let universe = self.universe_of(site, &mut cursor)?;

        self.plan(site, Plan::Universe(universe));

        Ok(())
    }

    /// The universe a universe form's pieces spell.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the form's `Type` tile.
    /// - ensures: the sort `+` or `-` and the level numeral written, the value
    ///   sort and level zero for whichever is left off.
    /// - provides: the one reading of a universe's spelling, shared by the
    ///   universe former and the decode that reads a binder's written type.
    /// - fails: a misplaced-tile fault for a bracket out of shape; the
    ///   unadmitted refusal for a level numeral wider than a level constant.
    /// - panics: none.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the supported spellings consume the complete form and
    ///   the spelling without brackets denotes the fuss-free universe. Explicit
    ///   sort and level values are checked by the same bounded spelling table.
    /// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
    #[spec(
        captures: plain = {
            let mut input = cursor.clone();
            let _keyword = input.tile(TileName::UNIVERSE);
            matches!(input.at(TileName::BRACKET_OPEN), Maybe::Absent(_))
        },
        ensures: |ret| {
            ret.as_ref().map_or(true, |universe| {
                matches!(cursor.peek(), Maybe::Absent(_))
                    && (!plain || *universe == Universe::FUSS_FREE)
            })
        },
    )]
    fn universe_of(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let universe = self.universe_tiles(site, cursor)?;
        exhausted(site, cursor)?;

        Ok(universe)
    }

    /// The universe the `Type` tile at `cursor` and the bracket after it spell,
    /// the cursor left past them.
    ///
    /// # Specification
    /// - requires: `cursor` stands at a `Type` tile.
    /// - ensures: as [`Self::universe_of`], the cursor left past the universe's
    ///   last tile rather than required at the form's end.
    /// - provides: the universe a path type's carrier spells inline.
    /// - fails: as [`Self::universe_of`].
    /// - panics: none.
    /// - executable: none — where the cursor stands after the call has no
    ///   observer but the tiles the caller reads next; [`Self::universe_of`]
    ///   holds the whole form to its end.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::universe_of`], and a path type at a
    ///   levelled universe; a level past the constants, refused at its numeral.
    /// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
    /// - witness: `lower::identity::tests::a_path_at_a_universe_reads_its_endpoints_as_types_402`
    /// - witness: `lower::tests::a_universe_level_past_the_constants_is_refused_at_its_numeral`
    fn universe_tiles(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let _keyword = cursor.tile(TileName::UNIVERSE);
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACKET_OPEN) {
            return Ok(Universe::FUSS_FREE);
        }
        let sort = match (cursor.tile(TileName::PLUS), cursor.tile(TileName::MINUS)) {
            (Maybe::Present(_), _) => GroundSort::Value,
            (Maybe::Absent(_), Maybe::Present(_)) => GroundSort::Computation,
            (Maybe::Absent(_), Maybe::Absent(_)) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
        };
        let level = match cursor.tile(TileName::COMMA) {
            Maybe::Present(_) => {
                let Maybe::Present(numeral) = cursor.tile(TileName::NUMBER)
                else {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                };
                let text = self.text_at(numeral);
                let spelled: &str = text.as_ref();
                let Ok(level) = spelled.parse::<u64>()
                else {
                    let level = Site {
                        at: numeral,
                        ..site
                    };
                    return Err(level.out(FragmentBoundary::Unadmitted));
                };
                LevelConstant::from(level)
            },
            Maybe::Absent(_) => LevelConstant::ZERO,
        };
        closed(site, cursor, TileName::BRACKET_CLOSE)?;

        Ok(Universe { sort, level })
    }

    /// The universe a code of the type at `declared`, applied statically to
    /// `applied` arguments, decodes in; `fallback` where the type does not
    /// say.
    ///
    /// # Specification
    /// - requires: `declared`, when present, is a node of the tree.
    /// - ensures: read through any grouping parentheses, each of the first
    ///   `applied` arrows of the type steps to its codomain, and the universe
    ///   form the walk then reaches is the universe it spells; `fallback` for
    ///   an absent type, for a walk that meets any other form or an arrow too
    ///   few or too many, and for a universe out of shape, whose own reading
    ///   reports it.
    /// - provides: the sort and level a decode of a binder, a declaration or a
    ///   static application of either is minted at.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Termination
    /// Every turn spends one unit of the lowerer's allowance and steps to an
    /// operand of the node it read, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at a sorted, levelled universe
    ///   inside a grouping, a declaration signed at one, an operator's codomain
    ///   reached through one static arrow, and an unwritten type at each sort
    ///   of position, each observed through the decode it mints; an operator
    ///   whose codomain does not fit the application decoding where it stands.
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `lower::tests::a_static_application_its_operator_does_not_fit_decodes_where_it_stands`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(declared, Maybe::Present(_))
                || ret.as_ref().is_ok_and(|universe| *universe == fallback)
        },
    )]
    fn written_universe(
        &mut self,
        declared: Maybe<NodeIndex, binder_type::Absent>,
        applied: OperandCount,
        fallback: Universe,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let Maybe::Present(mut position) = declared
        else {
            return Ok(fallback);
        };
        let mut remaining = usize::from(applied);
        loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(position)
            else {
                return Ok(fallback);
            };
            let Ok(Shape::Form { name, former }) = shape_of(self.pbg, node)
            else {
                return Ok(fallback);
            };
            let mut scratch = core::mem::take(&mut self.scratch);
            let read = read_pieces(self.pbg, self.tree, position, &mut scratch);
            let site = Site {
                at: Placed::of(position, node),
                name,
                reading: Reading::ValueType(Frame::Outermost),
            };
            let mut cursor = Cursor::new(&scratch.pieces, site.at.span);
            let step = match (read, former) {
                (Ok(()), Former::Universe) if remaining == 0_usize => {
                    ControlFlow::Break(self.universe_of(site, &mut cursor).unwrap_or(fallback))
                },
                (Ok(()), Former::ParenthesizedType) => {
                    let _open = cursor.tile(TileName::PAREN_OPEN);
                    match cursor.operands() {
                        Run::One(operand) => ControlFlow::Continue(operand.node),
                        Run::Empty(_) | Run::Several { .. } => ControlFlow::Break(fallback),
                    }
                },
                (Ok(()), Former::ArrowType) if remaining > 0_usize => {
                    remaining = remaining.saturating_sub(1_usize);
                    let _domain = cursor.operands();
                    let _arrow = cursor.tile(TileName::ARROW);
                    match cursor.operands() {
                        Run::One(operand) => ControlFlow::Continue(operand.node),
                        Run::Empty(_) | Run::Several { .. } => ControlFlow::Break(fallback),
                    }
                },
                _ => ControlFlow::Break(fallback),
            };
            self.scratch = scratch;
            match step {
                ControlFlow::Continue(operand) => position = operand,
                ControlFlow::Break(universe) => return Ok(universe),
            }
        }
    }

    /// Classify a type head applied to arguments, `Foo(A)`.
    ///
    /// # Specification
    /// - requires: `site` is a type application in type position, or in value
    ///   position where a type is quoted or a constructor applied.
    /// - ensures: an application standing where a value is read — an argument
    ///   of a type-position call — whose head names a constructor of a data
    ///   family declared strictly earlier stands as that constructor applied to
    ///   the arguments, as [`Self::construct`] plans it. Otherwise a head
    ///   naming a type family, as a component or a member, expands to the
    ///   family's type over the arguments; a head a binder or an earlier
    ///   declaration answers is read as the static application of that code to
    ///   the arguments, left to right, or, holding a function where a value is
    ///   read, as its call; any other head is the type former
    ///   [`Self::applied_head`] plans.
    /// - provides: the applied half of type-head resolution.
    /// - fails: yields the unresolved-head refusal for a head nothing answers
    ///   and no former takes at the arity it was written with, the wrong-sort
    ///   refusal for a former or an application whose sort does not suit the
    ///   position, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a former's head, a head no former takes, a head
    ///   written at two arguments, an operator a declaration and a binder name,
    ///   and a constructor applied in a type-position call's argument, each
    ///   asserted as the exact core node read back out of the arena or the
    ///   exact refusal; a forward member applied, refused at its head.
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::an_applied_head_no_former_answers_is_refused`
    /// - witness: `lower::tests::a_run_bound_type_and_a_constructor_argument_stand_in_a_type`
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    /// - witness: `lower::tests::a_forward_member_applied_as_a_type_is_refused_at_its_head`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Former(..) | Plan::Decode(..) | Plan::Unquote(..) | Plan::StaticApplication(..) | Plan::Called(..) | Plan::Data(..) | Plan::Expansion(..) | Plan::Path(..) | Plan::Flow(..) | Plan::Relation(..) | Plan::Stack(..) | Plan::Constructor(_)))
                )
        },
    )]
    fn type_application(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let head = match cursor.peek() {
            Maybe::Present(Piece::Tile { label, at })
                if label == TileName::TYPE_IDENTIFIER || label == TileName::TYPE_VARIABLE =>
            {
                let _head = cursor.tile(label);
                at
            },
            Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
        };
        let name = self.name_at(head);
        if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_OPEN) {
            return self.staged_unquote(site, name, cursor);
        }
        let start = self.operands.len();
        let read = arguments(site, &mut cursor, &mut self.operands);
        if let (Ok(()), Reading::Value(_)) = (read, site.reading)
            && let Maybe::Present(constructor) = self.constructor_named(site, name)
        {
            let fields = Stretch {
                start,
                end: self.operands.len(),
            };
            return self.construct(site, constructor, fields);
        }
        match read.and_then(|()| self.stated_named(site, name)) {
            Ok(Maybe::Present(TypeComponent {
                meaning: TypeMeaning::Family(family),
                held,
                ..
            })) => {
                let applied = Stretch {
                    start,
                    end: self.operands.len(),
                };
                return self.expansion(site, family, held, applied);
            },
            Ok(Maybe::Present(_) | Maybe::Absent(_)) => {},
            Err(refusal) => {
                self.operands.truncate(start);
                return Err(refusal);
            },
        }
        let resolved = read.and_then(|()| {
            let named = Site { at: head, ..site };
            self.resolve_name(named, site.reading.frame(), name)
        });
        match resolved {
            Ok(Maybe::Present(resolved)) => {
                let applied = Stretch {
                    start,
                    end: self.operands.len(),
                };
                return self.static_application(site, resolved, applied);
            },
            Ok(Maybe::Absent(named::Absent::Unresolved)) => {},
            Err(refusal) => {
                self.operands.truncate(start);
                return Err(refusal);
            },
        }

        let written = Stretch {
            start,
            end: self.operands.len(),
        };
        self.applied_head(site, head, name, written)
    }

    /// Classify the type former `name`, written at `head` and applied to the
    /// operands `written` holds in the operand store, which nothing the scope
    /// binds answers.
    ///
    /// # Specification
    /// - requires: `written` is the arguments the head was written with, left
    ///   to right, and the last the store holds.
    /// - ensures: the arguments leave the store; a head named `Path` and
    ///   applied to three arguments is the path type [`Self::written_path`]
    ///   plans, one named `Flow` and applied to three the directed identity
    ///   type [`Self::flow_type`] plans, one named `Stack` and applied to two
    ///   the continuation type [`Self::stack_type`] plans, one named `Iso` and
    ///   applied to two the quasi-inverse `A ≅ B` [`Self::relation_of`] plans;
    ///   any other head applied to one argument resolves against the unary
    ///   table, stands at the sort its former produces, reads its argument at
    ///   the sort the former takes, and is planned over it.
    /// - provides: the one table of type formers written as an application, in
    ///   a type and where a value is read.
    /// - fails: yields the unresolved-head refusal for a head no former takes
    ///   at the arity it was written with, and the wrong-sort refusal for a
    ///   former whose sort does not suit the position.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a former's head, a head no former takes, a head
    ///   written at two arguments, a path type and a list type written as calls
    ///   where a value is read, and `Iso(A, B)` beside `A ≅ B`, each asserted
    ///   as the exact core node read back out of the arena or the exact
    ///   refusal.
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::an_applied_head_no_former_answers_is_refused`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `lower::identity::tests::a_relation_lowers_to_the_type_it_abbreviates`
    #[spec(
        ensures: |ret| {
            self.operands.len() == written.start
                && (ret.is_err()
                    || matches!(
                        self.plans.get(usize::from(site.at.node)),
                        Some(&(Plan::Former(..) | Plan::Path(..) | Plan::Flow(..) | Plan::Stack(..) | Plan::Relation(..)))
                    ))
        },
    )]
    fn applied_head(
        &mut self,
        site: Site,
        head: Placed,
        name: SurfaceName<'source>,
        written: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let start = written.start;
        let count = written.end.saturating_sub(start);
        let first = self.operands.get(start).copied();
        let triple = self
            .operands
            .get(start .. written.end)
            .and_then(|operands| <[NodeIndex; 3]>::try_from(operands).ok());
        let pair = self
            .operands
            .get(start .. written.end)
            .and_then(|operands| <[NodeIndex; 2]>::try_from(operands).ok());
        self.operands.truncate(start);
        if let Some(written) = triple
            && name.as_ref() == TileName::PATH.as_ref()
        {
            return self.written_path(site, written);
        }
        if let Some(written) = triple
            && name.as_ref() == identity::FLOW
        {
            return self.flow_type(site, written);
        }
        if let Some(written) = pair
            && name.as_ref() == STACK
        {
            return self.stack_type(site, written);
        }
        if let Some(written) = pair
            && name.as_ref() == identity::ISO
        {
            return self.relation_of(site, Relation::Isomorphism, written);
        }
        let unresolved = |arity| LoweringRefusal::UnresolvedTypeHead {
            span: head.span,
            name,
            arity,
        };
        let (Some(argument), 1_usize) = (first, count)
        else {
            return Err(unresolved(HeadArity::Polyadic(OperandCount::from(count))));
        };
        let Maybe::Present(former) = type_former(name)
        else {
            return Err(unresolved(HeadArity::Unary));
        };

        self.apply_former(site, former, argument)
    }

    /// The type former `head`, the head of a call written at `site`, spells.
    ///
    /// # Specification
    /// - requires: `head` is the first operand of the call at `site`.
    /// - ensures: the head's name when it is a capitalised name spelling
    ///   `Path`, `Flow`, `Stack`, `Iso` or a unary type former, and no
    ///   constructor, binder, earlier declaration or stated type carries that
    ///   name; the unformed absence for any other head.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold; the refusals the name's resolution yields.
    /// - panics: none.
    ///
    /// # Errors
    /// The resolution's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path type and a list type written as calls where a
    ///   value is read are read as their formers, while a constructor and a
    ///   data family applied the same way keep their own readings.
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::native::tests::a_constructor_applies_to_its_fields`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body reads the head's spelling once; the check reads it once more"
        )
    )]
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(name)) => name == self.name_at(head),
            | _ => true,
        },
    )]
    fn former_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<SurfaceName<'source>, formed::Absent>, LoweringRefusal<'source>>
    {
        let unformed = Maybe::Absent(formed::Absent::Unformed);
        let Some(node) = self.tree.node(head.node)
        else {
            return Ok(unformed);
        };
        let Shape::Form {
            former: Former::Constructor,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Ok(unformed);
        };
        let name = self.name_at(head);
        let spelled = [
            TileName::PATH.as_ref(),
            identity::FLOW,
            STACK,
            identity::ISO,
        ]
        .contains(&name.as_ref())
            || matches!(type_former(name), Maybe::Present(_));
        if !spelled {
            return Ok(unformed);
        }
        if let Maybe::Present(_constructor) = self.constructor_named(site, name) {
            return Ok(unformed);
        }
        let named = Site { at: head, ..site };
        if let Maybe::Present(_shadowed) = self.resolve_name(named, site.reading.frame(), name)? {
            return Ok(unformed);
        }
        if let Maybe::Present(_stated) = self.stated_named(site, name)? {
            return Ok(unformed);
        }

        Ok(Maybe::Present(name))
    }

    /// Classify a continuation's type, `Stack(C, D)`, its two operands already
    /// read off the application.
    ///
    /// # Specification
    /// - requires: `site` is a type application headed `Stack`, which nothing
    ///   the scope binds answers, written over `input` and `output`.
    /// - ensures: the form stands as a value type, reads both operands as
    ///   computation types under its own frame, and is planned over the two in
    ///   order.
    /// - provides: the written spelling of the type a captured continuation
    ///   has, the spelling its presentation writes.
    /// - fails: yields the wrong-sort refusal where no value type is read.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a continuation type written over two returners, read
    ///   back out of the arena with its input and output in order.
    /// - witness: `lower::tests::a_written_stack_type_lowers_to_its_continuation_type_401`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Stack(input, output))
                        if [input, output] == written
                            && self.reading(input) == Reading::CompType(site.reading.frame())
                            && self.reading(output) == Reading::CompType(site.reading.frame())
                )
        },
    )]
    fn stack_type(
        &mut self,
        site: Site,
        written: [NodeIndex; 2],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let [input, output] = written;
        self.read(input, Reading::CompType(frame));
        self.read(output, Reading::CompType(frame));
        self.plan(site, Plan::Stack(input, output));

        Ok(())
    }

    /// Classify the static application of the code `resolved` names to the
    /// arguments `applied` holds in the operand store.
    ///
    /// # Specification
    /// - requires: `applied` is a stretch of the operand store, each entry an
    ///   argument the application was written with, left to right.
    /// - ensures: a data family stands as the nominal type over its arguments,
    ///   each read as a value under the site's frame, which a value position
    ///   quotes. Otherwise, where a value is read, the application stands as
    ///   itself; where a type is read, it stands as the decode of the
    ///   application, in the universe the code's written type reaches after one
    ///   arrow per argument, and else in the universe the position reads — the
    ///   computation types where only a computation type is read, the value
    ///   types everywhere else, at the fuss-free level. A dynamic function — a
    ///   declaration defined by a function tail, or a binder applied to at
    ///   least one argument whose written type is a thunk or which is written
    ///   with no type — is not a static operator: where a type is read, its
    ///   application is the unquote of the code the call returns, in the
    ///   universe the position reads, and where a value is read, an application
    ///   of it to at least one argument is the call, a computation the position
    ///   nests. Every argument is read as a value under the site's frame, and a
    ///   binder so named is recorded by [`Self::name_in_type`]: quoted in a
    ///   body quote, mentioned elsewhere.
    /// - provides: the one reading of a type operator's use, bare or applied,
    ///   as a value or as the type it denotes.
    /// - fails: yields the arity refusal for a data family applied to other
    ///   than its parameter count, and for a dynamic function named bare where
    ///   a type is read, which computes a code only once applied (#690); the
    ///   wrong-sort refusal where the position reads neither a value nor the
    ///   sort of the decode's universe; propagates
    ///   [`LoweringRefusal::BudgetExceeded`] from the walk of the code's type.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    ///
    /// # Termination
    /// The argument loop runs once per entry of the finite stretch `applied`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare head and an applied one, each where a value is
    ///   read and where a type is read, the decode's universe written by the
    ///   operator and left to the position, a function called where a type is
    ///   read, and a binder holding a thunk called where a type is read and in
    ///   a type-position call's argument, each asserted as the exact core node
    ///   read back out of the arena.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::native::tests::a_data_family_applies_to_its_parameters`
    /// - witness: `lower::tests::a_function_to_a_universe_unquotes_where_a_type_is_read`
    /// - witness: `lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::StaticApplication(_, planned)) => {
                        planned == applied && matches!(site.reading, Reading::Value(_))
                    },
                    | Some(&Plan::Called(_, planned)) => {
                        planned == applied
                            && applied.start < applied.end
                            && matches!(site.reading, Reading::Value(_))
                    },
                    | Some(&Plan::Decode(_, planned, _) | &Plan::Unquote(_, planned, _)) => {
                        planned == applied && !matches!(site.reading, Reading::Value(_))
                    },
                    | Some(&Plan::Data(_, planned)) => planned == applied,
                    | _ => false,
                }
        },
    )]
    fn static_application(
        &mut self,
        site: Site,
        resolved: Resolved,
        applied: Stretch,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Resolved::Declaration { constant, .. } = resolved
            && let Maybe::Present(arity) = self.data_family(constant)
        {
            return self.family(site, constant, arity, applied);
        }
        let from = site.reading.frame();
        let telescope = self.telescope_at(site.at.node);
        let (code, declared) = match resolved {
            Resolved::Binder(bound) => (
                Code::Bound {
                    from,
                    binder: bound.binder,
                    telescope,
                },
                bound.declared,
            ),
            Resolved::Declaration { constant, declared } => (Code::Constant(constant), declared),
        };
        let called = applied.start < applied.end;
        let dynamic = match code {
            Code::Constant(constant) => matches!(
                self.collected
                    .slots
                    .get(usize::from(constant))
                    .map(|slot| slot.definition),
                Some(Maybe::Present(Half {
                    operand: Operand::Function,
                    ..
                }))
            ),
            // A binder holds a function when its written type is a thunk, the
            // bridge or the alias, or when it is written with no type: a
            // pattern's field or a `run`'s result. A static lambda's operand
            // is an operator, and its application is static.
            Code::Bound { .. } => {
                called
                    && match declared {
                        Maybe::Present(written) => self.tree.node(written).is_some_and(|node| {
                            matches!(
                                shape_of(self.pbg, node),
                                Ok(Shape::Form {
                                    former: Former::ThunkType | Former::ValueFunctionType,
                                    ..
                                })
                            )
                        }),
                        Maybe::Absent(binder_type::Absent::Untyped) => true,
                        Maybe::Absent(binder_type::Absent::Operand) => false,
                    }
            },
        };
        let (plan, produced) = if let Reading::Value(_) = site.reading {
            if dynamic && called {
                (Plan::Called(code, applied), Produced::Computation)
            }
            else {
                (Plan::StaticApplication(code, applied), Produced::Value)
            }
        }
        else {
            let count = OperandCount::from(applied.end.saturating_sub(applied.start));
            if dynamic && !called {
                return Err(site.out(FragmentBoundary::Arity(count)));
            }
            let universe =
                self.written_universe(declared, count, site.reading.positional_universe())?;
            let produced = match universe.sort {
                GroundSort::Value => Produced::ValueType,
                GroundSort::Computation => Produced::CompType,
            };
            let plan = if dynamic {
                Plan::Unquote(code, applied, universe)
            }
            else {
                Plan::Decode(code, applied, universe)
            };
            (plan, produced)
        };
        let frame = self.require(site, produced)?;
        if let Code::Bound { binder, .. } = code {
            let _telescope = self.name_in_type(site.at.node, binder);
        }
        for position in applied.start .. applied.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(site, plan);

        Ok(())
    }

    /// Classify a type former written as its own keyword: `+U C` or `-F A`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk type or a returner type in type position.
    /// - ensures: the keyword resolves against the unary table, a thunk type's
    ///   grade `[ω]` reads as no grade written, a returner's bracket reads as
    ///   its effect row, the form stands at the sort its former produces, reads
    ///   its one operand at the sort the former takes, and is planned over it.
    /// - provides: the keyword spelling of the two type formers.
    /// - fails: yields the unresolved-head refusal for a keyword no former
    ///   answers, [`LoweringRefusal::GradedBridge`] for a thunk type graded
    ///   other than `ω`, the row's refusal for a returner's, the unadmitted
    ///   refusal for a bracket on a list type, the wrong-sort refusal for a
    ///   former whose sort does not suit the position, and the hole's own
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the thunk and returner spellings plan their
    ///   respective bridge former, while unsupported grades produce a located
    ///   refusal.
    /// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `lower::tests::a_graded_bridge_is_refused_by_name`
    /// - witness: `lower::capability::tests::a_returner_row_names_whole_interfaces`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Former(_, _) | Plan::Effectful(..)))
                )
        },
    )]
    fn formed_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.peek()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let _keyword = cursor.tile(label);
        let name = self.name_at(at);
        let Maybe::Present(former) = type_former(name)
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: at.span,
                name,
                arity: HeadArity::Unary,
            });
        };
        if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_OPEN) {
            match former {
                TypeFormer::Thunk => self.grade(site, &mut cursor)?,
                TypeFormer::Returner => {
                    let row = self.returner_row(site, &mut cursor)?;
                    let argument = site.one(cursor.operands())?;
                    exhausted(site, &cursor)?;
                    return self.effectful(site, row, argument.node);
                },
                TypeFormer::List | TypeFormer::Run => {
                    return Err(site.folded(FormName::GRADE, FragmentBoundary::Unadmitted));
                },
            }
        }
        let argument = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;

        self.apply_former(site, former, argument.node)
    }

    /// Read a bridge's grade, `[r]`, admitting only the default `ω`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the grade's `[`.
    /// - ensures: `ω` followed by `]` reads as the bridge with no grade
    ///   written, the cursor past the `]`.
    /// - provides: the one grade the core's bridge carries.
    /// - fails: [`LoweringRefusal::GradedBridge`] for a numeral or a name as
    ///   the grade, at the grade; a misplaced-tile fault for a grade out of
    ///   shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The grade's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the default grade, a numeral and a name, each
    ///   asserted as the lowered bridge or the exact refusal.
    /// - witness: `lower::tests::a_graded_bridge_is_refused_by_name`
    #[spec(
        captures: input = {
            let mut input = cursor.clone();
            (input.read(), input.read(), input.peek())
        },
        ensures: |ret| {
            ret.is_ok()
                == matches!(
                    input,
                    (
                        Maybe::Present(Piece::Tile {
                            label: TileName::OMEGA,
                            ..
                        }),
                        Maybe::Present(Piece::Tile {
                            label: TileName::BRACKET_CLOSE,
                            ..
                        }),
                        _
                    )
                )
                && (ret.is_err() || cursor.peek() == input.2)
        },
    )]
    fn grade(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.peek()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        if label == TileName::NUMBER || label == TileName::IDENTIFIER {
            return Err(LoweringRefusal::GradedBridge {
                span: at.span,
                grade: self.name_at(at),
            });
        }
        closed(site, cursor, TileName::OMEGA)?;

        closed(site, cursor, TileName::BRACKET_CLOSE)
    }

    /// Plan `former` applied to `argument` at `site`.
    ///
    /// # Specification
    /// - requires: `argument` is the one operand the former was written with.
    /// - ensures: the thunk former stands at value-type sort with its argument
    ///   read at computation-type sort, the returner former stands at
    ///   computation-type sort with its argument read at value-type sort, the
    ///   list former stands at value-type sort with its element type read at
    ///   value-type sort, and the run former stands at value-type sort with its
    ///   session code read as a value; the former decides both, so nothing is
    ///   pushed down that has to be re-derived.
    /// - provides: the one place a type former's sorts are decided.
    /// - fails: yields the wrong-sort refusal for a former whose produced sort
    ///   does not suit the position.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — thunk and returner read the argument in opposite
    ///   sorts; each then lowers to its own core bridge former, not the other
    ///   one; a list reads its element type as a value type.
    /// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || (matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Former(stored, child)) if stored == former && child == argument)
                    && self.reading(argument)
                        == match former {
                            | TypeFormer::Thunk => Reading::CompType(site.reading.frame()),
                            | TypeFormer::Returner | TypeFormer::List => Reading::ValueType(site.reading.frame()),
                            | TypeFormer::Run => Reading::Value(site.reading.frame()),
                        })
        },
    )]
    fn apply_former(
        &mut self,
        site: Site,
        former: TypeFormer,
        argument: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let produced = match former {
            TypeFormer::Thunk | TypeFormer::List | TypeFormer::Run => Produced::ValueType,
            TypeFormer::Returner => Produced::CompType,
        };
        let frame = self.require(site, produced)?;
        let inner = match former {
            TypeFormer::Thunk => Reading::CompType(frame),
            TypeFormer::Returner | TypeFormer::List => Reading::ValueType(frame),
            TypeFormer::Run => Reading::Value(frame),
        };
        self.read(argument, inner);

        self.plan(site, Plan::Former(former, argument));

        Ok(())
    }

    /// Classify an arrow type: the computation arrow `A -> C`, the dependent
    /// arrow `(x : A) -> C`, or the static Pi `A -> B` where a value type is
    /// read.
    ///
    /// # Specification
    /// - requires: `site` is an arrow in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: an arrow standing as a value type is the static Pi, its
    ///   domain and codomain each read as a value type under the arrow's own
    ///   frame, since the codomain binds nothing; any other arrow stands as a
    ///   computation type: one whose domain is one binder is the dependent
    ///   arrow [`Self::dependent_arrow`] plans, and the rest read their domain
    ///   as a value type and their codomain as a computation type. Each is
    ///   planned over both operands.
    /// - provides: the function type of the fragment and the classifier of a
    ///   type operator.
    /// - fails: yields the wrong-sort refusal where neither sort suits the
    ///   position, and either hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The arrow's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an arrow where a computation type is read, where a
    ///   value type is read, nested to the right as an operator's classifier,
    ///   and over a computation codomain where a value type is read, each
    ///   asserted as the exact core node read back out of the arena or the
    ///   exact refusal.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::an_arrow_where_a_value_type_is_read_is_a_static_pi`
    /// - witness: `lower::tests::a_computation_codomain_of_a_static_pi_is_refused`
    /// - witness: `lower::arity::tests::a_dependent_arrow_is_the_telescope_the_alias_abbreviates`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || match self.plans.get(usize::from(site.at.node)) {
                    | Some(&Plan::StaticPi(..)) => matches!(site.reading, Reading::ValueType(_)),
                    | Some(&(Plan::Arrow(..) | Plan::DependentArrow(..))) => !matches!(site.reading, Reading::ValueType(_)),
                    | _ => false,
                }
        },
    )]
    fn arrow(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let static_pi = matches!(site.reading, Reading::ValueType(_));
        let produced = if static_pi {
            Produced::ValueType
        }
        else {
            Produced::CompType
        };
        let frame = self.require(site, produced)?;
        let domain = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::ARROW)?;
        let codomain = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        if !static_pi
            && self.dependent_arrow(site, frame, domain, codomain)? == arity::Planned(true)
        {
            return Ok(());
        }
        self.read(domain.node, Reading::ValueType(frame));
        if static_pi {
            self.read(codomain.node, Reading::ValueType(frame));
            self.plan(site, Plan::StaticPi(domain.node, codomain.node));
        }
        else {
            self.read(codomain.node, Reading::CompType(frame));
            self.plan(site, Plan::Arrow(domain.node, codomain.node));
        }

        Ok(())
    }

    /// Classify an eager product type, `A * B`, or a sum type, `A + B`, and
    /// the chain it heads; `former` names which.
    ///
    /// # Specification
    /// - requires: `site` is a product or a sum in type position, or in value
    ///   position where a type is quoted, and `former` is its former.
    /// - ensures: the chain stands as a value type; an operand that is itself
    ///   an unparenthesized form of `former` contributes its own operands
    ///   instead, so a chain `A * B * C` is one product of three components and
    ///   `A + B + C` one sum of three summands however each associates, while
    ///   `(A * B) * C` keeps the parenthesized product as one component. Every
    ///   component is read as a value type under the chain's frame, in written
    ///   order, and the product or the sum is planned over them; the inner
    ///   links of the chain are not read.
    /// - provides: the eager product and the sum of the fragment, each the same
    ///   core type as the braced `#{A, B}` and `+{A, B}`.
    /// - fails: yields the wrong-sort refusal where no value type is read, and
    ///   the refusal of any link of the chain out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The chain's refusal.
    ///
    /// # Termination
    /// Each round of the chain walk consumes fuel and replaces one link of the
    /// finite tree by its two operands.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product and a sum of atoms, a chain of three of
    ///   each, a parenthesized inner product, a product inside a sum and a
    ///   product where a computation type is read, each asserted as the exact
    ///   core node read back out of the arena or the exact refusal.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::Product(components) | Plan::Sum(components))) if components.end.saturating_sub(components.start) >= 2_usize
                )
        },
    )]
    fn chain(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        former: Former,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let start = self.operands.len();
        let [first, second] = halves(site, &mut cursor, former)?;
        let mut pending = Vec::from([second, first]);
        while let Some(operand) = pending.pop() {
            match self
                .fuel
                .spend()
                .and_then(|()| self.chained(site, operand, former))
            {
                Ok(Some([inner_first, inner_second])) => {
                    pending.extend([inner_second, inner_first]);
                },
                Ok(None) => self.operands.push(operand),
                Err(refusal) => {
                    self.operands.truncate(start);
                    return Err(refusal);
                },
            }
        }
        let components = Stretch {
            start,
            end: self.operands.len(),
        };
        for position in components.start .. components.end {
            if let Some(&component) = self.operands.get(position) {
                self.read(component, Reading::ValueType(frame));
            }
        }
        let plan = if former == Former::SumType {
            Plan::Sum(components)
        }
        else {
            Plan::Product(components)
        };

        self.plan(site, plan);

        Ok(())
    }

    /// The two operands of `operand` when it is an unparenthesized form of
    /// `former`, a link of the chain a form of `former` heads.
    ///
    /// # Specification
    /// - requires: `operand` is an operand of a chain of `former` at `site`.
    /// - ensures: a form of `former` answers its operands in written order; any
    ///   other node, a parenthesized one of `former` included, answers nothing.
    /// - provides: the one place a product or a sum chain is followed.
    /// - fails: a repaired or ill-shaped link in the chain yields its own
    ///   refusal; [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// The inner link's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of three and a parenthesized inner product
    ///   separate the followed link from the kept component, and a product
    ///   inside a sum is kept as one summand.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |halves| halves.is_none_or(|[first, second]| first != operand && second != operand)))]
    fn chained(
        &mut self,
        site: Site,
        operand: NodeIndex,
        former: Former,
    ) -> Result<Option<[NodeIndex; 2]>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(operand)
        else {
            return Ok(None);
        };
        let Shape::Form { name, former: link } = shape_of(self.pbg, node)?
        else {
            return Ok(None);
        };
        if link != former {
            return Ok(None);
        }
        let link = Site {
            at: Placed::of(operand, node),
            name,
            reading: site.reading,
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, operand, &mut scratch).and_then(|()| {
            if let Maybe::Present(repaired) = scratch.repair {
                return Err(repaired.refusal(name));
            }
            halves(
                link,
                &mut Cursor::new(&scratch.pieces, link.at.span),
                former,
            )
        });
        self.scratch = scratch;

        read.map(Some)
    }

    /// Classify a value function space, `A => B` or `(A1, …, An) => B`, `n`
    /// zero included.
    ///
    /// # Specification
    /// - requires: `site` is a value function space in type position, or in
    ///   value position where a type is quoted.
    /// - ensures: the alias stands as a value type; a domain list naming a
    ///   binder, `(x : A, …) => B`, is the telescope; else its domains — each
    ///   member of a parenthesised list written before `=>`, none for `()`,
    ///   else the one operand there — and its codomain are each read as value
    ///   types under its own frame, and it is planned as the thunked arrow over
    ///   them.
    /// - provides: the value function space, the alias of `+U (A1 -> … -> An ->
    ///   -F B)`, which is `+U (-F B)` at no domain.
    /// - fails: yields the wrong-sort refusal where no value type is read,
    ///   either hole's own refusal, and a domain list's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The alias's refusal.
    ///
    /// # Termination
    /// The domain loop runs once per entry of the finite domain stretch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no domain, one domain, a list of two, and an alias
    ///   nested to the right, each asserted as the same core node the thunked
    ///   arrow it stands for lowers to.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::arity::tests::a_telescope_binds_each_entry_in_the_ones_after_it`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&(Plan::ValueFunction(..) | Plan::Telescope(..)))
                )
        },
    )]
    fn value_function(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let domain = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::FAT_ARROW)?;
        let codomain = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        if self.telescope_function(site, frame, domain, codomain)? == arity::Planned(true) {
            return Ok(());
        }
        let start = self.operands.len();
        if let Err(refusal) = self.domains(domain) {
            self.operands.truncate(start);
            return Err(refusal);
        }
        let domains = Stretch {
            start,
            end: self.operands.len(),
        };
        for position in domains.start .. domains.end {
            if let Some(&each) = self.operands.get(position) {
                self.read(each, Reading::ValueType(frame));
            }
        }
        self.read(codomain.node, Reading::ValueType(frame));

        self.plan(site, Plan::ValueFunction(domains, codomain.node));

        Ok(())
    }

    /// Append the domains a value function space's domain operand writes to
    /// the operand store.
    ///
    /// # Specification
    /// - requires: `domain` is the operand written before `=>`.
    /// - ensures: nothing for the empty list `()`, so `() => C` takes no
    ///   argument; each member of an unrepaired parenthesised list of more than
    ///   one, left to right; else `domain` itself, whose own reading groups or
    ///   reports a repair.
    /// - provides: the n-ary domain of the alias, the one place a type list is
    ///   read.
    /// - fails: yields the list's refusal for a member out of shape;
    ///   [`LoweringRefusal::UnknownMold`] for a mold the grammar does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// The list's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no domain, one domain and a list of two, each
    ///   asserted through the alias it lowers.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        captures: before = self.operands.len(),
        ensures: |ret| ret.is_err() || self.operands.len() >= before,
    )]
    fn domains(
        &mut self,
        domain: Placed,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(domain.node)
        else {
            self.operands.push(domain.node);
            return Ok(());
        };
        let Shape::Form {
            name,
            former: Former::ParenthesizedType,
        } = shape_of(self.pbg, node)?
        else {
            self.operands.push(domain.node);
            return Ok(());
        };
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, domain.node, &mut scratch);
        let listed = read.and_then(|()| {
            let commas = scratch.pieces.iter().any(
                |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::COMMA),
            );
            let empty = !scratch
                .pieces
                .iter()
                .any(|piece| matches!(*piece, Piece::Operand(_)));
            if empty && let Maybe::Absent(_) = scratch.repair {
                Ok(())
            }
            else if commas && let Maybe::Absent(_) = scratch.repair {
                let list = Site {
                    at: domain,
                    name,
                    reading: Reading::Unread,
                };
                arguments(
                    list,
                    &mut Cursor::new(&scratch.pieces, domain.span),
                    &mut self.operands,
                )
            }
            else {
                self.operands.push(domain.node);
                Ok(())
            }
        });
        self.scratch = scratch;

        listed
    }

    /// Classify a static abstraction, `\A. T`.
    ///
    /// # Specification
    /// - requires: `site` is a static abstraction in term or type position.
    /// - ensures: an abstraction standing as a value binds its one type name in
    ///   a frame extending its own, untyped — the checker reads the type from
    ///   the operator's signature — reads its body as a value under that frame,
    ///   so a type written there is quoted, and is planned as the static lambda
    ///   over it.
    /// - provides: the introduction of a type operator.
    /// - fails: yields the wrong-sort refusal where no value is read, a
    ///   misplaced-tile fault for a binder out of shape, the binder policy's
    ///   refusal, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The abstraction's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one abstraction, two nested whose body names both
    ///   binders, and an abstraction where a value type is read, each asserted
    ///   as the exact core node read back out of the arena or the exact
    ///   refusal; a lowercase binder name.
    /// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
    /// - witness: `lower::tests::a_static_abstraction_binds_a_lowercase_name`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::StaticLambda(_))
                )
        },
    )]
    fn static_abstraction(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        closed(site, &mut cursor, TileName::BACKSLASH)?;
        let binder = match cursor.peek() {
            Maybe::Present(Piece::Tile { label, at })
                if label == TileName::TYPE_IDENTIFIER || label == TileName::TYPE_VARIABLE =>
            {
                let _binder = cursor.tile(label);
                at
            },
            Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
        };
        closed(site, &mut cursor, TileName::DOT)?;
        let body = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        let extended = self
            .scope
            .extend_operand(frame, name, Maybe::Present(binder.span));
        self.read(body.node, Reading::Value(Frame::Inner(extended)));

        self.plan(site, Plan::StaticLambda(body.node));

        Ok(())
    }

    /// Classify a parenthesised type, `(T)`.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised type in type position.
    /// - ensures: the one operand is read at the form's own reading and
    ///   adopted.
    /// - provides: grouping in type position.
    /// - fails: yields the empty-list refusal for `()`, which is never the unit
    ///   type, the hole's own refusal, and a misplaced-tile fault at the first
    ///   comma of a list, which only a value function space's domain reads.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — parenthesized type operands keep the surrounding
    ///   reading and lower to the wrapped type rather than introducing a core
    ///   constructor; empty parentheses are refused by name.
    /// - witness: `lower::tests::an_arrow_lowers_under_a_thunk_type`
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::tests::the_empty_parentheses_are_never_the_unit`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Transparent(child)) if self.reading(child) == site.reading)
        },
    )]
    fn parenthesized_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _open = cursor.tile(TileName::PAREN_OPEN);
        let run = cursor.operands();
        if let Run::Empty(_) = run {
            let unit = Site {
                name: FormName::UNIT,
                ..site
            };
            return Err(unit.out(FragmentBoundary::EmptyList));
        }
        let inner = site.one(run)?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        self.read(inner.node, site.reading);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// How `position` is read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored reading; an absent position
    ///   is unread.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — paired declarations and refused siblings retain
    ///   distinct readings through the ascending classification sweep.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[spec(
        ensures: |ret| {
            ret == self
                .readings
                .get(usize::from(position))
                .copied()
                .unwrap_or(Reading::Unread)
        },
    )]
    fn reading(
        &self,
        position: NodeIndex,
    ) -> Reading
    {
        self.readings
            .get(usize::from(position))
            .copied()
            .unwrap_or(Reading::Unread)
    }

    /// Read `position` as `reading`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position takes the supplied reading without resizing
    ///   the table; an absent position changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signatures, definitions and nested binder bodies
    ///   receive their own expected sorts and frames.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
    #[spec(
        captures: count = self.readings.len(),
        ensures: |_| {
            self.readings.len() == count
                && self
                    .readings
                    .get(usize::from(position))
                    .is_none_or(|held| *held == reading)
        },
    )]
    fn read(
        &mut self,
        position: NodeIndex,
        reading: Reading,
    )
    {
        if let Some(held) = self.readings.get_mut(usize::from(position)) {
            *held = reading;
        }
        // A value a type reads — a type-position call's argument — stands in
        // that type's telescope, which the enclosing type carries as a whole.
        if let (Reading::Value(_), Family::Type) = (reading, self.reader.family()) {
            let _first = self.type_read.insert(position);
        }
    }

    /// Record `plan` for the form at `site`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position takes the supplied plan without resizing the
    ///   table; an absent position changes nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — literals, applications and quoted types preserve
    ///   their planned former through the minting sweep; their concrete
    ///   operands are checked by the consumer witnesses rather than copied into
    ///   a snapshot.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    #[spec(
        captures: before = (self.plans.len(), core::mem::discriminant(&plan)),
        ensures: |_| {
            self.plans.len() == before.0
                && self
                    .plans
                    .get(usize::from(site.at.node))
                    .is_none_or(|held| core::mem::discriminant(held) == before.1)
        },
    )]
    fn plan(
        &mut self,
        site: Site,
        plan: Plan,
    )
    {
        if let Some(held) = self.plans.get_mut(usize::from(site.at.node)) {
            *held = plan;
        }
    }

    /// The source text of `placed`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a node with a source fragment yields that fragment; an absent
    ///   fragment yields empty text.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source literal text is interpreted at its own syntax
    ///   node and malformed lexemes retain their exact refusal span.
    /// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
    /// - witness: `lower::tests::a_malformed_text_literal_is_refused`
    #[spec(
        ensures: |ret| {
            self.tree.fragment(placed.node).map_or_else(
                || ret.as_ref().is_empty(),
                |fragment| ret.as_ref() == fragment.as_ref(),
            )
        },
    )]
    fn text_at(
        &self,
        placed: Placed,
    ) -> SourceFragment<'source>
    {
        self.tree
            .fragment(placed.node)
            .unwrap_or_else(|| SourceFragment::from(""))
    }

    /// The name `placed` spells.
    ///
    /// # Specification
    /// trivial.
    fn name_at(
        &self,
        placed: Placed,
    ) -> SurfaceName<'source>
    {
        SurfaceName::from(self.text_at(placed))
    }

    /// The descending sweep: mint every planned node and record its origin.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: every type a manifest type component or a type member names
    ///   is minted first, one at a time in source order, each subtree
    ///   descending, so a type head that stands for one adopts a type already
    ///   minted wherever it sits; every functor application is renamed before
    ///   the first of those types written after it, so an instance's manifest
    ///   type is minted before a type naming it; every function result a
    ///   synthesised `cong` reads its codomain off, then every answer type a
    ///   match reads its motive from, is minted next, the same way, so a `cong`
    ///   in a type and a match deeper than its function's result find that
    ///   result minted, and every application not yet renamed is renamed. Every
    ///   other planned node is then minted, with its children already minted
    ///   because the level-order layout puts them at strictly higher positions;
    ///   every minted node gets an origin naming the syntax node that produced
    ///   it, terms and types alike, while an adopted child keeps its own. A
    ///   node whose position bridges its sort has the bridge minted over its
    ///   own core node, with the same syntax node's origin marked as inserted.
    ///   A node under a declaration that refused is not minted, and neither is
    ///   any node above it, unless it lies inside an attribute payload: the
    ///   side table files a payload whatever its declaration's outcome, so an
    ///   expectation about a refused declaration stays readable. Last, the body
    ///   of every witness of a member whose member and own type are unrefused
    ///   is minted as that member's constant, its origin the form that stated
    ///   the second type.
    /// - provides: the whole allocation half of the lowering.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the sweep outruns the
    ///   allowance; nothing else, because every decision was made ascending.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest component named before and after its own
    ///   position in the tree, and a witness agreeing and disagreeing with its
    ///   member, each asserted through the checker's verdict.
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `tests::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body carries out the plan of every node once; the check reads each plan once"
        )
    )]
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || self.plans.iter().enumerate().all(|(position, plan)| {
                    let position = NodeIndex::from(position);
                    (self.collected.refused(position).0 && !self.in_payload(position).0)
                        || *plan == Plan::Unplanned
                        || self.taken.get(usize::from(position)) == Some(&true)
                })
        },
    )]
    fn mint(
        &mut self,
        sink: &mut Sink<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let from = self.current;
        let owns =
            |position: &NodeIndex| self.source_of.get(usize::from(*position)) == Some(&from.source);
        let mut stated: Vec<Placed> = self
            .collected
            .structures
            .iter()
            .skip(from.structures)
            .flat_map(|structure| structure.types.iter().chain(&structure.type_members))
            .filter_map(|component| match component.meaning {
                TypeMeaning::Manifest(defined) => Some(defined),
                TypeMeaning::Sealed | TypeMeaning::Family(_) | TypeMeaning::Instantiated { .. } => {
                    None
                },
            })
            .chain(self.collected.families.iter().skip(from.families).flat_map(|family| {
                family
                    .parameters
                    .iter()
                    .map(|parameter| parameter.classifier)
                    .chain(core::iter::once(family.defined))
            }))
            // A data family's parameter types classify the constructors
            // written as its arguments, wherever those stand in the tree.
            .chain(
                self.argued
                    .iter()
                    .filter(|&(argument, _)| owns(argument))
                    .filter_map(|(_, argued)| self.collected.data.get(argued.form))
                    .flat_map(|form| form.parameters.iter().map(|parameter| parameter.classifier)),
            )
            .collect();
        stated.sort_unstable_by_key(|defined| (defined.span.start(), defined.node));
        stated.dedup();
        let mut manifests: Vec<NodeIndex> = stated.iter().map(|defined| defined.node).collect();
        manifests.extend(self.synthesised_types());
        manifests.extend(
            self.answers
                .iter()
                .filter(|&(position, _)| owns(position))
                .map(|(_, answer)| answer.node),
        );
        manifests.extend(
            self.inherited
                .iter()
                .filter(|&(position, _)| owns(position))
                .filter_map(|(_, inherited)| match *inherited {
                    native::Classifier::Written(written) => Some(written),
                    native::Classifier::Answered { .. }
                    | native::Classifier::Slot(_)
                    | native::Classifier::Inserted => None,
                }),
        );
        manifests.reverse();
        let mut subtree: Vec<NodeIndex> = Vec::new();
        let mut work: Vec<NodeIndex> = Vec::new();
        while let Some(root) = manifests.pop() {
            if let Some(node) = self.tree.node(root) {
                self.rename_instances_before(Maybe::Present(node.span().start()), sink);
            }
            subtree.clear();
            work.push(root);
            while let Some(position) = work.pop() {
                self.fuel.spend()?;
                subtree.push(position);
                work.extend(self.tree.children(position));
            }
            subtree.sort_unstable_by(|left, right| right.cmp(left));
            for &position in &subtree {
                self.mint_at(position, sink);
            }
        }
        self.rename_instances_before(
            Maybe::Absent(functor::renamed_through::Absent::Everything),
            sink,
        );
        let mut remaining = self.own.len();
        while let Some(next) = remaining.checked_sub(1_usize) {
            remaining = next;
            self.fuel.spend()?;
            let Some(&position) = self.own.get(next)
            else {
                continue;
            };
            self.mint_at(position, sink);
        }
        for (position, slot) in self.collected.slots.iter().enumerate().skip(from.slots) {
            if let Maybe::Present(Half {
                declaration,
                operand: Operand::Member(target),
            }) = slot.definition
                && let Maybe::Absent(_) = slot.refusal
                && let Some(member) = self.collected.slots.get(usize::from(target))
                && let Maybe::Absent(_) = member.refusal
                && let Maybe::Present(origin) = self.origin_at(declaration.node)
            {
                let id = sink.arena.value_constant(member.constant);
                let _minted = sink.value(id, origin);
                let _replaced = self.witnessed.insert(SlotIndex::from(position), id);
            }
        }
        self.record_labels(sink);

        Ok(())
    }

    /// Record every label planned against an entry that lowered, with what
    /// it names.
    ///
    /// # Specification
    /// - requires: every node is minted or absent.
    /// - ensures: one label per planned site whose entry lowered: a type's at
    ///   the type, with the names of the frames its entry is read under that
    ///   bind in the telescope the type counts its binders in, outermost first;
    ///   a term's at the term.
    /// - fails: never; a site whose entry did not lower records nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a record type's, a record's and a dependent arrow's
    ///   labels are each recorded with what they label.
    /// - witness: `lower::arity::tests::each_label_names_what_it_labels`
    #[spec(captures: before = sink.origins.labels().len(), ensures: sink.origins.labels().len() <= before.saturating_add(self.labels.len()))]
    fn record_labels(
        &self,
        sink: &mut Sink<'_>,
    )
    {
        let named = |frame: Frame, held: NodeIndex| -> Vec<String> {
            self.scope
                .telescope_names(frame, self.telescope_at(held))
                .into_iter()
                .map(|name| String::from(name.as_ref()))
                .collect()
        };
        for site in self.labels.iter().skip(self.current.labels) {
            let labelled = match site.read {
                LabelRead::ValueType(frame) => match self.value_type_at(site.held) {
                    Maybe::Present(ty) => Labelled::ValueType {
                        ty,
                        context: named(frame, site.held),
                    },
                    Maybe::Absent(_) => continue,
                },
                LabelRead::CompType(frame) => match self.comp_type_at(site.held) {
                    Maybe::Present(ty) => Labelled::CompType {
                        ty,
                        context: named(frame, site.held),
                    },
                    Maybe::Absent(_) => continue,
                },
                LabelRead::Term => match self.value_at(site.held) {
                    Maybe::Present(value) => Labelled::Value(value),
                    Maybe::Absent(_) => continue,
                },
            };
            sink.origins.record_label(Label {
                span: site.written,
                labelled,
            });
        }
    }

    /// Keep the label written at `written` against the entry at `held`, read
    /// as `read`, for [`Self::record_labels`].
    ///
    /// # Specification
    /// trivial.
    fn labelled(
        &mut self,
        written: ByteSpan,
        held: NodeIndex,
        read: LabelRead,
    )
    {
        self.labels.push(LabelSite {
            written,
            held,
            read,
        });
    }

    /// Mint the node at `position` by its plan, once.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the node's plan is carried out once, its bridge written over
    ///   it and the result kept as the node's lowered core node; the force over
    ///   the value head of a call of no arguments is that call, so it is minted
    ///   with the call's origin rather than as an insertion at the head; a tail
    ///   whose exit was inferred and minted as a computation is recorded with
    ///   that exit, `return` when the bridge is the inserted one and `become`
    ///   otherwise; a `return` crossing a handler's frame is minted as the
    ///   capture [`Self::unwind`] writes, and that capture recorded as the
    ///   exit; a `break`'s returner is recorded as a break; a loop end written
    ///   without an exit is bound and its loop run again, as [`Self::rerun`]
    ///   writes it; a constructor awaiting its data family's application is
    ///   left for that application, which mints it first; a node with no plan,
    ///   or whose plan was carried out, or under a refused declaration outside
    ///   a payload, is left as it is.
    /// - provides: the per-position half of [`Self::mint`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused declaration leaves its ordinary plans
    ///   untouched but still permits its attribute payloads to mint;
    ///   carried-out plans are not minted twice when a manifest and the full
    ///   traversal both reach them; a tail of each polarity records its own
    ///   exit once; a call of no arguments answers at the call, its head at the
    ///   head.
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `lower::tests::a_call_of_no_arguments_is_the_call_the_source_wrote_364`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    /// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    #[spec(
        captures: before = (
            (self.collected.refused(position).0 && !self.in_payload(position).0)
                || self.awaiting.contains(&position),
            matches!(
                self.plans.get(usize::from(position)),
                None | Some(&Plan::Unplanned)
            ) || self.taken.get(usize::from(position)) == Some(&true),
            self.lowered_at(position),
            self.plans.len(),
            self.lowered.len(),
        ),
        ensures: self.plans.len() == before.3
            && self.lowered.len() == before.4
            && (if before.0 || before.1 {
                self.lowered_at(position) == before.2
            }
            else {
                self.taken.get(usize::from(position)) == Some(&true)
            }),
    )]
    fn mint_at(
        &mut self,
        position: NodeIndex,
        sink: &mut Sink<'_>,
    )
    {
        if self.collected.refused(position).0 && !self.in_payload(position).0 {
            return;
        }
        // A constructor classified by its place in a data family's application
        // waits for the application, which mints it once every argument
        // before it is minted.
        if self.awaiting.contains(&position) {
            return;
        }
        if let Some(&Plan::Data(_, arguments)) = self.plans.get(usize::from(position)) {
            for place in arguments.start .. arguments.end {
                if let Some(&argument) = self.operands.get(place)
                    && self.awaiting.remove(&argument)
                {
                    self.mint_planned(argument, sink);
                }
            }
        }
        self.mint_planned(position, sink);
    }

    /// Mint the node at `position` by its plan, once, whatever declaration or
    /// application it waits on: [`Self::mint_at`]'s mint itself.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the plan is carried out once, as [`Self::mint_at`] states,
    ///   and kept; a type a term quotes is carried from its telescope into the
    ///   term's context before the quote wraps it, while a value a type reads
    ///   stays in the type's telescope; a node with no plan, or whose plan was
    ///   carried out, is left as it is.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constructor awaiting its family's application is
    ///   minted at its slot's type once the application reaches it, and a type
    ///   quoted in a body past an unmentioned parameter reads its binders at
    ///   their indices in the body; a grouped type head stands for what it
    ///   groups.
    /// - witness: `lower::native::tests::a_constructor_takes_its_slot_as_a_family_argument_421`
    /// - witness: `lower::tests::a_quote_in_a_body_reads_past_an_unmentioned_parameter`
    /// - witness: `lower::tests::a_type_head_answers_at_what_it_stands_for`
    #[spec(
        captures: before = (
            matches!(
                self.plans.get(usize::from(position)),
                None | Some(&Plan::Unplanned)
            ) || self.taken.get(usize::from(position)) == Some(&true),
            self.lowered_at(position),
            self.plans.len(),
            self.lowered.len(),
        ),
        ensures: self.plans.len() == before.2
            && self.lowered.len() == before.3
            && (if before.0 {
                self.lowered_at(position) == before.1
            }
            else {
                self.taken.get(usize::from(position)) == Some(&true)
            }),
    )]
    fn mint_planned(
        &mut self,
        position: NodeIndex,
        sink: &mut Sink<'_>,
    )
    {
        let Some(taken) = self.taken.get_mut(usize::from(position))
        else {
            return;
        };
        if core::mem::replace(taken, true) {
            return;
        }
        let Some(plan) = self.plans.get(usize::from(position))
        else {
            return;
        };
        if *plan == Plan::Unplanned {
            return;
        }
        let Maybe::Present(origin) = self.origin_at(position)
        else {
            return;
        };
        let bridge = self
            .bridges
            .get(usize::from(position))
            .copied()
            .unwrap_or(Bridge::Bare);
        let stands_in = matches!(*plan, Plan::Transparent(_) | Plan::Instantiated(..))
            && self.stand_ins.contains(&position);
        let minted = self.mint_plan(plan, sink, origin);
        if stands_in && let Maybe::Present(Lowered::ValueType(id)) = minted {
            sink.origins.record_stand_in(id, origin);
        }
        // A type a term quotes was minted in its telescope, which counts a
        // typed binder only once a type names it; the term's context binds
        // every binder, so the quote is carried into it (#540). A body's quote
        // counts in its own telescope, which its reads extend without making
        // the signature's arrows dependent (#547). A value a type reads stays
        // in that type's telescope.
        let minted = match (bridge, minted) {
            (Bridge::Inserted(Insertion::Quote), Maybe::Present(Lowered::ValueType(quoted)))
                if !self.type_read.contains(&position) && !self.in_type.contains(&position) =>
            {
                let frame = self.reading(position).frame();
                Maybe::Present(Lowered::ValueType(self.relocate_value_type(
                    quoted,
                    frame,
                    Telescope::Quote,
                    sink,
                    origin,
                )))
            },
            (Bridge::Inserted(Insertion::Quote), Maybe::Present(Lowered::CompType(quoted)))
                if !self.type_read.contains(&position) && !self.in_type.contains(&position) =>
            {
                let frame = self.reading(position).frame();
                Maybe::Present(Lowered::CompType(self.relocate_comp_type(
                    quoted,
                    frame,
                    Telescope::Quote,
                    sink,
                    origin,
                )))
            },
            (_, minted) => minted,
        };
        // A call of no arguments is its head's force, so that force is the
        // call the source wrote: it answers at the call, not at the head.
        let called = self
            .nullary
            .get(&position)
            .map(|&call| self.origin_at(call));
        let bridged = match (bridge, minted, called) {
            (
                Bridge::Inserted(Insertion::Force),
                Maybe::Present(Lowered::Value(forced)),
                Some(Maybe::Present(call)),
            ) => {
                let id = sink.arena.computation_force(forced);
                Maybe::Present(sink.computation(id, call))
            },
            (_, minted, _) => sink.bridge(minted, bridge, origin),
        };
        let bridged = match bridged {
            Maybe::Present(Lowered::Computation(returned)) if self.crossing.contains(&position) => {
                Maybe::Present(Lowered::Computation(Self::unwind(sink, returned, origin)))
            },
            bridged @ (Maybe::Present(_) | Maybe::Absent(_)) => bridged,
        };
        if self.leaving.contains(&position)
            && let Maybe::Present(Lowered::Computation(exit)) = bridged
        {
            let _first = sink.exits.insert(exit);
            if self.inferred.contains(&position) {
                self.elided.push((position, match bridge {
                    Bridge::Inserted(Insertion::Return) => Exit::Return,
                    Bridge::Bare | Bridge::Inserted(_) => Exit::Become,
                }));
            }
        }
        if self.breaking.contains(&position)
            && let Maybe::Present(Lowered::Computation(broken)) = bridged
        {
            let _first = sink.breaks.insert(broken);
        }
        let bridged = match (self.reentered.get(&position), bridged) {
            (Some(&own), Maybe::Present(Lowered::Computation(end))) => Maybe::Present(
                Lowered::Computation(self.rerun(position, end, own, sink, origin)),
            ),
            (_, bridged) => bridged,
        };
        if let Some(held) = self.lowered.get_mut(usize::from(position)) {
            *held = bridged;
        }
    }

    /// The origin of a core node the syntax node at `position` wrote.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live syntax node yields its own position and span as
    ///   written provenance; a missing node is unminted.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each minted family records the syntax origin that
    ///   produced it, independently of inserted bridges.
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == self
                .tree
                .node(position)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |node| {
                    Maybe::Present(Origin::new(position, node.span()))
                })
        },
    )]
    fn origin_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<Origin, lowered::Absent>
    {
        self.tree
            .node(position)
            .map_or(Maybe::Absent(lowered::Absent::Unminted), |node| {
                Maybe::Present(Origin::new(position, node.span()))
            })
    }

    /// Carry out one plan.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the plan's core node, minted over its children's lowered
    ///   nodes with its origin recorded; an adopted child's own node for a
    ///   transparent plan; nothing when a child did not lower at the sort the
    ///   plan takes. A variable is minted in its binder's zone: the linear zone
    ///   for a fork's end, the intuitionistic zone for every other binder; a
    ///   decode's code carries the written origin and its type the inserted
    ///   one.
    /// - provides: the per-node half of [`Self::mint`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the admitted plan families lower to their matching
    ///   core families; grouping reuses its child result and an unplanned node
    ///   cannot manufacture a value. Concrete constructors and origins are
    ///   witnessed through complete declarations and the fragment-specific
    ///   examples.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        captures: promised = (
            match *plan {
                | Plan::Variable(..)
                | Plan::ValueHole(_)
                | Plan::Constant(_)
                | Plan::Primitive(_)
                | Plan::Unit
                | Plan::Literal(_)
                | Plan::StaticApplication(..)
                | Plan::Tuple(_)
                | Plan::Record(_)
                | Plan::Injection(..)
                | Plan::StaticLambda(_)
                | Plan::Thunk(_)
                | Plan::Here(_)
                | Plan::Funext(..)
                | Plan::Equiv(..)
                | Plan::Univalence(_)
                | Plan::PathProduct(..)
                | Plan::Ua { .. }
                | Plan::ListNil
                | Plan::ListCons(..)
                | Plan::Run(_)
                | Plan::SessionRelated(..)
                | Plan::Stay(_)
                | Plan::Forward(_)
                | Plan::FunctionFlow(..)
                | Plan::FlowProduct(..)
                | Plan::Recorded(_)
                | Plan::Constructor(_) => Some(Produced::Value),
                | Plan::CompHole(_) | Plan::PrimitiveCall(..) | Plan::Return(_) | Plan::Force(_) | Plan::Lambda(..) | Plan::Block(_) | Plan::Loop(_) | Plan::While(..) | Plan::Break | Plan::Reenter(_) | Plan::Application(..) | Plan::Called(..) | Plan::Case(_) | Plan::EmptyCase(_) | Plan::Copattern(_) | Plan::Observe(..) | Plan::Select(..) | Plan::Derived(_) | Plan::Transport(..) | Plan::TelescopeTransport(_) | Plan::Exercise(_) | Plan::Scope(_) | Plan::Resume(..) | Plan::Action(..) | Plan::Access(_) | Plan::Ride(..) | Plan::FlowThen(..) | Plan::World(world::Worlded::Hold { .. } | world::Worlded::Migrate { .. }) => {
                    Some(Produced::Computation)
                },
                | Plan::Atom(_)
                | Plan::Sealed(_)
                | Plan::Instantiated(..)
                | Plan::Universe(_)
                | Plan::ValueFunction(..)
                | Plan::Telescope(..)
                | Plan::StaticPi(..)
                | Plan::Product(..)
                | Plan::RecordType(..)
                | Plan::Sum(_)
                | Plan::Former(TypeFormer::Thunk | TypeFormer::List | TypeFormer::Run, _)
                | Plan::Path(..)
                | Plan::Flow(..)
                | Plan::Relation(..)
                | Plan::Stack(..)
                | Plan::Data(..)
                | Plan::Expansion(..)
                | Plan::Capability(..)
                | Plan::Session(..)
                | Plan::World(world::Worlded::At { .. }) => Some(Produced::ValueType),
                | Plan::Arrow(..) | Plan::DependentArrow(..) | Plan::With(_) | Plan::Former(TypeFormer::Returner, _) | Plan::Effectful(..) => {
                    Some(Produced::CompType)
                },
                | Plan::Decode(_, _, universe) | Plan::Unquote(_, _, universe) => Some(match universe.sort {
                    | GroundSort::Value => Produced::ValueType,
                    | GroundSort::Computation => Produced::CompType,
                }),
                | Plan::Unplanned | Plan::Transparent(_) | Plan::Function(_) => None,
            },
            match *plan {
                | Plan::Transparent(child) => Some(self.lowered_at(child)),
                | _ => None,
            },
            matches!(plan, Plan::Unplanned),
            matches!(plan, Plan::Function(_)),
        ),
        ensures: |ret| {
            promised.1.map_or_else(
                || {
                    if promised.2 {
                        ret == Maybe::Absent(lowered::Absent::Unminted)
                    }
                    else if promised.3 {
                        matches!(
                            ret,
                            Maybe::Absent(_) | Maybe::Present(Lowered::Function { .. })
                        )
                    }
                    else {
                        matches!(
                            (promised.0, ret),
                            (Some(_), Maybe::Absent(_))
                                | (Some(Produced::Value), Maybe::Present(Lowered::Value(_)))
                                | (
                                    Some(Produced::Computation),
                                    Maybe::Present(Lowered::Computation(_))
                                )
                                | (
                                    Some(Produced::ValueType),
                                    Maybe::Present(Lowered::ValueType(_))
                                )
                                | (
                                    Some(Produced::CompType),
                                    Maybe::Present(Lowered::CompType(_))
                                )
                        )
                    }
                },
                |child| ret == child,
            )
        },
    )]
    fn mint_plan(
        &self,
        plan: &Plan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match *plan {
            Plan::ValueHole(hole) => {
                let id = sink.arena.value_hole(hole);
                Maybe::Present(sink.value(id, origin))
            },
            Plan::CompHole(hole) => {
                let id = sink.arena.computation_hole(hole);
                Maybe::Present(sink.computation(id, origin))
            },
            Plan::Primitive(primitive) => {
                let id = primitive.thunk(sink.arena);
                if let Some(&Value::Primitive { body, .. }) = sink.arena.value(id) {
                    let mut current = body;
                    let mut ancestors = [body; 3];
                    let mut count = 0_usize;
                    for ancestor in &mut ancestors {
                        *ancestor = current;
                        count = count.saturating_add(1);
                        match sink.arena.computation(current) {
                            Some(&Computation::Lambda(inner)) => current = inner,
                            Some(&Computation::Primitive { ref arguments, .. }) => {
                                for &argument in arguments.iter().rev() {
                                    sink.origins.record_value(argument, origin);
                                }
                                break;
                            },
                            _ => break,
                        }
                    }
                    for &computation in ancestors.iter().take(count).rev() {
                        sink.origins.record_computation(computation, origin);
                    }
                }
                Maybe::Present(sink.value(id, origin))
            },
            Plan::PrimitiveCall(primitive, arguments) => {
                use gandr_core_term::primitive::Arguments;
                let arguments = match arguments {
                    Arguments::Unary(argument) => self.value_at(argument).map(Arguments::Unary),
                    Arguments::Binary([first, second]) => self.value_at(first).and_then(|first| {
                        self.value_at(second)
                            .map(|second| Arguments::Binary([first, second]))
                    }),
                };
                arguments.map(|arguments| {
                    let id = sink.arena.computation_primitive(primitive, arguments);
                    sink.computation(id, origin)
                })
            },
            Plan::Unplanned => Maybe::Absent(lowered::Absent::Unminted),
            Plan::Variable(index, binder) => {
                let id = sink.arena.value_variable(self.scope.zone(binder), index);
                if let Maybe::Present(site) = self.scope.site(binder) {
                    sink.origins.record_binding(id, site);
                }
                Maybe::Present(sink.value(id, origin))
            },
            Plan::Constant(constant) => {
                let id = sink.arena.value_constant(constant);
                Maybe::Present(sink.value(id, origin))
            },
            Plan::Unit => {
                let id = sink.arena.value_unit();
                Maybe::Present(sink.value(id, origin))
            },
            Plan::Literal(ref literal) => {
                let id = sink.arena.value_literal(literal.clone());
                Maybe::Present(sink.value(id, origin))
            },
            Plan::Atom(atom) => Maybe::Present(sink.atom(atom, origin)),
            Plan::Instantiated(instance, defined) => self
                .instance_types
                .get(&(instance, defined))
                .copied()
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |id| {
                    Maybe::Present(Lowered::ValueType(id))
                }),
            Plan::Sealed(atom) => {
                let id = sink.arena.value_type_abstract(atom);
                sink.origins.record_value_type(id, origin);
                Maybe::Present(Lowered::ValueType(id))
            },
            Plan::Universe(universe) => {
                let id = sink.arena.value_type_universe(
                    Sort::Ground(universe.sort),
                    Level::constant(universe.level),
                );
                sink.origins.record_value_type(id, origin);
                Maybe::Present(Lowered::ValueType(id))
            },
            Plan::Decode(code, arguments, universe) => {
                self.mint_decode(code, arguments, universe, sink, origin)
            },
            Plan::Unquote(code, arguments, universe) => {
                self.mint_unquote(code, arguments, universe, sink, origin)
            },
            Plan::Called(code, arguments) => self
                .mint_called(code, arguments, sink, origin)
                .map(Lowered::Computation),
            Plan::StaticApplication(code, arguments) => self
                .mint_code(code, arguments, sink, origin)
                .map(Lowered::Value),
            Plan::Tuple(members) => self.mint_tuple(members, sink, origin),
            Plan::Record(ref fields) => self.mint_record(fields, sink, origin),
            Plan::Injection(summand, body) => self.mint_injection(summand, body, sink, origin),
            Plan::ValueFunction(domains, codomain) => {
                self.mint_value_function(domains, codomain, sink, origin)
            },
            Plan::Telescope(entries, codomain) => {
                self.mint_telescope(entries, codomain, sink, origin)
            },
            Plan::DependentArrow(entries, codomain) => {
                self.mint_dependent_arrow(entries, codomain, sink, origin)
            },
            Plan::Transparent(child) => self.lowered_at(child),
            Plan::Former(former, argument) => self.mint_former(former, argument, sink, origin),
            Plan::Application(head, arguments) => {
                self.mint_application(head, arguments, sink, origin)
            },
            Plan::Function(function) => self.mint_function(&function, sink, origin),
            Plan::Data(constant, arguments) => self.mint_family(constant, arguments, sink, origin),
            Plan::Expansion(family, arguments) => {
                self.mint_expansion(family, arguments, sink, origin)
            },
            Plan::Constructor(constructed) => self.mint_constructor(constructed, sink, origin),
            Plan::Case(case) => self.mint_case(case, sink, origin),
            Plan::EmptyCase(scrutinee) => self.value_at(scrutinee).map(|scrutinised| {
                let id = sink.arena.computation_case(scrutinised, &[]);
                sink.computation(id, origin)
            }),
            Plan::Product(components) => self.mint_product(components, sink, origin),
            Plan::RecordType(ref fields, binders, last) => {
                self.mint_labelled_type(fields, binders, last, sink, origin)
            },
            Plan::Sum(summands) => self.mint_sum(summands, sink, origin),
            Plan::With(entries) => self.mint_with(entries, sink, origin),
            Plan::Copattern(clauses) => self.mint_copattern(clauses, sink, origin),
            Plan::Observe(subject, observed) => self.mint_observe(subject, observed, sink, origin),
            Plan::Select(subject, selected) => self.mint_select(subject, selected, sink, origin),
            Plan::Block(block) => self.mint_block(block, sink).map(Lowered::Computation),
            Plan::Loop(body) => self.mint_loop(body, sink, origin),
            Plan::While(condition, body) => self.mint_while(condition, body, sink, origin),
            Plan::Break => {
                let unit = sink.arena.value_unit();
                sink.origins.record_value(unit, origin);
                let id = sink.arena.computation_return(unit);
                Maybe::Present(sink.computation(id, origin))
            },
            Plan::Reenter(index) => {
                let own = sink.arena.value_variable(Zone::Intuitionistic, index);
                sink.origins.record_value(own, origin);
                let id = sink.arena.computation_force(own);
                Maybe::Present(sink.computation(id, origin))
            },
            Plan::Derived(derived) => self.mint_derived(derived, sink, origin),
            Plan::TelescopeTransport(transported) => {
                self.mint_telescope_transport(transported, sink, origin)
            },
            Plan::Capability(ref authority, grade, region) => {
                Self::mint_capability(authority, grade, region, sink, origin)
            },
            Plan::Effectful(ref row, argument) => self.mint_effectful(row, argument, sink, origin),
            Plan::Exercise(ref exercised) => self.mint_exercise(exercised, sink, origin),
            Plan::Scope(ref scoped) => self.mint_scope(scoped, sink, origin),
            Plan::Resume(continuation, reply) => {
                self.mint_resume(continuation, reply, sink, origin)
            },
            Plan::Session(ref protocol, payloads, ref written) => {
                self.mint_session(protocol, payloads, written, sink, origin)
            },
            Plan::Action(ref action, subject, ref arms) => {
                self.mint_action(action, (subject, arms), sink, origin)
            },
            Plan::Access(accessed) => self.mint_access(accessed, sink, origin),
            Plan::World(worlded) => self.mint_world(worlded, sink, origin),
            Plan::Recorded(ref moves) => self.mint_recorded(moves, sink, origin),
            Plan::Ride(motive, flow, value) => self.mint_ride((motive, flow, value), sink, origin),
            Plan::FlowThen(first, second) => self.mint_flow_then(first, second, sink, origin),
            Plan::Relation(relation, left, right) => {
                self.mint_relation(relation, [left, right], sink, origin)
            },
            Plan::Arrow(..)
            | Plan::StaticPi(..)
            | Plan::Path(..)
            | Plan::Flow(..)
            | Plan::Stack(..)
            | Plan::SessionRelated(..)
            | Plan::Stay(_)
            | Plan::Forward(_)
            | Plan::FunctionFlow(..)
            | Plan::FlowProduct(..)
            | Plan::StaticLambda(_)
            | Plan::Thunk(_)
            | Plan::Here(_)
            | Plan::Funext(..)
            | Plan::Equiv(..)
            | Plan::Univalence(_)
            | Plan::PathProduct(..)
            | Plan::Ua { .. }
            | Plan::ListNil
            | Plan::ListCons(..)
            | Plan::Transport(..)
            | Plan::Return(_)
            | Plan::Force(_)
            | Plan::Run(_)
            | Plan::Lambda(..) => self.mint_over(plan, sink, origin),
        }
    }

    /// Mint a code: its head, applied statically to the arguments `arguments`
    /// names in the operand store, left to right.
    ///
    /// # Specification
    /// - requires: every type position has been classified, so every binder a
    ///   code names is recorded as mentioned; every argument is already minted
    ///   or absent.
    /// - ensures: a binder's head is the variable at its telescope index from
    ///   the use site and a declaration's the constant; `h(v1, …, vn)` mints as
    ///   `sapp(… sapp(h, v1) …, vn)`, every node with the written origin;
    ///   nothing is minted when an argument did not lower.
    /// - provides: the head of a decode and the value of a static application.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Both loops run once per entry of the finite stretch `arguments`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare binder, a bare declaration, and an operator
    ///   applied to one and to three arguments, each asserted as the exact core
    ///   node read back out of the arena.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(id) => match sink.arena.value(id) {
                | Some(&gandr_core_term::Value::StaticApplication(..)) => {
                    arguments.start < arguments.end
                },
                | Some(
                    &(gandr_core_term::Value::Variable { .. }
                    | gandr_core_term::Value::Constant(_)),
                ) => arguments.start >= arguments.end,
                | _ => false,
            },
            | Maybe::Absent(_) => true,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — bound and constant codes are applied to their
    ///   arguments in source order; every node in the static application spine
    ///   records the written origin, rather than an inserted decode origin.
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| match stretch(&self.operands, arguments)
            .iter()
            .find_map(|&argument| match self.value_at(argument) {
                | Maybe::Present(_) => None,
                | Maybe::Absent(reason) => Some(reason),
            }) {
            | Some(reason) => ret == Maybe::Absent(reason),
            | None => {
                matches!(ret, Maybe::Present(id) if sink.origins.value(id) == Maybe::Present(origin))
            },
        },
    )]
    fn mint_code(
        &self,
        code: Code,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        let written = stretch(&self.operands, arguments);
        for &argument in written {
            if let Maybe::Absent(reason) = self.value_at(argument) {
                return Maybe::Absent(reason);
            }
        }
        let mut applied = match code {
            Code::Bound {
                from,
                binder,
                telescope,
            } => sink.arena.value_variable(
                Zone::Intuitionistic,
                self.scope.index_in(from, binder, telescope),
            ),
            Code::Constant(constant) => sink.arena.value_constant(constant),
        };
        sink.origins.record_value(applied, origin);
        for &argument in written {
            let Maybe::Present(passed) = self.value_at(argument)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            applied = sink.arena.value_static_application(applied, passed);
            sink.origins.record_value(applied, origin);
        }

        Maybe::Present(applied)
    }

    /// Carry out a decode's plan: the code, and the type it denotes.
    ///
    /// # Specification
    /// - requires: as [`Self::mint_code`] does.
    /// - ensures: the code [`Self::mint_code`] mints, with the written origin;
    ///   the type is the decode of that code at the universe's level, a value
    ///   type for the value sort and a computation type for the computation
    ///   sort, with the origin marked inserted; nothing when the code did not
    ///   lower.
    /// - provides: the decode half of a value name, bare or applied, in type
    ///   position.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decode at each sort, of a bare code and of an
    ///   applied one, each asserted as the exact core type read back out of the
    ///   arena.
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::a_static_application_decodes_where_its_operator_says_or_where_it_stands`
    #[spec(
        ensures: |ret| match (ret, universe.sort) {
            | (Maybe::Present(Lowered::ValueType(id)), GroundSort::Value) => {
                matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Element { .. })
                )
            },
            | (Maybe::Present(Lowered::CompType(id)), GroundSort::Computation) => {
                matches!(
                    sink.arena.comp_type(id),
                    Some(&gandr_core_term::CompType::Element { .. })
                )
            },
            | (Maybe::Absent(_), _) => true,
            | _ => false,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — decoding uses the code’s written universe when
    ///   available and marks the element node as inserted, retaining the code’s
    ///   own origin.
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    #[spec(
        ensures: |ret| match stretch(&self.operands, arguments)
            .iter()
            .find_map(|&argument| match self.value_at(argument) {
                | Maybe::Present(_) => None,
                | Maybe::Absent(reason) => Some(reason),
            }) {
            | Some(reason) => ret == Maybe::Absent(reason),
            | None => match (universe.sort, ret) {
                | (GroundSort::Value, Maybe::Present(Lowered::ValueType(id))) => {
                    sink.origins.value_type(id)
                        == Maybe::Present(origin.inserted(Insertion::Decode))
                },
                | (GroundSort::Computation, Maybe::Present(Lowered::CompType(id))) => {
                    sink.origins.comp_type(id) == Maybe::Present(origin.inserted(Insertion::Decode))
                },
                | _ => false,
            },
        },
    )]
    fn mint_decode(
        &self,
        code: Code,
        arguments: Stretch,
        universe: Universe,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let value = match self.mint_code(code, arguments, sink, origin) {
            Maybe::Present(value) => value,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let level = Level::constant(universe.level);
        let decoded = origin.inserted(Insertion::Decode);
        match universe.sort {
            GroundSort::Value => {
                let id = sink.arena.value_type_element(value, level);
                sink.origins.record_value_type(id, decoded);
                Maybe::Present(Lowered::ValueType(id))
            },
            GroundSort::Computation => {
                let id = sink.arena.comp_type_element(value, level);
                sink.origins.record_comp_type(id, decoded);
                Maybe::Present(Lowered::CompType(id))
            },
        }
    }

    /// Carry out an unquote's plan: the call of a dynamic function, the code
    /// it returns, and the type that code denotes.
    ///
    /// # Specification
    /// - requires: every argument is already minted or absent.
    /// - ensures: `f(v1, …, vn)` where a type is read mints as the decode of
    ///   `returned(c)`, `c` the call [`Self::mint_called`] mints, at the
    ///   universe's level, a value type for the value sort and a computation
    ///   type for the computation sort; the returned code and the decode are
    ///   marked inserted. Nothing is minted when an argument did not lower.
    /// - provides: `El` as unquote: a function from values to a universe is a
    ///   first-order function to a code, and the type it denotes is the decode
    ///   of what the call returns, which the checker reduces by running it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function of one argument, a binder holding a thunk
    ///   and a decoder's own descent called where a type is read, each asserted
    ///   as the exact core type read back out of the arena, with each node's
    ///   origin.
    /// - witness: `lower::tests::a_function_to_a_universe_unquotes_where_a_type_is_read`
    /// - witness: `lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    /// - witness: `lower::native::tests::a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::ValueType(id)) => universe.sort == GroundSort::Value
                && matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Element { code, .. })
                        if matches!(sink.arena.value(code), Some(&gandr_core_term::Value::Returned(_)))
                ),
            | Maybe::Present(Lowered::CompType(id)) => universe.sort == GroundSort::Computation
                && matches!(
                    sink.arena.comp_type(id),
                    Some(&gandr_core_term::CompType::Element { code, .. })
                        if matches!(sink.arena.value(code), Some(&gandr_core_term::Value::Returned(_)))
                ),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    fn mint_unquote(
        &self,
        function: Code,
        arguments: Stretch,
        universe: Universe,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let called = match self.mint_called(function, arguments, sink, origin) {
            Maybe::Present(called) => called,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let code = sink.arena.value_returned(called);
        sink.origins
            .record_value(code, origin.inserted(Insertion::Endpoint));
        let level = Level::constant(universe.level);
        let decoded = origin.inserted(Insertion::Decode);
        match universe.sort {
            GroundSort::Value => {
                let id = sink.arena.value_type_element(code, level);
                sink.origins.record_value_type(id, decoded);
                Maybe::Present(Lowered::ValueType(id))
            },
            GroundSort::Computation => {
                let id = sink.arena.comp_type_element(code, level);
                sink.origins.record_comp_type(id, decoded);
                Maybe::Present(Lowered::CompType(id))
            },
        }
    }

    /// Carry out a dynamic call's plan: the function the code names, forced
    /// and applied to the arguments.
    ///
    /// # Specification
    /// - requires: every argument is already minted or absent.
    /// - ensures: `f(v1, …, vn)` mints as `app(… app(force f, v1) …, vn)`, `f`
    ///   the constant at its admission position or the variable at the binder's
    ///   index in the telescope of the type the call stands in. An argument a
    ///   type reads as the value a call returns, `⟨c⟩`, runs first instead: the
    ///   application is bound under one `c ← …` per such argument, in written
    ///   order, the first outermost, the argument read as its bind's variable
    ///   and everything else raised past the binds. The head and the
    ///   applications carry the written origin; the force is marked inserted,
    ///   and each bind the nested origin of the argument it runs. Nothing is
    ///   minted when an argument did not lower.
    /// - provides: the call an unquote decodes, and a type-position call's
    ///   argument written as a call, which the checker runs. A descent through
    ///   a function field, `el[<](b(x))`, is then the bind `c ← b(x); el[<](c)`
    ///   a body writes, whose variable stands below the stage as that descent's
    ///   does.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Every loop runs once per entry of the finite stretch `arguments`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_unquote`], whose calls it mints.
    /// - witness: `lower::tests::a_thunk_binder_called_in_a_type_unquotes_its_call`
    /// - witness: `lower::native::tests::a_decoders_descent_in_its_returned_type_unquotes_the_fixpoint`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(id) => matches!(
                sink.arena.computation(id),
                Some(&(gandr_core_term::Computation::Force(_) | gandr_core_term::Computation::Application(..) | gandr_core_term::Computation::Bind(..)))
            ),
            | Maybe::Absent(_) => true,
        },
    )]
    fn mint_called(
        &self,
        function: Code,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let written = stretch(&self.operands, arguments);
        let mut passed = Vec::with_capacity(written.len());
        let mut runs = Vec::new();
        for &argument in written {
            let value = match self.value_at(argument) {
                Maybe::Present(value) => value,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            if self.type_read.contains(&argument)
                && let Some(&Value::Returned(run)) = sink.arena.value(value)
            {
                let ran = match self.origin_at(argument) {
                    Maybe::Present(at) => at,
                    Maybe::Absent(_) => origin,
                };
                runs.push((passed.len(), run, ran));
            }
            passed.push(value);
        }
        let past = Binders::from(u32::try_from(runs.len()).unwrap_or(u32::MAX));
        // The copies first, each carrying its source's origin: every argument
        // no run takes, raised past the runs' binders, and each run under the
        // runs before it. The spine minted after them records its own.
        let mark = sink.arena.watermark();
        let mut carried = Vec::new();
        let mut raised = Vec::with_capacity(passed.len());
        for (position, &value) in passed.iter().enumerate() {
            if runs.is_empty() || runs.iter().any(|&(at, ..)| at == position) {
                raised.push(value);
                continue;
            }
            let wrapped = sink.arena.computation_return(value);
            let shifted =
                gandr_core_term::shift_computation_under(sink.arena, wrapped, Binders::NONE, past)
                    .settle_traced(sink.arena, &mut carried);
            raised.push(match sink.arena.computation(shifted) {
                Some(&gandr_core_term::Computation::Return(inner)) => inner,
                _ => value,
            });
        }
        let mut firsts = Vec::with_capacity(runs.len());
        for (order, &(_, run, _)) in runs.iter().enumerate() {
            let before = Binders::from(u32::try_from(order).unwrap_or(u32::MAX));
            firsts.push(
                gandr_core_term::shift_computation_under(sink.arena, run, Binders::NONE, before)
                    .settle_traced(sink.arena, &mut carried),
            );
        }
        exits::record_copies(sink, mark, &carried, origin);
        let head = match function {
            Code::Bound {
                from,
                binder,
                telescope,
            } => {
                let index = u32::from(self.scope.index_in(from, binder, telescope));
                sink.arena.value_variable(
                    Zone::Intuitionistic,
                    DeBruijnIndex::from(index.saturating_add(u32::from(past))),
                )
            },
            Code::Constant(constant) => sink.arena.value_constant(constant),
        };
        sink.origins.record_value(head, origin);
        let mut called = sink.arena.computation_force(head);
        sink.origins
            .record_computation(called, origin.inserted(Insertion::Force));
        for (position, &value) in raised.iter().enumerate() {
            let argument = match runs.iter().position(|&(at, ..)| at == position) {
                Some(order) => {
                    let index = runs.len().saturating_sub(order).saturating_sub(1);
                    let bound = sink.arena.value_variable(
                        Zone::Intuitionistic,
                        DeBruijnIndex::from(u32::try_from(index).unwrap_or(u32::MAX)),
                    );
                    let ran = runs.get(order).map_or(origin, |&(.., ran)| ran);
                    sink.origins
                        .record_value(bound, ran.inserted(Insertion::Nested));
                    bound
                },
                None => value,
            };
            called = sink.arena.computation_application(called, argument);
            sink.origins.record_computation(called, origin);
        }
        for (&first, &(.., ran)) in firsts.iter().zip(&runs).rev() {
            called = sink.arena.computation_bind(first, called);
            sink.origins
                .record_computation(called, ran.inserted(Insertion::Nested));
        }

        Maybe::Present(called)
    }

    /// Carry out a tuple's plan: its members, as one tuple.
    ///
    /// # Specification
    /// - requires: every member is already minted or absent.
    /// - ensures: `(v1, …, vn)` mints as one tuple of `n` components in written
    ///   order, with the written origin, so a tuple inhabits the product of as
    ///   many components that one `*` chain builds; nothing is minted when a
    ///   member did not lower.
    /// - provides: the introduction of the eager product.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per entry of the finite stretch `members`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of two and a tuple of four keep their members
    ///   in order as one node; the node records the tuple's origin.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let written = stretch(&self.operands, members);
            match written
                .iter()
                .find_map(|&member| match self.value_at(member) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                }) {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::Value(id))
                        if sink.origins.value(id) == Maybe::Present(origin)
                            && sink.arena.value(id).and_then(gandr_core_term::Value::components).is_some_and(|components| components.len() == written.len()))
                },
            }
        },
    )]
    fn mint_tuple(
        &self,
        members: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, members);
        let mut components = Vec::with_capacity(written.len());
        for &member in written {
            match self.value_at(member) {
                Maybe::Present(component) => components.push(component),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_tuple(&components);

        Maybe::Present(sink.value(id, origin))
    }

    /// Carry out a product's plan: its components, as one product.
    ///
    /// # Specification
    /// - requires: every component is already minted or absent.
    /// - ensures: `A1 * … * An` mints as one product of `n` components in
    ///   written order, with the written origin; nothing is minted when a
    ///   component did not lower.
    /// - provides: the eager product type.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per entry of the finite stretch `components`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product of two and a chain of four keep their
    ///   components in order as one node, which records the product's origin.
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let written = stretch(&self.operands, components);
            match written
                .iter()
                .find_map(|&component| match self.value_type_at(component) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                }) {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id))
                        if sink.origins.value_type(id) == Maybe::Present(origin)
                            && sink.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Product(ref parts) if parts.len() == written.len())))
                },
            }
        },
    )]
    fn mint_product(
        &self,
        components: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, components);
        let mut parts = Vec::with_capacity(written.len());
        for &component in written {
            match self.value_type_at(component) {
                Maybe::Present(part) => parts.push(part),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_type_product(&parts);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Carry out a value function space's plan: the thunked arrow it is the
    /// alias of.
    ///
    /// # Specification
    /// - requires: every domain and the codomain are already minted or absent.
    /// - ensures: `(A1, …, An) => B` mints as `+U (A1 -> … -> An -> -F B)`,
    ///   every node with the written origin, so the alias and the thunked arrow
    ///   it names are one core type; nothing is minted when a domain or the
    ///   codomain did not lower.
    /// - provides: the value function space.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Both loops run once per entry of the finite stretch `domains`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one domain, a list of two, and an alias nested to the
    ///   right, each asserted as the same core node the thunked arrow it stands
    ///   for lowers to.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::ValueType(id)) => {
                matches!(
                    sink.arena.value_type(id),
                    Some(&gandr_core_term::ValueType::Thunk(_))
                )
            },
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    /// # Adequacy
    /// - hypothesis: L3 — the value-function alias is a thunked arrow over a
    ///   returner, with domains in written order and the alias’s own origin.
    /// - witness: `lower::tests::the_alias_is_the_thunked_arrow`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| {
            let missing = stretch(&self.operands, domains)
                .iter()
                .find_map(|&domain| match self.value_type_at(domain) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                })
                .or_else(|| match self.value_type_at(codomain) {
                    | Maybe::Present(_) => None,
                    | Maybe::Absent(reason) => Some(reason),
                });
            match missing {
                | Some(reason) => ret == Maybe::Absent(reason),
                | None => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            }
        },
    )]
    fn mint_value_function(
        &self,
        domains: Stretch,
        codomain: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let written = stretch(&self.operands, domains);
        for &domain in written {
            if let Maybe::Absent(reason) = self.value_type_at(domain) {
                return Maybe::Absent(reason);
            }
        }
        let returned = match self.value_type_at(codomain) {
            Maybe::Present(returned) => returned,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut arrow = sink.arena.comp_type_returner(returned);
        sink.origins.record_comp_type(arrow, origin);
        for &domain in written.iter().rev() {
            let Maybe::Present(from) = self.value_type_at(domain)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            arrow = sink.arena.comp_type_arrow(from, arrow);
            sink.origins.record_comp_type(arrow, origin);
        }
        let id = sink.arena.value_type_thunk(arrow);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(Lowered::ValueType(id))
    }

    /// Carry out a type former's plan.
    ///
    /// # Specification
    /// - requires: the argument position is interpreted in this lowering run.
    /// - ensures: a thunk consumes a computation type, a returner and a list
    ///   each consume a value type, and a run type consumes the session code as
    ///   a value; successful nodes carry the supplied origin.
    /// - provides: the core bridge, list or run type over the already lowered
    ///   argument.
    /// - fails: a missing or wrong-sort argument preserves its absence reason.
    /// - panics: none under the origin table’s ordered-identifier invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both bridge formers retain their argument type and
    ///   stay distinct from one another and from ordinary names with similar
    ///   spellings.
    /// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
    /// - witness: `lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    /// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
    #[spec(
        ensures: |ret| match former {
            | TypeFormer::Thunk => match self.comp_type_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            },
            | TypeFormer::Returner => match self.value_type_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::CompType(id)) if sink.origins.comp_type(id) == Maybe::Present(origin))
                },
            },
            | TypeFormer::List => match self.value_type_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            },
            | TypeFormer::Run => match self.value_at(argument) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    matches!(ret, Maybe::Present(Lowered::ValueType(id)) if sink.origins.value_type(id) == Maybe::Present(origin))
                },
            },
        },
    )]
    fn mint_former(
        &self,
        former: TypeFormer,
        argument: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match former {
            TypeFormer::Thunk => self.comp_type_at(argument).map(|inner| {
                let id = sink.arena.value_type_thunk(inner);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            TypeFormer::Returner => self.value_type_at(argument).map(|inner| {
                let id = sink.arena.comp_type_returner(inner);
                sink.origins.record_comp_type(id, origin);
                Lowered::CompType(id)
            }),
            TypeFormer::List => self.value_type_at(argument).map(|element| {
                let id = sink.arena.value_type_list(element);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            TypeFormer::Run => self.value_at(argument).map(|session| {
                let id = sink.arena.value_type_run(session);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
        }
    }

    /// Carry out the plan of a former over already-minted children.
    ///
    /// # Specification
    /// - requires: child positions are interpreted in this lowering run.
    /// - ensures: each supported plan yields its own term or type family, with
    ///   the supplied origin on the new outer node.
    /// - provides: core constructors over previously lowered children.
    /// - fails: unsupported plans are Unminted; missing or wrong-sort children
    ///   preserve the first required absence.
    /// - panics: none under the origin table’s ordered-identifier invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — arrows, static products, pairs, abstraction, path
    ///   types, reflexivity and computation formers retain their distinct core
    ///   constructors and child order. These witnesses cover the admitted
    ///   fragment, not arbitrary foreign identifiers.
    /// - witness: `lower::tests::an_arrow_lowers_under_a_thunk_type`
    /// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
    /// - witness: `lower::tests::a_static_abstraction_binds_its_name_over_a_quoted_body`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Absent(_) => true,
            | Maybe::Present(Lowered::Value(id)) => {
                matches!(*plan, Plan::StaticLambda(_) | Plan::Thunk(_) | Plan::Run(_) | Plan::Here(_) | Plan::Funext(..) | Plan::Equiv(..) | Plan::Univalence(_) | Plan::PathProduct(..) | Plan::Ua { .. } | Plan::ListNil | Plan::ListCons(..) | Plan::SessionRelated(..) | Plan::Stay(_) | Plan::Forward(_) | Plan::FunctionFlow(..) | Plan::FlowProduct(..))
                    && sink.origins.value(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::Computation(id)) => {
                matches!(*plan, Plan::Return(_) | Plan::Force(_) | Plan::Lambda(..) | Plan::Transport(..))
                    && sink.origins.computation(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::ValueType(id)) => {
                matches!(*plan, Plan::StaticPi(_, _) | Plan::Path(..) | Plan::Flow(..) | Plan::Stack(..))
                    && sink.origins.value_type(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::CompType(id)) => {
                matches!(*plan, Plan::Arrow(_, _))
                    && sink.origins.comp_type(id) == Maybe::Present(origin)
            },
            | Maybe::Present(Lowered::Function { .. }) => false,
        },
    )]
    fn mint_over(
        &self,
        plan: &Plan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match *plan {
            Plan::Arrow(domain, codomain) => self.value_type_at(domain).and_then(|from| {
                self.comp_type_at(codomain).map(|to| {
                    let id = sink.arena.comp_type_arrow(from, to);
                    sink.origins.record_comp_type(id, origin);
                    Lowered::CompType(id)
                })
            }),
            Plan::StaticPi(domain, codomain) => self.value_type_at(domain).and_then(|from| {
                self.value_type_at(codomain).map(|to| {
                    let id = sink.arena.value_type_static_pi(from, to);
                    sink.origins.record_value_type(id, origin);
                    Lowered::ValueType(id)
                })
            }),
            Plan::Path(carrier, left, right) => {
                let over = match carrier {
                    Carrier::Written(carrier) => self.value_type_at(carrier),
                    Carrier::Universe(universe) => {
                        let id = sink.arena.value_type_universe(
                            Sort::Ground(universe.sort),
                            Level::constant(universe.level),
                        );
                        Maybe::Present(id)
                    },
                };
                over.and_then(|over| {
                    self.value_at(left).and_then(|from| {
                        self.value_at(right).map(|to| {
                            let id = sink.arena.value_type_path(over, from, to);
                            sink.origins.record_value_type(id, origin);
                            Lowered::ValueType(id)
                        })
                    })
                })
            },
            Plan::Here(point) => self.value_at(point).map(|at| {
                let id = sink.arena.value_here(at);
                sink.value(id, origin)
            }),
            Plan::Funext(left, right) => self.value_at(left).and_then(|first| {
                self.value_at(right).map(|second| {
                    let id = sink.arena.value_funext(first, second);
                    sink.value(id, origin)
                })
            }),
            Plan::Equiv(forward, backward) => self.value_at(forward).and_then(|first| {
                self.value_at(backward).map(|second| {
                    let id = sink.arena.value_equiv(first, second);
                    sink.value(id, origin)
                })
            }),
            Plan::Univalence(record) => self.value_at(record).map(|at| {
                let forward = gandr_core_term::identity::univalence_forward(sink.arena, at);
                let id = sink.arena.value_univalence(at, forward);
                sink.value(id, origin)
            }),
            Plan::PathProduct(first, second) => self.value_at(first).and_then(|left| {
                self.value_at(second).map(|right| {
                    let id = sink.arena.value_path_product(left, right);
                    sink.value(id, origin)
                })
            }),
            Plan::Ua {
                stratum,
                ref sides,
                named,
                forward,
                backward,
            } => self.value_at(forward).and_then(|first| {
                self.value_at(backward).map(|second| {
                    let id = sink
                        .arena
                        .value_ua(stratum, Arc::clone(sides), first, second);
                    sink.origins.record_sides(id, named);
                    sink.value(id, origin)
                })
            }),
            Plan::ListNil => {
                let id = sink.arena.value_list_nil();
                Maybe::Present(sink.value(id, origin))
            },
            Plan::ListCons(head, tail) => self.value_at(head).and_then(|first| {
                self.value_at(tail).map(|rest| {
                    let id = sink.arena.value_list_cons(first, rest);
                    sink.value(id, origin)
                })
            }),
            Plan::Transport(abstraction, path, value) => {
                self.mint_transport((abstraction, path, value), sink, origin)
            },
            Plan::StaticLambda(body) => self.value_at(body).map(|under| {
                let id = sink.arena.value_static_lambda(under);
                sink.value(id, origin)
            }),
            Plan::Thunk(body) => self.mint_body(body, sink, origin).map(|suspended| {
                let id = sink.arena.value_thunk(suspended);
                sink.value(id, origin)
            }),
            Plan::Return(value) => self.value_at(value).map(|returned| {
                let id = sink.arena.computation_return(returned);
                sink.computation(id, origin)
            }),
            Plan::Force(value) => self.value_at(value).map(|forced| {
                let id = sink.arena.computation_force(forced);
                sink.computation(id, origin)
            }),
            Plan::Run(computation) => self.computation_at(computation).map(|ran| {
                let id = sink.arena.value_run(ran);
                sink.value(id, origin)
            }),
            Plan::Flow(carrier, left, right) => self.value_type_at(carrier).and_then(|over| {
                self.value_at(left).and_then(|from| {
                    self.value_at(right).map(|to| {
                        let id = sink.arena.value_type_flow(over, from, to);
                        sink.origins.record_value_type(id, origin);
                        Lowered::ValueType(id)
                    })
                })
            }),
            Plan::Stack(input, output) => self.comp_type_at(input).and_then(|from| {
                self.comp_type_at(output).map(|to| {
                    let id = sink.arena.value_type_stack(from, to);
                    sink.origins.record_value_type(id, origin);
                    Lowered::ValueType(id)
                })
            }),
            Plan::SessionRelated(relation, left, right) => self.value_at(left).and_then(|from| {
                self.value_at(right).map(|to| {
                    let id = sink.arena.value_session_related(relation, from, to);
                    sink.value(id, origin)
                })
            }),
            Plan::Stay(point) => self.value_at(point).map(|at| {
                let id = sink.arena.value_stay(at);
                sink.value(id, origin)
            }),
            Plan::Forward(translator) => self.value_at(translator).map(|map| {
                let id = sink.arena.value_forward(map);
                sink.value(id, origin)
            }),
            Plan::FunctionFlow(domain, codomain) => self.value_at(domain).and_then(|into| {
                self.value_at(codomain).map(|out| {
                    let id = sink.arena.value_function_flow(into, out);
                    sink.value(id, origin)
                })
            }),
            Plan::FlowProduct(first, second) => self.value_at(first).and_then(|left| {
                self.value_at(second).map(|right| {
                    let id = sink.arena.value_flow_product(left, right);
                    sink.value(id, origin)
                })
            }),
            Plan::Lambda(body, binder) => self.mint_body(body, sink, origin).map(|under| {
                let id = sink.arena.computation_lambda(under);
                let lowered = sink.computation(id, origin);
                if let Maybe::Present(name) = self.origin_at(binder) {
                    sink.origins.record_binder(id, name);
                }
                lowered
            }),
            Plan::Unplanned
            | Plan::ValueHole(_)
            | Plan::CompHole(_)
            | Plan::Variable(..)
            | Plan::Constant(_)
            | Plan::Primitive(_)
            | Plan::PrimitiveCall(..)
            | Plan::Unit
            | Plan::Literal(_)
            | Plan::Atom(_)
            | Plan::Sealed(_)
            | Plan::Instantiated(..)
            | Plan::Universe(_)
            | Plan::Decode(..)
            | Plan::Unquote(..)
            | Plan::Called(..)
            | Plan::StaticApplication(..)
            | Plan::Tuple(_)
            | Plan::Record(_)
            | Plan::Injection(..)
            | Plan::ValueFunction(..)
            | Plan::Telescope(..)
            | Plan::DependentArrow(..)
            | Plan::Former(..)
            | Plan::Transparent(_)
            | Plan::Application(..)
            | Plan::Function(_)
            | Plan::Data(..)
            | Plan::Expansion(..)
            | Plan::Constructor(_)
            | Plan::Case(_)
            | Plan::EmptyCase(_)
            | Plan::Product(_)
            | Plan::RecordType(..)
            | Plan::Sum(_)
            | Plan::With(_)
            | Plan::Copattern(_)
            | Plan::Observe(..)
            | Plan::Select(..)
            | Plan::Block(_)
            | Plan::Loop(_)
            | Plan::While(..)
            | Plan::Break
            | Plan::Reenter(_)
            | Plan::Derived(_)
            | Plan::Session(..)
            | Plan::Action(..)
            | Plan::Access(_)
            | Plan::World(_)
            | Plan::TelescopeTransport(_)
            | Plan::Capability(..)
            | Plan::Effectful(..)
            | Plan::Exercise(_)
            | Plan::Scope(_)
            | Plan::Resume(..)
            | Plan::Recorded(_)
            | Plan::Ride(..)
            | Plan::FlowThen(..)
            | Plan::Relation(..) => Maybe::Absent(lowered::Absent::Unminted),
        }
    }

    /// Mint a block: its statements bound over its last computation.
    ///
    /// # Specification
    /// - requires: every node the block names is already minted or absent.
    /// - ensures: `run x1 <- c1 ; … run xn <- cn ; c` mints as `bind(c1, …
    ///   bind(cn, c))`, each bind's origin its statement's `run` tile, and a
    ///   typed `run x : A <- c ;` binds `c` ascribed the pure `-F A`; a fork
    ///   `fork (c : S) t as d ;` mints as the fork of `t` at `S` whose parent
    ///   is the rest of the block, at its `fork` tile's origin; a hold `hold x
    ///   = e ;` mints as the hold of `e` whose scope is the rest of the block,
    ///   at its `hold` tile's origin; a `leta x = v ;` mints as the opening of
    ///   `v` whose body is the rest of the block, at its `leta` tile's origin,
    ///   binding the name; a block of no statements is its last computation;
    ///   nothing is minted when any computation, value or protocol of the block
    ///   did not lower.
    /// - provides: the block half of thunks, lambdas and function tails.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — run statements wrap the final computation in source
    ///   order, each bind records its run token, and an empty statement prefix
    ///   leaves the existing final computation unchanged.
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| match self.computation_at(block.last) {
            | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
            | Maybe::Present(last) => {
                let statements = stretch(&self.statements, block.statements);
                let missing = statements.iter().find_map(|statement| {
                    match (self.statement_parts(statement), self.origin_at(statement.origin)) {
                        | (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => Some(reason),
                        | (Maybe::Present(()), Maybe::Present(_)) => None,
                    }
                });
                match missing {
                    | Some(reason) => ret == Maybe::Absent(reason),
                    | None => match statements.first() {
                        | None => ret == Maybe::Present(last),
                        | Some(first) => {
                            matches!(ret, Maybe::Present(id) if matches!((sink.origins.computation(id), self.origin_at(first.origin)), (Maybe::Present(stored), Maybe::Present(expected)) if stored == expected))
                        },
                    },
                }
            },
        },
    )]
    fn mint_block(
        &self,
        block: Block,
        sink: &mut Sink<'_>,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let statements = stretch(&self.statements, block.statements);
        let mut chain = match self.computation_at(block.last) {
            Maybe::Present(last) => last,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for statement in statements {
            if let Maybe::Absent(reason) = self.statement_parts(statement) {
                return Maybe::Absent(reason);
            }
            if let Maybe::Absent(reason) = self.origin_at(statement.origin) {
                return Maybe::Absent(reason);
            }
        }
        for statement in statements.iter().rev() {
            let Maybe::Present(origin) = self.origin_at(statement.origin)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            if let StatementBinding::Held { value } = statement.binding {
                let Maybe::Present(value) = self.value_at(value)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let id = sink
                    .arena
                    .computation_memory(MemoryForm::Hold { value, body: chain });
                sink.origins.record_computation(id, origin);
                chain = id;
                continue;
            }
            if let StatementBinding::Opened { value, name } = statement.binding {
                let Maybe::Present(value) = self.value_at(value)
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let id = sink
                    .arena
                    .computation_world(WorldForm::Leta { value, body: chain });
                sink.origins.record_computation(id, origin);
                if let Maybe::Present(name) = self.origin_at(name) {
                    sink.origins.record_binder(id, name);
                }
                chain = id;
                continue;
            }
            if let StatementBinding::Forked { protocol, child } = statement.binding {
                let (Maybe::Present(protocol), Maybe::Present(child)) =
                    (self.value_type_at(protocol), self.computation_at(child))
                else {
                    return Maybe::Absent(lowered::Absent::Unminted);
                };
                let id = sink.arena.computation_session(SessionAction::Fork {
                    protocol,
                    child,
                    parent: chain,
                });
                sink.origins.record_computation(id, origin);
                chain = id;
                continue;
            }
            let Maybe::Present(bound) = self.computation_at(statement.bound)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let split = match statement.binding {
                StatementBinding::Named(_)
                | StatementBinding::Typed { .. }
                | StatementBinding::Forked { .. }
                | StatementBinding::Held { .. }
                | StatementBinding::Opened { .. } => None,
                StatementBinding::Discarded => Some(gandr_core_term::ComponentCount::default()),
                StatementBinding::Split { arity, .. } => Some(arity),
            };
            if let Some(arity) = split {
                let tuple = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(tuple, origin);
                let split = sink.arena.computation_split(tuple, arity, chain);
                sink.origins.record_computation(split, origin);
                chain = split;
            }
            let bound = match statement.binding {
                StatementBinding::Typed { annotation, .. } => {
                    let Maybe::Present(written) = self.value_type_at(annotation)
                    else {
                        return Maybe::Absent(lowered::Absent::Unminted);
                    };
                    // The annotation was read as a type, in the signature's
                    // telescope; the computation it ascribes stands in the
                    // body, whose context binds every binder (#662).
                    let frame = self.reading(annotation).frame();
                    let result = self.relocate_value_type(
                        written,
                        frame,
                        Telescope::Signature,
                        sink,
                        origin,
                    );
                    let returner = sink.arena.comp_type_returner(result);
                    sink.origins.record_comp_type(returner, origin);
                    let ascribed = sink.arena.computation_ascribe(bound, returner);
                    sink.origins.record_computation(ascribed, origin);
                    ascribed
                },
                StatementBinding::Named(_)
                | StatementBinding::Discarded
                | StatementBinding::Split { .. }
                | StatementBinding::Forked { .. }
                | StatementBinding::Held { .. }
                | StatementBinding::Opened { .. } => bound,
            };
            let id = sink.arena.computation_bind(bound, chain);
            sink.origins.record_computation(id, origin);
            if let StatementBinding::Named(name) | StatementBinding::Typed { name, .. } =
                statement.binding
                && let Maybe::Present(name) = self.origin_at(name)
            {
                sink.origins.record_binder(id, name);
            }
            // A binder, or a tuple pattern, answers at what its bound
            // computation returns, read where the run judged that
            // computation: a rewrite of the block may leave no bind and no
            // use naming it (#298).
            if let StatementBinding::Named(written)
            | StatementBinding::Typed { name: written, .. }
            | StatementBinding::Split {
                pattern: written, ..
            } = statement.binding
                && let Maybe::Present(written) = self.origin_at(written)
            {
                sink.origins.record_label(Label {
                    span: written.span(),
                    labelled: Labelled::Bound(statement.bound),
                });
            }
            if statement.rest == exits::Rest::Distributed {
                let _first = sink.distributed.insert(id, origin);
            }
            chain = id;
        }

        Maybe::Present(chain)
    }

    /// Whether every node a statement mints from lowered: a fork's protocol
    /// and child, and every other statement's bound computation.
    ///
    /// # Specification
    /// - requires: the statement's nodes are minted or absent.
    /// - ensures: present when they lowered at their sorts; the first absence
    ///   otherwise, the protocol's before the child's.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block holding a fork and one holding a run, each
    ///   minted whole.
    /// - witness: `lower::session::tests::the_seat_exchange_lowers_both_ends`
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    #[spec(ensures: |ret| match statement.binding {
        | StatementBinding::Forked { protocol, child } => (ret == Maybe::Present(())) == (matches!(self.value_type_at(protocol), Maybe::Present(_)) && matches!(self.computation_at(child), Maybe::Present(_))),
        | StatementBinding::Held { value } | StatementBinding::Opened { value, .. } => (ret == Maybe::Present(())) == matches!(self.value_at(value), Maybe::Present(_)),
        | StatementBinding::Typed { annotation, .. } => (ret == Maybe::Present(())) == (matches!(self.computation_at(statement.bound), Maybe::Present(_)) && matches!(self.value_type_at(annotation), Maybe::Present(_))),
        | _ => (ret == Maybe::Present(())) == matches!(self.computation_at(statement.bound), Maybe::Present(_)),
    })]
    fn statement_parts(
        &self,
        statement: &Statement,
    ) -> Maybe<(), lowered::Absent>
    {
        match statement.binding {
            StatementBinding::Forked { protocol, child } => self
                .value_type_at(protocol)
                .and_then(|_protocol| self.computation_at(child))
                .map(|_child| ()),
            StatementBinding::Held { value } | StatementBinding::Opened { value, .. } => {
                self.value_at(value).map(|_value| ())
            },
            StatementBinding::Typed { annotation, .. } => self
                .computation_at(statement.bound)
                .and_then(|_bound| self.value_type_at(annotation))
                .map(|_annotation| ()),
            StatementBinding::Named(_)
            | StatementBinding::Discarded
            | StatementBinding::Split { .. } => {
                self.computation_at(statement.bound).map(|_bound| ())
            },
        }
    }

    /// Mint an application of `head` to `arguments`, left to right.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: `c(v1, …, vn)` mints as `app(… app(c, v1) …, vn)`, every
    ///   application carrying the call's origin; a call through a joint
    ///   fixpoint passes its argument injected at the called member's summand,
    ///   the injection marked as the fixpoint's insertion; a call of no
    ///   arguments is its head's own computation; nothing is minted when the
    ///   head or an argument did not lower.
    /// - provides: the curried elimination of a lambda.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — applications associate to the left, force a value
    ///   head only once when required, and preserve authored versus inserted
    ///   origins.
    /// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
    /// - witness: `lower::native::tests::a_mutual_blocks_recursive_functions_share_one_fixpoint`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        captures: written = stretch(&self.operands, arguments),
        ensures: |ret| match self.computation_at(head) {
            | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
            | Maybe::Present(called) => {
                match written
                    .iter()
                    .find_map(|&argument| match self.value_at(argument) {
                        | Maybe::Present(_) => None,
                        | Maybe::Absent(reason) => Some(reason),
                    }) {
                    | Some(reason) => ret == Maybe::Absent(reason),
                    | None if written.is_empty() => {
                        ret == Maybe::Present(Lowered::Computation(called))
                    },
                    | None => {
                        matches!(ret, Maybe::Present(Lowered::Computation(id)) if sink.origins.computation(id) == Maybe::Present(origin))
                    },
                }
            },
        },
    )]
    fn mint_application(
        &self,
        head: NodeIndex,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut applied = match self.computation_at(head) {
            Maybe::Present(called) => called,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let arguments = stretch(&self.operands, arguments);
        for &argument in arguments {
            if let Maybe::Absent(reason) = self.value_at(argument) {
                return Maybe::Absent(reason);
            }
        }
        for &argument in arguments {
            let mut passed = match self.value_at(argument) {
                Maybe::Present(passed) => passed,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            if let Some(&summand) = self.injected.get(&head) {
                let injected = sink.arena.value_injection(summand, passed);
                sink.origins
                    .record_value(injected, origin.inserted(Insertion::Fixpoint));
                passed = injected;
            }
            let id = sink.arena.computation_application(applied, passed);
            sink.origins.record_computation(id, origin);
            applied = id;
        }

        Maybe::Present(Lowered::Computation(applied))
    }

    /// Mint a function tail: its body, and its declared type when it states
    /// one.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: `(x1: A1, …, xn: An) -> C { b }` mints its body as `thunk (λ
    ///   … λ. b)`, one lambda per parameter with the binder tile's origin and
    ///   the thunk marked as inserted at the declaration form; a recursive tail
    ///   closes its staged parameter's lambda by a fixpoint marked as inserted
    ///   at the declaration form, its binder named where the function's own
    ///   name is written, `thunk (λ … λ. fix. λ … λ. b)`, claiming structural
    ///   descent when a call claims it and partial otherwise; its declared type
    ///   is `+U (A1 -> … -> An -> C)`, one arrow per parameter with the binder
    ///   tile's origin and `+U` the declaration form's, an arrow dependent
    ///   where a later type names its parameter; a tail missing a parameter or
    ///   result type mints the body alone; nothing is minted when the block did
    ///   not lower.
    /// - provides: the function tail's two halves, from one reading.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — function tails produce an inserted thunk over their
    ///   lambda chain even when a missing parameter or result type prevents a
    ///   signature.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    /// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `lower::native::tests::a_recursive_function_closes_a_fixpoint_over_its_staged_parameter`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Absent(_) => true,
            | Maybe::Present(Lowered::Function { signature, body }) => {
                sink.origins.value(body) == Maybe::Present(origin.inserted(Insertion::Thunk))
                    && match signature {
                        | Maybe::Absent(_) => true,
                        | Maybe::Present(id) => {
                            sink.origins.value_type(id) == Maybe::Present(origin)
                        },
                    }
            },
            | Maybe::Present(_) => false,
        },
    )]
    fn mint_function(
        &self,
        function: &Function,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let parameters = stretch(&self.parameters, function.parameters);
        for parameter in parameters {
            if let Maybe::Absent(reason) = self.origin_at(parameter.binder) {
                return Maybe::Absent(reason);
            }
        }
        let mut body = match self.mint_body(function.block, sink, origin) {
            Maybe::Present(block) => block,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut fixpoint = match self.evidence(function) {
            Maybe::Present(evidence) => Some(evidence),
            Maybe::Absent(_) => None,
        };
        let staged = match function.recursion {
            Maybe::Present(scope) => self.recursions.get(&scope).map_or(0, |recursion| {
                stretch(&self.parameters, recursion.uniform).len()
            }),
            Maybe::Absent(_) => 0,
        };
        for (position, parameter) in parameters.iter().enumerate().rev() {
            let Maybe::Present(binder) = self.origin_at(parameter.binder)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = sink.arena.computation_lambda(body);
            sink.origins.record_computation(id, binder);
            sink.origins.record_binder(id, binder);
            body = id;
            if position == staged
                && let Some(evidence) = fixpoint.take()
            {
                let closed = sink.arena.computation_fixpoint(body, evidence);
                sink.origins
                    .record_computation(closed, origin.inserted(Insertion::Fixpoint));
                // The fixpoint's binder is the function's own name, which
                // a type its identified fields read names it by.
                if let Maybe::Present(scope) = function.recursion
                    && let Some(recursion) = self.recursions.get(&scope)
                    && let Maybe::Present(named) = self.origin_at(recursion.named)
                {
                    sink.origins.record_binder(closed, named);
                }
                body = closed;
            }
        }
        let thunk = sink.arena.value_thunk(body);
        sink.origins
            .record_value(thunk, origin.inserted(Insertion::Thunk));

        Maybe::Present(Lowered::Function {
            signature: self.mint_signature(function, parameters, sink, origin),
            body: thunk,
        })
    }

    /// Mint a function tail's declared type, `+U (A1 -> … -> An -> C)`.
    ///
    /// # Specification
    /// - requires: `parameters` are the function's own, and every type position
    ///   has been classified, so every parameter a type names is recorded as
    ///   mentioned.
    /// - ensures: the declared type, as [`Self::mint_function`] states it, with
    ///   each parameter's arrow dependent exactly when a later parameter's type
    ///   or the result names it, and plain otherwise; nothing is minted when a
    ///   type is unstated or did not lower.
    /// - provides: the signature half of [`Self::mint_function`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter a later type names beside one no type
    ///   names, each asserted as the exact arrow read back out of the arena.
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    #[spec(
        ensures: |ret| match function.result {
            | Maybe::Absent(_) => ret == Maybe::Absent(lowered::Absent::Unstated),
            | Maybe::Present(result) => match self.comp_type_at(result) {
                | Maybe::Absent(reason) => ret == Maybe::Absent(reason),
                | Maybe::Present(_) => {
                    let missing =
                        parameters
                            .iter()
                            .find_map(|parameter| match parameter.declared {
                                | Maybe::Absent(_) => Some(lowered::Absent::Unstated),
                                | Maybe::Present(written) => match self.value_type_at(written) {
                                    | Maybe::Absent(reason) => Some(reason),
                                    | Maybe::Present(_) => None,
                                },
                            });
                    match missing {
                        | Some(reason) => ret == Maybe::Absent(reason),
                        | None if parameters.iter().any(|parameter| {
                            matches!(self.origin_at(parameter.binder), Maybe::Absent(_))
                        }) =>
                        {
                            ret == Maybe::Absent(lowered::Absent::Unminted)
                        },
                        | None => {
                            matches!(ret, Maybe::Present(id) if sink.origins.value_type(id) == Maybe::Present(origin))
                        },
                    }
                },
            },
        },
    )]
    fn mint_signature(
        &self,
        function: &Function,
        parameters: &[Parameter],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let Maybe::Present(result) = function.result
        else {
            return Maybe::Absent(lowered::Absent::Unstated);
        };
        let mut declared = match self.comp_type_at(result) {
            Maybe::Present(result) => result,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for parameter in parameters {
            let Maybe::Present(written) = parameter.declared
            else {
                return Maybe::Absent(lowered::Absent::Unstated);
            };
            if let Maybe::Absent(reason) = self.value_type_at(written) {
                return Maybe::Absent(reason);
            }
        }
        for parameter in parameters.iter().rev() {
            let (Maybe::Present(written), Maybe::Present(binder)) =
                (parameter.declared, self.origin_at(parameter.binder))
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let Maybe::Present(domain) = self.value_type_at(written)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = if bool::from(self.scope.mentioned(parameter.frame)) {
                let id = sink.arena.comp_type_pi(domain, declared);
                sink.origins.record_arrow(id, binder);
                id
            }
            else {
                sink.arena.comp_type_arrow(domain, declared)
            };
            sink.origins.record_comp_type(id, binder);
            declared = id;
        }
        let id = sink.arena.value_type_thunk(declared);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(id)
    }

    /// What `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a live position yields its stored lowering result; a missing
    ///   position is unminted.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independently lowered children feed their parent and
    ///   a refused declaration does not prevent its sibling from lowering.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[spec(
        ensures: |ret| {
            ret == self
                .lowered
                .get(usize::from(position))
                .copied()
                .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
        },
    )]
    fn lowered_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        self.lowered
            .get(usize::from(position))
            .copied()
            .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
    }

    /// The value `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Value(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn value_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::Value(id) => Maybe::Present(id),
            Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The computation `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Computation(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn computation_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::Computation(id) => Maybe::Present(id),
            Lowered::Value(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The value type `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::ValueType(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn value_type_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::ValueType(id) => Maybe::Present(id),
            Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The computation type `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an unminted result preserves its reason, the requested family
    ///   yields its id, and every other family yields an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value, computation and type operands are
    ///   read back in their own families while assembling completed
    ///   declarations.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::CompType(id)) => Maybe::Present(id),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn comp_type_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::CompType(id) => Maybe::Present(id),
            Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The declared type the function tail at `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a function yields its stored signature result; an unminted
    ///   result preserves its reason and other families yield an other-sort
    ///   reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signed and unsigned function tails preserve the body
    ///   while differing in whether they supply a derived signature.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Function { signature, .. }) => signature,
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn signature_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::Function { signature, .. } => signature,
            Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_) => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The body the function tail at `position` lowered to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a function yields its body id; an unminted result preserves
    ///   its reason and other families yield an other-sort reason.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — signed and unsigned function tails preserve the body
    ///   while differing in whether they supply a derived signature.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
    #[spec(
        ensures: |ret| {
            ret == match self.lowered_at(position) {
                | Maybe::Absent(reason) => Maybe::Absent(reason),
                | Maybe::Present(Lowered::Function { body, .. }) => Maybe::Present(body),
                | Maybe::Present(_) => Maybe::Absent(lowered::Absent::OtherSort),
            }
        },
    )]
    fn function_body_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            Lowered::Function { body, .. } => Maybe::Present(body),
            Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_) => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// Resolve every attribute against the registry and file it.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so an admitted payload already has
    ///   its core value.
    /// - ensures: every attribute of every declaration, refused or not, is
    ///   resolved against the registry and filed under the content identity of
    ///   the declaration form it decorates, in source order; an attribute
    ///   written twice for one declared name is refused wherever its two
    ///   spellings sit, and the earlier one is the one kept. A declaration's
    ///   lowering outcome does not gate its attributes: an expectation about a
    ///   refusal is read off the refused declaration, and an attribute's own
    ///   refusal competes with the declaration's other refusals by position. An
    ///   attribute decorating a top-level module is resolved alike and filed
    ///   under the module form's content identity, its refusal offered to the
    ///   module's first member. An `explicit_exits` attribute marks the slot it
    ///   decorates, or every member slot of the module it decorates, as asking
    ///   for written exits. The constants a `respects` or `entry` payload names
    ///   are filed beside its entry, as laws or as worlds.
    /// - provides: the attribute side table of the lowered module, and the
    ///   slots the `explicit-exits` lint reads as asked.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] abort the pass. Every other refusal
    ///   is offered to the declaration that owns the attribute rather than
    ///   raised.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — attributes are drained and filed even for a refused
    ///   declaration, while a failing schema is retained as a declaration
    ///   refusal; an `explicit_exits` attribute on a module and on a
    ///   declaration asks within its form and nowhere else.
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    /// - witness: `lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's attributes; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| {
            self.collected.slots.len() == before
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err()
                    || (self.collected.decorated.is_empty()
                        && self
                            .collected
                            .slots
                            .iter()
                            .all(|slot| slot.attributes.is_empty())))
        },
    )]
    fn attribute(
        &mut self,
        table: &mut AttributeTable,
        arena: &CoreArena,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut slots = core::mem::take(&mut self.collected.slots);
        let decorated = core::mem::take(&mut self.collected.decorated);
        let outcome = self
            .attribute_slots(&mut slots, table, arena)
            .and_then(|()| self.attribute_modules(&decorated, &mut slots, table, arena));
        self.collected.slots = slots;

        outcome
    }

    /// Resolve and file the attributes of every decorated module in
    /// `decorated`.
    ///
    /// # Specification
    /// - requires: as [`Self::attribute`], over the decorated modules and the
    ///   slots taken out of the collection.
    /// - ensures: as [`Self::attribute`], for the modules' attributes; each
    ///   spends one step.
    /// - provides: the module walk of [`Self::attribute`].
    /// - fails: as [`Self::attribute`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::attribute`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decorated module of two members and an undecorated
    ///   declaration after it, the attribute reaching the members only; a
    ///   module's laws filed under the module; a refused attribute refusing the
    ///   first member alone.
    /// - witness: `lower::exits::tests::an_explicit_exits_attribute_asks_within_its_form`
    /// - witness: `lower::tests::a_module_respects_attribute_files_its_laws_under_the_module`
    /// - witness: `lower::tests::a_module_attribute_refusal_refuses_its_first_member_alone`
    #[spec(
        captures: before = (self.fuel.remaining, usize::from(table.attributed_count())),
        ensures: |ret| {
            self.fuel.remaining <= before.0
                && usize::from(table.attributed_count()) >= before.1
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
        },
    )]
    fn attribute_modules(
        &mut self,
        decorated: &[DecoratedModule<'source>],
        slots: &mut [DeclarationSlot<'source>],
        table: &mut AttributeTable,
        arena: &CoreArena,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        for module in decorated {
            let mut seen: Vec<(RegisteredAttribute, ByteSpan)> = Vec::new();
            for written in &module.attributes {
                self.fuel.spend()?;
                match self.read_attribute(written, &mut seen, arena) {
                    Ok(Filing::Filed { entry, named }) => {
                        if entry.name() == RegisteredAttribute::EXPLICIT_EXITS {
                            self.asked.extend(
                                (usize::from(module.first) .. usize::from(module.end))
                                    .map(SlotIndex::from),
                            );
                        }
                        self.ask_runs(
                            &entry,
                            (usize::from(module.first) .. usize::from(module.end))
                                .map(SlotIndex::from),
                        );
                        let key = self.key_at(module.module.node);
                        let attribute = entry.name();
                        table.file(key, entry);
                        table.file_named(key, attribute, named);
                    },
                    Ok(Filing::Unlowered) => {},
                    Err(refusal) => {
                        if refusal.classify() == FailureClass::EngineFault {
                            return Err(refusal);
                        }
                        if let Some(slot) = slots.get_mut(usize::from(module.first)) {
                            slot.refuse(written.at.node, refusal);
                        }
                    },
                }
            }
        }

        Ok(())
    }

    /// Resolve and file the attributes of every slot in `slots`.
    ///
    /// # Specification
    /// - requires: as [`Self::attribute`], over the slots taken out of the
    ///   collection.
    /// - ensures: as [`Self::attribute`].
    /// - provides: the slot walk of [`Self::attribute`].
    /// - fails: as [`Self::attribute`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::attribute`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each written attribute spends one step, successful
    ///   entries append under their declaration key, and schema errors do not
    ///   prevent other declarations from lowering.
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body resolves every slot's attributes; the capture counts them once"
        )
    )]
    #[spec(
        captures: before = (
            self.fuel.remaining,
            slots.iter().fold(0_usize, |count, slot| {
                count.saturating_add(slot.attributes.len())
            }),
            usize::from(table.attributed_count()),
        ),
        ensures: |ret| {
            self.fuel.remaining <= before.0
                && usize::from(table.attributed_count()) >= before.2
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err() || self.fuel.remaining == before.0.saturating_sub(before.1))
        },
    )]
    fn attribute_slots(
        &mut self,
        slots: &mut [DeclarationSlot<'source>],
        table: &mut AttributeTable,
        arena: &CoreArena,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        for (index, slot) in slots.iter_mut().enumerate() {
            let mut seen: Vec<(RegisteredAttribute, ByteSpan)> = Vec::new();
            for written in core::mem::take(&mut slot.attributes) {
                self.fuel.spend()?;
                match self.read_attribute(&written, &mut seen, arena) {
                    Ok(Filing::Filed { entry, named }) => {
                        if entry.name() == RegisteredAttribute::EXPLICIT_EXITS {
                            let _first = self.asked.insert(SlotIndex::from(index));
                        }
                        self.ask_runs(&entry, [SlotIndex::from(index)]);
                        let key = self.key_at(written.decorates);
                        let attribute = entry.name();
                        table.file(key, entry);
                        table.file_named(key, attribute, named);
                    },
                    Ok(Filing::Unlowered) => {},
                    Err(refusal) => {
                        if refusal.classify() == FailureClass::EngineFault {
                            return Err(refusal);
                        }
                        slot.refuse(written.at.node, refusal);
                    },
                }
            }
        }

        Ok(())
    }

    /// Read every declaration's documentation and check its links.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so every declaration form's key is
    ///   final.
    /// - ensures: every piece of documentation of every declaration, refused or
    ///   not, is read and filed under the content identity of the form it
    ///   documents, pieces in source order; each link to a name the module
    ///   neither declares nor recognises refuses its declaration at the link,
    ///   as a misspelt attribute does. Every slot's documentation list is
    ///   drained.
    /// - provides: the documentation table of the lowered module.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] abort the pass; every other refusal
    ///   is offered to the declaration the documentation belongs to.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both spellings file one text under one key, a link to
    ///   a later declaration resolves, and a link to a missing name refuses its
    ///   declaration at the link's span.
    /// - witness: `lower::tests::documentation_is_filed_under_the_declaration_key`
    /// - witness: `lower::tests::a_link_to_a_missing_name_is_refused_at_the_link`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's documentation; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: |ret| {
            self.collected.slots.len() == before
                && ret
                    .as_ref()
                    .err()
                    .is_none_or(|refusal| refusal.classify() == FailureClass::EngineFault)
                && (ret.is_err() || self.collected.slots.iter().all(|slot| slot.docs.is_empty()))
        },
    )]
    fn document(
        &mut self
    ) -> Result<BTreeMap<UnitKey, Documentation<'source>>, LoweringRefusal<'source>>
    {
        let mut filed: BTreeMap<UnitKey, Documentation<'source>> = BTreeMap::new();
        let mut slots = core::mem::take(&mut self.collected.slots);
        let outcome = self.document_slots(&mut slots, &mut filed);
        self.collected.slots = slots;

        outcome.map(|()| filed)
    }

    /// Read and file the documentation of every slot in `slots` into `filed`.
    ///
    /// # Specification
    /// - requires: as [`Self::document`], over the slots taken out of the
    ///   collection.
    /// - ensures: as [`Self::document`]; each piece spends one step.
    /// - provides: the slot walk of [`Self::document`].
    /// - fails: as [`Self::document`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::document`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::document`], and a link to a module, its
    ///   member and a constructor, each resolved.
    /// - witness: `lower::tests::documentation_is_filed_under_the_declaration_key`
    /// - witness: `lower::tests::a_link_to_a_missing_name_is_refused_at_the_link`
    /// - witness: `lower::tests::a_link_resolves_to_a_module_its_member_or_a_constructor`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body drains every slot's documentation; the check reads each slot once"
        )
    )]
    #[spec(
        captures: before = self.fuel.remaining,
        ensures: |ret| self.fuel.remaining <= before
            && (ret.is_err() || slots.iter().all(|slot| slot.docs.is_empty())),
    )]
    fn document_slots(
        &mut self,
        slots: &mut [DeclarationSlot<'source>],
        filed: &mut BTreeMap<UnitKey, Documentation<'source>>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        for slot in slots.iter_mut() {
            for written in core::mem::take(&mut slot.docs) {
                self.fuel.spend()?;
                let documentation = filed.entry(self.key_at(written.documents)).or_default();
                let before = documentation.links().len();
                if let Err(refusal) = read_doc(self.pbg, self.tree, written.at.node, documentation)
                {
                    if refusal.classify() == FailureClass::EngineFault {
                        return Err(refusal);
                    }
                    slot.refuse(written.at.node, refusal);
                    continue;
                }
                for link in documentation.links().get(before ..).unwrap_or_default() {
                    let name = link.name();
                    let spelled: &str = name.as_ref();
                    let path =
                        NamePath::from(spelled.split('.').map(Segment::from).collect::<Vec<_>>());
                    let declared =
                        matches!(
                            self.recognition.resolve_path(&path),
                            PathResolution::Complete(_)
                        ) || self.collected.by_name.keys().any(|&(_, held)| held == name)
                            || self.collected.modules.keys().any(|&(_, held)| held == name)
                            || self
                                .collected
                                .constructors
                                .keys()
                                .any(|&(_, held)| held == name);
                    if !declared {
                        slot.refuse(written.at.node, LoweringRefusal::UnresolvedDocLink {
                            span: link.span(),
                            name,
                        });
                    }
                }
            }
        }

        Ok(())
    }

    /// Read one written attribute into an entry, or into the refusal it earns.
    ///
    /// # Specification
    /// - requires: `seen` holds the attributes already filed for this declared
    ///   name, with their spans.
    /// - ensures: a registered name whose payload its schema admits yields an
    ///   entry carrying the payload's already-minted value, and joins `seen`; a
    ///   payload whose form is not a value at all is refused before its schema
    ///   is consulted, because being no value is a different fact from being
    ///   the wrong one; nothing is filed for a payload the mint sweep left
    ///   unlowered, which is the case of a payload that itself refused; a text
    ///   where a marker-or-option schema stands is admitted only when it spells
    ///   the option, and is ill-typed as another text otherwise; a bare word
    ///   where a word schema stands is admitted only when it spells one of the
    ///   schema's words, filed with no value, and is ill-typed as another word
    ///   otherwise; a `respects` or `entry` payload is admitted only when it
    ///   names declarations, which the filing carries, and is ill-typed as
    ///   another value otherwise.
    /// - provides: the per-attribute half of the attribute pass.
    /// - fails: yields the unknown-attribute refusal with its bounded
    ///   suggestion, the duplicate refusal naming the first spelling, the
    ///   non-value-payload refusal, the missing-payload refusal, or the
    ///   ill-typed-payload refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The attribute's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a filed entry adds exactly one recognized name and
    ///   keeps its schema, payload and span; duplicate, unknown and ill-typed
    ///   attributes leave the per-declaration seen list unchanged.
    /// - witness: `lower::tests::an_attribute_written_twice_for_one_name_is_refused`
    /// - witness: `lower::tests::an_unknown_attribute_is_refused_with_its_suggestion`
    /// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
    /// - witness: `lower::tests::a_form_payload_is_read_as_one_of_its_words`
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `attribute::tests::a_respects_payload_names_its_laws_in_written_order`
    #[spec(
        captures: before = seen.len(),
        ensures: |ret| match ret.as_ref() {
            | Ok(&Filing::Filed { ref entry, ref named }) => {
                seen.len() == before.saturating_add(1_usize)
                    && seen.last() == Some(&(entry.name(), written.span))
                    && entry.span() == written.span
                    && AttributeRegistry::lookup(written.name)
                        == Maybe::Present((entry.name(), entry.schema()))
                    && match (written.payload, entry.payload()) {
                        | (Payload::Unwritten, Maybe::Absent(payload::Absent::Marker)) => true,
                        | (Payload::Written(_), Maybe::Absent(payload::Absent::Word)) => {
                            matches!(entry.schema(), AttributeSchema::Word(_))
                        },
                        | (Payload::Written(placed), Maybe::Present(value)) => {
                            self.value_at(placed.node) == Maybe::Present(value)
                        },
                        | _ => false,
                    }
                    && named.is_empty() == (entry.schema() != AttributeSchema::Names)
            },
            | Ok(&Filing::Unlowered) => {
                seen.len() == before
                    && matches!(written.payload, Payload::Written(placed) if matches!(self.value_at(placed.node), Maybe::Absent(_)))
            },
            | Err(_) => seen.len() == before,
        },
    )]
    fn read_attribute(
        &self,
        written: &WrittenAttribute<'source>,
        seen: &mut Vec<(RegisteredAttribute, ByteSpan)>,
        arena: &CoreArena,
    ) -> Result<Filing, LoweringRefusal<'source>>
    {
        let Maybe::Present((name, schema)) = AttributeRegistry::lookup(written.name)
        else {
            return Err(LoweringRefusal::UnknownAttribute {
                span: written.span,
                name: written.name,
                suggestion: AttributeRegistry::suggestion(written.name),
            });
        };
        if let Some(&(_held, first)) = seen.iter().find(|&&(held, _first)| held == name) {
            return Err(LoweringRefusal::DuplicateAttribute {
                span: written.span,
                name: written.name,
                first,
            });
        }
        let form = match (
            schema,
            self.payload_form_of(written, name)?,
            written.payload,
        ) {
            (AttributeSchema::MarkerOr(option), PayloadForm::Text, Payload::Written(placed))
                if !matches!(
                    parse_literal(Former::Text, self.text_at(placed)),
                    Maybe::Present(Literal::Text(ref text)) if text.as_ref() == option
                ) =>
            {
                PayloadForm::OtherText
            },
            (AttributeSchema::Word(words), PayloadForm::Word, Payload::Written(placed))
                if !words.contains(&self.text_at(placed).as_ref()) =>
            {
                PayloadForm::OtherWord
            },
            (_, form, _) => form,
        };
        match payload_verdict(schema, form) {
            PayloadVerdict::Admitted => {},
            PayloadVerdict::Missing => {
                return Err(LoweringRefusal::MissingPayload {
                    span: written.span,
                    name,
                    expected: schema,
                });
            },
            PayloadVerdict::IllTyped => {
                let span = match written.payload {
                    Payload::Written(payload) => payload.span,
                    Payload::Unwritten => written.span,
                };
                return Err(LoweringRefusal::IllTypedPayload {
                    span,
                    name,
                    expected: schema,
                    written: form,
                });
            },
        }
        let (value, named) = match written.payload {
            Payload::Unwritten => (Maybe::Absent(payload::Absent::Marker), Vec::new()),
            Payload::Written(_) if matches!(schema, AttributeSchema::Word(_)) => {
                (Maybe::Absent(payload::Absent::Word), Vec::new())
            },
            Payload::Written(placed) => {
                let Maybe::Present(value) = self.value_at(placed.node)
                else {
                    return Ok(Filing::Unlowered);
                };
                let named = if schema == AttributeSchema::Names {
                    let Maybe::Present(named) = names(arena, value)
                    else {
                        return Err(LoweringRefusal::IllTypedPayload {
                            span: placed.span,
                            name,
                            expected: schema,
                            written: form,
                        });
                    };
                    named
                }
                else {
                    Vec::new()
                };
                (Maybe::Present(value), named)
            },
        };
        seen.push((name, written.span));

        Ok(Filing::Filed {
            entry: AttributeEntry::new(name, schema, value, written.span),
            named,
        })
    }

    /// The form an attribute's payload was written in.
    ///
    /// # Specification
    /// - requires: `name` is the registered name `written` resolved to.
    /// - ensures: the absent form for no payload, and the payload form of the
    ///   payload's former otherwise.
    /// - provides: the syntactic half of the payload verdict.
    /// - fails: yields the non-value-payload refusal for a payload that cannot
    ///   stand as a value, and [`LoweringRefusal::UnknownMold`] for a foreign
    ///   mold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::NonValuePayload`] and
    /// [`LoweringRefusal::UnknownMold`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an absent payload is distinguished from a non-value
    ///   form and from an admitted value of the wrong schema-specific shape.
    /// - witness: `lower::tests::a_schema_taking_a_payload_refuses_an_absent_one`
    /// - witness: `lower::tests::a_non_value_payload_is_refused`
    /// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
    #[spec(
        ensures: |ret| {
            ret == match written.payload {
                | Payload::Unwritten => Ok(PayloadForm::Absent),
                | Payload::Written(placed) => match self.payload_former(placed) {
                    | Err(refusal) => Err(refusal),
                    | Ok((Shape::Form { former, .. }, ValueForm(true))) => Ok(payload_form(former)),
                    | Ok((Shape::Form { name: form, .. }, ValueForm(false))) => {
                        Err(LoweringRefusal::NonValuePayload {
                            span: placed.span,
                            name,
                            form,
                        })
                    },
                    | Ok(_) => Ok(PayloadForm::OtherValue),
                },
            }
        },
    )]
    fn payload_form_of(
        &self,
        written: &WrittenAttribute<'source>,
        name: RegisteredAttribute,
    ) -> Result<PayloadForm, LoweringRefusal<'source>>
    {
        let Payload::Written(placed) = written.payload
        else {
            return Ok(PayloadForm::Absent);
        };
        let (shape, value) = self.payload_former(placed)?;
        let Shape::Form { name: form, former } = shape
        else {
            return Ok(PayloadForm::OtherValue);
        };
        if !value.0 {
            return Err(LoweringRefusal::NonValuePayload {
                span: placed.span,
                name,
                form,
            });
        }

        Ok(payload_form(former))
    }

    /// The key of the node at `position` in its unit: the source holding it,
    /// then its top-level form's digest and its rank there.
    ///
    /// # Specification
    /// - requires: positions are interpreted in this source tree.
    /// - ensures: a node with a tree key yields it beside the source of the
    ///   unit whose text holds the node; any other position yields the all-zero
    ///   key in the first source.
    /// - provides: declaration keys for attribute and documentation filing,
    ///   apart for one form written in two sources of the unit (#596).
    /// - fails: the fallback does not distinguish a keyless position from an
    ///   equal key.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — filed attributes use the decorated declaration's key,
    ///   including declarations already refused for an unrelated source error;
    ///   one attributed form in two members of a component settles each under
    ///   its own expectation.
    /// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
    /// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
    /// - witness: `tests::namespace::one_form_in_two_sources_files_its_attributes_apart_596`
    #[spec(
        ensures: |ret| {
            ret == match (self.tree.key(position), self.tree.node(position)) {
                (Some(key), Some(node)) => {
                    UnitKey::new(self.collected.unit.source_at(node.span().start()), key)
                },
                _ => UnitKey::new(
                    SourceIndex::default(),
                    NodeKey::new(NodeDigest::from([0_u8; 32_usize]), FormRank::default()),
                ),
            }
        },
    )]
    fn key_at(
        &self,
        position: NodeIndex,
    ) -> UnitKey
    {
        match (self.tree.key(position), self.tree.node(position)) {
            (Some(key), Some(node)) => {
                UnitKey::new(self.collected.unit.source_at(node.span().start()), key)
            },
            _ => UnitKey::new(
                SourceIndex::default(),
                NodeKey::new(NodeDigest::from([0_u8; 32_usize]), FormRank::default()),
            ),
        }
    }

    /// The key of the form that wrote a half of `slot`'s name a second time,
    /// when that repetition is the slot's refusal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the key at the refusing node when the slot's refusal is a
    ///   duplicate signature or definition; absent otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module defining one member twice keys its second
    ///   definition, which no half reaches.
    /// - witness: `lower::tests::a_duplicate_definition_is_keyed_at_its_form`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_)) == matches!(slot.refusal, Maybe::Present((_, LoweringRefusal::DuplicateDefinition { .. } | LoweringRefusal::DuplicateSignature { .. }))))]
    fn duplicate_key(
        &self,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<UnitKey, declaration_half::Absent>
    {
        match slot.refusal {
            Maybe::Present((
                at,
                LoweringRefusal::DuplicateDefinition { .. }
                | LoweringRefusal::DuplicateSignature { .. },
            )) => Maybe::Present(self.key_at(at)),
            Maybe::Present(_) | Maybe::Absent(_) => {
                Maybe::Absent(declaration_half::Absent::Unwritten)
            },
        }
    }

    /// Mint each callable operation's type and body from its plan.
    ///
    /// # Specification
    /// - requires: the collection planned the operations.
    /// - ensures: one minted type and body per planned operation whose slot
    ///   holds no refusal, every node with the operation's origin.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a planned operation lowers to a completed declaration
    ///   the checker accepts and the machine runs.
    /// - witness: `operation::tests::a_many_out_operation_lowers_to_a_function_the_checker_accepts`
    /// - witness: `operation::tests::a_call_reaches_the_operation_before_a_builtin_of_its_name`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body mints every planned operation once; the check looks up each minted slot once"
        )
    )]
    #[spec(ensures: self.operated.keys().all(|slot| self.collected.operations.contains_key(slot)))]
    fn mint_operations(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        for (&slot, plan) in self
            .collected
            .operations
            .range(SlotIndex::from(self.current.slots) ..)
        {
            let Some(entry) = self.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let origin = Origin::new(entry.named.node, entry.named.span);
            let minted = crate::operation::mint_operation(plan, sink.arena, sink.origins, origin);
            let _first = self.operated.insert(slot, minted);
        }
    }

    /// Assemble one declaration per slot, in admission order.
    ///
    /// # Specification
    /// - requires: the classification, the mint sweep and the attribute pass
    ///   have all run.
    /// - ensures: a slot holding a refusal yields the refused outcome; a slot
    ///   whose signature and definition both lowered yields the completed
    ///   outcome — a witness's definition being the member it re-states; a
    ///   signature alone yields the uncompleted outcome, which is the
    ///   obligation this module owes; a definition alone yields the bodiless
    ///   outcome. A held slot holding no refusal yields nothing, and neither
    ///   does a witness whose member refused: there is no member to state a
    ///   second type for. Each declaration keeps its container, its role and
    ///   where its name tile is written, and takes its own origin token, handed
    ///   out in admission order.
    /// - provides: the declaration list a checker drives.
    /// - fails: never — a slot with neither half lowered and no refusal
    ///   contributes no declaration, which the classification makes unreachable
    ///   for every slot but a held one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — completed, one-sided and refused declarations retain
    ///   their own source metadata and appear in admission order; skipped
    ///   unminted slots do not fabricate declaration origins or change constant
    ///   coordinates.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
    /// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
    /// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
    /// - witness: `tests::modules::module_members_admit_in_source_order`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body assembles a row from every slot once; the check rebuilds each row once and compares it"
        )
    )]
    #[spec(
        captures: before = usize::from(origins.declaration_count()),
        ensures: |ret| {
            usize::from(origins.declaration_count()) == before.saturating_add(ret.len())
                && ret
                    .iter()
                    .map(|row| {
                        (
                            row.name(),
                            row.container(),
                            row.role(),
                            row.constant(),
                            row.span(),
                            row.named(),
                            row.signature(),
                            row.definition(),
                            row.duplicate(),
                            row.outcome(),
                            origins.declaration(row.origin()),
                        )
                    })
                    .eq(self.collected.slots.iter().enumerate().filter_map(
                        |(position, slot)| match self.outcome(SlotIndex::from(position), slot) {
                            | Maybe::Absent(_) => None,
                            | Maybe::Present(outcome) => Some((
                                slot.name,
                                slot.container,
                                slot.role,
                                slot.constant,
                                slot.introduced_by.span,
                                slot.named.span,
                                slot.signature
                                    .map(|half| self.key_at(half.declaration.node)),
                                slot.definition
                                    .map(|half| self.key_at(half.declaration.node)),
                                self.duplicate_key(slot),
                                outcome,
                                Maybe::Present(Origin::new(
                                    slot.introduced_by.node,
                                    slot.introduced_by.span,
                                )),
                            )),
                        },
                    ))
        },
    )]
    fn assemble(
        &self,
        origins: &mut OriginTable,
    ) -> Vec<LoweredDeclaration<'source>>
    {
        let mut declarations = Vec::with_capacity(self.collected.slots.len());
        for (position, slot) in self.collected.slots.iter().enumerate() {
            let Maybe::Present(outcome) = self.outcome(SlotIndex::from(position), slot)
            else {
                continue;
            };
            let introduced = slot.introduced_by;
            let origin = origins.record_declaration(Origin::new(introduced.node, introduced.span));
            declarations.push(LoweredDeclaration::from(DeclarationParts {
                name: slot.name,
                container: slot.container,
                role: slot.role,
                constant: slot.constant,
                span: introduced.span,
                named: slot.named.span,
                origin,
                signature: slot
                    .signature
                    .map(|half| self.key_at(half.declaration.node)),
                definition: slot
                    .definition
                    .map(|half| self.key_at(half.declaration.node)),
                duplicate: self.duplicate_key(slot),
                outcome,
            }));
        }

        declarations
    }

    /// What the slot at `position` amounts to in the lowered module.
    ///
    /// # Specification
    /// - requires: the slot and its member coordinates are interpreted in this
    ///   lowering run, and the applications are minted.
    /// - ensures: a slot of a functor's template is its own refusal when
    ///   [`Self::own_outcome`] refuses it, so a refusal inside a functor is
    ///   reported once, where it was written, and templated otherwise; a slot
    ///   of an application is the declaration its renaming minted, unminted
    ///   when its template refused or its argument's type did not lower; a
    ///   module's own slot is [`Self::own_outcome`], except that one
    ///   [`Self::own_outcome`] leaves absent while it holds a half that lowers
    ///   to a core term — any but a top-level `oper`'s, or a witness of a
    ///   member refused where it was written — is refused
    ///   [`LoweringRefusal::Unminted`] at the declaration, by its name.
    /// - provides: the per-slot row [`Self::assemble`] files, so a declaration
    ///   the lowering collected either lowers or is refused by name, never
    ///   dropped from the module.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a functor's body yields no declaration and each of
    ///   two applications yields its own; a function whose two halves the mint
    ///   left unminted, with no refusal filed, is refused by name where it used
    ///   to vanish.
    /// - witness: `tests::modules::functors::a_functor_body_never_reaches_the_kernel`
    /// - witness: `tests::modules::functors::two_applications_mint_distinct_atoms`
    /// - witness: `lower::tests::a_declaration_minting_neither_half_is_refused_by_name_455`
    #[spec(
        ensures: |ret| match self.collected.stratum_of(slot.container) {
            | Stratum::Module => match self.own_outcome(position, slot) {
                | Maybe::Absent(_) if self.lowers_a_half(slot) == Owed::Owed => ret == Maybe::Present(DeclarationOutcome::Refused(LoweringRefusal::Unminted {
                    span: slot.introduced_by.span,
                    name: slot.name,
                })),
                | own => ret == own,
            },
            | Stratum::Functor(_) | Stratum::Parameter(_) => match self.own_outcome(position, slot) {
                | Maybe::Present(DeclarationOutcome::Refused(refusal)) => ret == Maybe::Present(DeclarationOutcome::Refused(refusal)),
                | _ => ret == Maybe::Absent(lowered::Absent::Templated),
            },
            | Stratum::Instance(_) => ret == self.instantiated.get(&position).copied().map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
        },
    )]
    fn outcome(
        &self,
        position: SlotIndex,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>
    {
        match self.collected.stratum_of(slot.container) {
            Stratum::Module => match self.own_outcome(position, slot) {
                Maybe::Absent(reason) => match self.lowers_a_half(slot) {
                    Owed::Owed => {
                        Maybe::Present(DeclarationOutcome::Refused(LoweringRefusal::Unminted {
                            span: slot.introduced_by.span,
                            name: slot.name,
                        }))
                    },
                    Owed::Nothing => Maybe::Absent(reason),
                },
                Maybe::Present(outcome) => Maybe::Present(outcome),
            },
            Stratum::Functor(_) | Stratum::Parameter(_) => match self.own_outcome(position, slot) {
                Maybe::Present(DeclarationOutcome::Refused(refusal)) => {
                    Maybe::Present(DeclarationOutcome::Refused(refusal))
                },
                Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Templated),
            },
            Stratum::Instance(_) => self
                .instantiated
                .get(&position)
                .copied()
                .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
        }
    }

    /// Whether the slot holds a half that lowers to a core term.
    ///
    /// # Specification
    /// - requires: the slot's member coordinates are interpreted in this
    ///   lowering run.
    /// - ensures: [`Owed::Owed`] when either half is present and is neither a
    ///   top-level `oper`'s, which lowers to no core term, nor a witness of a
    ///   member that carries a refusal, which is reported where the member is
    ///   written; [`Owed::Nothing`] otherwise.
    /// - provides: the halves whose absence [`Self::outcome`] refuses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function whose halves the mint left unminted owes a
    ///   declaration; reading a top-level `oper` as owing one would refuse
    ///   every such declaration across the corpus.
    /// - witness: `lower::tests::a_declaration_minting_neither_half_is_refused_by_name_455`
    #[spec(
        ensures: |ret| (ret == Owed::Owed) == [slot.signature, slot.definition].into_iter().any(|half| match half {
            | Maybe::Present(Half { operand: Operand::Signature, .. }) | Maybe::Absent(_) => false,
            | Maybe::Present(Half { operand: Operand::Member(target), .. }) => !self
                .collected
                .slots
                .get(usize::from(target))
                .is_some_and(|member| matches!(member.refusal, Maybe::Present(_))),
            | Maybe::Present(_) => true,
        }),
    )]
    fn lowers_a_half(
        &self,
        slot: &DeclarationSlot<'source>,
    ) -> Owed
    {
        let owed = [slot.signature, slot.definition]
            .into_iter()
            .any(|half| match half {
                Maybe::Present(Half {
                    operand: Operand::Signature | Operand::World,
                    ..
                })
                | Maybe::Absent(_) => false,
                Maybe::Present(Half {
                    operand: Operand::Member(target),
                    ..
                }) => !self
                    .collected
                    .slots
                    .get(usize::from(target))
                    .is_some_and(|member| matches!(member.refusal, Maybe::Present(_))),
                Maybe::Present(Half {
                    operand:
                        Operand::Written(_)
                        | Operand::Function
                        | Operand::Data(_)
                        | Operand::Words(_)
                        | Operand::Loop { .. }
                        | Operand::Operation
                        | Operand::Presented
                        | Operand::Code
                        | Operand::Model(_),
                    ..
                }) => true,
            });
        if owed { Owed::Owed } else { Owed::Nothing }
    }

    /// What the slot at `position` amounts to by its own halves, whatever
    /// module it belongs to.
    ///
    /// # Specification
    /// - requires: the slot and its member coordinates are interpreted in this
    ///   lowering run.
    /// - ensures: a stored refusal takes precedence, then a refusal a check
    ///   after minting filed; a world declaration is the world it names; a data
    ///   declaration, or a described family the decoder admitted, `Theory`
    ///   among them, is the index of its minted signature; an operation, and a
    ///   `theory` block's definition, is the type and body minted for it; an
    ///   abstract slot is the abstract type it lowered to, and a kind witness
    ///   the check of its type member's code at the kind; otherwise the
    ///   available signature — written, a function tail's, or the type a model
    ///   derives — and body select Completed, Uncompleted or Bodied.
    /// - provides: the declaration outcome without manufacturing absent halves.
    /// - fails: a refused member witness is Unminted; if neither half exists,
    ///   the signature’s absence is preserved.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the three successful half combinations remain
    ///   distinct from a stored refusal, and an ascription witness does not
    ///   resurrect a refused member. Explicit signatures keep precedence over
    ///   derived ones.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
    /// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
    /// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
    /// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
    /// - witness: `lower::native::tests::a_data_declaration_lowers_to_its_signature`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::an_abstract_component_kinds_at_a_universe`
    #[spec(
        ensures: |ret| {
            if let Maybe::Present((_at, refusal)) = slot.refusal {
                ret == Maybe::Present(DeclarationOutcome::Refused(refusal))
            }
            else if let Some(&refusal) = self.faults.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Refused(refusal))
            }
            else if let Maybe::Present(Half { operand: Operand::World, .. }) = slot.definition {
                ret == Maybe::Present(DeclarationOutcome::World)
            }
            else if let Maybe::Present(Half { operand: Operand::Data(form), .. }) = slot.definition {
                ret == self.signatures.get(&form).map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| Maybe::Present(DeclarationOutcome::Data(index)))
            }
            else if let Maybe::Present(Half { operand: Operand::Words(words), .. }) = slot.definition {
                ret == self.worded.get(&words).map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| Maybe::Present(DeclarationOutcome::Data(index)))
            }
            else if let Maybe::Present(Half { operand: Operand::Loop { .. }, .. }) = slot.definition {
                ret == self.looped.get(&position).map_or(Maybe::Absent(lowered::Absent::Unminted), |&(declared_type, body)| Maybe::Present(DeclarationOutcome::Completed { declared_type, body }))
            }
            else if let Some(&index) = self.described.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Data(index))
            }
            else if let Maybe::Present(Half { operand: Operand::Operation, .. }) = slot.definition {
                ret == self.operated.get(&position).map_or(Maybe::Absent(lowered::Absent::Unminted), |&(declared_type, body)| Maybe::Present(DeclarationOutcome::Completed { declared_type, body }))
            }
            else if let Maybe::Present(Half { operand: Operand::Presented, .. }) = slot.definition {
                ret == self.presented.get(&position).map_or(Maybe::Absent(lowered::Absent::Unminted), |&(declared_type, body)| Maybe::Present(DeclarationOutcome::Completed { declared_type, body }))
            }
            else if let Some(&sealing) = self.sealings.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Abstract(sealing))
            }
            else if let Some(&(declared_type, body)) = self.kind_checks.get(&position) {
                ret == Maybe::Present(DeclarationOutcome::Completed { declared_type, body })
            }
            else if matches!(slot.definition, Maybe::Present(Half { operand: Operand::Member(target), .. }) if self.collected.slots.get(usize::from(target)).is_some_and(|member| matches!(member.refusal, Maybe::Present(_))))
            {
                ret == Maybe::Absent(lowered::Absent::Unminted)
            }
            else {
                let declared = match slot.signature {
                    | Maybe::Present(half) => match half.operand {
                        | Operand::Written(written) => self.value_type_at(written.node),
                        | Operand::Function => self.signature_at(half.declaration.node),
                        | Operand::Model(_) => self.modelled.get(&position).copied().map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                        | Operand::Member(_) | Operand::Data(_) | Operand::Words(_) | Operand::Loop { .. } | Operand::Operation | Operand::Signature | Operand::Presented | Operand::Code | Operand::World => Maybe::Absent(lowered::Absent::Unminted),
                    },
                    | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
                };
                let body = match slot.definition {
                    | Maybe::Present(half) => match half.operand {
                        | Operand::Written(written) => self.value_at(written.node),
                        | Operand::Function => self.function_body_at(half.declaration.node),
                        | Operand::Member(_) => self
                            .witnessed
                            .get(&position)
                            .copied()
                            .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                        | Operand::Data(_) | Operand::Words(_) | Operand::Loop { .. } | Operand::Operation | Operand::Signature | Operand::Presented | Operand::Code | Operand::Model(_) | Operand::World => Maybe::Absent(lowered::Absent::Unminted),
                    },
                    | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
                };
                match ret {
                    | Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body: value,
                    }) => {
                        declared == Maybe::Present(declared_type) && body == Maybe::Present(value)
                    },
                    | Maybe::Present(DeclarationOutcome::Uncompleted { declared_type }) => {
                        declared == Maybe::Present(declared_type)
                            && matches!(body, Maybe::Absent(_))
                    },
                    | Maybe::Present(DeclarationOutcome::Bodied { body: value }) => {
                        matches!(declared, Maybe::Absent(_)) && body == Maybe::Present(value)
                    },
                    | Maybe::Absent(reason) => {
                        declared == Maybe::Absent(reason) && matches!(body, Maybe::Absent(_))
                    },
                    | Maybe::Present(DeclarationOutcome::Refused(_) | DeclarationOutcome::Data(_) | DeclarationOutcome::Abstract(_) | DeclarationOutcome::World) => false,
                }
            }
        },
    )]
    fn own_outcome(
        &self,
        position: SlotIndex,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>
    {
        if let Maybe::Present((_at, refusal)) = slot.refusal {
            return Maybe::Present(DeclarationOutcome::Refused(refusal));
        }
        if let Some(&refusal) = self.faults.get(&position) {
            return Maybe::Present(DeclarationOutcome::Refused(refusal));
        }
        if let Maybe::Present(Half {
            operand: Operand::World,
            ..
        }) = slot.definition
        {
            return Maybe::Present(DeclarationOutcome::World);
        }
        if let Maybe::Present(Half {
            operand: Operand::Data(form),
            ..
        }) = slot.definition
        {
            return self
                .signatures
                .get(&form)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| {
                    Maybe::Present(DeclarationOutcome::Data(index))
                });
        }
        if let Maybe::Present(Half {
            operand: Operand::Words(words),
            ..
        }) = slot.definition
        {
            return self
                .worded
                .get(&words)
                .map_or(Maybe::Absent(lowered::Absent::Unminted), |&index| {
                    Maybe::Present(DeclarationOutcome::Data(index))
                });
        }
        if let Maybe::Present(Half {
            operand: Operand::Loop { .. },
            ..
        }) = slot.definition
        {
            return self.looped.get(&position).map_or(
                Maybe::Absent(lowered::Absent::Unminted),
                |&(declared_type, body)| {
                    Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    })
                },
            );
        }
        if let Some(&index) = self.described.get(&position) {
            return Maybe::Present(DeclarationOutcome::Data(index));
        }
        if let Maybe::Present(Half {
            operand: Operand::Operation,
            ..
        }) = slot.definition
        {
            return self.operated.get(&position).map_or(
                Maybe::Absent(lowered::Absent::Unminted),
                |&(declared_type, body)| {
                    Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    })
                },
            );
        }
        if let Maybe::Present(Half {
            operand: Operand::Presented,
            ..
        }) = slot.definition
        {
            return self.presented.get(&position).map_or(
                Maybe::Absent(lowered::Absent::Unminted),
                |&(declared_type, body)| {
                    Maybe::Present(DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    })
                },
            );
        }
        if let Some(&sealing) = self.sealings.get(&position) {
            return Maybe::Present(DeclarationOutcome::Abstract(sealing));
        }
        if let Some(&(declared_type, body)) = self.kind_checks.get(&position) {
            return Maybe::Present(DeclarationOutcome::Completed {
                declared_type,
                body,
            });
        }
        if let Maybe::Present(Half {
            operand: Operand::Member(target),
            ..
        }) = slot.definition
            && let Some(Maybe::Present(_)) = self
                .collected
                .slots
                .get(usize::from(target))
                .map(|member| member.refusal)
        {
            return Maybe::Absent(lowered::Absent::Unminted);
        }
        let declared = match slot.signature {
            Maybe::Present(half) => match half.operand {
                Operand::Written(written) => self.value_type_at(written.node),
                Operand::Function => self.signature_at(half.declaration.node),
                Operand::Model(_) => self
                    .modelled
                    .get(&position)
                    .copied()
                    .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                Operand::Member(_)
                | Operand::Data(_)
                | Operand::Words(_)
                | Operand::Loop { .. }
                | Operand::Operation
                | Operand::Signature
                | Operand::Presented
                | Operand::Code
                | Operand::World => Maybe::Absent(lowered::Absent::Unminted),
            },
            Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        let body = match slot.definition {
            Maybe::Present(half) => match half.operand {
                Operand::Written(written) => self.value_at(written.node),
                Operand::Function => self.function_body_at(half.declaration.node),
                Operand::Member(_) => self
                    .witnessed
                    .get(&position)
                    .copied()
                    .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
                Operand::Data(_)
                | Operand::Words(_)
                | Operand::Loop { .. }
                | Operand::Operation
                | Operand::Signature
                | Operand::Presented
                | Operand::Code
                | Operand::Model(_)
                | Operand::World => Maybe::Absent(lowered::Absent::Unminted),
            },
            Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        match (declared, body) {
            (Maybe::Present(declared_type), Maybe::Present(body)) => {
                Maybe::Present(DeclarationOutcome::Completed {
                    declared_type,
                    body,
                })
            },
            (Maybe::Present(declared_type), Maybe::Absent(_)) => {
                Maybe::Present(DeclarationOutcome::Uncompleted { declared_type })
            },
            (Maybe::Absent(_), Maybe::Present(body)) => {
                Maybe::Present(DeclarationOutcome::Bodied { body })
            },
            (Maybe::Absent(reason), Maybe::Absent(_)) => Maybe::Absent(reason),
        }
    }

    /// Carry each refused manifest type component's refusal to every
    /// declaration whose type names it.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: a declaration owning a type head that stands for a manifest
    ///   component whose type refused holds that refusal too, at the head's
    ///   position, so it keeps the lowest-positioned refusal it has; the
    ///   components are taken in signature order, so a component naming an
    ///   earlier refused one passes the refusal on.
    /// - provides: the rule that a declaration is not minted over a type that
    ///   did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of manifest aliases carries the original
    ///   located refusal into a member even when its body has independently
    ///   failed; the unrelated following declaration still lowers.
    /// - witness: `tests::modules::manifest_refusals_propagate_transitively_before_minting`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body sorts the manifest references and visits each once; the check reads each once and its neighbour once"
        )
    )]
    #[spec(
        captures: before = (self.manifests.len(), self.collected.slots.len()),
        ensures: |_| {
            self.manifests.len() == before.0 && self.collected.slots.len() == before.1 && self.manifests.windows(2).all(|pair| match *pair { [left, right] => left.0 <= right.0, _ => false }) && self.manifests.iter().all(|&(held, head)| { if !matches!(self.collected.slots.get(usize::from(held)), Some(slot) if matches!(slot.refusal, Maybe::Present(_))) { return true; } match self.collected.owner_of(head) { Maybe::Absent(_) => true, Maybe::Present(owner) => self.collected.slots.get(usize::from(owner)).is_none_or(|slot| matches!(slot.refusal, Maybe::Present((at, _)) if at <= head)) } })
        },
    )]
    fn propagate_manifests(&mut self)
    {
        let mut named = core::mem::take(&mut self.manifests);
        named.sort_by_key(|&(held, _head)| held);
        for &(held, head) in &named {
            let Some(Maybe::Present((_at, refusal))) = self
                .collected
                .slots
                .get(usize::from(held))
                .map(|slot| slot.refusal)
            else {
                continue;
            };
            let Maybe::Present(owner) = self.collected.owner_of(head)
            else {
                continue;
            };
            if let Some(slot) = self.collected.slots.get_mut(usize::from(owner)) {
                slot.refuse(head, refusal);
            }
        }
        self.manifests = named;
    }

    /// One stratum item per module, in pre-order.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: each module's path, its form's bytes, the value components
    ///   and nested modules it exports in export order — a value component with
    ///   the constant a reference reads, the witness an opaque ascription
    ///   exports in its member's place — each exported type component that
    ///   reads a type with the type it lowered to, each sealed one with its
    ///   atom, and whether matching coerced its body; a hidden member appears
    ///   in no item.
    /// - provides: the stratum half of [`LoweredModule`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested paths retain their member names, an ascription
    ///   exports only its selected values and modules, manifest components keep
    ///   their lowered type or their explicit Unlowered status, and a sealed
    ///   module exports its atoms and its witnesses.
    /// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
    /// - witness: `tests::modules::module_signature_matching_hides_extra_members`
    /// - witness: `tests::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::a_signed_member_of_a_sealed_module_exports_its_witness`
    #[spec(
        ensures: |ret| {
            ret.len() == self.collected.structures.len()
                && ret
                    .iter()
                    .zip(&self.collected.structures)
                    .all(|(lowered, structure)| {
                        if lowered.path().last() != Some(&structure.name)
                            || lowered.span() != structure.declared_by.span
                            || lowered.coerced() != structure.coerced
                        {
                            return false;
                        }
                        let mut values = lowered.values().iter();
                        let mut modules = lowered.modules().iter();
                        for &export in &structure.exports {
                            match export {
                                | Member::Slot(slot) => {
                                    let read = structure.exported_as.get(&slot).copied().unwrap_or(slot);
                                    if self.collected.slots.get(usize::from(slot)).is_some_and(
                                        |member| {
                                            !values.next().is_some_and(|value| {
                                                value.name == member.name
                                                    && usize::from(value.constant) == usize::from(read)
                                            })
                                        },
                                    ) {
                                        return false;
                                    }
                                },
                                | Member::Module(nested) => {
                                    if self
                                        .collected
                                        .structures
                                        .get(usize::from(nested))
                                        .is_some_and(|member| modules.next() != Some(&member.name))
                                    {
                                        return false;
                                    }
                                },
                            }
                        }
                        let mut types = lowered.types().iter();
                        let mut sealed = lowered.sealed().iter();
                        let stated = structure.exported_types().iter().all(|component| match component.meaning {
                            | TypeMeaning::Manifest(defined) => types.next().is_some_and(|lowered| {
                                lowered.name == component.name
                                    && lowered.defined
                                        == match self.value_type_at(defined.node) {
                                            | Maybe::Present(id) => Maybe::Present(id),
                                            | Maybe::Absent(_) => Maybe::Absent(manifest_type::Absent::Unlowered),
                                        }
                            }),
                            | TypeMeaning::Sealed => sealed.next().is_some_and(|lowered| {
                                lowered.name == component.name
                                    && usize::from(lowered.atom) == usize::from(component.held)
                            }),
                            | TypeMeaning::Instantiated { defined, instance } => types.next().is_some_and(|lowered| {
                                lowered.name == component.name
                                    && lowered.defined
                                        == self.instance_types.get(&(instance, defined.node)).copied().map_or(Maybe::Absent(manifest_type::Absent::Unlowered), Maybe::Present)
                            }),
                            | TypeMeaning::Family(_) => true,
                        });
                        stated
                            && lowered.stratum() == structure.stratum
                            && values.next().is_none()
                            && modules.next().is_none()
                            && types.next().is_none()
                            && sealed.next().is_none()
                    })
        },
    )]
    fn structures(&self) -> Vec<LoweredStructure<'source>>
    {
        let mut lowered = Vec::with_capacity(self.collected.structures.len());
        for (position, structure) in self.collected.structures.iter().enumerate() {
            let mut values = Vec::new();
            let mut modules = Vec::new();
            for &export in &structure.exports {
                match export {
                    Member::Slot(slot) => {
                        let read = structure.exported_as.get(&slot).copied().unwrap_or(slot);
                        if let Some(member) = self.collected.slots.get(usize::from(slot))
                            && let Some(reader) = self.collected.slots.get(usize::from(read))
                        {
                            values.push(ValueComponent {
                                name: member.name,
                                constant: reader.constant,
                            });
                        }
                    },
                    Member::Module(nested) => {
                        if let Some(member) = self.collected.structures.get(usize::from(nested)) {
                            modules.push(member.name);
                        }
                    },
                }
            }
            let mut types = Vec::new();
            let mut sealed = Vec::new();
            for component in structure.exported_types() {
                match component.meaning {
                    TypeMeaning::Manifest(defined) => types.push(ManifestComponent {
                        name: component.name,
                        defined: match self.value_type_at(defined.node) {
                            Maybe::Present(id) => Maybe::Present(id),
                            Maybe::Absent(_) => Maybe::Absent(manifest_type::Absent::Unlowered),
                        },
                    }),
                    TypeMeaning::Sealed => {
                        if let Some(atom) = self.collected.slots.get(usize::from(component.held)) {
                            sealed.push(SealedComponent {
                                name: component.name,
                                atom: atom.constant,
                            });
                        }
                    },
                    TypeMeaning::Instantiated { defined, instance } => {
                        types.push(ManifestComponent {
                            name: component.name,
                            defined: self
                                .instance_types
                                .get(&(instance, defined.node))
                                .copied()
                                .map_or(
                                    Maybe::Absent(manifest_type::Absent::Unlowered),
                                    Maybe::Present,
                                ),
                        });
                    },
                    TypeMeaning::Family(_) => {},
                }
            }
            lowered.push(LoweredStructure::new(
                self.collected
                    .path(Container::Module(StructureIndex::from(position))),
                structure.declared_by.span,
                values,
                modules,
                types,
                sealed,
                structure.coerced,
                structure.stratum,
            ));
        }

        lowered
    }

    /// The binders in scope at each node the lowering read under a binder:
    /// the scope's frames, beside each such node's span and its reading's
    /// frame.
    ///
    /// # Specification
    /// - requires: every source is lowered.
    /// - ensures: [`Scope::in_scope`] over this lowering's scope and one span
    ///   per node whose reading names an inner frame, a node of a refused
    ///   declaration included.
    /// - provides: the table [`LoweredModule::in_scope`] keeps.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the table's own builder and query carry the
    ///   predicates.
    /// - intension: one pass over the node readings.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::InScope::binders_at`].
    /// - witness: `tests::scopes::the_binders_in_scope_are_kept_for_a_refused_declaration_831`
    fn in_scope(&self) -> crate::InScope
    {
        let read = self
            .readings
            .iter()
            .enumerate()
            .filter_map(|(position, reading)| match reading.frame() {
                Frame::Inner(frame) => self
                    .tree
                    .node(NodeIndex::from(position))
                    .map(|node| (node.span(), frame)),
                Frame::Outermost => None,
            })
            .collect();
        self.scope.in_scope(read)
    }
}

/// What reading one attribute produced, short of a refusal.
///
/// # Specification
/// - requires: coordinates, when present, are interpreted in their originating
///   run.
/// - ensures: A filed entry has passed registry and payload checks; an
///   unlowered payload contributes no entry or seen-name update.
/// - provides: The non-refusal outcome of reading one attribute.
/// - fails: none as a data value; interpretation belongs to its consumers.
/// - panics: none as a data value.
/// - executable: none — The written attribute and seen-name list are absent;
///   `read_attribute` states the executable filing and state-update relation.
///
/// # Adequacy
/// - hypothesis: L3 — valid entries are filed under the declaration key, while
///   a refused declaration can still retain an independently valid payload.
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_key`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_key`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Filing
{
    /// The entry to file, and the declarations a `respects` or `entry`
    /// payload names: empty for every other attribute, and never empty for
    /// those two, whose payload names at least one.
    Filed
    {
        /// The entry.
        entry: AttributeEntry,
        /// The declarations its payload names, in written order.
        named: Vec<ConstantIndex>,
    },
    /// Nothing: the payload did not lower, which only a payload that itself
    /// refused leaves behind.
    Unlowered,
}

impl Sink<'_>
{
    /// Write `bridge` over `minted`, the core node of the syntax node at
    /// `origin`.
    ///
    /// # Specification
    /// - requires: `minted` is what the node's own plan minted.
    /// - ensures: a bare node is `minted` unchanged; a forced value is minted
    ///   as a force over it, a returned value type as a returner over it, a
    ///   quoted type as the quote of it at its own sort, a computation standing
    ///   as an endpoint as the value it returns, and a value standing at a tail
    ///   as the returner over it, each with `origin` marked as the insertion it
    ///   is; nothing when the node did not lower at the sort its bridge leaves,
    ///   which the classification makes unreachable.
    /// - provides: the minting half of the insertions a position's sort
    ///   decides.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forced heads, positive results, quoted types and
    ///   values at a tail acquire the intended inserted provenance, while an
    ///   author-written force stays written.
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    /// - witness: `lower::exits::tests::a_tail_without_an_exit_takes_the_one_its_polarity_names`
    #[spec(
        ensures: |ret| match bridge {
            | Bridge::Bare => ret == minted,
            | Bridge::Inserted(insertion) => match (minted, insertion, ret) {
                | (Maybe::Absent(reason), ..) => ret == Maybe::Absent(reason),
                | (
                    Maybe::Present(Lowered::Value(_)),
                    Insertion::Force | Insertion::Return,
                    Maybe::Present(Lowered::Computation(id)),
                ) => self.origins.computation(id) == Maybe::Present(origin.inserted(insertion)),
                | (
                    Maybe::Present(Lowered::ValueType(_)),
                    Insertion::Returner,
                    Maybe::Present(Lowered::CompType(id)),
                ) => self.origins.comp_type(id) == Maybe::Present(origin.inserted(insertion)),
                | (
                    Maybe::Present(Lowered::ValueType(_) | Lowered::CompType(_)),
                    Insertion::Quote,
                    Maybe::Present(Lowered::Value(id)),
                )
                | (
                    Maybe::Present(Lowered::Computation(_)),
                    Insertion::Endpoint | Insertion::Nested,
                    Maybe::Present(Lowered::Value(id)),
                ) => self.origins.value(id) == Maybe::Present(origin.inserted(insertion)),
                | (Maybe::Present(Lowered::Value(_)), Insertion::Force | Insertion::Return, _)
                | (Maybe::Present(Lowered::ValueType(_)), Insertion::Returner, _)
                | (Maybe::Present(Lowered::Computation(_)), Insertion::Endpoint | Insertion::Nested, _)
                | (
                    Maybe::Present(Lowered::ValueType(_) | Lowered::CompType(_)),
                    Insertion::Quote,
                    _,
                ) => false,
                | _ => ret == Maybe::Absent(lowered::Absent::OtherSort),
            },
        },
    )]
    fn bridge(
        &mut self,
        minted: Maybe<Lowered, lowered::Absent>,
        bridge: Bridge,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let Bridge::Inserted(insertion) = bridge
        else {
            return minted;
        };
        let inserted = origin.inserted(insertion);
        match (minted, insertion) {
            (Maybe::Present(Lowered::Value(forced)), Insertion::Force) => {
                let id = self.arena.computation_force(forced);
                Maybe::Present(self.computation(id, inserted))
            },
            (Maybe::Present(Lowered::ValueType(returned)), Insertion::Returner) => {
                let id = self.arena.comp_type_returner(returned);
                self.origins.record_comp_type(id, inserted);
                Maybe::Present(Lowered::CompType(id))
            },
            (Maybe::Present(Lowered::ValueType(quoted)), Insertion::Quote) => {
                let id = self.arena.value_quote(quoted);
                Maybe::Present(self.value(id, inserted))
            },
            (Maybe::Present(Lowered::CompType(quoted)), Insertion::Quote) => {
                let id = self.arena.value_quote_computation(quoted);
                Maybe::Present(self.value(id, inserted))
            },
            (Maybe::Present(Lowered::Computation(returned)), Insertion::Endpoint) => {
                let id = self.arena.value_returned(returned);
                Maybe::Present(self.value(id, inserted))
            },
            (Maybe::Present(Lowered::Computation(nested)), Insertion::Nested) => {
                let id = self.arena.value_nested(nested);
                Maybe::Present(self.value(id, inserted))
            },
            (Maybe::Present(Lowered::Value(returned)), Insertion::Return) => {
                let id = self.arena.computation_return(returned);
                Maybe::Present(self.computation(id, inserted))
            },
            (
                Maybe::Present(_),
                Insertion::Force
                | Insertion::Thunk
                | Insertion::Returner
                | Insertion::Quote
                | Insertion::Decode
                | Insertion::Return
                | Insertion::Classifier
                | Insertion::Match
                | Insertion::Fixpoint
                | Insertion::Loop
                | Insertion::Endpoint
                | Insertion::Identity
                | Insertion::Nested
                | Insertion::Unwind
                | Insertion::Model
                | Insertion::Relation,
            ) => Maybe::Absent(lowered::Absent::OtherSort),
            (Maybe::Absent(reason), _) => Maybe::Absent(reason),
        }
    }

    /// Record `id`'s origin and wrap it as a lowered value.
    ///
    /// # Specification
    /// - requires: the value id follows all values already recorded in this
    ///   origin table.
    /// - ensures: the supplied origin is recorded under the value id and the
    ///   lowered result retains that id and family.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every minted value has its own source origin, and an
    ///   inserted force does not relabel the source value it consumes.
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == Lowered::Value(id) && self.origins.value(id) == Maybe::Present(origin)
        },
    )]
    fn value(
        &mut self,
        id: ValueId,
        origin: Origin,
    ) -> Lowered
    {
        self.origins.record_value(id, origin);

        Lowered::Value(id)
    }

    /// Record `id`'s origin and wrap it as a lowered computation.
    ///
    /// # Specification
    /// - requires: the computation id follows all computations already recorded
    ///   in this origin table.
    /// - ensures: the supplied origin is recorded under the computation id and
    ///   the lowered result retains that id and family.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — written and inserted computations retain their own
    ///   source and provenance rather than borrowing an operand origin.
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    #[spec(
        ensures: |ret| {
            ret == Lowered::Computation(id)
                && self.origins.computation(id) == Maybe::Present(origin)
        },
    )]
    fn computation(
        &mut self,
        id: ComputationId,
        origin: Origin,
    ) -> Lowered
    {
        self.origins.record_computation(id, origin);

        Lowered::Computation(id)
    }

    /// Mint `atom`'s value type and record its origin.
    ///
    /// # Specification
    /// - requires: newly minted type ids follow those already recorded in the
    ///   origin table.
    /// - ensures: the selected unit, integer or text value type is minted and
    ///   receives the supplied origin.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete nullary type heads mint their own core type
    ///   and every minted type carries a source origin.
    /// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    #[spec(
        ensures: |ret| match ret {
            | Lowered::ValueType(id) => self.origins.value_type(id) == Maybe::Present(origin) && match atom {
                TypeAtom::Boolean => self.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Sum(ref parts) if parts.len() == 2 && parts.iter().all(|&part| self.arena.value_type(part) == Some(&ValueType::unit())))),
                TypeAtom::Unit => self.arena.value_type(id) == Some(&ValueType::unit()),
                TypeAtom::Integer => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::Integer)),
                TypeAtom::Text => self.arena.value_type(id) == Some(&ValueType::Base(BaseType::String)),
                TypeAtom::Void => self.arena.value_type(id).is_some_and(|held| matches!(*held, ValueType::Sum(ref parts) if parts.is_empty())),
            },
            | _ => false,
        },
    )]
    fn atom(
        &mut self,
        atom: TypeAtom,
        origin: Origin,
    ) -> Lowered
    {
        let id = match atom {
            TypeAtom::Boolean => {
                let unit = self.arena.value_type_unit();
                self.origins.record_value_type(unit, origin);
                self.arena.value_type_sum(&[unit, unit])
            },
            TypeAtom::Unit => self.arena.value_type_unit(),
            TypeAtom::Integer => self.arena.value_type_base(BaseType::Integer),
            TypeAtom::Text => self.arena.value_type_base(BaseType::String),
            TypeAtom::Void => self.arena.value_type_sum(&[]),
        };
        self.origins.record_value_type(id, origin);

        Lowered::ValueType(id)
    }
}

/// The parameter of a lambda: exactly one identifier between parentheses.
///
/// # Specification
/// - requires: `cursor` stands just past the lambda's `fn`.
/// - ensures: the one parameter's tile, with the cursor past the closing
///   parenthesis.
/// - provides: the binder reading of the lambda.
/// - fails: yields the unadmitted refusal for a typed parameter, the arity
///   refusal for any parameter count but one, and a misplaced-tile refusal for
///   a parameter list out of shape.
/// - panics: none.
///
/// # Errors
/// The lambda's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one and multiple binders select the documented
///   arity boundary; a successful header consumes its closing parenthesis but
///   not the following body, while typed binders remain outside this fragment.
/// - witness: `lower::tests::parameter_headers_preserve_the_body_and_locate_refusals`
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
#[spec(
    captures: input = cursor.clone(),
    ensures: |ret| {
        ret.as_ref().map_or(true, |binder| {
            let mut input = input.clone();
            if matches!(input.tile(TileName::PAREN_OPEN), Maybe::Absent(_)) {
                return false;
            }
            let mut seen = false;
            loop {
                match input.read() {
                    | Maybe::Present(Piece::Tile {
                        label: TileName::IDENTIFIER,
                        at,
                    }) => {
                        if seen || at != *binder {
                            return false;
                        }
                        seen = true;
                    },
                    | Maybe::Present(Piece::Tile {
                        label: TileName::COMMA,
                        ..
                    }) => {},
                    | Maybe::Present(Piece::Tile {
                        label: TileName::PAREN_CLOSE,
                        ..
                    }) => {
                        return seen
                            && cursor.peek() == input.peek()
                            && cursor.here() == input.here();
                    },
                    | _ => return false,
                }
            }
        })
    },
)]
fn parameter<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
) -> Result<Placed, LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    let mut first: Option<Placed> = None;
    let mut count = 0_usize;
    loop {
        if let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER) {
            count = count.saturating_add(1_usize);
            first = first.or(Some(binder));
            continue;
        }
        if let Maybe::Present(_) = cursor.tile(TileName::COMMA) {
            continue;
        }
        if let Maybe::Present(_) = cursor.at(TileName::COLON) {
            return Err(site.folded(FormName::PARAMETER, FragmentBoundary::Unadmitted));
        }
        if let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE) {
            break;
        }
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    match first {
        Some(binder) if count == 1_usize => Ok(binder),
        Some(_) | None => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
    }
}

/// The statements a block opens with a keyword the fragment does not read, by
/// that keyword, with the form a refusal names each by and the way each
/// leaves the fragment: `val` and `unpack` are not admitted, and `acquire`
/// and `release` are reserved for shared sessions; `fork` is read apart,
/// because its two statements share the keyword.
///
/// # Specification
/// - requires: lookup is by a block’s leading keyword.
/// - ensures: each listed keyword retains its distinct refused statement form
///   and boundary; `fork` is handled separately because its shared form
///   requires lookahead.
/// - provides: the keyword-to-refusal naming table.
/// - fails: no default entry for an unlisted keyword.
/// - panics: none.
/// - executable: none — the specification attribute does not accept constant
///   items; `statement_form` checks the lookup and fork exception.
///
/// # Adequacy
/// - hypothesis: L3 — the refused statement cases retain their own form names
///   and boundaries, including the shared fork outside this table.
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
/// - witness: `lower::session::tests::sharing_is_reserved_by_name`
const UNREAD_STATEMENTS: [(TileName, FormName, FragmentBoundary); 4_usize] = [
    (
        TileName::VAL,
        FormName::VAL_STATEMENT,
        FragmentBoundary::Unadmitted,
    ),
    (
        TileName::UNPACK,
        FormName::UNPACK_STATEMENT,
        FragmentBoundary::Unadmitted,
    ),
    (
        TileName::ACQUIRE,
        FormName::ACQUIRE_STATEMENT,
        FragmentBoundary::Reserved,
    ),
    (
        TileName::RELEASE,
        FormName::RELEASE_STATEMENT,
        FragmentBoundary::Reserved,
    ),
];

/// The refused statement the tile `label`, at `cursor`, opens, with the way
/// it leaves the fragment.
///
/// # Specification
/// - requires: `cursor` stands at the tile `label`, in a block, at a place a
///   statement may start.
/// - ensures: `fork` followed by `!` is the shared fork, reserved; a keyword of
///   the table its form and boundary; `run`, `recv`, `hold`, `leta` and `fork`
///   without `!` open statements the block reads, [`statement::Absent::Read`].
/// - provides: the names a block's refused statements are written as;
///   [`statement::Absent::NotAKeyword`] for a tile no statement starts with.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the refused statement spellings receive their own form
///   names and boundaries, and the shared fork is told from the read one.
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
/// - witness: `lower::session::tests::sharing_is_reserved_by_name`
#[spec(
    captures: shared = label == TileName::FORK && {
        let mut ahead = cursor.clone();
        let _lead = ahead.read();
        matches!(ahead.at(TileName::BANG), Maybe::Present(_))
    },
    ensures: |ret| {
        ret == if shared {
            Maybe::Present((FormName::FORK_SHARED_STATEMENT, FragmentBoundary::Reserved))
        }
        else if label == TileName::FORK || label == TileName::RUN || label == TileName::RECV || label == TileName::HOLD || label == TileName::LETA {
            Maybe::Absent(statement::Absent::Read)
        }
        else {
            UNREAD_STATEMENTS
                .iter()
                .find(|&&(keyword, _form, _boundary)| keyword == label)
                .map_or(
                    Maybe::Absent(statement::Absent::NotAKeyword),
                    |&(_keyword, form, boundary)| Maybe::Present((form, boundary)),
                )
        }
    },
)]
fn statement_form(
    label: TileName,
    cursor: &Cursor<'_>,
) -> Maybe<(FormName, FragmentBoundary), statement::Absent>
{
    if label == TileName::FORK {
        let mut ahead = cursor.clone();
        let _fork = ahead.read();
        return match ahead.at(TileName::BANG) {
            Maybe::Present(_) => {
                Maybe::Present((FormName::FORK_SHARED_STATEMENT, FragmentBoundary::Reserved))
            },
            Maybe::Absent(_) => Maybe::Absent(statement::Absent::Read),
        };
    }
    if label == TileName::RUN
        || label == TileName::RECV
        || label == TileName::HOLD
        || label == TileName::LETA
    {
        return Maybe::Absent(statement::Absent::Read);
    }

    UNREAD_STATEMENTS
        .iter()
        .find(|&&(keyword, _form, _boundary)| keyword == label)
        .map_or(
            Maybe::Absent(statement::Absent::NotAKeyword),
            |&(_keyword, form, boundary)| Maybe::Present((form, boundary)),
        )
}

/// Read a parenthesised, comma-separated argument list into `written`.
///
/// # Specification
/// - requires: `cursor` stands at the list's `(`.
/// - ensures: every argument written is appended to `written`, left to right,
///   with the cursor past the closing `)` and nothing after it; empty
///   parentheses append nothing, and a comma after the last argument is
///   admitted.
/// - provides: the argument reading of calls and type applications.
/// - fails: yields the hole's own refusal for an empty or juxtaposed argument,
///   and a misplaced-tile refusal for a list out of shape; the arguments read
///   before the refusal stay appended.
/// - panics: none.
///
/// # Errors
/// The form's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — empty, multi-argument and comma-closed calls append their
///   own ordered operand range; a failure preserves the already-read prefix and
///   locates the unexpected operand or tile instead of silently accepting a
///   suffix. The predicate re-reads the list as the body did and compares it
///   with only the operands this call appended.
/// - witness: `lower::tests::argument_lists_preserve_prefixes_and_locate_the_first_fault`
/// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
#[spec(
    captures: before = (written.len(), cursor.clone()),
    ensures: |ret| {
        written.len() >= before.0
            && ret.as_ref().map_or(true, |&()| written.get(before.0 ..).is_some_and(|appended| {
                let mut input = before.1.clone();
                let mut appended = appended.iter();
                if matches!(input.tile(TileName::PAREN_OPEN), Maybe::Absent(_)) {
                    return false;
                }
                if matches!(input.tile(TileName::PAREN_CLOSE), Maybe::Present(_)) {
                    return appended.next().is_none()
                        && matches!(input.peek(), Maybe::Absent(_))
                        && cursor.peek() == input.peek();
                }
                loop {
                    match input.read() {
                        | Maybe::Present(Piece::Operand(at))
                            if appended.next() == Some(&at.node) => {},
                        | _ => return false,
                    }
                    if matches!(input.tile(TileName::PAREN_CLOSE), Maybe::Present(_)) {
                        break;
                    }
                    if matches!(input.tile(TileName::COMMA), Maybe::Absent(_)) {
                        return false;
                    }
                    if matches!(input.tile(TileName::PAREN_CLOSE), Maybe::Present(_)) {
                        break;
                    }
                }
                appended.next().is_none()
                    && matches!(input.peek(), Maybe::Absent(_))
                    && cursor.peek() == input.peek()
            }))
    },
)]
fn arguments<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    written: &mut Vec<NodeIndex>,
) -> Result<(), LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    loop {
        let run = cursor.operands();
        let closing = cursor.tile(TileName::PAREN_CLOSE);
        if let (Run::Empty(_), Maybe::Present(_)) = (run, closing) {
            break;
        }
        let argument = site.one(run)?;
        written.push(argument.node);
        if let Maybe::Present(_) = closing {
            break;
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        }
    }

    exhausted(site, cursor)
}

/// The entries of `store` that `stretch` names.
///
/// # Specification
/// - requires: the range is interpreted against the supplied store.
/// - ensures: an ordered in-bounds range returns that borrowed slice; a
///   reversed or out-of-bounds range returns an empty slice.
/// - provides: an allocation-free view of the recorded operand, parameter or
///   statement range.
/// - fails: invalid ranges are represented by the empty view.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty, interior and full ranges retain the requested
///   members; reversed and past-end ranges do not read an unrelated prefix.
/// - witness: `lower::tests::recorded_ranges_keep_valid_members_and_reject_invalid_bounds`
#[spec(
    ensures: |ret| match store.get(stretch.start .. stretch.end) {
        | Some(expected) => core::ptr::eq(&raw const *ret, &raw const *expected),
        | None => ret.is_empty(),
    },
)]
fn stretch<Entry>(
    store: &[Entry],
    stretch: Stretch,
) -> &[Entry]
{
    store.get(stretch.start .. stretch.end).unwrap_or(&[])
}

/// Read the closing tile `label`, refusing anything else in its place.
///
/// # Specification
/// - requires: the cursor describes the site’s remaining pieces.
/// - ensures: the requested tile is consumed if present; otherwise the cursor
///   is unchanged and the refusal locates its current piece or gap.
/// - provides: a checked closing tile for the form reader.
/// - fails: an absent or different tile is `MisplacedTile`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — matching and mismatched closing tiles separate
///   consumption from a located refusal, including the exhausted-cursor gap.
/// - witness: `lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
#[spec(
    captures: before = {
        let found = cursor.at(label);
        let here = cursor.here();
        let mut next = cursor.clone();
        if matches!(found, Maybe::Present(_)) {
            let _piece = next.read();
        }
        (found, here, next.peek(), next.here())
    },
    ensures: |ret| {
        ret == match before.0 {
            | Maybe::Present(_) => Ok(()),
            | Maybe::Absent(_) => Err(site.fault(before.1, FormFault::MisplacedTile)),
        } && cursor.peek() == before.2
            && cursor.here() == before.3
    },
)]
fn closed<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    label: TileName,
) -> Result<(), LoweringRefusal<'source>>
{
    match cursor.tile(label) {
        Maybe::Present(_) => Ok(()),
        Maybe::Absent(_) => Err(site.fault(cursor.here(), FormFault::MisplacedTile)),
    }
}

/// Refuse a piece left after a form's last.
///
/// # Specification
/// - requires: the cursor describes the site’s remaining pieces.
/// - ensures: only an exhausted cursor succeeds; a remaining operand and a
///   remaining tile yield their distinct located refusals.
/// - provides: a check that a form reader consumed its complete input.
/// - fails: an operand is `ExtraOperand` and a tile is `MisplacedTile`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — remaining operands and tiles are distinguished from the
///   terminal gap without consuming the unexpected piece.
/// - witness: `lower::tests::closing_and_exhaustion_distinguish_tiles_operands_and_gaps`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
#[spec(
    ensures: |ret| {
        ret == match cursor.peek() {
            | Maybe::Absent(_) => Ok(()),
            | Maybe::Present(Piece::Operand(at)) => {
                Err(site.fault(at.span, FormFault::ExtraOperand))
            },
            | Maybe::Present(Piece::Tile { at, .. }) => {
                Err(site.fault(at.span, FormFault::MisplacedTile))
            },
        }
    },
)]
fn exhausted<'source>(
    site: Site,
    cursor: &Cursor<'_>,
) -> Result<(), LoweringRefusal<'source>>
{
    match cursor.peek() {
        Maybe::Absent(_) => Ok(()),
        Maybe::Present(Piece::Operand(stray)) => {
            Err(site.fault(stray.span, FormFault::ExtraOperand))
        },
        Maybe::Present(Piece::Tile { at, .. }) => {
            Err(site.fault(at.span, FormFault::MisplacedTile))
        },
    }
}

/// The two operands of the product `site`, `A * B`, or of the sum `site`,
/// `A + B`, in written order; `former` names which.
///
/// # Specification
/// - requires: `cursor` holds the pieces of a form of `former` at `site`.
/// - ensures: one operand, the `*` tile of a product or the `+` tile of a sum,
///   and one operand, nothing after them.
/// - provides: the shape check every link of a product or a sum chain shares.
/// - fails: either hole's own refusal, and a misplaced-tile or extra-operand
///   refusal for a link out of shape.
/// - panics: none.
///
/// # Errors
/// The link's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — a well-shaped product and a well-shaped sum answer their
///   operands in order.
/// - witness: `lower::tests::the_eager_product_and_pair_lower_to_their_formers`
/// - witness: `lower::tests::the_bridge_tokens_are_compound_and_sum_is_unaffected`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&[first, second]| first != second))]
fn halves<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    former: Former,
) -> Result<[NodeIndex; 2], LoweringRefusal<'source>>
{
    let tile = if former == Former::SumType {
        TileName::PLUS
    }
    else {
        TileName::STAR
    };
    let first = site.one(cursor.operands())?;
    closed(site, cursor, tile)?;
    let second = site.one(cursor.operands())?;
    exhausted(site, cursor)?;

    Ok([first.node, second.node])
}

/// Whether a form can stand where a value is expected.
///
/// # Specification
/// - requires: nothing; the function is total over the former vocabulary.
/// - ensures: exactly the value-producing formers answer affirmatively — a
///   name, a capitalised name, a number, a string, the unit, a parenthesised
///   expression, a thunk, a telescope value and an injection — the reserved
///   tuple among them, since a reserved form is a value the fragment declines
///   rather than a form of another sort, and keeping the two apart is what lets
///   an attribute payload written as a computation be reported as a non-value
///   rather than as a sort error.
/// - provides: the guard the attribute payload reading takes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the vocabulary is a finite class, enumerated exhaustively
///   with each former's exact answer asserted, so promoting or demoting any
///   single former breaks one row.
/// - witness: `lower::tests::only_the_value_forms_can_stand_as_a_payload`
#[spec(
    ensures: |ret| {
        ret.0
            == matches!(
                former,
                Former::Name
                    | Former::Constructor
                    | Former::Number
                    | Former::Text
                    | Former::Parenthesized
                    | Former::Unit
                    | Former::Thunk
                    | Former::Telescope
                    | Former::Injection
            )
    },
)]
const fn is_value_form(former: Former) -> ValueForm
{
    ValueForm(matches!(
        former,
        Former::Name
            | Former::Constructor
            | Former::Number
            | Former::Text
            | Former::Parenthesized
            | Former::Unit
            | Former::Thunk
            | Former::Telescope
            | Former::Injection
    ))
}

/// Parse a literal's own text into a core literal.
///
/// # Specification
/// - requires: `text` is the literal node's whole source text.
/// - ensures: a number is the canonical non-negative magnitude of its digits,
///   so a padded spelling and its unpadded form are one literal; a string is
///   the text between its delimiting quotes with its escapes decoded — `\n`,
///   `\t`, `\r`, `\0`, `\\`, `\"` and `\'` to the character each names, a
///   backslash before a line break elided with the break, any other escaped
///   character to itself, and a trailing lone backslash dropped.
/// - provides: the only place a lexeme becomes a core literal.
/// - fails: never; the malformed absence for a number holding a non-digit or
///   nothing at all and a string missing either delimiter, and the
///   not-a-literal absence for every other former.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two decision surfaces (the magnitude guard and the
///   delimiter strip) and the escape table, separated by a padded integer, an
///   empty integer, an integer holding a letter, a quoted text, an escaped
///   text, an unterminated text, a bare quote and an unquoted text, each
///   asserted as an exact literal or absence.
/// - witness: `lower::tests::an_integer_literal_is_its_canonical_magnitude`
/// - witness: `lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
/// - witness: `lower::tests::a_lexeme_of_the_wrong_shape_parses_to_nothing`
#[spec(
    ensures: |ret| {
        let spelled: &str = text.as_ref();
        match former {
            | Former::Number => {
                if spelled.is_empty() || !spelled.bytes().all(|byte| byte.is_ascii_digit()) {
                    matches!(ret, Maybe::Absent(literal::Absent::Malformed))
                }
                else {
                    let unpadded = spelled.trim_start_matches('0');
                    let expected = if unpadded.is_empty() { "0" } else { unpadded };
                    matches!(ret, Maybe::Present(Literal::Integer(ref integer)) if integer.sign() == Sign::NonNegative && integer.magnitude().as_ref() == expected)
                }
            },
            | Former::Text => match spelled
                .strip_prefix('"')
                .and_then(|opened| opened.strip_suffix('"'))
            {
                | Some(content) => match ret {
                    | Maybe::Present(Literal::Text(ref literal)) => {
                        let content: &str = content;
                        let actual: &str = literal.as_ref();
                        let mut escaped = false;
                        let mut after_cr = false;
                        actual.chars().eq(content.chars().filter_map(|character| {
                            if after_cr {
                                after_cr = false;
                                if character == '\n' {
                                    return None;
                                }
                            }
                            if escaped {
                                escaped = false;
                                match character {
                                    | 'n' => Some('\n'),
                                    | 't' => Some('\t'),
                                    | 'r' => Some('\r'),
                                    | '0' => Some('\0'),
                                    | '\r' => {
                                        after_cr = true;
                                        None
                                    },
                                    | '\n' => None,
                                    | other => Some(other),
                                }
                            }
                            else if character == '\\' {
                                escaped = true;
                                None
                            }
                            else {
                                Some(character)
                            }
                        }))
                    },
                    | _ => false,
                },
                | None => matches!(ret, Maybe::Absent(literal::Absent::Malformed)),
            },
            | _ => matches!(ret, Maybe::Absent(literal::Absent::NotALiteral)),
        }
    },
)]
pub fn parse_literal(
    former: Former,
    text: SourceFragment<'_>,
) -> Maybe<Literal, literal::Absent>
{
    let spelled: &str = text.as_ref();
    let found = match former {
        Former::Number => Magnitude::from_decimal_text(String::from(spelled))
            .map(|magnitude| Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))),
        Former::Text => spelled
            .strip_prefix('"')
            .and_then(|opened| opened.strip_suffix('"'))
            .map(|content| {
                Literal::Text(StringLiteral::new(decode_escapes(SourceFragment::from(
                    content,
                ))))
            }),
        Former::Name
        | Former::Hole
        | Former::Binary
        | Former::Unary
        | Former::Constructor
        | Former::Parenthesized
        | Former::Unit
        | Former::Thunk
        | Former::Lambda
        | Former::Block
        | Former::Return
        | Former::Exit
        | Former::Become
        | Former::Loop
        | Former::While
        | Former::For
        | Former::Break
        | Former::Continue
        | Former::Force
        | Former::Run
        | Former::Call
        | Former::Case
        | Former::Telescope
        | Former::Injection
        | Former::LazyRecord
        | Former::Instantiation
        | Former::Projection
        | Former::TypeHead
        | Former::TypePath
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::SumType
        | Former::LazyProductType
        | Former::TelescopeType
        | Former::LabelledSumType
        | Former::LazyRecordType
        | Former::ValueFunctionType
        | Former::StaticAbstraction
        | Former::ParenthesizedType
        | Former::PathType
        | Former::RelationType
        | Former::CapabilityType
        | Former::AtType
        | Former::Scope
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Data
        | Former::Mutual
        | Former::SessionType
        | Former::Action
        | Former::Offer
        | Former::Access
        | Former::World
        | Former::WorldDeclaration
        | Former::Reserved
        | Former::Unadmitted => return Maybe::Absent(literal::Absent::NotALiteral),
    };

    found.map_or(Maybe::Absent(literal::Absent::Malformed), Maybe::Present)
}

/// Decode the escapes of a string literal's or an import address's content.
///
/// # Specification
/// - requires: the input is UTF-8 content without its surrounding quote tiles.
/// - ensures: n, t, r and 0 escapes decode to their control characters; escaped
///   LF and CRLF or CR are removed; every other escaped character loses only
///   its backslash.
/// - provides: decoded literal or import-address content, preserving unescaped
///   Unicode.
/// - fails: a trailing backslash contributes no character; unknown escapes are
///   not rejected.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the named escape classes, CR/LF continuations, unknown
///   escapes, Unicode and a trailing backslash have exact decoded values.
/// - witness: `lower::tests::escape_decoding_covers_continuations_unknowns_and_unicode`
/// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
#[spec(
    ensures: |ret| {
        let content: &str = content.as_ref();
        let actual: &str = ret.as_str();
        let mut escaped = false;
        let mut after_cr = false;
        actual.chars().eq(content.chars().filter_map(|character| {
            if after_cr {
                after_cr = false;
                if character == '\n' {
                    return None;
                }
            }
            if escaped {
                escaped = false;
                match character {
                    | 'n' => Some('\n'),
                    | 't' => Some('\t'),
                    | 'r' => Some('\r'),
                    | '0' => Some('\0'),
                    | '\r' => {
                        after_cr = true;
                        None
                    },
                    | '\n' => None,
                    | other => Some(other),
                }
            }
            else if character == '\\' {
                escaped = true;
                None
            }
            else {
                Some(character)
            }
        }))
    },
)]
#[inline]
pub fn decode_escapes(content: SourceFragment<'_>) -> String
{
    let spelled: &str = content.as_ref();
    let mut decoded = String::with_capacity(spelled.len());
    let mut chars = spelled.chars().peekable();
    while let Some(character) = chars.next() {
        if character != '\\' {
            decoded.push(character);
            continue;
        }
        match chars.next() {
            Some('n') => decoded.push('\n'),
            Some('t') => decoded.push('\t'),
            Some('r') => decoded.push('\r'),
            Some('0') => decoded.push('\0'),
            Some('\r') => {
                if chars.peek() == Some(&'\n') {
                    let _break = chars.next();
                }
            },
            Some('\n') | None => {},
            Some(other) => decoded.push(other),
        }
    }

    decoded
}

/// Whether `text` is a numeric lexeme with a fraction or an exponent.
///
/// # Specification
/// - requires: the input is interpreted as an unsigned numeric lexeme.
/// - ensures: a decimal or exponent marker is required; the whole part and each
///   present fraction or exponent contain nonempty ASCII digits, with at most
///   one exponent sign.
/// - provides: the distinction between an unadmitted fractional number and a
///   malformed integer spelling.
/// - fails: malformed, unmarked, signed-whole and non-ASCII spellings return
///   false.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — decimal and exponent boundaries distinguish unsupported
///   fractional numbers from malformed spellings, including empty fields,
///   repeated markers, exponent signs and non-ASCII digits.
/// - witness: `lower::tests::fractional_spellings_distinguish_unsupported_numbers_from_malformed_ones`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
#[spec(
    ensures: |ret| {
        let spelled: &str = text.as_ref();
        let mut bytes = spelled.bytes().peekable();
        let digits = |bytes: &mut core::iter::Peekable<core::str::Bytes<'_>>| {
            let present = bytes.peek().is_some_and(u8::is_ascii_digit);
            while bytes.peek().is_some_and(u8::is_ascii_digit) {
                let _digit = bytes.next();
            }
            present
        };
        let whole = digits(&mut bytes);
        let fraction = bytes.next_if_eq(&b'.').is_some();
        let fraction_ok = !fraction || digits(&mut bytes);
        let exponent = bytes.next_if(|&byte| matches!(byte, b'e' | b'E')).is_some();
        let exponent_ok = !exponent || {
            let _sign = bytes.next_if(|&byte| matches!(byte, b'+' | b'-'));
            digits(&mut bytes)
        };
        ret.0
            == (whole
                && (fraction || exponent)
                && fraction_ok
                && exponent_ok
                && bytes.next().is_none())
    },
)]
fn fractional(text: SourceFragment<'_>) -> Fractional
{
    let spelled: &str = text.as_ref();
    let (mantissa, exponent) = spelled
        .split_once(['e', 'E'])
        .map_or((spelled, None), |(left, right)| (left, Some(right)));
    let (whole, fraction) = mantissa
        .split_once('.')
        .map_or((mantissa, None), |(left, right)| (left, Some(right)));
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    let fraction_ok = fraction.is_none_or(digits);
    let exponent_ok =
        exponent.is_none_or(|part| digits(part.strip_prefix(['+', '-']).unwrap_or(part)));
    let marked = fraction.is_some() || exponent.is_some();

    Fractional(marked && digits(whole) && fraction_ok && exponent_ok)
}

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
        let declared = declared_of(module.declarations()[0].outcome());
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

    #[test]
    fn native_bindings_keep_generated_origins()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def subtract = sub ;"), &mut arena);
        let value = body_of(module.declarations()[0].outcome());
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
        let body = body_of(module.declarations()[0].outcome());
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
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;
    use gandr_surface_syntax::SyntaxTree;
    use quenchant_shape::shape::Maybe;

    use super::Fuel;
    use super::LoweringBudget;
    use super::is_value_form;
    use super::literal;
    use super::lower_module;
    use super::parse_literal;
    use crate::attribute::AttributeRegistry;
    use crate::attribute::AttributeSchema;
    use crate::attribute::payload_form;
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
            }) && ret.declarations().windows(2).all(|pair| match *pair {
                | [ref left, ref right] => left.constant() < right.constant(),
                | _ => false,
            })
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
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
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
        assert_eq!(
            summands(declared_of(lowered[2])),
            ["Integer", "Unit"],
            "a sign against a word that begins with the bridge letter is still the sum"
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
        for source in [
            "def x : Integer +U Integer ;",
            "def x : Integer -F Integer ;",
        ] {
            assert_eq!(
                refusal(SourceText::from(source)),
                LoweringRefusal::MalformedForm {
                    span: at(16_usize, 26_usize),
                    form: FormName::DECLARATION,
                    fault: FormFault::ExtraOperand,
                },
                "a bridge after an operand is no sum, and `{source}` is refused"
            );
        }
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
                    span: at(8_usize, 9_usize),
                    name: SurfaceName::from(name),
                    arity,
                },
                "the bridges are `+U` and `-F`, so `{source}` names a type nothing declares"
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
                "def endo(a : Type, n : Integer) -> -F Type { return (a => a) } def lifted(a : \
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

    #[test]
    fn a_run_bound_type_and_a_constructor_argument_stand_in_a_type()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "data U : Type { NatC : U; Arrow : (a : U, b : U) --> U; } def pick(n : \
                 Integer) -> -F Type { return Integer } def twice(n : Integer) -> -F Type { \
                 run x <- pick(n); return (x => x) } def el(u : U) -> -F Type { return Integer \
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
            panic!("`run x <- pick(n)` binds the call");
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
            panic!("the `run`-bound `x` is a decode");
        };
        assert_eq!(
            arena.value(code),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            "of the variable `run` bound"
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

    #[test]
    fn a_type_where_a_value_is_read_is_quoted()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a = Integer ; def b = -F Integer ; def c = Type ; def d = +U (-F Integer) ; \
                 def e = Path(Integer, 1, 1) ; def f = List(Integer) ;",
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
                if arena.value_type(carrier) == Some(&ValueType::Base(BaseType::Integer))
                    && provenance == inserted),
            "a path type written as a call where a value is read is its code (#539): {path:?}"
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
                FailureClass::Unrepresentable,
                "a grade is a form the fragment does not represent"
            );
        }
    }

    #[test]
    fn a_lambda_body_binds_its_own_de_bruijn_index()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x = thunk { fn (y) { return y } } ;"),
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

    #[test]
    fn a_variable_keeps_its_binder()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let source = "def k = thunk { fn (y) { fn (y) { fn (z) { return y } } } } ;";
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
        let module = lowered(
            SourceText::from("def x : Unit ; def x = unit ;"),
            &mut arena,
        );
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
            SourceText::from(concat!(
                "def g(x : Unit) -> -F Integer { case x { unit => return 1 } }\n",
                "def h(x : Unit) -> -F Integer { case x { #{} => return 1 } }\n",
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

    #[test]
    fn force_and_application_lower_over_their_children()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { become (force g)(3) } ;"),
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
                "def a = thunk { become (return 1)(2) } ;",
                24_usize,
                32_usize,
                "return_expression",
            ),
            (
                "def a = thunk { become (become pure 1)(2) } ;",
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
                "def a = thunk { run y <- return 1 ; return y } ;",
                36_usize,
                44_usize,
            ),
            (
                "def a = thunk { run y <- become pure 1 ; return y } ;",
                41_usize,
                49_usize,
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
                "def f(x: Integer, y: String) -> -F Integer { run z <- pure y ; return x }",
            ),
            &mut arena,
        );
        let [ref declaration] = *module.declarations()
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
            "def f(x: Integer) { return x }",
            "def f(x, y: Integer) -> -F Integer { return y }",
        ] {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            let [ref declaration] = *module.declarations()
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

    #[test]
    fn a_declaration_minting_neither_half_is_refused_by_name_455()
    {
        let pbg = grammar();
        let tree = parsed(
            &pbg,
            SourceText::from("def f(x: Integer) -> -F Integer { return x }"),
        );
        let mut arena = CoreArena::new();
        let mut fuel = Fuel::new(LoweringBudget::DEFAULT);
        let collected = crate::module::collect(&pbg, &tree, &Unit::single(), &mut fuel).unwrap();
        let mut lowerer = super::Lowerer::new(&pbg, &tree, collected, fuel, Recognition::default());
        lowerer.declare();
        lowerer.seed().unwrap();
        lowerer.survey().unwrap();
        lowerer.classify().unwrap();
        lowerer.refuse_unsynthesised().unwrap();
        lowerer.propagate_manifests();
        while lowerer.refuse_unrepresented().0 {
            lowerer.propagate_manifests();
        }
        let mut origins = super::OriginTable::new();
        let mut sink = super::Sink {
            arena: &mut arena,
            origins: &mut origins,
            exits: super::BTreeSet::new(),
            distributed: super::BTreeMap::new(),
            host: super::capability::Host::Unminted,
            loops: super::BTreeSet::new(),
            breaks: super::BTreeSet::new(),
            identities: super::BTreeMap::new(),
        };
        lowerer.mint(&mut sink).unwrap();
        let [ref slot] = *lowerer.collected.slots
        else {
            panic!("`f` is the one declared name");
        };
        let Maybe::Present(half) = slot.definition
        else {
            panic!("`f` has a definition half");
        };
        // The two halves of the issue's `windHom`: the function tail's node
        // left unminted, with no refusal filed against the name.
        let node = usize::from(half.declaration.node);
        lowerer.lowered[node] = Maybe::Absent(super::lowered::Absent::Unminted);
        let declarations = lowerer.assemble(&mut origins);
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
    fn a_block_binds_each_statement_over_the_next()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run x <- pure 1 ; run y <- pure x ; return x } ;"),
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
            "a bind's origin is its statement's `run`"
        );
    }

    #[test]
    fn each_named_binder_records_where_its_name_is_written()
    {
        let text = "def f(n: Integer) -> -F Integer { run m <- pure n ; pure 2 ; return m }";
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
            SourceText::from("def a = thunk { run x <- pure 1 ; pure 2 ; return x } ;"),
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
            Maybe::Present(at(34_usize, 40_usize)),
            "a discarded statement's bind has its computation's origin"
        );
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run x <- pure 1 ; run _ <- pure 2 ; return x } ;"),
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

    /// `run (q, r) <- c ;` binds the tuple under a binder no name reaches and
    /// splits it, the first component outermost, so `q` is read one index
    /// further out than `r`.
    #[test]
    fn a_tuple_binder_splits_the_returned_tuple_in_order()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run (q, r) <- pure (1, 2) ; return (r, q) } ;"),
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

    /// `run q : Integer <- c ;` binds `c` ascribed the pure returner of the
    /// written type, and the rest of the block reads `q` as the bind's own
    /// binder.
    #[test]
    fn a_typed_bind_ascribes_its_computation()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run q : Integer <- pure 1 ; return q } ;"),
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

    #[test]
    fn a_block_standing_as_a_computation_binds_its_statements()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { { run x <- pure 1 ; return x } } ;"),
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
                "def g = thunk { fn (x) { fn (y) { return x } } } ; def h = thunk { become g(1, 2) } ; \
                 def k = thunk { become g() } ;",
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
    fn a_call_of_no_arguments_is_the_call_the_source_wrote_364()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        // `g()` at 52..55 with its head at 52..53; `M.z()` at 131..136 with
        // its head at 131..134.
        let module = lowered(
            SourceText::from(
                "def g = thunk { return 1 } ; def k = thunk { become g() } ; \
                 module M { def z() -> -F Integer { return 0 } } \
                 def m = thunk { become M.z() } ;",
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
                Maybe::Present((Provenance::Written, at(52_usize, 55_usize))),
                Maybe::Present(at(52_usize, 53_usize)),
            ),
            "the force is the call the source wrote, and its head stays at the head"
        );
        assert_eq!(
            called("m"),
            (
                Maybe::Present((Provenance::Written, at(131_usize, 136_usize))),
                Maybe::Present(at(131_usize, 134_usize)),
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
                "def g = thunk { fn (x) { return x } } ; def h = thunk { become g(1) } ;",
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
            Maybe::Present(at(63_usize, 64_usize)),
            "the inserted force names the head whose position demanded it"
        );
    }

    #[test]
    fn an_author_written_force_is_not_marked_inserted()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { become (force g)(3) } ;"),
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
                "def f(x: Integer) -> Integer { return x } def g(x: Integer) -> -F Integer { return x }",
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
    fn an_undefined_type_head_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def a : Intgr ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 13_usize),
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
            LoweringRefusal::MalformedForm {
                span: at(13_usize, 20_usize),
                form: FormName::DECLARATION,
                fault: FormFault::ExtraOperand,
            },
            "juxtaposition is not application: the second head is an operand too many"
        );
    }

    #[test]
    fn an_applied_head_no_former_answers_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Foo(Integer) ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 11_usize),
                name: SurfaceName::from("Foo"),
                arity: HeadArity::Unary,
            },
            "a head applied to one argument is looked up among the unary formers"
        );
        assert_eq!(
            refusal(SourceText::from("def a : Foo(Integer, String) ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 11_usize),
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
                "def a : Integer => String ; def b : +U (Integer -> -F String) ; def c : \
                 (Integer, String) => Unit ; def d : +U (Integer -> String -> -F Unit) ; def e \
                 : Integer => Integer => String ; def f : +U (Integer -> -F (+U (Integer -> -F \
                 String))) ; def g : () => String ; def h : +U (-F String) ; def i : Unit => \
                 String ;",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let declared = |at: usize| spine(&arena, declared_of(lowered[at]));

        assert_eq!(
            declared(0_usize),
            ["U", "->", "Integer", "F", "String"],
            "`A => B` lowers to the thunked arrow into the returner"
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
            "the alias nests to the right, each level its own thunk"
        );
        assert_eq!(
            declared(6_usize),
            ["U", "F", "String"],
            "`() => C` takes no argument"
        );
        assert_eq!(
            declared(6_usize),
            declared(7_usize),
            "and is the thunked returner itself"
        );
        assert_eq!(
            declared(8_usize),
            ["U", "->", "Unit", "F", "String"],
            "`Unit => C` takes the unit value, a type of its own"
        );
        assert_eq!(
            refusal(SourceText::from("def z : (Integer, String) ;")),
            LoweringRefusal::MalformedForm {
                span: at(16_usize, 17_usize),
                form: FormName::from(NamedKind("parenthesized_type")),
                fault: FormFault::MisplacedTile,
            },
            "a type list anywhere but before `=>` is refused at its first comma"
        );
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
    fn a_computation_codomain_of_a_static_pi_is_refused()
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
            "an arrow in a declaration's type is a static Pi, whose codomain is a value type"
        );
    }

    #[test]
    fn the_eager_product_and_pair_lower_to_their_formers()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def p : Integer * String ; def q = (1, \"a\") ; def r : Integer * Unit * String ; \
                 def s = (1, unit, \"a\") ; def l : (Integer * Unit) * String ; def m : Integer \
                 * (Unit * String) ; def o = (1,) ;",
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
                span: at(12_usize, 29_usize),
                form: FormName::from(NamedKind("product_type")),
                sort: FragmentSort::CompType,
                boundary: FragmentBoundary::WrongSort,
            },
            "a product is a value type, not a computation type"
        );
        assert_eq!(
            refusal(SourceText::from(
                "def u = thunk { run x <- (1, 2) ; return x } ;"
            )),
            LoweringRefusal::OutOfFragment {
                span: at(25_usize, 31_usize),
                form: FormName::TUPLE,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::WrongSort,
            },
            "a pair is a value, not a computation: off a tail no exit is inferred for it"
        );
    }

    #[test]
    fn a_static_abstraction_binds_its_name_over_a_quoted_body()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def k = \\A. \\B. A * B ;"), &mut arena);
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
            panic!("each backslash is one static lambda");
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
            refusal(SourceText::from("def m : \\A. A ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 13_usize),
                form: FormName::from(NamedKind("static_abstraction")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "a static abstraction is a value, not a type"
        );
    }

    #[test]
    fn a_static_application_decodes_where_its_operator_says_or_where_it_stands()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def t : Type -> Type[-, 1] ; def a : +U (t(Integer)) ; def w = \\X. t(X) ; def k \
                 = \\G. \\A. +U (G(A)) * A ;",
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
        let Some(&Computation::Bind(inner, outer)) = arena.computation(returned(argued))
        else {
            panic!(
                "an argument calling the binder is bound ahead: {:?}",
                arena.computation(returned(argued))
            );
        };
        // `v` binds nothing for `w`'s type, a plain arrow's rest, so the binder
        // is the nearest one.
        assert_eq!(call(inner).0, variable(0), "the binder's call runs first");
        assert_eq!(
            call(outer),
            (
                Some(Value::Constant(ConstantIndex::from(0_usize))),
                variable(0)
            ),
            "and the outer call takes what it returned"
        );
    }

    #[test]
    fn a_lambda_in_value_position_is_nested_and_marked_inserted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = fn (y) { return y } ;"),
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
            Maybe::Present(at(8_usize, 27_usize)),
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
        let unadmitted = |start: usize, end: usize, form: FormName, sort: FragmentSort| {
            LoweringRefusal::OutOfFragment {
                span: at(start, end),
                form,
                sort,
                boundary: FragmentBoundary::Unadmitted,
            }
        };
        let rows = [
            (
                "def a = 1.5 ;",
                unadmitted(
                    8_usize,
                    11_usize,
                    FormName::from(NamedKind("number")),
                    FragmentSort::Value,
                ),
            ),
            (
                "def a = thunk { val y = 3; return y } ;",
                unadmitted(
                    16_usize,
                    19_usize,
                    FormName::VAL_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { pure 1 ; } ;",
                unadmitted(
                    16_usize,
                    24_usize,
                    FormName::EXPRESSION_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { run (y, z) : Integer <- pure (1, 2); return y } ;",
                unadmitted(
                    27_usize,
                    28_usize,
                    FormName::ANNOTATION,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def f @[a : Type] (x) { return x }",
                unadmitted(
                    0_usize,
                    34_usize,
                    FormName::PARAMETERS,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def rec f() { return 1 }",
                unadmitted(
                    0_usize,
                    24_usize,
                    FormName::RECURSIVE,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def f(A) { return 1 }",
                unadmitted(
                    6_usize,
                    7_usize,
                    FormName::PARAMETER,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def a = (3 : Integer) ;",
                unadmitted(8_usize, 21_usize, FormName::ANNOTATION, FragmentSort::Value),
            ),
            (
                "def a = \"a${b}\" ;",
                unadmitted(
                    8_usize,
                    15_usize,
                    FormName::INTERPOLATION,
                    FragmentSort::Value,
                ),
            ),
        ];
        for (source, expected) in rows {
            let refused = refusal(SourceText::from(source));
            assert_eq!(refused, expected, "`{source}` is outside the fragment");
            assert_eq!(
                refused.classify(),
                FailureClass::Unrepresentable,
                "`{source}` is unrepresentable, not malformed"
            );
        }
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
                "def a = thunk { fn (x, y) { return x } } ;",
                arity(
                    16_usize,
                    38_usize,
                    FormName::from(NamedKind("lambda_expression")),
                    2_usize,
                ),
            ),
            (
                "def a = thunk {} ;",
                arity(14_usize, 16_usize, FormName::BLOCK, 0_usize),
            ),
            (
                "def a = thunk { run x <- pure 1; } ;",
                arity(14_usize, 34_usize, FormName::BLOCK, 0_usize),
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
            SourceText::from(
                "def rank() -> -F Integer {\n  case (Green : Color) {\n    Red => return 0,\n",
            ),
        );
        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(72_usize, 72_usize),
                form: FormName::CASE,
                fault: FormFault::Repaired(Repair::GhostClose(
                    gandr_surface_syntax::ClosingClass::Brace,
                )),
            },
            "the source ends with both the case and the definition open; the refusal names \
             the case at the end of its last arm, not the definition at its opening brace"
        );
    }

    #[test]
    fn a_keyword_in_a_classifier_slot_is_read_with_its_offer_293()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(
            &pbg,
            SourceText::from("theory Magma {\n  sort M : type;\n}\n"),
        );
        let LoweringRefusal::MalformedForm { span, fault, .. } = refusal_in(&pbg, &tree)
        else {
            panic!("a keyword in a classifier slot refuses its form");
        };
        assert_eq!(
            span,
            at(26_usize, 30_usize),
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

    #[test]
    fn an_unended_form_names_its_missing_tile_where_it_belongs()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        for (source, point, form, tile, why) in [
            (
                "def a : Integer ;\ndef a = 1\ndef b : Integer ;\ndef b = 2 ;\n",
                27_usize,
                "def_value",
                crate::form::TileName::SEMICOLON,
                "a definition missing its `;` before the next is pointed past its value",
            ),
            (
                "def s : String ;\ndef s = \"abc ;\n",
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

    #[test]
    fn a_juxtaposed_operand_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        let refused = refusal(SourceText::from("def a = thunk { return 1 2 } ;"));

        assert_eq!(
            refused,
            LoweringRefusal::MalformedForm {
                span: at(25_usize, 26_usize),
                form: FormName::from(NamedKind("thunk_expression")),
                fault: FormFault::ExtraOperand,
            },
            "a thunk's block holds one computation, and a second juxtaposed beside it is \
             refused where it stands"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a juxtaposition is the author's mistake"
        );
        assert_eq!(
            refusal(SourceText::from("def f(x: Integer Integer) { return x }")),
            LoweringRefusal::MalformedForm {
                span: at(17_usize, 24_usize),
                form: FormName::FUNCTION,
                fault: FormFault::ExtraOperand,
            },
            "a parameter's type is one form, and a second juxtaposed beside it is refused as \
             the function's"
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
        let [ref declaration] = *module.declarations()
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

    #[test]
    fn an_attribute_is_filed_under_its_declaration_key()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("@[ owes(1) ] def a : Integer ;"),
            &mut arena,
        );
        let [ref declaration] = *module.declarations()
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
            SourceText::from(
                "/// Squares, as [cube] cubes.\n/// Twice.\ndef square = 1 ;\n@[ doc(\"Cubes.\") ] def cube = 2 ;\n/// A colour.\ndata Color : Type { Red : Color; }\ndef plain = 3 ;",
            ),
            &mut arena,
        );
        let [ref square, ref cube, ref color, ref plain] = *module.declarations()
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
        let [ref undocumented] = *bare.declarations()
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
    fn a_link_to_a_missing_name_is_refused_at_the_link()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("/// See [gone].\ndef a = 1 ;\n@[ doc(\"Or [`a`].\") ] def b = 2 ;"),
            &mut arena,
        );
        let [ref stale, ref linked] = *module.declarations()
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
                 @[ respects((q, p)) ] def r(n : Integer) -> -F Integer { return n } \
                 @[ respects(p) ] def s : +U (Integer -> -F Integer) ; \
                 def s = thunk { fn (n) { return n } } ; \
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
        let [ref defined, ref signed] = *module.declarations()
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
                "def p : Integer ; def q : Integer ; @[ respects((q, p)) ] def r(n : Integer) -> \
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
            SourceText::from("def p : Integer ; @[ respects(p) ] module M { def x = 1 ; }");
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
        let [ref p, _] = *module.declarations()
        else {
            panic!("`p` and `x` are declared");
        };
        let filed = (0_usize ..)
            .map(gandr_surface_syntax::NodeIndex::from)
            .map_while(|at| tree.node(at).map(|_| at))
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
    fn a_link_resolves_to_a_module_its_member_or_a_constructor()
    {
        let mut arena = CoreArena::new();
        let source = "/// See [M], [Red] and [x].\ndef a = 1 ;\nmodule M { def x = 1 ; }\ndata Color \
                      : Type { Red : Color; }\n/// Not [gone].\ndef b = 2 ;";
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

    #[test]
    fn a_module_attribute_refusal_refuses_its_first_member_alone()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("@[ checkz ] module M { def x = 1 ; }\ndef y = 2 ;"),
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
    fn an_unknown_constructor_where_a_value_is_read_is_unadmitted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        assert_eq!(
            refusal(SourceText::from("def a = Foo ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 11_usize),
                form: FormName::from(NamedKind("constructor")),
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Unadmitted,
            },
            "only `Type` is a universe; another unanswered capital is no form the fragment has"
        );
    }

    #[test]
    fn a_split_of_three_components_lowers()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run (x, y, z) <- pure (1, 2, 3) ; return x } ;"),
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
    fn a_universe_level_past_the_constants_is_refused_at_its_numeral()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        assert_eq!(
            refusal(SourceText::from(
                "def d : Type[+, 99999999999999999999999] ;"
            )),
            LoweringRefusal::OutOfFragment {
                span: at(16_usize, 39_usize),
                form: FormName::from(NamedKind("universe_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::Unadmitted,
            },
            "the refusal stands at the level, not the whole universe"
        );
    }

    #[test]
    fn a_forward_member_applied_as_a_type_is_refused_at_its_head()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("module M { def a : f(Integer) ; def f : Type -> Type ; }"),
            &mut arena,
        );
        assert_eq!(
            outcome_named(&module, "a"),
            DeclarationOutcome::Refused(LoweringRefusal::ForwardMemberReference {
                span: at(19_usize, 20_usize),
                name: SurfaceName::from("f"),
                declared: at(36_usize, 37_usize),
            }),
            "the refusal stands at the operator's name, not the whole application"
        );
    }

    #[test]
    fn a_static_abstraction_binds_a_lowercase_name()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def t : Type -> Type ; def w = \\x. t(x) ;"),
            &mut arena,
        );
        assert!(
            !matches!(outcome_named(&module, "w"), DeclarationOutcome::Refused(_)),
            "a type variable binds as a type identifier does: {:?}",
            outcome_named(&module, "w")
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
        let [ref declaration] = *module.declarations()
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
        let text = "module NatAdd : #{ type M = Integer, zero : M } {\n  type M = Integer;\n  def \
                    zero = 0;\n}\n\nmodule MkCounter(S : #{ type T, zero : T }) :> #{ type T, \
                    seed : T } {\n  type T = S.T;\n  def seed = S.zero;\n}\n\nmodule Seed {\n  \
                    type T = Integer;\n  def zero = 0;\n}\n\nmodule A = MkCounter(Seed) ;\n";
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
            from("zero : T })").is_some_and(|at| heads.contains(&at.saturating_add(7))),
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
        let [ref twice, ref once] = *module.declarations()
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
            (twice.definition(), twice.duplicate())
        else {
            panic!("the first definition and the repetition are both keyed");
        };
        assert_ne!(first, second, "the repetition is keyed at its own form");
        assert!(
            matches!(once.duplicate(), Maybe::Absent(_)),
            "a name written once keys no repetition"
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
            Former::Text,
            Former::Parenthesized,
            Former::Unit,
            Former::Thunk,
            Former::Telescope,
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
    fn a_lexeme_of_the_wrong_shape_parses_to_nothing()
    {
        let rows = [
            (Former::Number, "", literal::Absent::Malformed),
            (Former::Number, "3x", literal::Absent::Malformed),
            (Former::Text, "\"abc", literal::Absent::Malformed),
            (Former::Text, "\"", literal::Absent::Malformed),
            (Former::Text, "abc", literal::Absent::Malformed),
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

    #[test]
    fn the_last_step_of_an_allowance_is_spendable()
    {
        let mut fuel = Fuel::new(LoweringBudget::from(1_usize));

        assert_eq!(fuel.spend(), Ok(()), "an allowance of one admits one step");
    }

    #[test]
    fn a_step_past_the_allowance_is_refused()
    {
        let budget = LoweringBudget::from(1_usize);
        let mut fuel = Fuel::new(budget);
        let _first = fuel.spend();

        assert_eq!(
            fuel.spend(),
            Err(LoweringRefusal::BudgetExceeded { budget }),
            "the step past the allowance is refused, naming the allowance"
        );
    }

    /// Escape classes and continuations preserve their specified characters.
    #[test]
    fn escape_decoding_covers_continuations_unknowns_and_unicode()
    {
        for (written, expected) in [
            ("plain λ", "plain λ"),
            ("\\n\\t\\r\\0", "\n\t\r\0"),
            ("a\\\nb", "ab"),
            ("a\\\r\nb", "ab"),
            ("a\\\rb", "ab"),
            ("a\\q\\λ", "aqλ"),
            ("a\\", "a"),
            ("a\r\nb", "a\r\nb"),
            ("\\\\", "\\"),
            ("\\\r\\n", "\n"),
        ] {
            assert_eq!(
                super::decode_escapes(SourceFragment::from(written)),
                expected
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
            node: super::NodeIndex::from(index),
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

    /// Parameter arities consume the header but preserve the following body.
    #[test]
    fn parameter_headers_preserve_the_body_and_locate_refusals()
    {
        let placed = |index: usize, start: usize, end: usize| super::Placed {
            node: super::NodeIndex::from(index),
            span: span(ByteOffset::from(start), ByteOffset::from(end)),
        };
        let lead = super::Piece::Tile {
            label: super::TileName::FN,
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
        let form = FormName::from(NamedKind("lambda_expression"));
        let site = super::Site {
            at: placed(0_usize, 0_usize, 12_usize),
            name: form,
            reading: super::Reading::Computation(super::Frame::Outermost),
        };
        for (pieces, expected, next) in [
            (
                [lead, open, identifier, close, body].as_slice(),
                Ok(first),
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
                [lead, open, identifier, colon, body].as_slice(),
                Err(LoweringRefusal::OutOfFragment {
                    span: site.at.span,
                    form: FormName::PARAMETER,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::Unadmitted,
                }),
                colon,
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
            let _lead = cursor.tile(super::TileName::FN);
            assert_eq!(super::parameter(site, &mut cursor), expected);
            assert_eq!(cursor.peek(), Maybe::Present(next));
        }
    }

    /// Argument failures retain appended operands and identify the first fault.
    #[test]
    fn argument_lists_preserve_prefixes_and_locate_the_first_fault()
    {
        let placed = |index: usize, start: usize, end: usize| super::Placed {
            node: super::NodeIndex::from(index),
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
        let previous = super::NodeIndex::from(99_usize);
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
}
