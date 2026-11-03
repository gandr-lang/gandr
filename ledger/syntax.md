# Syntax ledger

Generated from the built-in grammar by `gandr ledger syntax --write ledger`; never edited by hand. `mise run check:syntax-ledger` regenerates it and fails while this file differs. `syntax.json` holds the same rows for machines, each form as a tree with every tile's mold.

- Grammar fingerprint: `0xc048b33b171ef45b`
- Rules: 174 — 173 committed, 1 internal
- Molds: 2952
- Attributes: 17

## Reading a form

A form spells its rule's tiles and holes in order.

| Notation | Reads |
| -------- | ----- |
| `def` | a tile written as this text |
| `‹identifier›` | a tile of a lexical class: any identifier |
| `EXPRESSION` | a hole holding a form of that sort |
| `⦅ a ‖ b ⦆` | one of the alternatives |
| `⦅ a ⦆?` | the part, or nothing |
| `⦅ a ⦆*` | the part, any number of times |
| `⟨block⟩` | the whole form of rule `block`, written out in place: its tiles are this rule's own |

A rule holding a glyph tile writes its form twice: the glyph spelling, then `or` and the ASCII spelling the labeler reads as the same tile. The isomorphism's ASCII spelling is a call of `Iso` over its operands, which the lowering reads as the same type.

Each committed rule links its exemplar, a small source the exemplar gate parses and checks for a tile of the rule; a glyph rule's exemplar holds one item per spelling, and the gate checks each is written. The group is the rule's precedence group. The kind is the named node kind the rule realises; `*` marks a kind the surface's tree-sitter grammar does not have. The admission is what lowering the exemplar makes of that kind: `unadmitted` or `reserved` where it refuses a form of the kind out of the fragment at that boundary, which the exemplar states as `refuses("OutOfFragment.<kind>…")` and `check:exemplars` settles, `admitted` otherwise. The roles are the highlight roles of the rule's tiles, each once, first use first.

## `item` — 16 rules

| Rule | Form | Group | Kind | Admission | Roles |
| ---- | ---- | ----- | ---- | --------- | ----- |
| [`def_value`](../corpus/ledger/syntax/def-value.gandr) | `def ⦅ rec ‹identifier› ⦅ [ ⦅ ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? ] ⦆? ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ ⦅ -> TYPE ⦆? { ⦅ ⦅ . ‹identifier› => EXPRESSION ‖ _ => EXPRESSION ⦆ ⦅ , ⦅ . ‹identifier› => EXPRESSION ‖ _ => EXPRESSION ⦆ ⦆* ⦅ , ⦆? ‖ ⦅ let PATTERN ⦅ : TYPE ⦆? = EXPRESSION ; ‖ unpack ‹identifier› : TYPE = EXPRESSION ; ‖ leta ‹identifier› = EXPRESSION ; ‖ var ⦅ [ ‹number› ] ⦆? ‹identifier› ⦅ : TYPE ⦆? = EXPRESSION ; ‖ EXPRESSION ; ‖ EXPRESSION ⦅ = ‖ += ‖ -= ‖ *= ⦆ EXPRESSION ; ‖ import ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ; ⦆* ⦅ EXPRESSION ⦆? ⦆ } ‖ : TYPE where { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ⦆ ‖ : TYPE where { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ⦆ ‖ ‹identifier› ⦅ [ ⦅ ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? ] ⦆? ⦅ : TYPE ⦅ ⦅ = EXPRESSION ⦆? ; ‖ where { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ⦆ ‖ = EXPRESSION ; ‖ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ ⦅ -> TYPE ⦆? ⟨block⟩ ‖ : TYPE where { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ⦆ ⦆ ⦆` | `item.singleton` | `def_value` | admitted | Keyword, FunctionDef, Other, VariableParam, TypeVariable, Type, Operator, Member, Variable, VariableDef, Number |
| [`data_declaration`](../corpus/ledger/syntax/data-declaration.gandr) | `data ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : ⦅ TYPE ‖ ( ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> ⦅ TYPE ‖ ( ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ⦅ , ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ⦆? where { ⦅ \| ⦅ ‹constructor› : ⦅ TYPE ‖ ( ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> ⦅ TYPE ‖ ( ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ⦅ , ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ‖ ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ‖ ⦅ oper ‖ op ⦆ ‹identifier› : ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) --> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ‖ TYPE ⦆ ; ‖ rule ⦅ ‹identifier› ⦆? : EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ; ⦆* }` or `data ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : ⦅ TYPE ‖ ( ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> ⦅ TYPE ‖ ( ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ⦅ , ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ⦆? where { ⦅ \| ⦅ ‹constructor› : ⦅ TYPE ‖ ( ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> ⦅ TYPE ‖ ( ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ⦅ , ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ‖ ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ‖ ⦅ oper ‖ op ⦆ ‹identifier› : ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) --> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ‖ TYPE ⦆ ; ‖ rule ⦅ ‹identifier› ⦆? : EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ; ⦆* }` | `item.singleton` | `data_declaration` * | admitted | Keyword, Type, Other, TypeVariable, VariableParam, Number, Operator, Constructor, Member, FunctionDef |
| [`codata_declaration`](../corpus/ledger/syntax/codata-declaration.gandr) | `codata ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : TYPE ⦆? where { ⦅ ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : ⦅ ( ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ⦅ , ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ⦆* ⦅ , ⦆? ) --> TYPE ‖ TYPE ⦆ ‖ oper ‹identifier› : ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) --> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ‖ TYPE ⦆ ‖ rule ⦅ ‹identifier› ⦆? : EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦅ ⦅ ; ‖ , ⦆ ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : ⦅ ( ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ⦅ , ‹identifier› ⦅ [ ⦅ ‹number› ‖ ω ⦆ ] ⦆? : TYPE ⦆* ⦅ , ⦆? ) --> TYPE ‖ TYPE ⦆ ‖ oper ‹identifier› : ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) --> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ‖ TYPE ⦆ ‖ rule ⦅ ‹identifier› ⦆? : EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦆* ⦅ ; ‖ , ⦆? ⦆? }` or `codata ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : TYPE ⦆? where { ⦅ ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : ⦅ ( ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ⦅ , ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ⦆* ⦅ , ⦆? ) --> TYPE ‖ TYPE ⦆ ‖ oper ‹identifier› : ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) --> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ‖ TYPE ⦆ ‖ rule ⦅ ‹identifier› ⦆? : EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦅ ⦅ ; ‖ , ⦆ ⦅ ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : ⦅ ( ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ⦅ , ‹identifier› ⦅ [ ⦅ ‹number› ‖ inf ⦆ ] ⦆? : TYPE ⦆* ⦅ , ⦆? ) --> TYPE ‖ TYPE ⦆ ‖ oper ‹identifier› : ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) --> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ‖ TYPE ⦆ ‖ rule ⦅ ‹identifier› ⦆? : EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦆* ⦅ ; ‖ , ⦆? ⦆? }` | `item.singleton` | `codata_declaration` * | admitted | Keyword, Type, Other, TypeVariable, Member, Number, VariableParam, Operator, FunctionDef |
| [`module_declaration`](../corpus/ledger/syntax/module-declaration.gandr) | `module ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ⦅ = ‹type_identifier› ( ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ) ; ‖ ⦅ ( ‹type_identifier› : ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ) ⦆? ⦅ : ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ‖ :> ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ⦆? where { ⦅ MODULE_MEMBER ⦆* } ⦆` | `item.singleton` | `module_declaration` | admitted | Keyword, Type, VariableDef, Other, Member, TypeVariable, Operator |
| [`flow_declaration`](../corpus/ledger/syntax/flow-declaration.gandr) | `flow ‹identifier› : ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ⇝ ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* where { ⦅ MODULE_MEMBER ⦆* }` or `flow ‹identifier› : ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ~~> ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* where { ⦅ MODULE_MEMBER ⦆* }` | `item.singleton` | `flow_declaration` * | admitted | Keyword, FunctionDef, Other, Type, Member, Operator |
| [`import_declaration`](../corpus/ledger/syntax/import-declaration.gandr) | `import ⦅ " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ‖ ‹identifier› ⦅ . ‹identifier› ⦆* ⦆ ⦅ as ‹identifier› ⦆? ⦅ : ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ⦅ via ‹identifier› ⦆? ⦆? ⦅ ( ⦅ ‹identifier› ‖ ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› ‖ ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ) ⦆? ;` | `item.singleton` | `import_declaration` * | admitted | Keyword, StringLit, Escape, Variable, Other, Member, VariableDef, Type |
| [`world_declaration`](../corpus/ledger/syntax/world-declaration.gandr) | `world ‹identifier› ⦅ requires [ ⦅ TYPE : ⦆? ‹type_identifier› ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦅ , ⦅ TYPE : ⦆? ‹type_identifier› ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆* ⦅ , ⦆? ] ⦆? ;` | `item.singleton` | `world_declaration` * | admitted | Keyword, Label, Other, Type |
| [`offers_declaration`](../corpus/ledger/syntax/offers-declaration.gandr) | `offers [ ⦅ ‹type_identifier› ‖ ‹identifier› = ‹type_identifier› ⦆ ⦅ , ⦅ ‹type_identifier› ‖ ‹identifier› = ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ] ;` | `item.singleton` | `offers_declaration` * | admitted | Keyword, Other, Type, Label |
| [`rec_block`](../corpus/ledger/syntax/rec-block.gandr) | `rec { ⦅ ITEM ⦆* }` | `item.singleton` | `rec_block` * | admitted | Keyword, Other |
| [`pub_declaration`](../corpus/ledger/syntax/pub-declaration.gandr) | `pub` | `item.singleton` | `pub_declaration` * | admitted | Keyword |
| [`attribute_block`](../corpus/ledger/syntax/attribute-block.gandr) | `@[ ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦆* ⦅ , ⦆? ]` | `item.singleton` | `attribute_block` | admitted | Other |
| [`inner_attribute_block`](../corpus/ledger/syntax/inner-attribute-block.gandr) | `@![ ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦆* ⦅ , ⦆? ]` | `item.singleton` | `inner_attribute_block` * | unadmitted | Other |
| [`extern_block`](../corpus/ledger/syntax/extern-block.gandr) | `extern ⦅ " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ‖ ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ⦆ from " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ⦅ as ⦅ ‹identifier› ‖ ‹type_identifier› ⦆ ⦆? { ⦅ type ‹type_identifier› ; ‖ def ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ; ⦆* }` | `item.singleton` | `extern_block` | unadmitted | Keyword, StringLit, Escape, Type, Variable, Other, Member, VariableDef, FunctionDef, VariableParam, TypeVariable, Operator |
| [`theory_declaration`](../corpus/ledger/syntax/theory-declaration.gandr) | `theory ‹type_identifier› ⦅ . ‹type_identifier› ⦆* where { ⦅ ⦅ ⟨attribute_block⟩ ⦆* ⦅ sort ‹type_identifier› ⦅ ( ⦅ ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ‖ bind ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ‖ ‹type_identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ‖ bind ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ‖ ‹type_identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆? : TYPE ‖ data ‹constructor› : ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ‖ bind ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ‖ bind ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦆? ‖ ⦅ ⦅ oper ‖ obs ⦆ ‹identifier› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ‖ bind ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ‖ bind ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦆? ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆? ‖ ( ⦅ ‹identifier› ⦅ : TYPE ⦆? ⦅ , ‹identifier› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ⦆ ‖ rule ‹identifier› ⦅ : ⦅ ( ⦅ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ‖ ‹identifier› : TYPE ⦆ ⦅ , ⦅ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ‖ ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ‖ EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦅ where { ⦅ \| ⦅ ‹identifier› # ‹identifier› ‖ under [ ‹type_identifier› ⦅ , ‹type_identifier› ⦆* ⦅ , ⦆? ⦅ \| ‹identifier› ⦆? ] ⦆ ⦆* } ⦆? ⦆ ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆? ‖ EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦆ ‖ shape ‹type_identifier› : ‹number› { ⦅ ‹identifier› = { ⦅ ‹number› ⦅ , ‹number› ⦆* ⦆? } ; ⦆* } ‖ include ‹type_identifier› ‖ ext ‹type_identifier› = ‹type_identifier› on ‹identifier› is ‹identifier› ‖ law ‹identifier› : TYPE ‖ boundary ‹type_identifier› { ⦅ ‹identifier› ⦅ , ‹identifier› ⦆* ⦆? } ‖ face ‹identifier› = { ⦅ ‹identifier› ⦅ , ‹identifier› ⦆* ⦆? } ⦆ ; ⦆* }` | `item.singleton` | `theory_declaration` * | admitted | Keyword, Type, Other, VariableParam, Operator, Constructor, FunctionDef, VariableDef, FunctionCall, Member, Number |
| [`circuit_declaration`](../corpus/ledger/syntax/circuit-declaration.gandr) | `⦅ oper ‖ rule ⦆ ‹identifier› : ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ‖ bind ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ‖ bind ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆? ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆?` | `item.singleton` | `circuit_declaration` * | admitted | Keyword, FunctionDef, Other, VariableParam, Operator, VariableDef, FunctionCall |
| [`derive_declaration`](../corpus/ledger/syntax/derive-declaration.gandr) | `derive ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION in ‹type_identifier›` | `item.singleton` | `derive_declaration` * | admitted | Keyword, FunctionDef, Other, Operator, Type |

## `pattern` — 14 rules

| Rule | Form | Group | Kind | Admission | Roles |
| ---- | ---- | ----- | ---- | --------- | ----- |
| [`wildcard`](../corpus/ledger/syntax/wildcard.gandr) | `_` | `pattern.atom` | `wildcard` | admitted | Variable |
| [`constructor_pattern`](../corpus/ledger/syntax/constructor-pattern.gandr) | `‹constructor› ⦅ . ⦅ ‹constructor› ‖ ‹identifier› ⦆ ⦆? ⦅ ( PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦆? ) ⦆?` | `pattern.atom` | `constructor_pattern` | admitted | Constructor, Other, Member |
| [`tuple_pattern`](../corpus/ledger/syntax/tuple-pattern.gandr) | `( PATTERN , PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦆? )` | `pattern.atom` | `tuple_pattern` | admitted | Other |
| [`telescope_pattern`](../corpus/ledger/syntax/telescope-pattern.gandr) | `#{ ⦅ ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ = PATTERN ⦆? ‖ PATTERN ⦅ = PATTERN ⦆? ⦆ ⦅ , ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ = PATTERN ⦆? ‖ PATTERN ⦅ = PATTERN ⦆? ⦆ ⦆* ⦅ , ⦆? ⦆? }` | `pattern.atom` | `telescope_pattern` * | admitted | Other, Member, Number |
| [`labelled_sum_pattern`](../corpus/ledger/syntax/labelled-sum-pattern.gandr) | `+ { . ⦅ ‹identifier› ‖ ‹number› ⦆ = PATTERN }` | `pattern.atom` | `labelled_sum_pattern` * | admitted | Operator, Other, Member, Number |
| [`list_pattern`](../corpus/ledger/syntax/list-pattern.gandr) | `⦅ #[ ‖ [ ⦆ ⦅ PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦅ ⟨rest_pattern⟩ ⦆? ⦆? ‖ ⟨rest_pattern⟩ ⦆? ]` | `pattern.atom` | `list_pattern` | admitted | Other, Operator |
| [`rest_pattern`](../corpus/ledger/syntax/rest-pattern.gandr) | `.. PATTERN` | `pattern.atom` | `rest_pattern` | admitted | Operator |
| [`literal_pattern`](../corpus/ledger/syntax/literal-pattern.gandr) | `‹number› ‖ ‹typed_number› ‖ " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ‖ true ‖ false` | `pattern.atom` | `literal_pattern` | admitted | Number, StringLit, Escape, Boolean |
| [`hole.pattern`](../corpus/ledger/syntax/hole.pattern.gandr) | `? ⦅ ‹hole_name› ⦆?` | `pattern.atom` | `hole` | admitted | Hole, Label |
| [`cons_pattern`](../corpus/ledger/syntax/cons-pattern.gandr) | `‹identifier› ⦅ ( ‹identifier› ) ⦆? ∷ PATTERN` or `‹identifier› ⦅ ( ‹identifier› ) ⦆? :: PATTERN` | `pattern.cons` | `cons_pattern` * | admitted | Variable, Other, Operator |
| [`or_pattern`](../corpus/ledger/syntax/or-pattern.gandr) | `PATTERN \| PATTERN` | `pattern.or` | `or_pattern` | admitted | Operator |
| [`as_pattern`](../corpus/ledger/syntax/as-pattern.gandr) | `PATTERN ⦅ @ ‖ .@ ⦆ PATTERN` | `pattern.as` | `as_pattern` | admitted | Other |
| [`identifier.pattern`](../corpus/ledger/syntax/identifier.pattern.gandr) | `‹identifier›` | `pattern.atom` | `identifier` | admitted | Variable |
| [`unit.pattern`](../corpus/ledger/syntax/unit.pattern.gandr) | `unit` | `pattern.atom` | `unit` | admitted | Keyword |

## `expression` — 90 rules

| Rule | Form | Group | Kind | Admission | Roles |
| ---- | ---- | ----- | ---- | --------- | ----- |
| [`pure_expression`](../corpus/ledger/syntax/pure-expression.gandr) | `pure EXPRESSION` | `expression.pure` | `pure_expression` | admitted | Keyword |
| [`return_expression`](../corpus/ledger/syntax/return-expression.gandr) | `return EXPRESSION` | `expression.pure` | `return_expression` * | admitted | Keyword |
| [`become_expression`](../corpus/ledger/syntax/become-expression.gandr) | `become EXPRESSION` | `expression.pure` | `become_expression` * | admitted | Keyword |
| [`bind_expression`](../corpus/ledger/syntax/bind-expression.gandr) | `bind ‹identifier› . EXPRESSION` | `expression.pure` | `bind_expression` * | admitted | Keyword, Variable, Other |
| [`binary_expression.or`](../corpus/ledger/syntax/binary-expression.or.gandr) | `EXPRESSION \|\| EXPRESSION` | `expression.or` | `binary_expression` | admitted | Operator |
| [`binary_expression.and`](../corpus/ledger/syntax/binary-expression.and.gandr) | `EXPRESSION && EXPRESSION` | `expression.and` | `binary_expression` | admitted | Operator |
| [`binary_expression.cmp.eq`](../corpus/ledger/syntax/binary-expression.cmp.eq.gandr) | `EXPRESSION == EXPRESSION` | `expression.cmp` | `binary_expression` | admitted | Operator |
| [`binary_expression.cmp.ne`](../corpus/ledger/syntax/binary-expression.cmp.ne.gandr) | `EXPRESSION != EXPRESSION` | `expression.cmp` | `binary_expression` | admitted | Operator |
| [`binary_expression.cmp.lt`](../corpus/ledger/syntax/binary-expression.cmp.lt.gandr) | `EXPRESSION < EXPRESSION` | `expression.cmp` | `binary_expression` | admitted | Operator |
| [`binary_expression.cmp.le`](../corpus/ledger/syntax/binary-expression.cmp.le.gandr) | `EXPRESSION <= EXPRESSION` | `expression.cmp` | `binary_expression` | admitted | Operator |
| [`binary_expression.cmp.gt`](../corpus/ledger/syntax/binary-expression.cmp.gt.gandr) | `EXPRESSION > EXPRESSION` | `expression.cmp` | `binary_expression` | admitted | Operator |
| [`binary_expression.cmp.ge`](../corpus/ledger/syntax/binary-expression.cmp.ge.gandr) | `EXPRESSION >= EXPRESSION` | `expression.cmp` | `binary_expression` | admitted | Operator |
| [`binary_expression.cons`](../corpus/ledger/syntax/binary-expression.cons.gandr) | `EXPRESSION ∷ EXPRESSION` or `EXPRESSION :: EXPRESSION` | `expression.cons` | `binary_expression` | admitted | Operator |
| [`binary_expression.add.concat`](../corpus/ledger/syntax/binary-expression.add.concat.gandr) | `EXPRESSION ++ EXPRESSION` | `expression.add` | `binary_expression` | unadmitted | Operator |
| [`binary_expression.add.plus`](../corpus/ledger/syntax/binary-expression.add.plus.gandr) | `EXPRESSION + EXPRESSION` | `expression.add` | `binary_expression` | admitted | Operator |
| [`binary_expression.add.minus`](../corpus/ledger/syntax/binary-expression.add.minus.gandr) | `EXPRESSION - EXPRESSION` | `expression.add` | `binary_expression` | admitted | Operator |
| [`binary_expression.mul.times`](../corpus/ledger/syntax/binary-expression.mul.times.gandr) | `EXPRESSION * EXPRESSION` | `expression.mul` | `binary_expression` | admitted | Operator |
| [`unary_expression`](../corpus/ledger/syntax/unary-expression.gandr) | `- EXPRESSION` | `expression.unary` | `unary_expression` | admitted | Operator |
| [`force_expression`](../corpus/ledger/syntax/force-expression.gandr) | `force EXPRESSION` | `expression.unary` | `force_expression` | admitted | Keyword |
| [`run_expression`](../corpus/ledger/syntax/run-expression.gandr) | `run EXPRESSION` | `expression.unary` | `run_expression` * | admitted | Keyword |
| [`hold_expression`](../corpus/ledger/syntax/hold-expression.gandr) | `hold EXPRESSION` | `expression.unary` | `hold_expression` | admitted | Keyword |
| [`splice_expression`](../corpus/ledger/syntax/splice-expression.gandr) | `~ EXPRESSION` | `expression.unary` | `splice_expression` * | admitted | Other |
| [`pack_expression`](../corpus/ledger/syntax/pack-expression.gandr) | `pack [ TYPE ⦅ , TYPE ⦆* ⦅ , ⦆? ] EXPRESSION` | `expression.pure` | `pack_expression` * | unadmitted | Keyword, Other |
| [`pack_model_expression`](../corpus/ledger/syntax/pack-model-expression.gandr) | `pack EXPRESSION at TYPE` | `expression.pure` | `pack_model_expression` * | admitted | Keyword |
| [`call_expression`](../corpus/ledger/syntax/call-expression.gandr) | `EXPRESSION ( ⦅ EXPRESSION ⦅ , EXPRESSION ⦆* ⦅ , ⦆? ⦆? )` | `expression.postfix` | `call_expression` | admitted | Other |
| [`instantiation_expression`](../corpus/ledger/syntax/instantiation-expression.gandr) | `EXPRESSION [ INSTANTIATION ⦅ , INSTANTIATION ⦆* ⦅ , ⦆? ]` | `expression.postfix` | `instantiation_expression` | admitted | Other |
| [`projection_expression`](../corpus/ledger/syntax/projection-expression.gandr) | `EXPRESSION . ⦅ ‹identifier› ‖ ‹constructor› ‖ ‹number› ⦆` | `expression.postfix` | `projection_expression` | admitted | Other, Member, Constructor, Number |
| [`record_selection_expression`](../corpus/ledger/syntax/record-selection-expression.gandr) | `EXPRESSION .#{ . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ , . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦆* ⦅ , ⦆? }` | `expression.postfix` | `record_selection_expression` * | admitted | Other, Member, Number |
| [`view_expression`](../corpus/ledger/syntax/view-expression.gandr) | `EXPRESSION as ‹identifier› ⟨block⟩` | `expression.postfix` | `view_expression` * | admitted | Keyword, VariableDef, Other, Number, Type, Member |
| [`index_expression`](../corpus/ledger/syntax/index-expression.gandr) | `EXPRESSION ⦅ .#[ ‖ [ ⦆ EXPRESSION ]` | `expression.postfix` | `index_expression` * | admitted | Other |
| [`hole`](../corpus/ledger/syntax/hole.gandr) | `? ⦅ ‹hole_name› ⦆?` | `expression.atom` | `hole` | admitted | Hole, Label |
| [`wildcard.expression`](../corpus/ledger/syntax/wildcard.expression.gandr) | `_` | `expression.atom` | `wildcard` | admitted | Variable |
| [`parenthesized_expression`](../corpus/ledger/syntax/parenthesized-expression.gandr) | `( ⦅ ) ‖ EXPRESSION ⦅ ) ‖ , ⦅ EXPRESSION ⦅ , EXPRESSION ⦅ , EXPRESSION ⦆* ⦆? ⦅ , ⦆? ⦆? ) ‖ : TYPE ) ⦆ ⦆` | `expression.atom` | `parenthesized_expression` | admitted | Other |
| [`type_quote_expression`](../corpus/ledger/syntax/type-quote-expression.gandr) | `type( TYPE )` | `expression.atom` | `type_quote_expression` * | admitted | Keyword, Other |
| [`list_expression`](../corpus/ledger/syntax/list-expression.gandr) | `⦅ #[ ‖ [ ⦆ ⦅ EXPRESSION ⦅ , EXPRESSION ⦆* ⦅ , ⦆? ⦆? ]` | `expression.atom` | `list_expression` | admitted | Other |
| [`block`](../corpus/ledger/syntax/block.gandr) | `{ ⦅ let PATTERN ⦅ : TYPE ⦆? = EXPRESSION ; ‖ unpack ‹identifier› : TYPE = EXPRESSION ; ‖ leta ‹identifier› = EXPRESSION ; ‖ var ⦅ [ ‹number› ] ⦆? ‹identifier› ⦅ : TYPE ⦆? = EXPRESSION ; ‖ EXPRESSION ; ‖ EXPRESSION ⦅ = ‖ += ‖ -= ‖ *= ⦆ EXPRESSION ; ‖ import ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ; ⦆* ⦅ EXPRESSION ⦆? }` | `expression.atom` | `block` | admitted | Other, Keyword, VariableDef, Number, Type, Member |
| [`lambda_expression`](../corpus/ledger/syntax/lambda-expression.gandr) | `fun ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) BLOCK ‖ { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ‖ [ ‹type_variable› ⦅ , ‹type_variable› ⦆* ⦅ , ⦆? ] BLOCK ⦆` | `expression.atom` | `lambda_expression` | admitted | Keyword, Other, VariableParam, TypeVariable, Type, Operator |
| [`thunk_expression`](../corpus/ledger/syntax/thunk-expression.gandr) | `thunk ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? BLOCK` or `thunk ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ inf ⦆ ] ⦆? BLOCK` | `expression.atom` | `thunk_expression` | admitted | Keyword, Other, Number |
| [`match_expression`](../corpus/ledger/syntax/match-expression.gandr) | `match EXPRESSION ⦅ with EXPRESSION ⦆? ⦅ -> TYPE ⦆? ⦅ { } ‖ ⦅ { PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ‖ { \| PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ⦆ ⦆` | `expression.atom` | `match_expression` | admitted | Keyword, Operator, Other |
| [`handle_expression`](../corpus/ledger/syntax/handle-expression.gandr) | `handle ‹identifier› : ‹type_identifier› ⦅ with sort ‹type_identifier› = TYPE ⦆* ⟨block⟩ ⦅ with ⦅ { ⦅ pure ( ‹identifier› ) => EXPRESSION ‖ oper ‹identifier› ( ‹identifier› ⦅ , ‹identifier› ⦅ , ‹identifier› ⦆? ⦆? ) => EXPRESSION ⦆ ⦅ , ⦅ pure ( ‹identifier› ) => EXPRESSION ‖ oper ‹identifier› ( ‹identifier› ⦅ , ‹identifier› ⦅ , ‹identifier› ⦆? ⦆? ) => EXPRESSION ⦆ ⦆* ⦅ , ⦆? } ‖ ‹type_identifier› ⦆ ⦆?` | `expression.atom` | `handle_expression` * | admitted | Keyword, VariableDef, Other, Type, Number, Member, VariableParam, Operator, FunctionDef |
| [`if_expression`](../corpus/ledger/syntax/if-expression.gandr) | `if EXPRESSION ⦅ -> TYPE ⦆? ⟨block⟩ else ⦅ BLOCK ‖ if EXPRESSION ⦅ -> TYPE ⦆? ⟨block⟩ else BLOCK ⦆` | `expression.atom` | `if_expression` | admitted | Keyword, Operator, Other, VariableDef, Number, Type, Member |
| [`for_expression`](../corpus/ledger/syntax/for-expression.gandr) | `for ‹identifier› in EXPRESSION ⟨block⟩` | `expression.atom` | `for_expression` * | admitted | Keyword, VariableDef, Other, Number, Type, Member |
| [`while_expression`](../corpus/ledger/syntax/while-expression.gandr) | `while EXPRESSION ⟨block⟩` | `expression.atom` | `while_expression` * | admitted | Keyword, Other, VariableDef, Number, Type, Member |
| [`loop_expression`](../corpus/ledger/syntax/loop-expression.gandr) | `loop ⟨block⟩` | `expression.atom` | `loop_expression` * | admitted | Keyword, Other, VariableDef, Number, Type, Member |
| [`break_expression`](../corpus/ledger/syntax/break-expression.gandr) | `break` | `expression.atom` | `break_expression` * | admitted | Keyword |
| [`break_value_expression`](../corpus/ledger/syntax/break-value-expression.gandr) | `break ( EXPRESSION )` | `expression.atom` | `break_value_expression` * | admitted | Keyword, Other |
| [`continue_expression`](../corpus/ledger/syntax/continue-expression.gandr) | `continue` | `expression.atom` | `continue_expression` * | admitted | Keyword |
| [`co_expression`](../corpus/ledger/syntax/co-expression.gandr) | `co { ‹identifier› = EXPRESSION ⦅ , ‹identifier› = EXPRESSION ⦆* ⦅ , ⦆? }` | `expression.atom` | `co_expression` | admitted | Keyword, Other, Member |
| [`glob_expression`](../corpus/ledger/syntax/glob-expression.gandr) | `glob { ⦅ ‹identifier› = EXPRESSION ; ⦆* }` | `expression.atom` | `glob_expression` * | admitted | Keyword, Other, Member |
| [`telescope_expression`](../corpus/ledger/syntax/telescope-expression.gandr) | `#{ . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ = EXPRESSION ⦆? ⦅ , . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ = EXPRESSION ⦆? ⦆* ⦅ , ⦆? } ‖ #{ ⦅ } ‖ EXPRESSION ⦅ = EXPRESSION ⦆? ⦅ \| ‹identifier› = EXPRESSION ⦅ , ‹identifier› = EXPRESSION ⦆* ⦅ , ⦆? } ‖ ⦅ , EXPRESSION ⦅ = EXPRESSION ⦆? ⦆* ⦅ , ⦆? } ⦆ ⦆` | `expression.atom` | `telescope_expression` * | admitted | Other, Member, Number, Operator |
| [`labelled_sum_expression`](../corpus/ledger/syntax/labelled-sum-expression.gandr) | `+ { . ⦅ ‹identifier› ‖ ‹number› ⦆ = EXPRESSION }` | `expression.atom` | `labelled_sum_expression` * | admitted | Operator, Other, Member, Number |
| [`lazy_record_expression`](../corpus/ledger/syntax/lazy-record-expression.gandr) | `& { ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ => EXPRESSION ⦅ , . ⦅ ‹identifier› ‖ ‹number› ⦆ => EXPRESSION ⦆* ⦅ , ⦆? ⦆? }` | `expression.atom` | `lazy_record_expression` * | admitted | Operator, Other, Member, Number |
| [`offer_expression`](../corpus/ledger/syntax/offer-expression.gandr) | `offer ( EXPRESSION ) ⦅ { PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ‖ { \| PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ⦆` | `expression.atom` | `offer_expression` | admitted | Keyword, Other, Operator |
| [`migrate_expression`](../corpus/ledger/syntax/migrate-expression.gandr) | `migrate [ ‹identifier› ] BLOCK` | `expression.atom` | `migrate_expression` | admitted | Keyword, Other, Label |
| [`send_expression`](../corpus/ledger/syntax/send-expression.gandr) | `send ( EXPRESSION , EXPRESSION )` | `expression.atom` | `send_expression` | admitted | Keyword, Other |
| [`close_expression`](../corpus/ledger/syntax/close-expression.gandr) | `close ( EXPRESSION )` | `expression.atom` | `close_expression` | admitted | Keyword, Other |
| [`select_expression`](../corpus/ledger/syntax/select-expression.gandr) | `select ( EXPRESSION , ‹identifier› )` | `expression.atom` | `select_expression` | admitted | Keyword, Other, Label |
| [`dup_expression`](../corpus/ledger/syntax/dup-expression.gandr) | `dup ( EXPRESSION )` | `expression.atom` | `dup_expression` | reserved | Keyword, Other |
| [`drop_expression`](../corpus/ledger/syntax/drop-expression.gandr) | `drop ( EXPRESSION )` | `expression.atom` | `drop_expression` | admitted | Keyword, Other |
| [`recv_expression`](../corpus/ledger/syntax/recv-expression.gandr) | `recv ( EXPRESSION )` | `expression.atom` | `recv_expression` * | admitted | Keyword, Other |
| [`acquire_expression`](../corpus/ledger/syntax/acquire-expression.gandr) | `acquire ( EXPRESSION )` | `expression.atom` | `acquire_expression` * | reserved | Keyword, Other |
| [`release_expression`](../corpus/ledger/syntax/release-expression.gandr) | `release ( EXPRESSION )` | `expression.atom` | `release_expression` * | reserved | Keyword, Other |
| [`fork_expression`](../corpus/ledger/syntax/fork-expression.gandr) | `fork ⦅ ! ⦆? ( ‹identifier› : TYPE ) EXPRESSION` | `expression.atom` | `fork_expression` * | admitted | Keyword, Other, VariableParam |
| [`access_expression`](../corpus/ledger/syntax/access-expression.gandr) | `access ⦅ shared ‖ exclusive ⦆? ‹identifier› ⦅ ⦅ .#[ ‖ [ ⦆ EXPRESSION ] ⦆? as ‹identifier› BLOCK ⦅ unwind BLOCK ⦆?` | `expression.atom` | `access_expression` * | admitted | Keyword, Other, Variable, VariableDef |
| [`resume_expression`](../corpus/ledger/syntax/resume-expression.gandr) | `resume ( ‹identifier› , EXPRESSION )` | `expression.atom` | `resume_expression` * | admitted | Keyword, Other, Variable |
| [`abort_expression`](../corpus/ledger/syntax/abort-expression.gandr) | `abort ( ‹identifier› )` | `expression.atom` | `abort_expression` * | admitted | Keyword, Other, Variable |
| [`shell_block`](../corpus/ledger/syntax/shell-block.gandr) | `#!{ ⦅ EXPRESSION ⦆? }` | `expression.atom` | `shell_block` | unadmitted | Other |
| [`identifier.expression`](../corpus/ledger/syntax/identifier.expression.gandr) | `‹identifier›` | `expression.atom` | `identifier` | admitted | Variable |
| [`constructor.expression`](../corpus/ledger/syntax/constructor.expression.gandr) | `‹constructor›` | `expression.atom` | `constructor` | admitted | Constructor |
| [`boolean.expression`](../corpus/ledger/syntax/boolean.expression.gandr) | `true ‖ false` | `expression.atom` | `boolean` | admitted | Boolean |
| [`unit.expression`](../corpus/ledger/syntax/unit.expression.gandr) | `unit` | `expression.atom` | `unit` | admitted | Keyword |
| [`number.expression`](../corpus/ledger/syntax/number.expression.gandr) | `‹number›` | `expression.atom` | `number` | admitted | Number |
| [`typed_number.expression`](../corpus/ledger/syntax/typed-number.expression.gandr) | `‹typed_number›` | `expression.atom` | `typed_number` | admitted | Number |
| [`character`](../corpus/ledger/syntax/character.gandr) | `‹character›` | `expression.atom` | `character` | admitted | Character |
| [`string.expression`](../corpus/ledger/syntax/string.expression.gandr) | `" ⦅ ‹escape_sequence› ‖ ‹string_fragment› ‖ ${ EXPRESSION } ⦆* "` | `expression.atom` | `string` | admitted | StringLit, Escape, Other |
| [`list_operator`](../corpus/ledger/syntax/list-operator.gandr) | `; ‖ & ‖ newline` | `expression.atom` | `list_operator` | admitted | Operator |
| [`pipeline.pipe`](../corpus/ledger/syntax/pipeline.pipe.gandr) | `EXPRESSION \| EXPRESSION` | `expression.postfix` | `pipeline` | admitted | Operator |
| [`pipeline.pipe_both`](../corpus/ledger/syntax/pipeline.pipe-both.gandr) | `EXPRESSION \|& EXPRESSION` | `expression.postfix` | `pipeline` | admitted | Operator |
| [`environment_assignment`](../corpus/ledger/syntax/environment-assignment.gandr) | `‹environment_assignment›` | `expression.atom` | `environment_assignment` | admitted | VariableParam |
| [`shell_word`](../corpus/ledger/syntax/shell-word.gandr) | `‹shell_word›` | `expression.atom` | `shell_word` | admitted | Path |
| [`single_quoted_string`](../corpus/ledger/syntax/single-quoted-string.gandr) | `' ‹single_quoted_content› '` | `expression.atom` | `single_quoted_string` | admitted | StringLit |
| [`double_quoted_string`](../corpus/ledger/syntax/double-quoted-string.gandr) | `" ⦅ ‹double_string_fragment› ‖ ‹escape_sequence› ‖ ⟨variable_expansion⟩ ⦆* "` | `expression.atom` | `double_quoted_string` | admitted | StringLit, Escape, Other, Variable |
| [`variable_expansion`](../corpus/ledger/syntax/variable-expansion.gandr) | `$ ‹variable_name› ‖ ${ ‹variable_name› }` | `expression.atom` | `variable_expansion` | admitted | Other, Variable |
| [`variable_name`](../corpus/ledger/syntax/variable-name.gandr) | `‹variable_name›` | `expression.atom` | `variable_name` | admitted | Variable |
| [`command_substitution`](../corpus/ledger/syntax/command-substitution.gandr) | `$!{ }` | `expression.atom` | `command_substitution` | admitted | Other |
| [`host_escape`](../corpus/ledger/syntax/host-escape.gandr) | `$ ( EXPRESSION )` | `expression.atom` | `host_escape` | admitted | Other |
| [`subshell`](../corpus/ledger/syntax/subshell.gandr) | `[ ⦅ EXPRESSION ⦆? ]` | `expression.atom` | `subshell` | admitted | Other |
| [`file_descriptor`](../corpus/ledger/syntax/file-descriptor.gandr) | `‹file_descriptor›` | `expression.atom` | `file_descriptor` | admitted | Number |
| [`redirection_operator`](../corpus/ledger/syntax/redirection-operator.gandr) | `<> ‖ <& ‖ >& ‖ >> ‖ < ‖ >` | `expression.atom` | `redirection_operator` | admitted | Operator |
| [`forget_model_expression`](../corpus/ledger/syntax/forget-model-expression.gandr) | `forget [ TYPE ⦅ , TYPE ⦆* ⦅ , ⦆? ] ( EXPRESSION ) at TYPE` | `expression.pure` | `forget_model_expression` * | admitted | Other, Keyword |

## `type` — 41 rules

| Rule | Form | Group | Kind | Admission | Roles |
| ---- | ---- | ----- | ---- | --------- | ----- |
| [`package_type`](../corpus/ledger/syntax/package-type.gandr) | `package [ ‹type_identifier› ⦅ , ‹type_identifier› ⦆* ⦅ , ⦆? ] TYPE` | `type.application` | `package_type` * | unadmitted | Keyword, Other, Type |
| [`function_type`](../corpus/ledger/syntax/function-type.gandr) | `TYPE -> TYPE` | `type.arrow` | `function_type` | admitted | Operator |
| [`value_function_type`](../corpus/ledger/syntax/value-function-type.gandr) | `TYPE => TYPE` | `type.arrow` | `value_function_type` * | admitted | Operator |
| [`union_type`](../corpus/ledger/syntax/union-type.gandr) | `TYPE \| TYPE` | `type.union` | `union_type` | unadmitted | Operator |
| [`lazy_product_type`](../corpus/ledger/syntax/lazy-product-type.gandr) | `TYPE & TYPE` | `type.lazy_product` | `lazy_product_type` | admitted | Operator |
| [`equivalence_type`](../corpus/ledger/syntax/equivalence-type.gandr) | `TYPE ≃ TYPE` or `TYPE <~> TYPE` | `type.equivalence` | `equivalence_type` * | admitted | Operator |
| [`isomorphism_type`](../corpus/ledger/syntax/isomorphism-type.gandr) | `TYPE ≅ TYPE` or `Iso(TYPE, TYPE)` | `type.equivalence` | `isomorphism_type` * | admitted | Operator |
| [`universe_flow_type`](../corpus/ledger/syntax/universe-flow-type.gandr) | `TYPE ⇝ TYPE` or `TYPE ~~> TYPE` | `type.equivalence` | `universe_flow_type` * | admitted | Operator |
| [`manifest_type`](../corpus/ledger/syntax/manifest-type.gandr) | `TYPE with TYPE` | `type.equivalence` | `manifest_type` * | admitted | Keyword |
| [`manifest_sort`](../corpus/ledger/syntax/manifest-sort.gandr) | `sort ‹type_identifier› = TYPE` | `type.union` | `manifest_sort` * | admitted | Keyword, Type, Other |
| [`sum_type`](../corpus/ledger/syntax/sum-type.gandr) | `TYPE + TYPE` | `type.sum` | `sum_type` | admitted | Operator |
| [`product_type`](../corpus/ledger/syntax/product-type.gandr) | `TYPE * TYPE` | `type.product` | `product_type` | admitted | Operator |
| [`f_type.row`](../corpus/ledger/syntax/f-type.row.gandr) | `-F [ ⦅ ‹type_identifier› ⦅ , ‹type_identifier› ⦆* ⦅ , ⦆? ⦅ \| TYPE ⦆? ‖ TYPE ⦆ ] TYPE` | `type.application` | `f_type` | admitted | Keyword, Other, Type, Operator |
| [`f_type`](../corpus/ledger/syntax/f-type.gandr) | `-F TYPE` | `type.application` | `f_type` | admitted | Keyword |
| [`f_type.result`](../corpus/ledger/syntax/f-type.result.gandr) | `[ ⦅ ‹type_identifier› ⦅ , ‹type_identifier› ⦆* ⦅ , ⦆? ⦅ \| TYPE ⦆? ‖ TYPE ⦆ ] TYPE` | `type.application` | `f_type` | admitted | Other, Type, Operator |
| [`u_type`](../corpus/ledger/syntax/u-type.gandr) | `+U ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? TYPE` or `+U ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ inf ⦆ ] ⦆? TYPE` | `type.application` | `u_type` | admitted | Keyword, Other, Number |
| [`universe_type`](../corpus/ledger/syntax/universe-type.gandr) | `Type ⦅ [ ⦅ + ‖ - ⦆ ⦅ , ‹number› ⦆? ] ⦆?` | `type.atom` | `universe_type` * | admitted | TypeBuiltin, Other, Keyword, Number |
| [`representable_universe_type`](../corpus/ledger/syntax/representable-universe-type.gandr) | `Type+` | `type.atom` | `representable_universe_type` * | admitted | TypeBuiltin |
| [`at_type`](../corpus/ledger/syntax/at-type.gandr) | `TYPE at ‹identifier›` | `type.application` | `at_type` | admitted | Keyword, Label |
| [`path_type`](../corpus/ledger/syntax/path-type.gandr) | `Path ( ⦅ Type ⦅ [ ⦅ + ‖ - ⦆ ⦅ , ‹number› ⦆? ] ⦆? , TYPE , TYPE ‖ TYPE , EXPRESSION , EXPRESSION ⦆ )` | `type.application` | `path_type` * | admitted | TypeBuiltin, Other, Operator, Number |
| [`bridge_type`](../corpus/ledger/syntax/bridge-type.gandr) | `Bridge ( ⦅ Type ⦅ [ ⦅ + ‖ - ⦆ ⦅ , ‹number› ⦆? ] ⦆? , TYPE , TYPE ‖ TYPE , EXPRESSION , EXPRESSION ⦆ )` | `type.application` | `bridge_type` * | admitted | TypeBuiltin, Other, Operator, Number |
| [`type_application`](../corpus/ledger/syntax/type-application.gandr) | `⦅ ‹type_identifier› ‖ ‹type_variable› ⦅ [ < ] ⦆? ⦆ ( TYPE ⦅ , TYPE ⦆* ⦅ , ⦆? )` | `type.application` | `type_application` | admitted | Type, TypeVariable, Other, Operator |
| [`type_path`](../corpus/ledger/syntax/type-path.gandr) | `TYPE . ⦅ ‹type_variable› . ⦆? ‹type_identifier›` | `type.path` | `type_path` * | admitted | Other, TypeVariable, Type |
| [`staged_type`](../corpus/ledger/syntax/staged-type.gandr) | `TYPE [ ⦅ < ⦆? ‹identifier› ] ⦅ ( TYPE ⦅ , TYPE ⦆* ⦅ , ⦆? ) ⦆?` | `type.path` | `staged_type` * | admitted | Other, Operator, VariableParam |
| [`parenthesized_type`](../corpus/ledger/syntax/parenthesized-type.gandr) | `( TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? )` | `type.atom` | `parenthesized_type` | admitted | Other |
| [`telescope_type`](../corpus/ledger/syntax/telescope-type.gandr) | `#{ ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `telescope_type` * | admitted | Other |
| [`send_session_type`](../corpus/ledger/syntax/send-session-type.gandr) | `! TYPE ⦅ >> ‖ . ⦆ TYPE` | `type.arrow` | `send_session_type` | admitted | Operator, Other |
| [`receive_session_type`](../corpus/ledger/syntax/receive-session-type.gandr) | `? TYPE ⦅ >> ‖ . ⦆ TYPE` | `type.arrow` | `receive_session_type` | admitted | Operator, Other |
| [`end_session_type`](../corpus/ledger/syntax/end-session-type.gandr) | `end` | `type.atom` | `end_session_type` | admitted | Keyword |
| [`labelled_sum_type`](../corpus/ledger/syntax/labelled-sum-type.gandr) | `+ { ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `labelled_sum_type` * | admitted | Operator, Other |
| [`lazy_record_type`](../corpus/ledger/syntax/lazy-record-type.gandr) | `& { ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `lazy_record_type` * | admitted | Operator, Other |
| [`mu_session_type`](../corpus/ledger/syntax/mu-session-type.gandr) | `⦅ rec ‹type_variable› => ‖ mu ‹type_variable› . ⦆ TYPE` | `type.arrow` | `mu_session_type` | admitted | Keyword, TypeVariable, Operator, Other |
| [`primitive_type`](../corpus/ledger/syntax/primitive-type.gandr) | `Any ‖ Unknown ‖ Never ‖ Boolean ‖ Integer ‖ u32 ‖ u64 ‖ i32 ‖ i64 ‖ f32 ‖ f64 ‖ Char ‖ String ‖ Symbol ‖ Unit ‖ Void ‖ Buf` | `type.atom` | `primitive_type` | admitted | TypeBuiltin |
| [`unknown_type`](../corpus/ledger/syntax/unknown-type.gandr) | `?` | `type.atom` | `unknown_type` * | unadmitted | TypeBuiltin |
| [`type_identifier`](../corpus/ledger/syntax/type-identifier.gandr) | `‹type_identifier›` | `type.atom` | `type_identifier` | admitted | Type |
| [`type_variable`](../corpus/ledger/syntax/type-variable.gandr) | `‹type_variable›` | `type.atom` | `type_variable` | admitted | TypeVariable |
| [`moded_type`](../corpus/ledger/syntax/moded-type.gandr) | `‹type_variable› TYPE` | `type.arrow` | `moded_type` * | admitted | TypeVariable |
| [`capability_type`](../corpus/ledger/syntax/capability-type.gandr) | `Cap ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? { ‹identifier› ⦅ , ‹identifier› ⦆* ⦅ , ⦆? }` or `Cap ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ inf ⦆ ] ⦆? { ‹identifier› ⦅ , ‹identifier› ⦆* ⦅ , ⦆? }` | `type.atom` | `capability_type` * | admitted | TypeBuiltin, Other, Number, Member |
| [`number.type`](../corpus/ledger/syntax/number.type.gandr) | `‹number›` | `type.atom` | `number` | admitted | Number |
| [`f_type.row.labelled`](../corpus/ledger/syntax/f-type.row.labelled.gandr) | `-F [ ⦅ TYPE : ⦆? ‹type_identifier› ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦅ , ⦅ TYPE : ⦆? ‹type_identifier› ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆* ⦅ , ⦆? ⦅ \| TYPE ⦆? ] TYPE` | `type.application` | `f_type` | admitted | Keyword, Other, Type, Operator |
| [`f_type.result.labelled`](../corpus/ledger/syntax/f-type.result.labelled.gandr) | `[ ⦅ TYPE : ⦆? ‹type_identifier› ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦅ , ⦅ TYPE : ⦆? ‹type_identifier› ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆* ⦅ , ⦆? ⦅ \| TYPE ⦆? ] TYPE` | `type.application` | `f_type` | admitted | Other, Type, Keyword, Operator |

## `instantiation` — 4 rules

| Rule | Form | Group | Kind | Admission | Roles |
| ---- | ---- | ----- | ---- | --------- | ----- |
| [`instantiation.direction.descent`](../corpus/ledger/syntax/instantiation.direction.descent.gandr) | `<` | `expression.atom` | `instantiation_expression` | admitted | Operator |
| [`instantiation.direction.productivity`](../corpus/ledger/syntax/instantiation.direction.productivity.gandr) | `>` | `expression.atom` | `instantiation_expression` | admitted | Operator |
| [`instantiation.explicit`](../corpus/ledger/syntax/instantiation.explicit.gandr) | `. ‹identifier› ⦅ = EXPRESSION ‖ < ‖ > ⦆?` | `expression.pure` | `instantiation_expression` | reserved | Other, VariableParam, Operator |
| [`instantiation.tail`](../corpus/ledger/syntax/instantiation.tail.gandr) | `tail` | `expression.atom` | `instantiation_expression` | reserved | Keyword |

## `module_member` — 7 rules

| Rule | Form | Group | Kind | Admission | Roles |
| ---- | ---- | ----- | ---- | --------- | ----- |
| [`module_definition_member`](../corpus/ledger/syntax/module-definition-member.gandr) | `def ⦅ rec ‹identifier› ⦅ [ ⦅ ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? ] ⦆? ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ ⦅ -> TYPE ⦆? { ⦅ ⦅ . ‹identifier› => EXPRESSION ‖ _ => EXPRESSION ⦆ ⦅ , ⦅ . ‹identifier› => EXPRESSION ‖ _ => EXPRESSION ⦆ ⦆* ⦅ , ⦆? ‖ ⦅ let PATTERN ⦅ : TYPE ⦆? = EXPRESSION ; ‖ unpack ‹identifier› : TYPE = EXPRESSION ; ‖ leta ‹identifier› = EXPRESSION ; ‖ var ⦅ [ ‹number› ] ⦆? ‹identifier› ⦅ : TYPE ⦆? = EXPRESSION ; ‖ EXPRESSION ; ‖ EXPRESSION ⦅ = ‖ += ‖ -= ‖ *= ⦆ EXPRESSION ; ‖ import ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ; ⦆* ⦅ EXPRESSION ⦆? ⦆ } ‖ : TYPE where { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ⦆ ‖ : TYPE where { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ⦆ ‖ ‹identifier› ⦅ [ ⦅ ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? ] ⦆? ⦅ : TYPE ⦅ ⦅ = EXPRESSION ⦆? ; ‖ where { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ⦆ ‖ = EXPRESSION ; ‖ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ shared ‖ consumed ⦆? TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ ⦅ -> TYPE ⦆? ⟨block⟩ ‖ : TYPE where { ⦅ \| PATTERN ⦅ , PATTERN ⦆* ⦅ if EXPRESSION ⦆? => EXPRESSION ⦆* } ⦆ ⦆ ⦆` | `item.singleton` | `module_declaration` | admitted | Keyword, FunctionDef, Other, VariableParam, TypeVariable, Type, Operator, Member, Variable, VariableDef, Number |
| [`attributed_module_member`](../corpus/ledger/syntax/attributed-module-member.gandr) | `⟨attribute_block⟩ ⦅ ⟨attribute_block⟩ ⦆* ⦅ ⟨def_value⟩ ‖ ⟨module_type_member⟩ ‖ ⟨module_law_member⟩ ⦆` | `item.singleton` | `module_declaration` | admitted | Other, Keyword, FunctionDef, VariableParam, TypeVariable, Type, Operator, Member, Variable, VariableDef, Number |
| [`module_type_member`](../corpus/ledger/syntax/module-type-member.gandr) | `type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? = TYPE ⦅ ; ‖ where { ⦅ face ‹identifier› = { ⦅ ‹identifier› ⦅ , ‹identifier› ⦆* ⦆? } ; ⦆* } ⦆` | `item.singleton` | `module_declaration` | admitted | Keyword, Type, Other, TypeVariable, Member |
| [`nested_module_member`](../corpus/ledger/syntax/nested-module-member.gandr) | `module ⦅ ‹identifier› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ‖ :> ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ⦆? where { ⦅ MODULE_MEMBER ⦆* }` | `item.singleton` | `module_declaration` | admitted | Keyword, VariableDef, Type, Other, Member, TypeVariable, Operator |
| [`module_include_member`](../corpus/ledger/syntax/module-include-member.gandr) | `include ‹type_identifier› ;` | `item.singleton` | `module_declaration` | admitted | Keyword, Type, Other |
| [`module_law_member`](../corpus/ledger/syntax/module-law-member.gandr) | `law ‹identifier› admitted ;` | `item.singleton` | `module_declaration` | admitted | Keyword, FunctionDef, Other |
| [`inner_attribute_member`](../corpus/ledger/syntax/inner-attribute-member.gandr) | `@![ ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ⦅ = EXPRESSION ⦆? ) ⦆? ⦆* ⦅ , ⦆? ]` | `item.singleton` | `module_declaration` | admitted | Other |

## `block` — 1 rule

| Rule | Form | Group | Kind | Admission | Roles |
| ---- | ---- | ----- | ---- | --------- | ----- |
| [`statement_block`](../corpus/ledger/syntax/statement-block.gandr) | `{ ⦅ let PATTERN ⦅ : TYPE ⦆? = EXPRESSION ; ‖ unpack ‹identifier› : TYPE = EXPRESSION ; ‖ leta ‹identifier› = EXPRESSION ; ‖ var ⦅ [ ‹number› ] ⦆? ‹identifier› ⦅ : TYPE ⦆? = EXPRESSION ; ‖ EXPRESSION ; ‖ EXPRESSION ⦅ = ‖ += ‖ -= ‖ *= ⦆ EXPRESSION ; ‖ import ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ; ⦆* ⦅ EXPRESSION ⦆? }` | `expression.atom` | `block` | admitted | Other, Keyword, VariableDef, Number, Type, Member |

## Internal — 1 rule

A rule no source can mold, with the reason and what the reason is read from: the grammar's forms, the labeler over a tile's own text, or a parser probe. These rules have no exemplar.

| Rule | Sort | Form | Reason | Read from |
| ---- | ---- | ---- | ------ | --------- |
| `instantiation.type` | instantiation | `TYPE` | the form holds no tile, so no tree names the rule | grammar |

## Attributes — 17 attributes

Every attribute the lowering's registry admits in an `@[ … ]` block, with the payload its schema takes, linking its exemplar, which the exemplar gate lowers and checks the attribute is filed.

| Attribute | Payload |
| --------- | ------- |
| [`checks`](../corpus/ledger/attributes/checks.gandr) | no payload |
| [`owes`](../corpus/ledger/attributes/owes.gandr) | an integer payload |
| [`refuses`](../corpus/ledger/attributes/refuses.gandr) | a text payload |
| [`runs`](../corpus/ledger/attributes/runs.gandr) | a text payload |
| [`normalizes`](../corpus/ledger/attributes/normalizes.gandr) | a text payload |
| [`decomposes`](../corpus/ledger/attributes/decomposes.gandr) | an unquoted form |
| [`traces`](../corpus/ledger/attributes/traces.gandr) | an unquoted form |
| [`reads`](../corpus/ledger/attributes/reads.gandr) | an unquoted form |
| [`doc`](../corpus/ledger/attributes/doc.gandr) | a text payload |
| [`explicit_exits`](../corpus/ledger/attributes/explicit_exits.gandr) | no payload |
| [`explicit_runs`](../corpus/ledger/attributes/explicit_runs.gandr) | no payload or the text "effects" |
| [`respects`](../corpus/ledger/attributes/respects.gandr) | a declared name or a tuple of declared names |
| [`entry`](../corpus/ledger/attributes/entry.gandr) | a declared name or a tuple of declared names |
| [`form`](../corpus/ledger/attributes/form.gandr) | one of the words `explicit`, `sugared` |
| [`identity`](../corpus/ledger/attributes/identity.gandr) | a tuple of two or three declared names: a relation, its reflexivity and optionally its transport law |
| [`deprecated`](../corpus/ledger/attributes/deprecated.gandr) | no payload or a record of the texts `since`, `note` |
| [`boundary`](../corpus/ledger/attributes/boundary.gandr) | a declared name or a tuple of declared names |

## Decisions — 110 of 174 rules decided at every token

Where the molder decides a rule's own tokens as it reads them, read off the mold table. A rule opens on the labels its first tiles carry. It shares an opener with each other rule of its sort that opens on one of those labels, a hole facing both openers alike or neither: at that token the molder ranks them and may read on. A fork is a tile after which one label continues the form at two places or more, so the molder reads on to choose. A rule with no shared opener and no fork is decided at each of its own tokens; the tokens in its holes are their own rules' to decide.

| Rule | Sort | Molds | Opens on | Shares its opener with | Forks |
| ---- | ---- | ----- | -------- | ---------------------- | ----- |
| `def_value` | item | 194 | `def` | — | 40 |
| `data_declaration` | item | 138 | `data` | — | 34 |
| `codata_declaration` | item | 132 | `codata` | — | 52 |
| `module_declaration` | item | 171 | `module` | — | 60 |
| `flow_declaration` | item | 15 | `flow` | — | 0 |
| `import_declaration` | item | 26 | `import` | — | 4 |
| `world_declaration` | item | 20 | `world` | — | 4 |
| `offers_declaration` | item | 14 | `offers` | — | 4 |
| `rec_block` | item | 3 | `rec` | — | 0 |
| `pub_declaration` | item | 1 | `pub` | — | 0 |
| `attribute_block` | item | 12 | `@[` | — | 4 |
| `inner_attribute_block` | item | 12 | `@![` | — | 4 |
| `extern_block` | item | 43 | `extern` | — | 12 |
| `module_definition_member` | module_member | 194 | `def` | — | 40 |
| `attributed_module_member` | module_member | 246 | `@[` | — | 52 |
| `module_type_member` | module_member | 24 | `type` | — | 4 |
| `nested_module_member` | module_member | 106 | `module` | — | 40 |
| `module_include_member` | module_member | 3 | `include` | — | 0 |
| `module_law_member` | module_member | 4 | `law` | — | 0 |
| `inner_attribute_member` | module_member | 12 | `@![` | — | 4 |
| `wildcard` | pattern | 1 | `_` | — | 0 |
| `constructor_pattern` | pattern | 8 | `constructor` | — | 2 |
| `tuple_pattern` | pattern | 5 | `(` | — | 2 |
| `telescope_pattern` | pattern | 14 | `#{` | — | 10 |
| `labelled_sum_pattern` | pattern | 7 | `+` | — | 0 |
| `list_pattern` | pattern | 7 | `#[` `[` | — | 3 |
| `rest_pattern` | pattern | 1 | `..` | — | 0 |
| `literal_pattern` | pattern | 8 | `"` `false` `number` `true` `typed_number` | — | 0 |
| `hole.pattern` | pattern | 2 | `?` | — | 0 |
| `cons_pattern` | pattern | 5 | `identifier` | `identifier.pattern` | 0 |
| `or_pattern` | pattern | 1 | `\|` | — | 0 |
| `as_pattern` | pattern | 2 | `.@` `@` | — | 0 |
| `instantiation.type` | instantiation | 0 | — | — | 0 |
| `instantiation.direction.descent` | instantiation | 1 | `<` | — | 0 |
| `instantiation.direction.productivity` | instantiation | 1 | `>` | — | 0 |
| `instantiation.explicit` | instantiation | 5 | `.` | — | 0 |
| `instantiation.tail` | instantiation | 1 | `tail` | — | 0 |
| `pure_expression` | expression | 1 | `pure` | — | 0 |
| `return_expression` | expression | 1 | `return` | — | 0 |
| `become_expression` | expression | 1 | `become` | — | 0 |
| `bind_expression` | expression | 3 | `bind` | — | 0 |
| `binary_expression.or` | expression | 1 | `\|\|` | — | 0 |
| `binary_expression.and` | expression | 1 | `&&` | — | 0 |
| `binary_expression.cmp.eq` | expression | 1 | `==` | — | 0 |
| `binary_expression.cmp.ne` | expression | 1 | `!=` | — | 0 |
| `binary_expression.cmp.lt` | expression | 1 | `<` | — | 0 |
| `binary_expression.cmp.le` | expression | 1 | `<=` | — | 0 |
| `binary_expression.cmp.gt` | expression | 1 | `>` | — | 0 |
| `binary_expression.cmp.ge` | expression | 1 | `>=` | — | 0 |
| `binary_expression.cons` | expression | 1 | `∷` | — | 0 |
| `binary_expression.add.concat` | expression | 1 | `++` | — | 0 |
| `binary_expression.add.plus` | expression | 1 | `+` | — | 0 |
| `binary_expression.add.minus` | expression | 1 | `-` | — | 0 |
| `binary_expression.mul.times` | expression | 1 | `*` | — | 0 |
| `unary_expression` | expression | 1 | `-` | — | 0 |
| `force_expression` | expression | 1 | `force` | — | 0 |
| `run_expression` | expression | 1 | `run` | — | 0 |
| `hold_expression` | expression | 1 | `hold` | — | 0 |
| `splice_expression` | expression | 1 | `~` | — | 0 |
| `pack_expression` | expression | 5 | `pack` | `pack_model_expression` | 2 |
| `pack_model_expression` | expression | 2 | `pack` | `pack_expression` | 0 |
| `call_expression` | expression | 4 | `(` | — | 2 |
| `instantiation_expression` | expression | 4 | `[` | `index_expression` | 2 |
| `projection_expression` | expression | 4 | `.` | — | 0 |
| `record_selection_expression` | expression | 10 | `.#{` | — | 4 |
| `view_expression` | expression | 38 | `as` | — | 0 |
| `index_expression` | expression | 3 | `.#[` `[` | `instantiation_expression` | 0 |
| `hole` | expression | 2 | `?` | — | 0 |
| `wildcard.expression` | expression | 1 | `_` | — | 0 |
| `parenthesized_expression` | expression | 10 | `(` | — | 4 |
| `type_quote_expression` | expression | 2 | `type(` | — | 0 |
| `list_expression` | expression | 5 | `#[` `[` | — | 3 |
| `block` | expression | 36 | `{` | — | 0 |
| `lambda_expression` | expression | 29 | `fun` | — | 14 |
| `thunk_expression` | expression | 6 | `thunk` | — | 0 |
| `match_expression` | expression | 24 | `match` | — | 9 |
| `handle_expression` | expression | 80 | `handle` | — | 4 |
| `if_expression` | expression | 78 | `if` | — | 0 |
| `for_expression` | expression | 39 | `for` | — | 0 |
| `while_expression` | expression | 37 | `while` | — | 0 |
| `loop_expression` | expression | 37 | `loop` | — | 0 |
| `break_expression` | expression | 1 | `break` | `break_value_expression` | 0 |
| `break_value_expression` | expression | 3 | `break` | `break_expression` | 0 |
| `continue_expression` | expression | 1 | `continue` | — | 0 |
| `co_expression` | expression | 9 | `co` | — | 2 |
| `glob_expression` | expression | 6 | `glob` | — | 0 |
| `telescope_expression` | expression | 27 | `#{` | — | 12 |
| `labelled_sum_expression` | expression | 7 | `+` | — | 0 |
| `lazy_record_expression` | expression | 13 | `&` | `list_operator` | 2 |
| `offer_expression` | expression | 22 | `offer` | — | 7 |
| `migrate_expression` | expression | 4 | `migrate` | — | 0 |
| `send_expression` | expression | 4 | `send` | — | 0 |
| `close_expression` | expression | 3 | `close` | — | 0 |
| `select_expression` | expression | 5 | `select` | — | 0 |
| `dup_expression` | expression | 3 | `dup` | — | 0 |
| `drop_expression` | expression | 3 | `drop` | — | 0 |
| `recv_expression` | expression | 3 | `recv` | — | 0 |
| `acquire_expression` | expression | 3 | `acquire` | — | 0 |
| `release_expression` | expression | 3 | `release` | — | 0 |
| `fork_expression` | expression | 6 | `fork` | — | 0 |
| `access_expression` | expression | 10 | `access` | — | 0 |
| `resume_expression` | expression | 5 | `resume` | — | 0 |
| `abort_expression` | expression | 4 | `abort` | — | 0 |
| `shell_block` | expression | 2 | `#!{` | — | 0 |
| `identifier.pattern` | pattern | 1 | `identifier` | `cons_pattern` | 0 |
| `unit.pattern` | pattern | 1 | `unit` | — | 0 |
| `identifier.expression` | expression | 1 | `identifier` | — | 0 |
| `constructor.expression` | expression | 1 | `constructor` | — | 0 |
| `boolean.expression` | expression | 2 | `false` `true` | — | 0 |
| `unit.expression` | expression | 1 | `unit` | — | 0 |
| `number.expression` | expression | 1 | `number` | — | 0 |
| `typed_number.expression` | expression | 1 | `typed_number` | — | 0 |
| `character` | expression | 1 | `character` | — | 0 |
| `string.expression` | expression | 6 | `"` | `double_quoted_string` | 0 |
| `statement_block` | block | 36 | `{` | — | 0 |
| `package_type` | type | 7 | `package` | — | 2 |
| `function_type` | type | 1 | `->` | — | 0 |
| `value_function_type` | type | 1 | `=>` | — | 0 |
| `union_type` | type | 1 | `\|` | — | 0 |
| `lazy_product_type` | type | 1 | `&` | — | 0 |
| `equivalence_type` | type | 1 | `≃` | — | 0 |
| `isomorphism_type` | type | 1 | `≅` | — | 0 |
| `universe_flow_type` | type | 1 | `⇝` | — | 0 |
| `manifest_type` | type | 1 | `with` | — | 0 |
| `manifest_sort` | type | 3 | `sort` | — | 0 |
| `sum_type` | type | 1 | `+` | — | 0 |
| `product_type` | type | 1 | `*` | — | 0 |
| `f_type.row` | type | 8 | `-F` | `f_type`, `f_type.row.labelled` | 2 |
| `f_type` | type | 1 | `-F` | `f_type.row`, `f_type.row.labelled` | 0 |
| `f_type.result` | type | 7 | `[` | `f_type.result.labelled` | 2 |
| `u_type` | type | 6 | `+U` | — | 0 |
| `universe_type` | type | 7 | `Type` | — | 0 |
| `representable_universe_type` | type | 1 | `Type+` | — | 0 |
| `at_type` | type | 2 | `at` | — | 0 |
| `path_type` | type | 14 | `Path` | — | 0 |
| `bridge_type` | type | 14 | `Bridge` | — | 0 |
| `type_application` | type | 9 | `type_identifier` `type_variable` | `moded_type`, `type_identifier`, `type_variable` | 2 |
| `type_path` | type | 4 | `.` | — | 0 |
| `staged_type` | type | 8 | `[` | — | 2 |
| `parenthesized_type` | type | 6 | `(` | — | 4 |
| `telescope_type` | type | 6 | `#{` | — | 4 |
| `send_session_type` | type | 3 | `!` | — | 0 |
| `receive_session_type` | type | 3 | `?` | `unknown_type` | 0 |
| `end_session_type` | type | 1 | `end` | — | 0 |
| `labelled_sum_type` | type | 7 | `+` | — | 4 |
| `lazy_record_type` | type | 7 | `&` | — | 4 |
| `mu_session_type` | type | 6 | `mu` `rec` | — | 0 |
| `primitive_type` | type | 17 | `Any` `Boolean` `Buf` `Char` `Integer` `Never` `String` `Symbol` `Unit` `Unknown` `Void` `f32` `f64` `i32` `i64` `u32` `u64` | — | 0 |
| `unknown_type` | type | 1 | `?` | `receive_session_type` | 0 |
| `type_identifier` | type | 1 | `type_identifier` | `type_application` | 0 |
| `type_variable` | type | 1 | `type_variable` | `moded_type`, `type_application` | 0 |
| `moded_type` | type | 1 | `type_variable` | `type_application`, `type_variable` | 0 |
| `capability_type` | type | 12 | `Cap` | — | 2 |
| `number.type` | type | 1 | `number` | — | 0 |
| `list_operator` | expression | 3 | `&` `;` `newline` | `lazy_record_expression` | 0 |
| `pipeline.pipe` | expression | 1 | `\|` | — | 0 |
| `pipeline.pipe_both` | expression | 1 | `\|&` | — | 0 |
| `environment_assignment` | expression | 1 | `environment_assignment` | — | 0 |
| `shell_word` | expression | 1 | `shell_word` | — | 0 |
| `single_quoted_string` | expression | 3 | `'` | — | 0 |
| `double_quoted_string` | expression | 9 | `"` | `string.expression` | 0 |
| `variable_expansion` | expression | 5 | `$` `${` | `host_escape` | 0 |
| `variable_name` | expression | 1 | `variable_name` | — | 0 |
| `command_substitution` | expression | 2 | `command_substitution_start` | — | 0 |
| `host_escape` | expression | 3 | `$` | `variable_expansion` | 0 |
| `subshell` | expression | 2 | `subshell_open` | — | 0 |
| `file_descriptor` | expression | 1 | `file_descriptor` | — | 0 |
| `redirection_operator` | expression | 6 | `<` `<&` `<>` `>` `>&` `>>` | — | 0 |
| `theory_declaration` | item | 446 | `theory` | — | 122 |
| `circuit_declaration` | item | 123 | `oper` `rule` | — | 38 |
| `derive_declaration` | item | 9 | `derive` | — | 0 |
| `forget_model_expression` | expression | 8 | `forget` | — | 2 |
| `f_type.row.labelled` | type | 18 | `-F` | `f_type`, `f_type.row` | 4 |
| `f_type.result.labelled` | type | 17 | `[` | `f_type.result` | 4 |

## Menus — 203 labels

Every label a tile carries, with the molds the molder ranks when it reads the label, the rules they belong to and how many of them can open a form. The largest menu comes first.

| Label | Molds | Rules | Opening |
| ----- | ----- | ----- | ------- |
| `identifier` | 385 | 55 | 3 |
| `,` | 275 | 53 | 0 |
| `:` | 263 | 32 | 0 |
| `type_identifier` | 170 | 34 | 2 |
| `=` | 144 | 31 | 0 |
| `;` | 138 | 25 | 1 |
| `)` | 127 | 43 | 0 |
| `(` | 123 | 42 | 4 |
| `}` | 79 | 41 | 0 |
| `type_variable` | 70 | 15 | 3 |
| `.` | 69 | 32 | 3 |
| `]` | 67 | 41 | 0 |
| `{` | 62 | 32 | 2 |
| `[` | 61 | 38 | 7 |
| `number` | 52 | 30 | 3 |
| `_` | 48 | 7 | 2 |
| `=>` | 45 | 10 | 1 |
| `-->` | 31 | 5 | 0 |
| `<=>` | 27 | 5 | 0 |
| `==>` | 27 | 5 | 0 |
| `<->` | 24 | 4 | 0 |
| `shared` | 23 | 8 | 0 |
| `type` | 23 | 5 | 1 |
| `consumed` | 22 | 7 | 0 |
| `arm_bar` | 21 | 8 | 0 |
| `where` | 21 | 10 | 0 |
| `<` | 18 | 9 | 3 |
| `ω` | 17 | 5 | 0 |
| `import` | 16 | 12 | 1 |
| `*=` | 15 | 11 | 0 |
| `+=` | 15 | 11 | 0 |
| `-=` | 15 | 11 | 0 |
| `if` | 15 | 5 | 1 |
| `let` | 15 | 11 | 0 |
| `leta` | 15 | 11 | 0 |
| `rule` | 15 | 4 | 1 |
| `unpack` | 15 | 11 | 0 |
| `var` | 15 | 11 | 0 |
| `with` | 15 | 8 | 1 |
| `sort` | 14 | 8 | 1 |
| `"` | 12 | 5 | 3 |
| `->` | 12 | 8 | 1 |
| `data` | 12 | 3 | 1 |
| `mobile` | 10 | 2 | 0 |
| `#{` | 9 | 5 | 4 |
| `bind` | 9 | 3 | 1 |
| `\|` | 9 | 9 | 3 |
| `+` | 8 | 8 | 5 |
| `pi+` | 8 | 2 | 0 |
| `oper` | 7 | 5 | 1 |
| `constructor` | 6 | 5 | 2 |
| `escape_sequence` | 6 | 5 | 0 |
| `-` | 5 | 5 | 2 |
| `rec` | 5 | 5 | 2 |
| `string_fragment` | 5 | 4 | 0 |
| `variable_name` | 5 | 3 | 1 |
| `&` | 4 | 4 | 4 |
| `>` | 4 | 4 | 3 |
| `?` | 4 | 4 | 4 |
| `@[` | 4 | 3 | 2 |
| `as` | 4 | 4 | 1 |
| `def` | 4 | 4 | 2 |
| `$` | 3 | 3 | 2 |
| `${` | 3 | 3 | 1 |
| `-F` | 3 | 3 | 3 |
| `..` | 3 | 2 | 1 |
| `>>` | 3 | 3 | 1 |
| `Type` | 3 | 3 | 1 |
| `at` | 3 | 3 | 1 |
| `face` | 3 | 3 | 0 |
| `feed` | 3 | 2 | 0 |
| `law` | 3 | 3 | 1 |
| `node` | 3 | 2 | 0 |
| `pure` | 3 | 2 | 1 |
| `~>` | 3 | 2 | 0 |
| `!` | 2 | 2 | 1 |
| `#[` | 2 | 2 | 2 |
| `'` | 2 | 1 | 1 |
| `*` | 2 | 2 | 2 |
| `.#[` | 2 | 2 | 1 |
| `:>` | 2 | 2 | 0 |
| `@![` | 2 | 2 | 2 |
| `admitted` | 2 | 2 | 0 |
| `break` | 2 | 2 | 2 |
| `else` | 2 | 1 | 0 |
| `false` | 2 | 2 | 2 |
| `hole_name` | 2 | 2 | 0 |
| `in` | 2 | 2 | 0 |
| `include` | 2 | 2 | 1 |
| `module` | 2 | 2 | 2 |
| `pack` | 2 | 2 | 2 |
| `true` | 2 | 2 | 2 |
| `typed_number` | 2 | 2 | 2 |
| `unit` | 2 | 2 | 2 |
| `⇝` | 2 | 2 | 1 |
| `∷` | 2 | 2 | 1 |
| `!=` | 1 | 1 | 1 |
| `#` | 1 | 1 | 0 |
| `#!{` | 1 | 1 | 1 |
| `&&` | 1 | 1 | 1 |
| `++` | 1 | 1 | 1 |
| `+U` | 1 | 1 | 1 |
| `.#{` | 1 | 1 | 1 |
| `.@` | 1 | 1 | 1 |
| `<&` | 1 | 1 | 1 |
| `<=` | 1 | 1 | 1 |
| `<>` | 1 | 1 | 1 |
| `==` | 1 | 1 | 1 |
| `>&` | 1 | 1 | 1 |
| `>=` | 1 | 1 | 1 |
| `@` | 1 | 1 | 1 |
| `Any` | 1 | 1 | 1 |
| `Boolean` | 1 | 1 | 1 |
| `Bridge` | 1 | 1 | 1 |
| `Buf` | 1 | 1 | 1 |
| `Cap` | 1 | 1 | 1 |
| `Char` | 1 | 1 | 1 |
| `Integer` | 1 | 1 | 1 |
| `Never` | 1 | 1 | 1 |
| `Path` | 1 | 1 | 1 |
| `String` | 1 | 1 | 1 |
| `Symbol` | 1 | 1 | 1 |
| `Type+` | 1 | 1 | 1 |
| `Unit` | 1 | 1 | 1 |
| `Unknown` | 1 | 1 | 1 |
| `Void` | 1 | 1 | 1 |
| `abort` | 1 | 1 | 1 |
| `access` | 1 | 1 | 1 |
| `acquire` | 1 | 1 | 1 |
| `become` | 1 | 1 | 1 |
| `boundary` | 1 | 1 | 0 |
| `character` | 1 | 1 | 1 |
| `close` | 1 | 1 | 1 |
| `co` | 1 | 1 | 1 |
| `codata` | 1 | 1 | 1 |
| `command_substitution_start` | 1 | 1 | 1 |
| `continue` | 1 | 1 | 1 |
| `derive` | 1 | 1 | 1 |
| `double_string_fragment` | 1 | 1 | 0 |
| `drop` | 1 | 1 | 1 |
| `dup` | 1 | 1 | 1 |
| `end` | 1 | 1 | 1 |
| `environment_assignment` | 1 | 1 | 1 |
| `exclusive` | 1 | 1 | 0 |
| `ext` | 1 | 1 | 0 |
| `extern` | 1 | 1 | 1 |
| `f32` | 1 | 1 | 1 |
| `f64` | 1 | 1 | 1 |
| `file_descriptor` | 1 | 1 | 1 |
| `flow` | 1 | 1 | 1 |
| `for` | 1 | 1 | 1 |
| `force` | 1 | 1 | 1 |
| `forget` | 1 | 1 | 1 |
| `fork` | 1 | 1 | 1 |
| `from` | 1 | 1 | 0 |
| `fun` | 1 | 1 | 1 |
| `glob` | 1 | 1 | 1 |
| `handle` | 1 | 1 | 1 |
| `hold` | 1 | 1 | 1 |
| `i32` | 1 | 1 | 1 |
| `i64` | 1 | 1 | 1 |
| `is` | 1 | 1 | 0 |
| `loop` | 1 | 1 | 1 |
| `match` | 1 | 1 | 1 |
| `migrate` | 1 | 1 | 1 |
| `mu` | 1 | 1 | 1 |
| `newline` | 1 | 1 | 1 |
| `obs` | 1 | 1 | 0 |
| `offer` | 1 | 1 | 1 |
| `offers` | 1 | 1 | 1 |
| `on` | 1 | 1 | 0 |
| `op` | 1 | 1 | 0 |
| `package` | 1 | 1 | 1 |
| `pub` | 1 | 1 | 1 |
| `recv` | 1 | 1 | 1 |
| `release` | 1 | 1 | 1 |
| `requires` | 1 | 1 | 0 |
| `resume` | 1 | 1 | 1 |
| `return` | 1 | 1 | 1 |
| `run` | 1 | 1 | 1 |
| `select` | 1 | 1 | 1 |
| `send` | 1 | 1 | 1 |
| `shape` | 1 | 1 | 0 |
| `shell_word` | 1 | 1 | 1 |
| `single_quoted_content` | 1 | 1 | 0 |
| `subshell_close` | 1 | 1 | 0 |
| `subshell_open` | 1 | 1 | 1 |
| `tail` | 1 | 1 | 1 |
| `theory` | 1 | 1 | 1 |
| `thunk` | 1 | 1 | 1 |
| `type(` | 1 | 1 | 1 |
| `u32` | 1 | 1 | 1 |
| `u64` | 1 | 1 | 1 |
| `under` | 1 | 1 | 0 |
| `unwind` | 1 | 1 | 0 |
| `via` | 1 | 1 | 0 |
| `while` | 1 | 1 | 1 |
| `world` | 1 | 1 | 1 |
| `\|&` | 1 | 1 | 1 |
| `\|\|` | 1 | 1 | 1 |
| `~` | 1 | 1 | 1 |
| `≃` | 1 | 1 | 1 |
| `≅` | 1 | 1 | 1 |
