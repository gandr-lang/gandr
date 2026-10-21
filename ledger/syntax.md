# Syntax ledger

Generated from the built-in grammar by `gandr ledger syntax --write ledger`; never edited by hand. `mise run check:syntax-ledger` regenerates it and fails while this file differs. `syntax.json` holds the same rows for machines, each form as a tree with every tile's mold.

- Grammar fingerprint: `0x4b523a2ae1ddf3e2`
- Rules: 152 — 151 committed, 1 internal
- Molds: 2925
- Attributes: 11

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

Each committed rule links its exemplar, a small source the exemplar gate parses and checks for a tile of the rule; a glyph rule's exemplar holds one item per spelling, and the gate checks each is written. The group is the rule's precedence group. The kind is the named node kind the rule realises; `*` marks a kind the surface's tree-sitter grammar does not have. The roles are the highlight roles of the rule's tiles, each once, first use first.

## `item` — 12 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| [`def_value`](exemplars/syntax/def_value.gandr) | `def ⦅ rec ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? { ⦅ ⦅ . ‹identifier› => EXPRESSION ‖ _ => EXPRESSION ⦆ ⦅ , ⦅ . ‹identifier› => EXPRESSION ‖ _ => EXPRESSION ⦆ ⦆* ⦅ , ⦆? ‖ ⦅ val PATTERN = EXPRESSION ; ‖ run PATTERN ⦅ : TYPE ⦆? <- EXPRESSION ; ‖ unpack ‹identifier› : TYPE = EXPRESSION ; ‖ leta ‹identifier› = EXPRESSION ; ‖ hold ⦅ [ ‹number› ] ⦆? ‹identifier› = EXPRESSION ; ‖ recv ( EXPRESSION ) as ‹identifier› ; ‖ acquire ( EXPRESSION ) as ‹identifier› ; ‖ release ( EXPRESSION ) as ‹identifier› ; ‖ fork ( ‹identifier› : TYPE ) EXPRESSION as ‹identifier› ; ‖ fork ! ( ‹identifier› : TYPE ) EXPRESSION ; ‖ EXPRESSION ; ⦆* ⦅ EXPRESSION ⦆? ⦆ } ‖ ‹identifier› ⦅ @[ ⦅ ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? ] ⦆? ⦅ : TYPE ; ‖ = EXPRESSION ; ‖ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ⟨block⟩ ⦆ ⦆` | `item.singleton` | `def_value` | Keyword, FunctionDef, Other, VariableParam, TypeVariable, Type, Operator, Member, Variable, VariableDef, Number |
| [`data_declaration`](exemplars/syntax/data_declaration.gandr) | `data ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : TYPE ⦆? { ⦅ ⦅ ‹constructor› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> TYPE ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ‖ ⦅ ( ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦅ : TYPE ⦆? ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ⦆ ‖ ⦅ oper ‖ op ⦆ ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ‖ ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦅ ⦅ ; ‖ , ⦆ ⦅ ‹constructor› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> TYPE ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ‖ ⦅ ( ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦅ : TYPE ⦆? ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ⦆ ‖ ⦅ oper ‖ op ⦆ ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ‖ ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦆* ⦅ ; ‖ , ⦆? ⦆? }` or `data ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : TYPE ⦆? { ⦅ ⦅ ‹constructor› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> TYPE ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ‖ ⦅ ( ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦅ : TYPE ⦆? ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ⦆ ‖ ⦅ oper ‖ op ⦆ ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ‖ ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦅ ⦅ ; ‖ , ⦆ ⦅ ‹constructor› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> TYPE ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ‖ ⦅ ( ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦅ : TYPE ⦆? ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ⦆ ‖ ⦅ oper ‖ op ⦆ ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ‖ ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦆* ⦅ ; ‖ , ⦆? ⦆? }` | `item.singleton` | `data_declaration` * | Keyword, Type, Other, TypeVariable, Constructor, Number, VariableParam, Operator, FunctionDef, Member |
| [`codata_declaration`](exemplars/syntax/codata_declaration.gandr) | `codata ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : TYPE ⦆? { ⦅ ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› ⦅ ( ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆? : TYPE ‖ oper ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦅ ⦅ ; ‖ , ⦆ ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› ⦅ ( ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆? : TYPE ‖ oper ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦆* ⦅ ; ‖ , ⦆? ⦆? }` or `codata ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : TYPE ⦆? { ⦅ ⦅ ⦅ ‹number› ‖ inf ⦆? ‹identifier› ⦅ ( ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆? : TYPE ‖ oper ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦅ ⦅ ; ‖ , ⦆ ⦅ ⦅ ‹number› ‖ inf ⦆? ‹identifier› ⦅ ( ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ inf ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆? : TYPE ‖ oper ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦆* ⦅ ; ‖ , ⦆? ⦆? }` | `item.singleton` | `codata_declaration` * | Keyword, Type, Other, TypeVariable, Number, Member, VariableParam, FunctionDef, Operator |
| [`module_declaration`](exemplars/syntax/module_declaration.gandr) | `module ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦅ = ‹type_identifier› ( ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ) ; ‖ ⦅ ( ‹type_identifier› : ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ) ⦆? ⦅ : ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ‖ :> ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ⦆? { ⦅ MODULE_MEMBER ⦆* } ⦆` | `item.singleton` | `module_declaration` | Keyword, Type, VariableDef, Other, Member, TypeVariable, Operator |
| [`import_declaration`](exemplars/syntax/import_declaration.gandr) | `import " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ⦅ as ‹identifier› ⦆? ;` | `item.singleton` | `import_declaration` * | Keyword, StringLit, Escape, VariableDef, Other |
| [`world_declaration`](exemplars/syntax/world_declaration.gandr) | `world ‹identifier› ;` | `item.singleton` | `world_declaration` * | Keyword, Label, Other |
| [`operator_declaration`](exemplars/syntax/operator_declaration.gandr) | `op ⦅ infixl ‖ infixr ‖ infix ‖ prefix ‖ postfix ⦆ ‹number› " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ;` | `item.singleton` | `operator_declaration` * | Keyword, Number, StringLit, Escape, Other |
| [`rec_block`](exemplars/syntax/rec_block.gandr) | `rec { ⦅ ITEM ⦆* }` | `item.singleton` | `rec_block` * | Keyword, Other |
| [`attribute_block`](exemplars/syntax/attribute_block.gandr) | `@[ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ]` | `item.singleton` | `attribute_block` | Other |
| [`extern_block`](exemplars/syntax/extern_block.gandr) | `extern " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " from " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ⦅ as ‹identifier› ⦆? { ⦅ type ‹type_identifier› ; ‖ def ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ; ⦆* }` | `item.singleton` | `extern_block` | Keyword, StringLit, Escape, VariableDef, Other, Type, FunctionDef, VariableParam, TypeVariable, Operator |
| [`theory_declaration`](exemplars/syntax/theory_declaration.gandr) | `theory ‹type_identifier› { ⦅ ⦅ sort ‹type_identifier› ⦅ ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆? : TYPE ‖ data ‹constructor› : ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦆? ‖ ⦅ ⦅ oper ‖ obs ⦆ ‹identifier› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦆? ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆? ‖ ( ⦅ ‹identifier› ⦅ : TYPE ⦆? ⦅ , ‹identifier› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ⦆ ‖ rule ‹identifier› ⦅ : ⦅ ( ⦅ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ‖ ‹identifier› : TYPE ⦆ ⦅ , ⦅ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ‖ ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ‖ EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆? ‖ EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦆ ‖ shape ‹type_identifier› : ‹number› { ⦅ ‹identifier› = { ⦅ ‹number› ⦅ , ‹number› ⦆* ⦆? } ; ⦆* } ‖ include ‹type_identifier› ‖ ext ‹type_identifier› = ‹type_identifier› on ‹identifier› is ‹identifier› ⦆ ; ⦆* }` | `item.singleton` | `theory_declaration` * | Keyword, Type, Other, VariableParam, Operator, Constructor, FunctionDef, VariableDef, FunctionCall, Number, Member |
| [`circuit_declaration`](exemplars/syntax/circuit_declaration.gandr) | `⦅ oper ‖ rule ⦆ ‹identifier› : ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆? ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆?` | `item.singleton` | `circuit_declaration` * | Keyword, FunctionDef, Other, VariableParam, Operator, VariableDef, FunctionCall |

## `pattern` — 14 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| [`wildcard`](exemplars/syntax/wildcard.gandr) | `_` | `pattern.atom` | `wildcard` | Variable |
| [`constructor_pattern`](exemplars/syntax/constructor_pattern.gandr) | `‹constructor› ⦅ ( PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦆? ) ⦆?` | `pattern.atom` | `constructor_pattern` | Constructor, Other |
| [`tuple_pattern`](exemplars/syntax/tuple_pattern.gandr) | `( PATTERN , PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦆? )` | `pattern.atom` | `tuple_pattern` | Other |
| [`telescope_pattern`](exemplars/syntax/telescope_pattern.gandr) | `#{ ⦅ ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ = PATTERN ⦆? ‖ PATTERN ⦅ = PATTERN ⦆? ⦆ ⦅ , ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ = PATTERN ⦆? ‖ PATTERN ⦅ = PATTERN ⦆? ⦆ ⦆* ⦅ , ⦆? ⦆? }` | `pattern.atom` | `telescope_pattern` * | Other, Member, Number |
| [`labelled_sum_pattern`](exemplars/syntax/labelled_sum_pattern.gandr) | `+ { . ⦅ ‹identifier› ‖ ‹number› ⦆ = PATTERN }` | `pattern.atom` | `labelled_sum_pattern` * | Operator, Other, Member, Number |
| [`list_pattern`](exemplars/syntax/list_pattern.gandr) | `[ ⦅ PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦅ ⟨rest_pattern⟩ ⦆? ⦆? ‖ ⟨rest_pattern⟩ ⦆? ]` | `pattern.atom` | `list_pattern` | Other, Operator |
| [`rest_pattern`](exemplars/syntax/rest_pattern.gandr) | `.. PATTERN` | `pattern.atom` | `rest_pattern` | Operator |
| [`literal_pattern`](exemplars/syntax/literal_pattern.gandr) | `‹number› ‖ ‹typed_number› ‖ " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ‖ true ‖ false` | `pattern.atom` | `literal_pattern` | Number, StringLit, Escape, Boolean |
| [`hole.pattern`](exemplars/syntax/hole.pattern.gandr) | `? ⦅ ‹hole_name› ⦆?` | `pattern.atom` | `hole` | Hole, Label |
| [`cons_pattern`](exemplars/syntax/cons_pattern.gandr) | `‹identifier› ⦅ ( ‹identifier› ) ⦆? ∷ PATTERN` or `‹identifier› ⦅ ( ‹identifier› ) ⦆? :: PATTERN` | `pattern.cons` | `cons_pattern` * | Variable, Other, Operator |
| [`or_pattern`](exemplars/syntax/or_pattern.gandr) | `PATTERN \| PATTERN` | `pattern.or` | `or_pattern` | Operator |
| [`as_pattern`](exemplars/syntax/as_pattern.gandr) | `PATTERN as ‹identifier›` | `pattern.as` | `as_pattern` | Keyword, VariableDef |
| [`identifier.pattern`](exemplars/syntax/identifier.pattern.gandr) | `‹identifier›` | `pattern.atom` | `identifier` | Variable |
| [`unit.pattern`](exemplars/syntax/unit.pattern.gandr) | `unit` | `pattern.atom` | `unit` | Keyword |

## `expression` — 79 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| [`pure_expression`](exemplars/syntax/pure_expression.gandr) | `pure EXPRESSION` | `expression.pure` | `pure_expression` | Keyword |
| [`return_expression`](exemplars/syntax/return_expression.gandr) | `return EXPRESSION` | `expression.pure` | `return_expression` * | Keyword |
| [`become_expression`](exemplars/syntax/become_expression.gandr) | `become EXPRESSION` | `expression.pure` | `become_expression` * | Keyword |
| [`binary_expression.or`](exemplars/syntax/binary_expression.or.gandr) | `EXPRESSION \|\| EXPRESSION` | `expression.or` | `binary_expression` | Operator |
| [`binary_expression.and`](exemplars/syntax/binary_expression.and.gandr) | `EXPRESSION && EXPRESSION` | `expression.and` | `binary_expression` | Operator |
| [`binary_expression.cmp.eq`](exemplars/syntax/binary_expression.cmp.eq.gandr) | `EXPRESSION == EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| [`binary_expression.cmp.ne`](exemplars/syntax/binary_expression.cmp.ne.gandr) | `EXPRESSION != EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| [`binary_expression.cmp.lt`](exemplars/syntax/binary_expression.cmp.lt.gandr) | `EXPRESSION < EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| [`binary_expression.cmp.le`](exemplars/syntax/binary_expression.cmp.le.gandr) | `EXPRESSION <= EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| [`binary_expression.cmp.gt`](exemplars/syntax/binary_expression.cmp.gt.gandr) | `EXPRESSION > EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| [`binary_expression.cmp.ge`](exemplars/syntax/binary_expression.cmp.ge.gandr) | `EXPRESSION >= EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| [`binary_expression.then`](exemplars/syntax/binary_expression.then.gandr) | `EXPRESSION then EXPRESSION` | `expression.cmp` | `binary_expression` | Keyword |
| [`binary_expression.cons`](exemplars/syntax/binary_expression.cons.gandr) | `EXPRESSION ∷ EXPRESSION` or `EXPRESSION :: EXPRESSION` | `expression.cons` | `binary_expression` | Operator |
| [`binary_expression.add.concat`](exemplars/syntax/binary_expression.add.concat.gandr) | `EXPRESSION ++ EXPRESSION` | `expression.add` | `binary_expression` | Operator |
| [`binary_expression.add.plus`](exemplars/syntax/binary_expression.add.plus.gandr) | `EXPRESSION + EXPRESSION` | `expression.add` | `binary_expression` | Operator |
| [`binary_expression.add.minus`](exemplars/syntax/binary_expression.add.minus.gandr) | `EXPRESSION - EXPRESSION` | `expression.add` | `binary_expression` | Operator |
| [`binary_expression.mul.times`](exemplars/syntax/binary_expression.mul.times.gandr) | `EXPRESSION * EXPRESSION` | `expression.mul` | `binary_expression` | Operator |
| [`unary_expression`](exemplars/syntax/unary_expression.gandr) | `- EXPRESSION` | `expression.unary` | `unary_expression` | Operator |
| [`force_expression`](exemplars/syntax/force_expression.gandr) | `force EXPRESSION` | `expression.unary` | `force_expression` | Keyword |
| [`run_expression`](exemplars/syntax/run_expression.gandr) | `run EXPRESSION` | `expression.unary` | `run_expression` * | Keyword |
| [`hold_expression`](exemplars/syntax/hold_expression.gandr) | `hold EXPRESSION` | `expression.unary` | `hold_expression` | Keyword |
| [`pack_expression`](exemplars/syntax/pack_expression.gandr) | `pack [ TYPE ⦅ , TYPE ⦆* ⦅ , ⦆? ] EXPRESSION` | `expression.pure` | `pack_expression` * | Keyword, Other |
| [`call_expression`](exemplars/syntax/call_expression.gandr) | `EXPRESSION ( ⦅ EXPRESSION ⦅ , EXPRESSION ⦆* ⦅ , ⦆? ⦆? )` | `expression.postfix` | `call_expression` | Other |
| [`instantiation_expression`](exemplars/syntax/instantiation_expression.gandr) | `EXPRESSION [ INSTANTIATION ⦅ , INSTANTIATION ⦆* ⦅ , ⦆? ]` | `expression.postfix` | `instantiation_expression` | Other |
| [`projection_expression`](exemplars/syntax/projection_expression.gandr) | `EXPRESSION . ⦅ ‹identifier› ‖ ‹constructor› ‖ ‹number› ⦆` | `expression.postfix` | `projection_expression` | Other, Member, Constructor, Number |
| [`hole`](exemplars/syntax/hole.gandr) | `? ⦅ ‹hole_name› ⦆?` | `expression.atom` | `hole` | Hole, Label |
| [`parenthesized_expression`](exemplars/syntax/parenthesized_expression.gandr) | `( ⦅ ) ‖ EXPRESSION ⦅ ) ‖ , ⦅ EXPRESSION ⦅ , EXPRESSION ⦅ , EXPRESSION ⦆* ⦆? ⦅ , ⦆? ⦆? ) ‖ : TYPE ) ⦆ ⦆` | `expression.atom` | `parenthesized_expression` | Other |
| [`type_quote_expression`](exemplars/syntax/type_quote_expression.gandr) | `type( TYPE )` | `expression.atom` | `type_quote_expression` * | Keyword, Other |
| [`list_expression`](exemplars/syntax/list_expression.gandr) | `[ ⦅ EXPRESSION ⦅ , EXPRESSION ⦆* ⦅ , ⦆? ⦆? ]` | `expression.atom` | `list_expression` | Other |
| [`block`](exemplars/syntax/block.gandr) | `{ ⦅ val PATTERN = EXPRESSION ; ‖ run PATTERN ⦅ : TYPE ⦆? <- EXPRESSION ; ‖ unpack ‹identifier› : TYPE = EXPRESSION ; ‖ leta ‹identifier› = EXPRESSION ; ‖ hold ⦅ [ ‹number› ] ⦆? ‹identifier› = EXPRESSION ; ‖ recv ( EXPRESSION ) as ‹identifier› ; ‖ acquire ( EXPRESSION ) as ‹identifier› ; ‖ release ( EXPRESSION ) as ‹identifier› ; ‖ fork ( ‹identifier› : TYPE ) EXPRESSION as ‹identifier› ; ‖ fork ! ( ‹identifier› : TYPE ) EXPRESSION ; ‖ EXPRESSION ; ⦆* ⦅ EXPRESSION ⦆? }` | `expression.atom` | `block` | Other, Keyword, Operator, VariableDef, Number, VariableParam |
| [`lambda_expression`](exemplars/syntax/lambda_expression.gandr) | `fn ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⟨block⟩ ‖ [ ‹type_variable› ⦅ , ‹type_variable› ⦆* ⦅ , ⦆? ] ⟨block⟩ ⦆` | `expression.atom` | `lambda_expression` | Keyword, Other, VariableParam, TypeVariable, Type, Operator, VariableDef, Number |
| [`thunk_expression`](exemplars/syntax/thunk_expression.gandr) | `thunk ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? ⟨block⟩` or `thunk ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ inf ⦆ ] ⦆? ⟨block⟩` | `expression.atom` | `thunk_expression` | Keyword, Other, Number, Operator, VariableDef, VariableParam |
| [`case_expression`](exemplars/syntax/case_expression.gandr) | `case EXPRESSION ⦅ with EXPRESSION ⦆? ⦅ -> TYPE ⦆? ⦅ { } ‖ ⦅ { PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ‖ { \| PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ⦆ ⦆` | `expression.atom` | `case_expression` | Keyword, Operator, Other |
| [`handle_expression`](exemplars/syntax/handle_expression.gandr) | `handle ‹identifier› : ‹type_identifier› ⟨block⟩ with { ⦅ pure ( ‹identifier› ) => EXPRESSION ‖ oper ‹identifier› ( ‹identifier› , ‹identifier› ) => EXPRESSION ⦆ ⦅ , ⦅ pure ( ‹identifier› ) => EXPRESSION ‖ oper ‹identifier› ( ‹identifier› , ‹identifier› ) => EXPRESSION ⦆ ⦆* ⦅ , ⦆? }` | `expression.atom` | `handle_expression` * | Keyword, VariableDef, Other, Type, Operator, Number, VariableParam, FunctionDef |
| [`if_expression`](exemplars/syntax/if_expression.gandr) | `if EXPRESSION ⦅ -> TYPE ⦆? ⟨block⟩ else ⦅ ⟨block⟩ ‖ if EXPRESSION ⦅ -> TYPE ⦆? ⟨block⟩ else ⟨block⟩ ⦆` | `expression.atom` | `if_expression` | Keyword, Operator, Other, VariableDef, Number, VariableParam |
| [`for_expression`](exemplars/syntax/for_expression.gandr) | `for ‹identifier› in EXPRESSION ⟨block⟩` | `expression.atom` | `for_expression` * | Keyword, VariableDef, Other, Operator, Number, VariableParam |
| [`while_expression`](exemplars/syntax/while_expression.gandr) | `while EXPRESSION ⟨block⟩` | `expression.atom` | `while_expression` * | Keyword, Other, Operator, VariableDef, Number, VariableParam |
| [`loop_expression`](exemplars/syntax/loop_expression.gandr) | `loop ⟨block⟩` | `expression.atom` | `loop_expression` * | Keyword, Other, Operator, VariableDef, Number, VariableParam |
| [`break_expression`](exemplars/syntax/break_expression.gandr) | `break` | `expression.atom` | `break_expression` * | Keyword |
| [`break_value_expression`](exemplars/syntax/break_value_expression.gandr) | `break ( EXPRESSION )` | `expression.atom` | `break_value_expression` * | Keyword, Other |
| [`continue_expression`](exemplars/syntax/continue_expression.gandr) | `continue` | `expression.atom` | `continue_expression` * | Keyword |
| [`co_expression`](exemplars/syntax/co_expression.gandr) | `co { ⟨instantiation.explicit⟩ ⦅ , ⟨instantiation.explicit⟩ ⦆* ⦅ , ⦆? }` | `expression.atom` | `co_expression` | Keyword, Other, Member |
| [`glob_expression`](exemplars/syntax/glob_expression.gandr) | `glob { ⦅ ⟨instantiation.explicit⟩ ; ⦆* }` | `expression.atom` | `glob_expression` * | Keyword, Other, Member |
| [`telescope_expression`](exemplars/syntax/telescope_expression.gandr) | `#{ . ⦅ ‹identifier› ‖ ‹number› ⦆ = EXPRESSION ⦅ , . ⦅ ‹identifier› ‖ ‹number› ⦆ = EXPRESSION ⦆* ⦅ , ⦆? } ‖ #{ ⦅ } ‖ EXPRESSION ⦅ = EXPRESSION ⦆? ⦅ \| ⟨instantiation.explicit⟩ ⦅ , ⟨instantiation.explicit⟩ ⦆* ⦅ , ⦆? } ‖ ⦅ , EXPRESSION ⦅ = EXPRESSION ⦆? ⦆* ⦅ , ⦆? } ⦆ ⦆` | `expression.atom` | `telescope_expression` * | Other, Member, Number, Operator |
| [`labelled_sum_expression`](exemplars/syntax/labelled_sum_expression.gandr) | `+ { . ⦅ ‹identifier› ‖ ‹number› ⦆ = EXPRESSION }` | `expression.atom` | `labelled_sum_expression` * | Operator, Other, Member, Number |
| [`lazy_record_expression`](exemplars/syntax/lazy_record_expression.gandr) | `& { ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ => EXPRESSION ⦅ , . ⦅ ‹identifier› ‖ ‹number› ⦆ => EXPRESSION ⦆* ⦅ , ⦆? ⦆? }` | `expression.atom` | `lazy_record_expression` * | Operator, Other, Member, Number |
| [`offer_expression`](exemplars/syntax/offer_expression.gandr) | `offer ( EXPRESSION ) ⦅ { PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ‖ { \| PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ⦆` | `expression.atom` | `offer_expression` | Keyword, Other, Operator |
| [`migrate_expression`](exemplars/syntax/migrate_expression.gandr) | `migrate [ ‹identifier› ] ⟨block⟩` | `expression.atom` | `migrate_expression` | Keyword, Other, Label, Operator, VariableDef, Number, VariableParam |
| [`send_expression`](exemplars/syntax/send_expression.gandr) | `send ( EXPRESSION , EXPRESSION )` | `expression.atom` | `send_expression` | Keyword, Other |
| [`close_expression`](exemplars/syntax/close_expression.gandr) | `close ( EXPRESSION )` | `expression.atom` | `close_expression` | Keyword, Other |
| [`select_expression`](exemplars/syntax/select_expression.gandr) | `select ( EXPRESSION , ‹identifier› )` | `expression.atom` | `select_expression` | Keyword, Other, Label |
| [`dup_expression`](exemplars/syntax/dup_expression.gandr) | `dup ( EXPRESSION )` | `expression.atom` | `dup_expression` | Keyword, Other |
| [`drop_expression`](exemplars/syntax/drop_expression.gandr) | `drop ( EXPRESSION )` | `expression.atom` | `drop_expression` | Keyword, Other |
| [`access_expression`](exemplars/syntax/access_expression.gandr) | `access ⦅ shared ‖ exclusive ⦆? ‹identifier› ⦅ [ EXPRESSION ] ⦆? as ‹identifier› ⟨block⟩ ⦅ unwind ⟨block⟩ ⦆?` | `expression.atom` | `access_expression` * | Keyword, Other, Variable, VariableDef, Operator, Number, VariableParam |
| [`resume_expression`](exemplars/syntax/resume_expression.gandr) | `resume ( ‹identifier› , EXPRESSION )` | `expression.atom` | `resume_expression` * | Keyword, Other, Variable |
| [`abort_expression`](exemplars/syntax/abort_expression.gandr) | `abort ( ‹identifier› )` | `expression.atom` | `abort_expression` * | Keyword, Other, Variable |
| [`shell_block`](exemplars/syntax/shell_block.gandr) | `#!{ ⦅ EXPRESSION ⦆? }` | `expression.atom` | `shell_block` | Other |
| [`identifier.expression`](exemplars/syntax/identifier.expression.gandr) | `‹identifier›` | `expression.atom` | `identifier` | Variable |
| [`constructor.expression`](exemplars/syntax/constructor.expression.gandr) | `‹constructor›` | `expression.atom` | `constructor` | Constructor |
| [`boolean.expression`](exemplars/syntax/boolean.expression.gandr) | `true ‖ false` | `expression.atom` | `boolean` | Boolean |
| [`unit.expression`](exemplars/syntax/unit.expression.gandr) | `unit` | `expression.atom` | `unit` | Keyword |
| [`number.expression`](exemplars/syntax/number.expression.gandr) | `‹number›` | `expression.atom` | `number` | Number |
| [`typed_number.expression`](exemplars/syntax/typed_number.expression.gandr) | `‹typed_number›` | `expression.atom` | `typed_number` | Number |
| [`character`](exemplars/syntax/character.gandr) | `‹character›` | `expression.atom` | `character` | Character |
| [`string.expression`](exemplars/syntax/string.expression.gandr) | `" ⦅ ‹escape_sequence› ‖ ‹string_fragment› ‖ ${ EXPRESSION } ⦆* "` | `expression.atom` | `string` | StringLit, Escape, Other |
| [`list_operator`](exemplars/syntax/list_operator.gandr) | `; ‖ & ‖ newline` | `expression.atom` | `list_operator` | Operator |
| [`pipeline.pipe`](exemplars/syntax/pipeline.pipe.gandr) | `EXPRESSION \| EXPRESSION` | `expression.postfix` | `pipeline` | Operator |
| [`pipeline.pipe_both`](exemplars/syntax/pipeline.pipe_both.gandr) | `EXPRESSION \|& EXPRESSION` | `expression.postfix` | `pipeline` | Operator |
| [`environment_assignment`](exemplars/syntax/environment_assignment.gandr) | `‹environment_assignment›` | `expression.atom` | `environment_assignment` | VariableParam |
| [`shell_word`](exemplars/syntax/shell_word.gandr) | `‹shell_word›` | `expression.atom` | `shell_word` | Path |
| [`single_quoted_string`](exemplars/syntax/single_quoted_string.gandr) | `' ‹single_quoted_content› '` | `expression.atom` | `single_quoted_string` | StringLit |
| [`double_quoted_string`](exemplars/syntax/double_quoted_string.gandr) | `" ⦅ ‹double_string_fragment› ‖ ‹escape_sequence› ‖ ⟨variable_expansion⟩ ⦆* "` | `expression.atom` | `double_quoted_string` | StringLit, Escape, Other, Variable |
| [`variable_expansion`](exemplars/syntax/variable_expansion.gandr) | `$ ‹variable_name› ‖ ${ ‹variable_name› }` | `expression.atom` | `variable_expansion` | Other, Variable |
| [`variable_name`](exemplars/syntax/variable_name.gandr) | `‹variable_name›` | `expression.atom` | `variable_name` | Variable |
| [`command_substitution`](exemplars/syntax/command_substitution.gandr) | `$!{ }` | `expression.atom` | `command_substitution` | Other |
| [`host_escape`](exemplars/syntax/host_escape.gandr) | `$ ( EXPRESSION )` | `expression.atom` | `host_escape` | Other |
| [`subshell`](exemplars/syntax/subshell.gandr) | `[ ⦅ EXPRESSION ⦆? ]` | `expression.atom` | `subshell` | Other |
| [`file_descriptor`](exemplars/syntax/file_descriptor.gandr) | `‹file_descriptor›` | `expression.atom` | `file_descriptor` | Number |
| [`redirection_operator`](exemplars/syntax/redirection_operator.gandr) | `<> ‖ <& ‖ >& ‖ >> ‖ < ‖ >` | `expression.atom` | `redirection_operator` | Operator |

## `type` — 37 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| [`forall_type`](exemplars/syntax/forall_type.gandr) | `forall ⦅ ‹type_variable› ⦆* . TYPE` | `type.arrow` | `forall_type` | Keyword, TypeVariable, Other |
| [`package_type`](exemplars/syntax/package_type.gandr) | `package [ ‹type_identifier› ⦅ , ‹type_identifier› ⦆* ⦅ , ⦆? ] TYPE` | `type.application` | `package_type` * | Keyword, Other, Type |
| [`function_type`](exemplars/syntax/function_type.gandr) | `TYPE -> TYPE` | `type.arrow` | `function_type` | Operator |
| [`value_function_type`](exemplars/syntax/value_function_type.gandr) | `TYPE => TYPE` | `type.arrow` | `value_function_type` * | Operator |
| [`static_abstraction`](exemplars/syntax/static_abstraction.gandr) | `\ ⦅ ‹type_identifier› ‖ ‹type_variable› ⦆ . TYPE` | `type.arrow` | `static_abstraction` * | Operator, Type, TypeVariable, Other |
| [`union_type`](exemplars/syntax/union_type.gandr) | `TYPE \| TYPE` | `type.union` | `union_type` | Operator |
| [`intersection_type`](exemplars/syntax/intersection_type.gandr) | `TYPE /\ TYPE` | `type.intersection` | `intersection_type` | Operator |
| [`lazy_product_type`](exemplars/syntax/lazy_product_type.gandr) | `TYPE & TYPE` | `type.lazy_product` | `lazy_product_type` | Operator |
| [`equivalence_type`](exemplars/syntax/equivalence_type.gandr) | `TYPE ≃ TYPE` or `TYPE <~> TYPE` | `type.equivalence` | `equivalence_type` * | Operator |
| [`isomorphism_type`](exemplars/syntax/isomorphism_type.gandr) | `TYPE ≅ TYPE` or `Iso(TYPE, TYPE)` | `type.equivalence` | `isomorphism_type` * | Operator |
| [`universe_flow_type`](exemplars/syntax/universe_flow_type.gandr) | `TYPE ⇝ TYPE` or `TYPE ~~> TYPE` | `type.equivalence` | `universe_flow_type` * | Operator |
| [`sum_type`](exemplars/syntax/sum_type.gandr) | `TYPE + TYPE` | `type.sum` | `sum_type` | Operator |
| [`product_type`](exemplars/syntax/product_type.gandr) | `TYPE * TYPE` | `type.product` | `product_type` | Operator |
| [`f_type.row`](exemplars/syntax/f_type.row.gandr) | `-F [ ‹type_identifier› ⦅ , ‹type_identifier› ⦆* ⦅ , ⦆? ] TYPE` | `type.application` | `f_type` | Keyword, Other, Type |
| [`f_type`](exemplars/syntax/f_type.gandr) | `-F TYPE` | `type.application` | `f_type` | Keyword |
| [`u_type`](exemplars/syntax/u_type.gandr) | `+U ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? TYPE` or `+U ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ inf ⦆ ] ⦆? TYPE` | `type.application` | `u_type` | Keyword, Other, Number |
| [`universe_type`](exemplars/syntax/universe_type.gandr) | `Type ⦅ [ ⦅ + ‖ - ⦆ ⦅ , ‹number› ⦆? ] ⦆?` | `type.atom` | `universe_type` * | TypeBuiltin, Other, Keyword, Number |
| [`representable_universe_type`](exemplars/syntax/representable_universe_type.gandr) | `Type+` | `type.atom` | `representable_universe_type` * | TypeBuiltin |
| [`at_type`](exemplars/syntax/at_type.gandr) | `TYPE at ‹identifier›` | `type.application` | `at_type` | Keyword, Label |
| [`path_type`](exemplars/syntax/path_type.gandr) | `Path ( ⦅ Type ⦅ [ ⦅ + ‖ - ⦆ ⦅ , ‹number› ⦆? ] ⦆? , TYPE , TYPE ‖ TYPE , EXPRESSION , EXPRESSION ⦆ )` | `type.application` | `path_type` * | TypeBuiltin, Other, Operator, Number |
| [`type_application`](exemplars/syntax/type_application.gandr) | `⦅ ‹type_identifier› ‖ ‹type_variable› ⦅ [ < ] ⦆? ⦆ ( TYPE ⦅ , TYPE ⦆* ⦅ , ⦆? )` | `type.application` | `type_application` | Type, TypeVariable, Other, Operator |
| [`type_path`](exemplars/syntax/type_path.gandr) | `TYPE . ‹type_identifier›` | `type.path` | `type_path` * | Other, Type |
| [`staged_type`](exemplars/syntax/staged_type.gandr) | `TYPE [ ⦅ < ⦆? ‹identifier› ]` | `type.path` | `staged_type` * | Other, Operator, VariableParam |
| [`parenthesized_type`](exemplars/syntax/parenthesized_type.gandr) | `( TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? )` | `type.atom` | `parenthesized_type` | Other |
| [`telescope_type`](exemplars/syntax/telescope_type.gandr) | `#{ ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `telescope_type` * | Other |
| [`send_session_type`](exemplars/syntax/send_session_type.gandr) | `! TYPE . TYPE` | `type.arrow` | `send_session_type` | Operator, Other |
| [`receive_session_type`](exemplars/syntax/receive_session_type.gandr) | `? TYPE . TYPE` | `type.arrow` | `receive_session_type` | Operator, Other |
| [`end_session_type`](exemplars/syntax/end_session_type.gandr) | `end` | `type.atom` | `end_session_type` | Keyword |
| [`labelled_sum_type`](exemplars/syntax/labelled_sum_type.gandr) | `+ { ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `labelled_sum_type` * | Operator, Other |
| [`lazy_record_type`](exemplars/syntax/lazy_record_type.gandr) | `& { ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `lazy_record_type` * | Operator, Other |
| [`mu_session_type`](exemplars/syntax/mu_session_type.gandr) | `mu ‹type_variable› . TYPE` | `type.arrow` | `mu_session_type` | Keyword, TypeVariable, Other |
| [`primitive_type`](exemplars/syntax/primitive_type.gandr) | `Any ‖ Unknown ‖ Never ‖ Boolean ‖ Integer ‖ u32 ‖ u64 ‖ i32 ‖ i64 ‖ f32 ‖ f64 ‖ Char ‖ String ‖ Symbol ‖ Unit ‖ Void` | `type.atom` | `primitive_type` | TypeBuiltin |
| [`unknown_type`](exemplars/syntax/unknown_type.gandr) | `?` | `type.atom` | `unknown_type` * | TypeBuiltin |
| [`type_identifier`](exemplars/syntax/type_identifier.gandr) | `‹type_identifier›` | `type.atom` | `type_identifier` | Type |
| [`type_variable`](exemplars/syntax/type_variable.gandr) | `‹type_variable›` | `type.atom` | `type_variable` | TypeVariable |
| [`capability_type`](exemplars/syntax/capability_type.gandr) | `Cap ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? { ‹identifier› ⦅ , ‹identifier› ⦆* ⦅ , ⦆? }` or `Cap ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ inf ⦆ ] ⦆? { ‹identifier› ⦅ , ‹identifier› ⦆* ⦅ , ⦆? }` | `type.atom` | `capability_type` * | TypeBuiltin, Other, Number, Member |
| [`number.type`](exemplars/syntax/number.type.gandr) | `‹number›` | `type.atom` | `number` | Number |

## `instantiation` — 5 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| [`instantiation.direction.descent`](exemplars/syntax/instantiation.direction.descent.gandr) | `<` | `expression.atom` | `instantiation_expression` | Operator |
| [`instantiation.direction.productivity`](exemplars/syntax/instantiation.direction.productivity.gandr) | `>` | `expression.atom` | `instantiation_expression` | Operator |
| [`instantiation.named_measure`](exemplars/syntax/instantiation.named_measure.gandr) | `‹identifier› <` | `expression.atom` | `instantiation_expression` | VariableParam, Operator |
| [`instantiation.explicit`](exemplars/syntax/instantiation.explicit.gandr) | `‹identifier› = EXPRESSION` | `expression.pure` | `instantiation_expression` | VariableParam, Other |
| [`instantiation.tail`](exemplars/syntax/instantiation.tail.gandr) | `tail` | `expression.atom` | `instantiation_expression` | Keyword |

## `module_member` — 4 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| [`module_definition_member`](exemplars/syntax/module_definition_member.gandr) | `def ‹identifier› ⦅ @[ ⦅ ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ‖ ‹identifier› < ‹identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? ] ⦆? ⦅ : TYPE ; ‖ = EXPRESSION ; ‖ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ⟨block⟩ ⦆` | `item.singleton` | `module_declaration` | Keyword, FunctionDef, Other, VariableParam, TypeVariable, Type, Operator, VariableDef, Number |
| [`attributed_module_member`](exemplars/syntax/attributed_module_member.gandr) | `⟨attribute_block⟩ ⦅ ⟨attribute_block⟩ ⦆* ⦅ ⟨module_definition_member⟩ ‖ ⟨module_type_member⟩ ⦆` | `item.singleton` | `module_declaration` | Other, Keyword, FunctionDef, VariableParam, TypeVariable, Type, Operator, VariableDef, Number |
| [`module_type_member`](exemplars/syntax/module_type_member.gandr) | `type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? = TYPE ;` | `item.singleton` | `module_declaration` | Keyword, Type, Other, TypeVariable |
| [`nested_module_member`](exemplars/syntax/nested_module_member.gandr) | `module ⦅ ‹identifier› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ‖ :> ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦅ with sort ‹type_identifier› = TYPE ⦆* ⦆ ⦆? { ⦅ MODULE_MEMBER ⦆* }` | `item.singleton` | `module_declaration` | Keyword, VariableDef, Type, Other, Member, TypeVariable, Operator |

## Internal — 1 rule

A rule no source can mold, with the reason and what the reason is read from: the grammar's forms, the labeler over a tile's own text, or a parser probe. These rules have no exemplar.

| Rule | Sort | Form | Reason | Read from |
| ---- | ---- | ---- | ------ | --------- |
| `instantiation.type` | instantiation | `TYPE` | the form holds no tile, so no tree names the rule | grammar |

## Attributes — 11 attributes

Every attribute the lowering's registry admits in an `@[ … ]` block, with the payload its schema takes, linking its exemplar, which the exemplar gate lowers and checks the attribute is filed.

| Attribute | Payload |
| --------- | ------- |
| [`checks`](exemplars/attributes/checks.gandr) | no payload |
| [`owes`](exemplars/attributes/owes.gandr) | an integer payload |
| [`refuses`](exemplars/attributes/refuses.gandr) | a text payload |
| [`runs`](exemplars/attributes/runs.gandr) | a text payload |
| [`normalizes`](exemplars/attributes/normalizes.gandr) | a text payload |
| [`doc`](exemplars/attributes/doc.gandr) | a text payload |
| [`explicit_exits`](exemplars/attributes/explicit_exits.gandr) | no payload |
| [`explicit_runs`](exemplars/attributes/explicit_runs.gandr) | no payload or the text "effects" |
| [`respects`](exemplars/attributes/respects.gandr) | a declared name or a tuple of declared names |
| [`entry`](exemplars/attributes/entry.gandr) | a declared name or a tuple of declared names |
| [`form`](exemplars/attributes/form.gandr) | one of the words `explicit`, `sugared` |
