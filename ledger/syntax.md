# Syntax ledger

Generated from the built-in grammar by `gandr ledger syntax --write ledger`; never edited by hand. `mise run check:syntax-ledger` regenerates it and fails while this file differs. `syntax.json` holds the same rows for machines, each form as a tree with every tile's mold.

- Grammar fingerprint: `0x53f68bb00a999c4b`
- Rules: 174 — 173 committed, 1 internal
- Molds: 2999
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

The group is the rule's precedence group. The kind is the named node kind the rule realises; `*` marks a kind the surface's tree-sitter grammar does not have. The roles are the highlight roles of the rule's tiles, each once, first use first.

## `item` — 25 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| `def_value` | `def ⦅ rec ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? { ⦅ ⦅ . ‹identifier› => EXPRESSION ‖ _ => EXPRESSION ⦆ ⦅ , ⦅ . ‹identifier› => EXPRESSION ‖ _ => EXPRESSION ⦆ ⦆* ⦅ , ⦆? ‖ ⦅ ⟨val_statement⟩ ‖ ⟨bind_statement⟩ ‖ ⟨unpack_statement⟩ ‖ ⟨leta_statement⟩ ‖ ⟨hold_statement⟩ ‖ ⟨recv_statement⟩ ‖ ⟨acquire_statement⟩ ‖ ⟨release_statement⟩ ‖ fork ( ‹identifier› : TYPE ) EXPRESSION as ‹identifier› ; ‖ fork ! ( ‹identifier› : TYPE ) EXPRESSION ; ‖ ⟨expression_statement⟩ ⦆* ⦅ EXPRESSION ⦆? ⦆ } ‖ ‹identifier› ⦅ @[ ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ⦆* ⦅ , ⦆? ⦆? ] ⦆? ⦅ : TYPE ; ‖ = EXPRESSION ; ‖ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ⟨block⟩ ⦆ ⦆` | `item.singleton` | `def_value` | Keyword, FunctionDef, Other, VariableParam, TypeVariable, Type, Operator, Member, Variable, VariableDef |
| `data_declaration` | `data ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : TYPE ⦆? { ⦅ ⦅ ‹constructor› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> TYPE ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ‖ ⦅ ( ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦅ : TYPE ⦆? ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ⦆ ‖ ⦅ oper ‖ op ⦆ ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ‖ ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦅ ⦅ ; ‖ , ⦆ ⦅ ‹constructor› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦆ ⦅ --> TYPE ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ‖ ⦅ ( ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦅ : TYPE ⦆? ⦆? ⦅ [ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ] ⦆? ⦆ ‖ ⦅ oper ‖ op ⦆ ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ‖ ‹identifier› : EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦆* ⦅ ; ‖ , ⦆? ⦆? }` | `item.singleton` | `data_declaration` * | Keyword, Type, Other, TypeVariable, Constructor, Number, VariableParam, Operator, FunctionDef, Member |
| `codata_declaration` | `codata ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ : TYPE ⦆? { ⦅ ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› ⦅ ( ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆? : TYPE ‖ oper ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦅ ⦅ ; ‖ , ⦆ ⦅ ⦅ ‹number› ‖ ω ⦆? ‹identifier› ⦅ ( ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦅ , ⦅ ‹number› ‖ ω ⦆? ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆? : TYPE ‖ oper ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> ⦅ TYPE ‖ ( ‹identifier› : TYPE ⦅ , ‹identifier› : TYPE ⦆* ⦅ , ⦆? ) ⦆ ⦆? ‖ rule EXPRESSION ⦅ ==> ‖ <=> ‖ ~> ⦆ EXPRESSION ⦆ ⦆* ⦅ ; ‖ , ⦆? ⦆? }` | `item.singleton` | `codata_declaration` * | Keyword, Type, Other, TypeVariable, Number, Member, VariableParam, FunctionDef, Operator |
| `module_declaration` | `module ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦅ = ‹type_identifier› ( ‹type_identifier› ⦅ . ⦅ ‹type_identifier› ‖ ‹identifier› ⦆ ⦆* ) ; ‖ ⦅ ( ‹type_identifier› : #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ) ⦆? ⦅ : ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦆ ‖ :> ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦆ ⦆? { ⦅ MODULE_MEMBER ⦆* } ⦆` | `item.singleton` | `module_declaration` | Keyword, Type, VariableDef, Other, Member, TypeVariable, Operator |
| `import_declaration` | `import ⟨string.pattern⟩ ⦅ as ‹identifier› ⦆? ;` | `item.singleton` | `import_declaration` * | Keyword, StringLit, Escape, VariableDef, Other |
| `world_declaration` | `world ‹identifier› ;` | `item.singleton` | `world_declaration` * | Keyword, Label, Other |
| `operator_declaration` | `op ⦅ infixl ‖ infixr ‖ infix ‖ prefix ‖ postfix ⦆ ‹number› ⟨string.pattern⟩ ;` | `item.singleton` | `operator_declaration` * | Keyword, Number, StringLit, Escape, Other |
| `rec_block` | `rec { ⦅ ITEM ⦆* }` | `item.singleton` | `rec_block` * | Keyword, Other |
| `attribute_block` | `@[ ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦅ , ‹identifier› ⦅ ( EXPRESSION ) ⦆? ⦆* ⦅ , ⦆? ]` | `item.singleton` | `attribute_block` | Other |
| `extern_block` | `extern ⟨string.pattern⟩ from ⟨string.pattern⟩ ⦅ as ‹identifier› ⦆? { ⦅ type ‹type_identifier› ; ‖ def ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ; ⦆* }` | `item.singleton` | `extern_block` | Keyword, StringLit, Escape, VariableDef, Other, Type, FunctionDef, VariableParam, TypeVariable, Operator |
| `val_statement` | `val PATTERN = EXPRESSION ;` | `item.singleton` | `val_statement` | Keyword, Other |
| `bind_statement` | `run PATTERN ⦅ : TYPE ⦆? <- EXPRESSION ;` | `item.singleton` | `bind_statement` | Keyword, Other, Operator |
| `unpack_statement` | `unpack ‹identifier› : TYPE = EXPRESSION ;` | `item.singleton` | `unpack_statement` * | Keyword, VariableDef, Other |
| `leta_statement` | `leta ‹identifier› = EXPRESSION ;` | `item.singleton` | `leta_statement` | Keyword, VariableDef, Other |
| `hold_statement` | `hold ‹identifier› = EXPRESSION ;` | `item.singleton` | `hold_statement` * | Keyword, VariableDef, Other |
| `recv_statement` | `recv ( EXPRESSION ) as ‹identifier› ;` | `item.singleton` | `recv_statement` | Keyword, Other, VariableDef |
| `acquire_statement` | `acquire ( EXPRESSION ) as ‹identifier› ;` | `item.singleton` | `acquire_statement` | Keyword, Other, VariableDef |
| `release_statement` | `release ( EXPRESSION ) as ‹identifier› ;` | `item.singleton` | `release_statement` | Keyword, Other, VariableDef |
| `fork_statement` | `fork ( ‹identifier› : TYPE ) ⟨block⟩ as ‹identifier› ;` | `item.singleton` | `fork_statement` | Keyword, Other, VariableParam, Operator, VariableDef |
| `fork_shared_statement` | `fork ! ( ‹identifier› : TYPE ) ⟨block⟩ ;` | `item.singleton` | `fork_shared_statement` | Keyword, Other, VariableParam, Operator, VariableDef |
| `expression_statement` | `EXPRESSION ;` | `item.singleton` | `expression_statement` | Other |
| `line_comment` | `line_comment` | `item.singleton` | `line_comment` | Comment |
| `shebang` | `shebang` | `item.singleton` | `shebang` | Directive |
| `theory_declaration` | `theory ‹type_identifier› { ⦅ ⦅ sort ‹type_identifier› ⦅ ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆? : TYPE ‖ data ‹constructor› : ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦆? ‖ ⦅ oper ‹identifier› ⦅ : ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ⦅ TYPE ‖ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆ ⦆? ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆? ‖ ( ⦅ ‹identifier› ⦅ : TYPE ⦆? ⦅ , ‹identifier› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ⦆ ‖ rule ‹identifier› ⦅ : ⦅ ( ⦅ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ‖ ‹identifier› : TYPE ⦆ ⦅ , ⦅ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ‖ ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ‖ EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆? ‖ EXPRESSION ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ EXPRESSION ⦆ ⦆ ‖ shape ‹type_identifier› : ‹number› { ⦅ ‹identifier› = { ⦅ ‹number› ⦅ , ‹number› ⦆* ⦆? } ; ⦆* } ⦆ ; ⦆* }` | `item.singleton` | `theory_declaration` * | Keyword, Type, Other, VariableParam, Operator, Constructor, FunctionDef, VariableDef, FunctionCall, Number, Member |
| `circuit_declaration` | `⦅ oper ‖ rule ⦆ ‹identifier› : ( ⦅ ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦅ , ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : ⦅ pi+ ( ‹identifier› : TYPE ) . ⦆* TYPE ‖ TYPE ⦆ ‖ rule ‹identifier› : TYPE ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ TYPE ‖ data ‹identifier› : TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦅ , ⦅ ⦅ ‹identifier› ‖ _ ⦆ : TYPE ‖ TYPE ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦆? ⦅ { ⦅ node ⦅ ‹identifier› ⦆? : ‹identifier› ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ‖ feed ⦅ ‹identifier› ⦆? : ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ⦅ --> ‖ <-> ‖ ==> ‖ <=> ⦆ ( ⦅ ⦅ ‹identifier› ‖ _ ⦆ ⦅ , ⦅ ‹identifier› ‖ _ ⦆ ⦆* ⦅ , ⦆? ⦆? ) ; ⦆* } ⦆?` | `item.singleton` | `circuit_declaration` * | Keyword, FunctionDef, Other, VariableParam, Operator, VariableDef, FunctionCall |

## `pattern` — 19 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| `wildcard` | `_` | `pattern.atom` | `wildcard` | Variable |
| `constructor_pattern` | `‹constructor› ⦅ ( PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦆? ) ⦆?` | `pattern.atom` | `constructor_pattern` | Constructor, Other |
| `tuple_pattern` | `( PATTERN , PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦆? )` | `pattern.atom` | `tuple_pattern` | Other |
| `telescope_pattern` | `#{ ⦅ ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ = PATTERN ⦆? ‖ PATTERN ⦅ = PATTERN ⦆? ⦆ ⦅ , ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ ⦅ = PATTERN ⦆? ‖ PATTERN ⦅ = PATTERN ⦆? ⦆ ⦆* ⦅ , ⦆? ⦆? }` | `pattern.atom` | `telescope_pattern` * | Other, Member, Number |
| `labelled_sum_pattern` | `+ { . ⦅ ‹identifier› ‖ ‹number› ⦆ = PATTERN }` | `pattern.atom` | `labelled_sum_pattern` * | Operator, Other, Member, Number |
| `list_pattern` | `[ ⦅ PATTERN ⦅ , PATTERN ⦆* ⦅ , ⦅ ⟨rest_pattern⟩ ⦆? ⦆? ‖ ⟨rest_pattern⟩ ⦆? ]` | `pattern.atom` | `list_pattern` | Other, Operator |
| `rest_pattern` | `.. PATTERN` | `pattern.atom` | `rest_pattern` | Operator |
| `literal_pattern` | `‹number› ‖ ‹typed_number› ‖ " ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* " ‖ true ‖ false` | `pattern.atom` | `literal_pattern` | Number, StringLit, Escape, Boolean |
| `hole.pattern` | `? ⦅ ‹hole_name› ⦆?` | `pattern.atom` | `hole` | Hole, Label |
| `cons_pattern` | `‹identifier› ⦅ ( ‹identifier› ) ⦆? ∷ PATTERN` | `pattern.cons` | `cons_pattern` * | Variable, Other, Operator |
| `or_pattern` | `PATTERN \| PATTERN` | `pattern.or` | `or_pattern` | Operator |
| `as_pattern` | `PATTERN as ‹identifier›` | `pattern.as` | `as_pattern` | Keyword, VariableDef |
| `identifier.pattern` | `‹identifier›` | `pattern.atom` | `identifier` | Variable |
| `constructor.pattern` | `‹constructor›` | `pattern.atom` | `constructor` | Constructor |
| `boolean.pattern` | `true ‖ false` | `pattern.atom` | `boolean` | Boolean |
| `unit.pattern` | `unit` | `pattern.atom` | `unit` | Keyword |
| `number.pattern` | `‹number›` | `pattern.atom` | `number` | Number |
| `typed_number.pattern` | `‹typed_number›` | `pattern.atom` | `typed_number` | Number |
| `string.pattern` | `" ⦅ ‹escape_sequence› ‖ ‹string_fragment› ⦆* "` | `pattern.atom` | `string` | StringLit, Escape |

## `expression` — 83 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| `pure_expression` | `pure EXPRESSION` | `expression.pure` | `pure_expression` | Keyword |
| `return_expression` | `return EXPRESSION` | `expression.pure` | `return_expression` * | Keyword |
| `become_expression` | `become EXPRESSION` | `expression.pure` | `become_expression` * | Keyword |
| `binary_expression.or` | `EXPRESSION \|\| EXPRESSION` | `expression.or` | `binary_expression` | Operator |
| `binary_expression.and` | `EXPRESSION && EXPRESSION` | `expression.and` | `binary_expression` | Operator |
| `binary_expression.cmp.eq` | `EXPRESSION == EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| `binary_expression.cmp.ne` | `EXPRESSION != EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| `binary_expression.cmp.lt` | `EXPRESSION < EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| `binary_expression.cmp.le` | `EXPRESSION <= EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| `binary_expression.cmp.gt` | `EXPRESSION > EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| `binary_expression.cmp.ge` | `EXPRESSION >= EXPRESSION` | `expression.cmp` | `binary_expression` | Operator |
| `binary_expression.then` | `EXPRESSION then EXPRESSION` | `expression.cmp` | `binary_expression` | Keyword |
| `binary_expression.cons` | `EXPRESSION ∷ EXPRESSION` | `expression.cons` | `binary_expression` | Operator |
| `binary_expression.add.concat` | `EXPRESSION ++ EXPRESSION` | `expression.add` | `binary_expression` | Operator |
| `binary_expression.add.plus` | `EXPRESSION + EXPRESSION` | `expression.add` | `binary_expression` | Operator |
| `binary_expression.add.minus` | `EXPRESSION - EXPRESSION` | `expression.add` | `binary_expression` | Operator |
| `binary_expression.mul.times` | `EXPRESSION * EXPRESSION` | `expression.mul` | `binary_expression` | Operator |
| `unary_expression` | `- EXPRESSION` | `expression.unary` | `unary_expression` | Operator |
| `force_expression` | `force EXPRESSION` | `expression.unary` | `force_expression` | Keyword |
| `run_expression` | `run EXPRESSION` | `expression.unary` | `run_expression` * | Keyword |
| `hold_expression` | `hold EXPRESSION` | `expression.unary` | `hold_expression` | Keyword |
| `pack_expression` | `pack [ TYPE ⦅ , TYPE ⦆* ⦅ , ⦆? ] EXPRESSION` | `expression.pure` | `pack_expression` * | Keyword, Other |
| `call_expression` | `EXPRESSION ( ⦅ EXPRESSION ⦅ , EXPRESSION ⦆* ⦅ , ⦆? ⦆? )` | `expression.postfix` | `call_expression` | Other |
| `instantiation_expression` | `EXPRESSION [ INSTANTIATION ⦅ , INSTANTIATION ⦆* ⦅ , ⦆? ]` | `expression.postfix` | `instantiation_expression` | Other |
| `projection_expression` | `EXPRESSION . ⦅ ‹identifier› ‖ ‹number› ⦆` | `expression.postfix` | `projection_expression` | Other, Member, Number |
| `hole` | `? ⦅ ‹hole_name› ⦆?` | `expression.atom` | `hole` | Hole, Label |
| `parenthesized_expression` | `( ⦅ ) ‖ EXPRESSION ⦅ ) ‖ , ⦅ EXPRESSION ⦅ , EXPRESSION ⦅ , EXPRESSION ⦆* ⦆? ⦅ , ⦆? ⦆? ) ‖ : TYPE ) ⦆ ⦆` | `expression.atom` | `parenthesized_expression` | Other |
| `list_expression` | `[ ⦅ EXPRESSION ⦅ , EXPRESSION ⦆* ⦅ , ⦆? ⦆? ]` | `expression.atom` | `list_expression` | Other |
| `block` | `{ ⦅ ⟨val_statement⟩ ‖ ⟨bind_statement⟩ ‖ ⟨unpack_statement⟩ ‖ ⟨leta_statement⟩ ‖ ⟨hold_statement⟩ ‖ ⟨recv_statement⟩ ‖ ⟨acquire_statement⟩ ‖ ⟨release_statement⟩ ‖ fork ( ‹identifier› : TYPE ) EXPRESSION as ‹identifier› ; ‖ fork ! ( ‹identifier› : TYPE ) EXPRESSION ; ‖ ⟨expression_statement⟩ ⦆* ⦅ EXPRESSION ⦆? }` | `expression.atom` | `block` | Other, Keyword, Operator, VariableDef, VariableParam |
| `lambda_expression` | `fn ⦅ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⟨block⟩ ‖ [ ‹type_variable› ⦅ , ‹type_variable› ⦆* ⦅ , ⦆? ] ⟨block⟩ ⦆` | `expression.atom` | `lambda_expression` | Keyword, Other, VariableParam, TypeVariable, Type, Operator, VariableDef |
| `thunk_expression` | `thunk ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? ⟨block⟩` | `expression.atom` | `thunk_expression` | Keyword, Other, Number, Operator, VariableDef, VariableParam |
| `case_expression` | `case EXPRESSION ⦅ with EXPRESSION ⦆? ⦅ -> TYPE ⦆? ⦅ { } ‖ ⦅ { PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ‖ { \| PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ⦆ ⦆` | `expression.atom` | `case_expression` | Keyword, Operator, Other |
| `handle_expression` | `handle ‹identifier› : ‹type_identifier› ⟨block⟩ with { ⦅ pure ( ‹identifier› ) => EXPRESSION ‖ oper ‹identifier› ( ‹identifier› , ‹identifier› ) => EXPRESSION ⦆ ⦅ , ⦅ pure ( ‹identifier› ) => EXPRESSION ‖ oper ‹identifier› ( ‹identifier› , ‹identifier› ) => EXPRESSION ⦆ ⦆* ⦅ , ⦆? }` | `expression.atom` | `handle_expression` * | Keyword, VariableDef, Other, Type, Operator, VariableParam, FunctionDef |
| `if_expression` | `if EXPRESSION ⦅ -> TYPE ⦆? ⟨block⟩ else ⦅ ⟨block⟩ ‖ if EXPRESSION ⦅ -> TYPE ⦆? ⟨block⟩ else ⟨block⟩ ⦆` | `expression.atom` | `if_expression` | Keyword, Operator, Other, VariableDef, VariableParam |
| `for_expression` | `for ‹identifier› in EXPRESSION ⟨block⟩` | `expression.atom` | `for_expression` * | Keyword, VariableDef, Other, Operator, VariableParam |
| `while_expression` | `while EXPRESSION ⟨block⟩` | `expression.atom` | `while_expression` * | Keyword, Other, Operator, VariableDef, VariableParam |
| `loop_expression` | `loop ⟨block⟩` | `expression.atom` | `loop_expression` * | Keyword, Other, Operator, VariableDef, VariableParam |
| `break_expression` | `break` | `expression.atom` | `break_expression` * | Keyword |
| `break_value_expression` | `break ( EXPRESSION )` | `expression.atom` | `break_value_expression` * | Keyword, Other |
| `continue_expression` | `continue` | `expression.atom` | `continue_expression` * | Keyword |
| `co_expression` | `co { ⟨instantiation.explicit⟩ ⦅ , ⟨instantiation.explicit⟩ ⦆* ⦅ , ⦆? }` | `expression.atom` | `co_expression` | Keyword, Other, Member |
| `glob_expression` | `glob { ⦅ ⟨instantiation.explicit⟩ ; ⦆* }` | `expression.atom` | `glob_expression` * | Keyword, Other, Member |
| `telescope_expression` | `#{ . ⦅ ‹identifier› ‖ ‹number› ⦆ = EXPRESSION ⦅ , . ⦅ ‹identifier› ‖ ‹number› ⦆ = EXPRESSION ⦆* ⦅ , ⦆? } ‖ #{ ⦅ } ‖ EXPRESSION ⦅ = EXPRESSION ⦆? ⦅ \| ⟨instantiation.explicit⟩ ⦅ , ⟨instantiation.explicit⟩ ⦆* ⦅ , ⦆? } ‖ ⦅ , EXPRESSION ⦅ = EXPRESSION ⦆? ⦆* ⦅ , ⦆? } ⦆ ⦆` | `expression.atom` | `telescope_expression` * | Other, Member, Number, Operator |
| `labelled_sum_expression` | `+ { . ⦅ ‹identifier› ‖ ‹number› ⦆ = EXPRESSION }` | `expression.atom` | `labelled_sum_expression` * | Operator, Other, Member, Number |
| `lazy_record_expression` | `& { ⦅ . ⦅ ‹identifier› ‖ ‹number› ⦆ => EXPRESSION ⦅ , . ⦅ ‹identifier› ‖ ‹number› ⦆ => EXPRESSION ⦆* ⦅ , ⦆? ⦆? }` | `expression.atom` | `lazy_record_expression` * | Operator, Other, Member, Number |
| `offer_expression` | `offer ( EXPRESSION ) ⦅ { PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ‖ { \| PATTERN => EXPRESSION ⦅ , PATTERN => EXPRESSION ‖ , \| PATTERN => EXPRESSION ⦆* ⦅ , ⦆? } ⦆` | `expression.atom` | `offer_expression` | Keyword, Other, Operator |
| `migrate_expression` | `migrate [ ‹identifier› ] ⟨block⟩` | `expression.atom` | `migrate_expression` | Keyword, Other, Label, Operator, VariableDef, VariableParam |
| `send_expression` | `send ( EXPRESSION , EXPRESSION )` | `expression.atom` | `send_expression` | Keyword, Other |
| `close_expression` | `close ( EXPRESSION )` | `expression.atom` | `close_expression` | Keyword, Other |
| `select_expression` | `select ( EXPRESSION , ‹identifier› )` | `expression.atom` | `select_expression` | Keyword, Other, Label |
| `dup_expression` | `dup ( EXPRESSION )` | `expression.atom` | `dup_expression` | Keyword, Other |
| `drop_expression` | `drop ( EXPRESSION )` | `expression.atom` | `drop_expression` | Keyword, Other |
| `access_expression` | `access ‹identifier› as ‹identifier› ⟨block⟩ ⦅ unwind ⟨block⟩ ⦆?` | `expression.atom` | `access_expression` * | Keyword, Variable, VariableDef, Other, Operator, VariableParam |
| `resume_expression` | `resume ( ‹identifier› , EXPRESSION )` | `expression.atom` | `resume_expression` * | Keyword, Other, Variable |
| `abort_expression` | `abort ( ‹identifier› )` | `expression.atom` | `abort_expression` * | Keyword, Other, Variable |
| `shell_block` | `#!{ ⦅ EXPRESSION ⦆? }` | `expression.atom` | `shell_block` | Other |
| `identifier.expression` | `‹identifier›` | `expression.atom` | `identifier` | Variable |
| `constructor.expression` | `‹constructor›` | `expression.atom` | `constructor` | Constructor |
| `boolean.expression` | `true ‖ false` | `expression.atom` | `boolean` | Boolean |
| `unit.expression` | `unit` | `expression.atom` | `unit` | Keyword |
| `number.expression` | `‹number›` | `expression.atom` | `number` | Number |
| `typed_number.expression` | `‹typed_number›` | `expression.atom` | `typed_number` | Number |
| `character` | `‹character›` | `expression.atom` | `character` | Character |
| `string.expression` | `" ⦅ ‹escape_sequence› ‖ ‹string_fragment› ‖ ${ EXPRESSION } ⦆* "` | `expression.atom` | `string` | StringLit, Escape, Other |
| `escape_sequence` | `‹escape_sequence›` | `expression.atom` | `escape_sequence` | Escape |
| `shell_list` | `shell_or ⦅ list_operator shell_or ⦆* ⦅ list_operator ⦆?` | `expression.atom` | `shell_list` | Other, Operator |
| `list_operator` | `; ‖ & ‖ newline` | `expression.atom` | `list_operator` | Operator |
| `or_expression` | `shell_and ⦅ \|\| shell_and ⦆*` | `expression.or` | `or_expression` | Other, Operator |
| `and_expression` | `pipeline_operand ⦅ && pipeline_operand ⦆*` | `expression.and` | `and_expression` | Other, Operator |
| `pipeline.pipe` | `EXPRESSION \| EXPRESSION` | `expression.postfix` | `pipeline` | Operator |
| `pipeline.pipe_both` | `EXPRESSION \|& EXPRESSION` | `expression.postfix` | `pipeline` | Operator |
| `negation` | `negation` | `expression.atom` | `negation` | Operator |
| `environment_assignment` | `‹environment_assignment›` | `expression.atom` | `environment_assignment` | VariableParam |
| `shell_word` | `‹shell_word›` | `expression.atom` | `shell_word` | Path |
| `single_quoted_string` | `' ‹single_quoted_content› '` | `expression.atom` | `single_quoted_string` | StringLit |
| `double_quoted_string` | `" ⦅ ‹double_string_fragment› ‖ ‹escape_sequence› ‖ ⟨variable_expansion⟩ ⦆* "` | `expression.atom` | `double_quoted_string` | StringLit, Escape, Other, Variable |
| `variable_expansion` | `$ ‹variable_name› ‖ ${ ‹variable_name› }` | `expression.atom` | `variable_expansion` | Other, Variable |
| `variable_name` | `‹variable_name›` | `expression.atom` | `variable_name` | Variable |
| `command_substitution` | `$!{ ⦅ list_operator ⦆? ⦅ shell_list ⦆? }` | `expression.atom` | `command_substitution` | Other, Operator |
| `host_escape` | `$ ( EXPRESSION )` | `expression.atom` | `host_escape` | Other |
| `subshell` | `[ ⦅ EXPRESSION ⦆? ]` | `expression.atom` | `subshell` | Other |
| `file_descriptor` | `‹file_descriptor›` | `expression.atom` | `file_descriptor` | Number |
| `redirection_operator` | `<> ‖ <& ‖ >& ‖ >> ‖ < ‖ >` | `expression.atom` | `redirection_operator` | Operator |

## `type` — 36 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| `forall_type` | `forall ⦅ ‹type_variable› ⦆* . TYPE` | `type.arrow` | `forall_type` | Keyword, TypeVariable, Other |
| `package_type` | `package [ ‹type_identifier› ⦅ , ‹type_identifier› ⦆* ⦅ , ⦆? ] TYPE` | `type.application` | `package_type` * | Keyword, Other, Type |
| `function_type` | `TYPE -> TYPE` | `type.arrow` | `function_type` | Operator |
| `value_function_type` | `TYPE => TYPE` | `type.arrow` | `value_function_type` * | Operator |
| `static_abstraction` | `\ ⦅ ‹type_identifier› ‖ ‹type_variable› ⦆ . TYPE` | `type.arrow` | `static_abstraction` * | Operator, Type, TypeVariable, Other |
| `union_type` | `TYPE \| TYPE` | `type.union` | `union_type` | Operator |
| `intersection_type` | `TYPE /\ TYPE` | `type.intersection` | `intersection_type` | Operator |
| `lazy_product_type` | `TYPE & TYPE` | `type.lazy_product` | `lazy_product_type` | Operator |
| `equivalence_type` | `TYPE ≃ TYPE` | `type.equivalence` | `equivalence_type` * | Operator |
| `isomorphism_type` | `TYPE ≅ TYPE` | `type.equivalence` | `isomorphism_type` * | Operator |
| `universe_flow_type` | `TYPE ⇝ TYPE` | `type.equivalence` | `universe_flow_type` * | Operator |
| `sum_type` | `TYPE + TYPE` | `type.sum` | `sum_type` | Operator |
| `product_type` | `TYPE * TYPE` | `type.product` | `product_type` | Operator |
| `f_type.row` | `-F [ ‹type_identifier› ⦅ , ‹type_identifier› ⦆* ⦅ , ⦆? ] TYPE` | `type.application` | `f_type` | Keyword, Other, Type |
| `f_type` | `-F TYPE` | `type.application` | `f_type` | Keyword |
| `u_type` | `+U ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? TYPE` | `type.application` | `u_type` | Keyword, Other, Number |
| `universe_type` | `Type ⦅ [ ⦅ + ‖ - ⦆ ⦅ , ‹number› ⦆? ] ⦆?` | `type.atom` | `universe_type` * | TypeBuiltin, Other, Keyword, Number |
| `representable_universe_type` | `Type+` | `type.atom` | `representable_universe_type` * | TypeBuiltin |
| `at_type` | `TYPE at ‹identifier›` | `type.application` | `at_type` | Keyword, Label |
| `path_type` | `Path ( ⦅ Type ⦅ [ ⦅ + ‖ - ⦆ ⦅ , ‹number› ⦆? ] ⦆? , TYPE , TYPE ‖ TYPE , EXPRESSION , EXPRESSION ⦆ )` | `type.application` | `path_type` * | TypeBuiltin, Other, Operator, Number |
| `type_application` | `⦅ ‹type_identifier› ‖ ‹type_variable› ⦅ [ < ] ⦆? ⦆ ( TYPE ⦅ , TYPE ⦆* ⦅ , ⦆? )` | `type.application` | `type_application` | Type, TypeVariable, Other, Operator |
| `type_path` | `TYPE . ‹type_identifier›` | `type.path` | `type_path` * | Other, Type |
| `parenthesized_type` | `( TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? )` | `type.atom` | `parenthesized_type` | Other |
| `telescope_type` | `#{ ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `telescope_type` * | Other |
| `send_session_type` | `! TYPE . TYPE` | `type.arrow` | `send_session_type` | Operator, Other |
| `receive_session_type` | `? TYPE . TYPE` | `type.arrow` | `receive_session_type` | Operator, Other |
| `end_session_type` | `end` | `type.atom` | `end_session_type` | Keyword |
| `labelled_sum_type` | `+ { ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `labelled_sum_type` * | Operator, Other |
| `lazy_record_type` | `& { ⦅ TYPE ⦅ : TYPE ⦆? ⦅ , TYPE ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? }` | `type.atom` | `lazy_record_type` * | Operator, Other |
| `mu_session_type` | `mu ‹type_variable› . TYPE` | `type.arrow` | `mu_session_type` | Keyword, TypeVariable, Other |
| `primitive_type` | `Any ‖ Unknown ‖ Never ‖ Boolean ‖ Integer ‖ u32 ‖ u64 ‖ i32 ‖ i64 ‖ f32 ‖ f64 ‖ Char ‖ String ‖ Symbol ‖ Unit ‖ Void` | `type.atom` | `primitive_type` | TypeBuiltin |
| `unknown_type` | `?` | `type.atom` | `unknown_type` * | TypeBuiltin |
| `type_identifier` | `‹type_identifier›` | `type.atom` | `type_identifier` | Type |
| `type_variable` | `‹type_variable›` | `type.atom` | `type_variable` | TypeVariable |
| `capability_type` | `Cap ⦅ [ ⦅ ‹number› ‖ ‹identifier› ‖ ω ⦆ ] ⦆? { ‹identifier› ⦅ , ‹identifier› ⦆* ⦅ , ⦆? }` | `type.atom` | `capability_type` * | TypeBuiltin, Other, Number, Member |
| `number.type` | `‹number›` | `type.atom` | `number` | Number |

## `instantiation` — 6 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| `instantiation.type` | `TYPE` | `expression.atom` | `instantiation_expression` | — |
| `instantiation.direction.descent` | `<` | `expression.atom` | `instantiation_expression` | Operator |
| `instantiation.direction.productivity` | `>` | `expression.atom` | `instantiation_expression` | Operator |
| `instantiation.named_measure` | `‹identifier› <` | `expression.atom` | `instantiation_expression` | VariableParam, Operator |
| `instantiation.explicit` | `‹identifier› = EXPRESSION` | `expression.atom` | `instantiation_expression` | VariableParam, Other |
| `instantiation.tail` | `tail` | `expression.atom` | `instantiation_expression` | Keyword |

## `module_member` — 4 rules

| Rule | Form | Group | Kind | Roles |
| ---- | ---- | ----- | ---- | ----- |
| `module_definition_member` | `def ‹identifier› ⦅ @[ ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ : TYPE ⦆* ⦅ , ⦆? ⦆? ] ⦆? ⦅ : TYPE ; ‖ = EXPRESSION ; ‖ ( ⦅ ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦅ , ⦅ ‹identifier› ‖ ‹type_variable› ‖ ‹type_identifier› ⦆ ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ⦆? ) ⦅ -> TYPE ⦆? ⟨block⟩ ⦆` | `item.singleton` | `module_declaration` | Keyword, FunctionDef, Other, VariableParam, TypeVariable, Type, Operator, VariableDef |
| `attributed_module_member` | `⟨attribute_block⟩ ⦅ ⟨attribute_block⟩ ⦆* ⦅ ⟨module_definition_member⟩ ‖ ⟨module_type_member⟩ ⦆` | `item.singleton` | `module_declaration` | Other, Keyword, FunctionDef, VariableParam, TypeVariable, Type, Operator, VariableDef |
| `module_type_member` | `type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? = TYPE ;` | `item.singleton` | `module_declaration` | Keyword, Type, Other, TypeVariable |
| `nested_module_member` | `module ⦅ ‹identifier› ‖ ‹type_identifier› ⦆ ⦅ : ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦆ ‖ :> ⦅ #{ ⦅ ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦅ , ⦅ ‹identifier› : TYPE ‖ type ‹type_identifier› ⦅ ( ‹type_variable› ⦅ : TYPE ⦆? ⦅ , ‹type_variable› ⦅ : TYPE ⦆? ⦆* ⦅ , ⦆? ) ⦆? ⦅ = TYPE ‖ : TYPE ⦆? ‖ mobile type ‹type_identifier› ⦆ ⦆* ⦅ , ⦆? ⦆? } ‖ ‹type_identifier› ( ‹type_identifier› ) ⦆ ⦆? { ⦅ MODULE_MEMBER ⦆* }` | `item.singleton` | `module_declaration` | Keyword, VariableDef, Type, Other, Member, TypeVariable, Operator |

## Internal — 1 rule

A rule whose every reading passes a tile the labeler reads as layout: layout takes no mold, so no source molds the rule.

| Rule | Sort | Form | Layout tile |
| ---- | ---- | ---- | ----------- |
| `block_comment` | item | `/* ⦅ block_comment ‖ block_comment_content ⦆* */` | `/*` |

## Attributes — 11 attributes

Every attribute the lowering's registry admits in an `@[ … ]` block, with the payload its schema takes.

| Attribute | Payload |
| --------- | ------- |
| `checks` | no payload |
| `owes` | an integer payload |
| `refuses` | a text payload |
| `runs` | a text payload |
| `normalizes` | a text payload |
| `doc` | a text payload |
| `explicit_exits` | no payload |
| `explicit_runs` | no payload or the text "effects" |
| `respects` | a declared name or a tuple of declared names |
| `entry` | a declared name or a tuple of declared names |
| `form` | one of the words `explicit`, `sugared` |
