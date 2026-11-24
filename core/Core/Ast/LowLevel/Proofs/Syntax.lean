module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level lexical and grammatical proofs

Prove each statement for every `LowLevel.Form`. Use the shared lexical adapter
and canonical printer certificates. Invert `TypeReads` for the view's operand.

- `ParseAussage`
- `InversionAussage`
- `EindeutigAussage`
- `DruckAussage`
-/
