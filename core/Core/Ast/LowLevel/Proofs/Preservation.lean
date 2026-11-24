module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level preservation, safety and cost proofs

Invert the composed transition and replay the shared internal plan. Check the
four M7S fields, M10 commit and answer discipline, and M9 event counts.

- `ErhaltungAussage`
- `RegelSicherAussage`
- `RegelAntwortSicherAussage`
- `AussenLokalAussage`
- `KostenAussage`
-/
