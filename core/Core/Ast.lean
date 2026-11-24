module

public import Core.Ast.Grammar
public import Core.Ast.LowLevel.Exec.Proofs.ExecStop
public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Proofs.View
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Freigabe
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Tabelle
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Lauf
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Reserviert
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Sicht
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Erfuellbar
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Fuellung
public import Core.Ast.LowLevel.Mem.Proofs.Flush.Flush
public import Core.Ast.LowLevel.Mem.Proofs.Map.Map
public import Core.Ast.LowLevel.Mem.Proofs.Unmap.Unmap
public import Core.Ast.LowLevel.Mem.Proofs.Unmap.UnmapSat
public import Core.Ast.LowLevel.Mem.Proofs.Activate.Activate
public import Core.Ast.LowLevel.Mem.Proofs.NewSpace
public import Core.Ast.LowLevel.Mem.Proofs.SplitAt
public import Core.Ast.LowLevel.Mem.Proofs.SplitPages.SplitPages
public import Core.Ast.LowLevel.Mem.Proofs.SplitPages.SplitPagesSatisfiability
public import Core.Ast.LowLevel.Mem.Proofs.Merge.Merge
public import Core.Ast.LowLevel.Mem.Proofs.Protect.Protect
public import Core.Ast.LowLevel.Exec.Proofs.ExecWait
public import Core.Ast.LowLevel.Exec.Proofs.ExecStateDecl
public import Core.Ast.LowLevel.Exec.Proofs.ExecEntry
public import Core.Ast.LowLevel.Proofs.Syntax
public import Core.Ast.LowLevel.Proofs.Elaboration
public import Core.Ast.LowLevel.Proofs.Execution
public import Core.Ast.LowLevel.Proofs.Preservation
public import Core.Ast.LowLevel.Proofs.Meaning
public import Core.Ast.LowLevel.Proofs.Satisfiability
public import Core.Ast.LowLevel.Proofs.EnvTypes
public import Core.Ast.LowLevel.Proofs.EnvironmentPacket
public import Core.Ast.LowLevel.Proofs.RegionUnit
public import Core.Ast.LowLevel.Proofs.RegionSatisfiability
public import Core.Ast.LowLevel.Proofs.DeviceRegisters
public import Core.Ast.LowLevel.Proofs.DeviceTransition
public import Core.Ast.LowLevel.Proofs.DeviceLend
public import Core.Ast.LowLevel.Proofs.DeviceDma
public import Core.Ast.LowLevel.Proofs.DeviceSatisfiability
public import Core.Ast.LowLevel.Exec.Proofs.ExecJumpLong
public import Core.Ast.Inventory.All
public import Core.Ast.Inventory.Registry
public import Core.Ast.Program.BatchSurface
public import Core.Ast.Expression.Proofs
public import Core.Ast.Semantik.Recipe
public import Core.Ast.Program.Progress
public import Core.Ast.Aggregate.ArrayValueProofs
public import Core.Ast.Aggregate.ArrayIndexProofs
public import Core.Ast.Aggregate.TupleValueProofs
public import Core.Ast.Aggregate.TupleFieldProofs
public import Core.Ast.Aggregate.Types.ArrayProofs
public import Core.Ast.Aggregate.Types.CarrierIndexProofs
public import Core.Ast.Aggregate.Types.CarrierIndexOptionProofs
public import Core.Ast.Aggregate.Carrier.TableProofs
public import Core.Ast.Aggregate.Carrier.Option.ConstructProofs
public import Core.Ast.Aggregate.Carrier.Option.TestProofs
public import Core.Ast.Aggregate.Carrier.Option.MatchProofs
public import Core.Ast.Aggregate.Carrier.Effects.GroupProofs
public import Core.Ast.Aggregate.Carrier.Effects.InferenceProofs
public import Core.Ast.Aggregate.Types.TupleProofs
public import Core.Ast.Aggregate.TupleBindProofs
public import Core.Ast.Aggregate.Records.RecordDeclProofs
public import Core.Ast.Aggregate.Records.MutableValueProofs
public import Core.Ast.Aggregate.Records.ConstructionProofs
public import Core.Ast.Aggregate.Records.RecordFieldProofs
public import Core.Ast.Aggregate.Records.AssignFieldProofs
public import Core.Ast.Variant.TaggedDeclProofs
public import Core.Ast.Variant.VariantValueProofs
public import Core.Ast.Variant.VariantMatchProofs
public import Core.Ast.TextValue.LiteralProofs
public import Core.Ast.TextValue.LengthProofs
public import Core.Ast.TextValue.ConcatProofs
public import Core.Ast.TextValue.IndexProofs
public import Core.Ast.TextValue.SubstringProofs
public import Core.Ast.TextValue.TypeProofs

/-!
# M6 aggregate and tagged-form proof handoff

Each target module lists its pinned propositions by form. Add theorems to the
assigned target modules. The registry packets remain open until their entries
are assembled from those theorems.

| Group | Target modules | Propositions |
| --- | --- | ---: |
| Array type, value and index | `Aggregate.Types.ArrayProofs`, `Aggregate.ArrayValueProofs`, `Aggregate.ArrayIndexProofs` | 43 |
| Tuple type, value and binding | `Aggregate.Types.TupleProofs`, `Aggregate.TupleValueProofs`, `Aggregate.TupleBindProofs` | 42 |
| Record declaration and construction, inferred mutable binding | `Aggregate.Records.RecordDeclProofs`, `Aggregate.Records.MutableValueProofs`, `Aggregate.Records.ConstructionProofs` | 41 |
| Record read and update, tuple projection | `Aggregate.Records.RecordFieldProofs`, `Aggregate.Records.AssignFieldProofs`, `Aggregate.TupleFieldProofs` | 42 |
| Tagged declaration, construction and match | `Variant.TaggedDeclProofs`, `Variant.VariantValueProofs`, `Variant.VariantMatchProofs` | 43 |
-/

/-!
# Adding one inventory form

`Tree` defines the reference families. `Ty` is indexed by kind, `Expr` by incoming scope and result
type, and `Stmt`, `Block`, `Decl` and `UnitBody` by incoming and outgoing scopes. A `Binding` holds its
written name, value type and mutability. The newest binding is first and `Local` is its typed de Bruijn
index. A local occurrence production must prove that its written name resolves to that index under
the language's shadowing rules. Read the initializer in the incoming scope, then extend the outgoing
scope. A block's outgoing index describes the end of its body. A scope-delimiting statement chooses
which bindings are visible outside it. A whole unit starts with the empty scope.

A fragment reader fixes its incoming scope and returns an expression together with its inferred type.
Every ordinary integer type is an inclusive range `Ty.int lo hi`. A literal has a singleton range.
Addition adds corresponding endpoints and multiplication takes the minimum and maximum of the four
endpoint products. An unannotated immutable `let` extends the scope with exactly the initializer’s
type. Named integer types and range annotations must elaborate to the range written by the source.
An explicit narrowing form uses the declared range guard. SG-1 widening uses the written attribute
and containment proofs. Storage width belongs to the implementation. The empty unit and braced
blocks have complete productions.

The tree stores structural source information such as binder spellings. Exact half-open offsets are
on the terminals of the grammar derivation. A prefix production reads through its own tokens and
returns the untouched suffix. `ExprReads.consumes`, `StmtReads.consumes` and `Text.locatedSplit` give the
located slice at those boundaries. `Text.Lexed.spanSpelling` identifies its terminal spellings in the
raw source. Printing generates fresh positions. It emits decimal numerals, one space after each
token and parentheses around each infix node. `Text.Canonicalisation` ignores trivia and spelling
variants with the same token values. `Ast.Canonicalisation` additionally permits the canonical
grouping for the tree.

## Syntax steps

1. Read the exact key in `Inventory/Existing.lean` or the other inventory tables and its owning
   milestone and source reference. Read the corresponding production in `dokumente/SYNTAX.md`.
   Keep the inventory key. Use its written operands and type indices.
2. In `Tree.lean` append the constructor and its reference docstring at the end of its category
   inductive. Use typed children directly. Return the exact scope and type promised by the form.
   Use `Local` when a resolved local is a child. Preserve existing constructor ordinals.
3. Append the typed production in `Expression.lean`, `Statement.lean` or `Declaration.lean`. Keep the
   input and remaining token suffix in the relation. For an atom, add `AtomReads.NAME_inversion`
   on its leading token and return the typed tree and suffix equalities. Use `cases read` and apply
   each child's deterministic theorem in token order. Add its case to `ExprReads.deterministic`
   and `ExprReads.consumes` using the inversion and the existing suffix lemmas. For a fixed
   statement keyword, add the corresponding `StmtReads` cases. For `let` variants with the same
   header, append to `LetTailReads` and invert at the discriminator after the initializer.
   For an operator with the existing arithmetic signature, append to `Arith`, provide its
   spelling, precedence and result interval, and extend the spelling injectivity and delimiter disjointness
   proofs. The recursive right operand uses the operator precedence plus one for left
   associativity. When leading tokens overlap, use the common prefix once and dispatch at
   the first unequal token, and prove that the resulting typed tree is unique.
4. In `Print.lean` or the declaration module add the constructor arm of `printPieces` using
   `PrintedToken` values. Prove the corresponding case of `printAtom` or `printReads` using
   its child proofs and the same production. `PrintedToken.renderLexed` certifies whitespace
   separation once. An unfamiliar lexical class needs a local `PrintedToken` certificate
   using its spelling, lexeme, and separation proofs. Leave the raw round-trip and
   determinism theorems in `Grammar.lean` and `Text/Syntax.lean` untouched.
5. In `Surface.lean` provide `NAME`, `NAME_print`, `NAME_erfuellbar`, and `NAME_entry`.
   The rule's `tree` applies the real constructor, and `production` states the token
   premises of its source production. `Entry.reads` instantiates that production,
   `Entry.prints` proves the same premises for the canonical token stream, and
   `Entry.erfuellbar` proves them jointly with lexing. For an ordinary case use
   `Rule.satisfiableOfPrint` with concrete constructor arguments. For a precedence
   interaction follow `binary_erfuellbar`, using explicit derivation constructors.
   `Rule.Entry.parse` gives the corresponding raw `Ast.Parse` proof.
6. In `Core/Waechter/Check.lean` refresh the changed closure hashes from the guard's
   measured output. A type edit can change every dependent family pin. Register any
   new module from this root or its category module. Build the changed modules and
   then `Core` at the configured heartbeat budget. Check both raw syntax round trips
   and parse determinism still export their original statements.

## M6 registry completion

The semantic statement and proof recipe is in `Core.Ast.Semantik.Recipe`. The existing literal,
binary and binding forms have strict entries for their source productions and semantic rules.

## Worked syntax diff for the next leaf

This syntax diff adds the inventoried `true` literal at the existing `Ty.bool` type.
The expression category carries the inferred type alongside the tree. Complete the semantic
entry as described in `Core.Ast.Semantik.Recipe`, then measure the affected pins with the Core guards.

```diff
--- a/core/Core/Ast/Tree.lean
+++ b/core/Core/Ast/Tree.lean
@@ -58,6 +58,9 @@
   | binary (op : Arith) (left : Expr scope (.int lo₁ hi₁))
       (right : Expr scope (.int lo₂ hi₂)) : Expr scope (op.result lo₁ hi₁ lo₂ hi₂)

+  /-- The written Boolean literal `true`. -/
+  | trueLit : Expr scope .bool
+
 abbrev TypedExpr (scope : Scope) := (type : Ty .value) × Expr scope type

 def Expr.typed (tree : Expr scope type) : TypedExpr scope := ⟨type, tree⟩
--- a/core/Core/Ast/Expression.lean
+++ b/core/Core/Ast/Expression.lean
@@ -59,6 +59,8 @@
   | grouped : ExprReads scope 0 input tree (closeParen :: rest) →
       AtomReads scope (openParen :: input) tree rest

+  | trueLit : AtomReads scope (.word ['t', 'r', 'u', 'e'] :: rest) .trueLit rest
+
 /-- Higher-precedence operators stay in the right operand. A same-precedence operator
     belongs to the outer continuation, giving left associativity. -/
 inductive ExprTail (scope : Scope) :
@@ -79,6 +81,12 @@
   cases read
   exact ⟨rfl, rfl⟩

+theorem AtomReads.trueLit_inversion
+    (read : AtomReads scope (.word ['t', 'r', 'u', 'e'] :: rest) tree suffix) :
+    tree.typed = (Expr.trueLit (scope := scope)).typed ∧ suffix = rest := by
+  cases read
+  exact ⟨rfl, rfl⟩
+
 /-- One precedence proof for all registered infix operators. Adding an operator
     only extends the token and precedence tables and the token injectivity proof. -/
 theorem ExprReads.deterministic (left : ExprReads scope minimum input a rest)
@@ -91,7 +99,7 @@
       ∀ {otherType} {b : Expr scope otherType} {rest'}, AtomReads scope input b rest' → a.typed = b.typed ∧ rest = rest')
     (motive_3 := fun min _ first input _ a rest _ =>
       ∀ {otherType} {b : Expr scope otherType} {rest'}, ExprTail scope min first input b rest' → a.typed = b.typed ∧ rest = rest')
-    ?_ ?_ ?_ ?_ ?_ left
+    ?_ ?_ ?_ ?_ ?_ ?_ left
   · intro _ _ _ _ _ _ _ _ _ _ atomDet tailDet _ _ _ other
     cases other with
     | atom atom tail =>
@@ -106,6 +114,9 @@
     | grouped inside =>
       obtain ⟨same, suffix⟩ := insideDet inside
       exact ⟨same, (List.cons.inj suffix).2⟩
+  · intro _ _ _ _ other
+    obtain ⟨same, suffix⟩ := other.trueLit_inversion
+    exact ⟨same.symm, suffix.symm⟩
   · intro _ _ _ _ blocked _ _ _ other
     cases other with
     | stop => exact ⟨rfl, rfl⟩
@@ -127,13 +138,15 @@
     (motive_1 := fun _ input _ _ rest _ => rest <:+ input)
     (motive_2 := fun input _ _ rest _ => rest <:+ input)
     (motive_3 := fun _ _ _ input _ _ rest _ => rest <:+ input)
-    ?_ ?_ ?_ ?_ ?_ read
+    ?_ ?_ ?_ ?_ ?_ ?_ read
   · intro _ _ _ _ _ _ _ _ _ _ atom tail
     exact tail.trans atom
   · intro _ _
     exact List.suffix_cons _ _
   · intro input _ _ rest _ child
     exact ((List.suffix_cons closeParen rest).trans child).trans (List.suffix_cons openParen input)
+  · intro _
+    exact List.suffix_cons _ _
   · intro _ rest _ _ _
     exact List.suffix_refl rest
   · intro _ input _ _ _ _ _ _ _ _ _ _ op _ _ _ operand tail
--- a/core/Core/Ast/Print.lean
+++ b/core/Core/Ast/Print.lean
@@ -94,12 +94,22 @@
   · exact Or.inl (Or.inl (Or.inl ⟨by change 97 ≤ 101; omega, by change 101 ≤ 122; omega⟩))
   · exact Or.inl (Or.inl (Or.inl ⟨by change 97 ≤ 116; omega, by change 116 ≤ 122; omega⟩))⟩

+def trueName : Identifier := ⟨['t', 'r', 'u', 'e'], 't', ['r', 'u', 'e'], rfl, by
+  exact Or.inl (Or.inl ⟨by change 97 ≤ 116; omega, by change 116 ≤ 122; omega⟩), by
+  intro c member
+  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
+  rcases member with rfl | rfl | rfl
+  · exact Or.inl (Or.inl (Or.inl ⟨by change 97 ≤ 114; omega, by change 114 ≤ 122; omega⟩))
+  · exact Or.inl (Or.inl (Or.inl ⟨by change 97 ≤ 117; omega, by change 117 ≤ 122; omega⟩))
+  · exact Or.inl (Or.inl (Or.inl ⟨by change 97 ≤ 101; omega, by change 101 ≤ 122; omega⟩))⟩
+
 /-- Parenthesise each binary node. This gives a canonical, precedence-independent
     rendering of a tree, while the grammar also admits ordinary infix spelling. -/
 def Expr.printPieces : Expr scope type → List PrintedToken
   | .lit value => [printInteger value]
   | .binary op left right =>
     [printOpen] ++ left.printPieces ++ [op.print] ++ right.printPieces ++ [printClose]
+  | .trueLit => [trueName.print]

 def Expr.printTokens (tree : Expr scope type) : List Token :=
   tree.printPieces.map PrintedToken.value
@@ -122,6 +132,7 @@
     apply ExprReads.atom (leftIH (op.token :: right.printTokens ++ closeParen :: rest))
     exact .binary op (Nat.zero_le _) (.atom (rightIH (closeParen :: rest))
       (.stop noOperatorAtClose)) (.stop noOperatorAtClose)
+  | trueLit => exact .trueLit

 theorem Expr.printReads (tree : Expr scope type) (blocked : ¬ Continues minimum rest) :
     ExprReads scope minimum (tree.printTokens ++ rest) tree rest :=
--- a/core/Core/Ast/Surface.lean
+++ b/core/Core/Ast/Surface.lean
@@ -149,4 +149,26 @@
   prints := letValue_print
   erfuellbar := letValue_erfuellbar scope

+/-- Inventory key `surface.SExpr.tru`. -/
+def trueLiteral (scope : Scope) : Rule (.expression scope) PUnit where
+  tree := fun _ => Expr.trueLit.typed
+  production := fun _ tokens => tokens = [.word ['t', 'r', 'u', 'e']]
+
+theorem trueLiteral_print (scope : Scope) :
+    (trueLiteral scope).production PUnit.unit
+      (((Category.expression scope).printPieces Expr.trueLit.typed).map PrintedToken.value) :=
+  rfl
+
+theorem trueLiteral_erfuellbar (scope : Scope) : (trueLiteral scope).Satisfiable :=
+  Rule.satisfiableOfPrint PUnit.unit (trueLiteral_print scope)
+
+theorem trueLiteral_entry (scope : Scope) : (trueLiteral scope).Entry where
+  reads := by
+    intro _ tokens same
+    change tokens = [.word ['t', 'r', 'u', 'e']] at same
+    subst tokens
+    exact .atom .trueLit (.stop noOperatorAtEnd)
+  prints := fun _ => trueLiteral_print scope
+  erfuellbar := trueLiteral_erfuellbar scope
+
 end Gabbro.Core.Ast.Surface
```
-/

/-!
# M6 bounded text proof handoff

Each group has one proof file. Fill the statements listed in that file.

| Group | Target module under `Core.Ast.TextValue` | Propositions |
| --- | --- | ---: |
| UTF-8 literal | `LiteralProofs` | 16 |
| Concatenation | `ConcatProofs` | 16 |
| Byte indexing | `IndexProofs` | 16 |
| Half-open substring | `SubstringProofs` | 16 |
| Current byte length | `LengthProofs` | 16 |
| Bounded string type and widening | `TypeProofs` | 16 |
-/
