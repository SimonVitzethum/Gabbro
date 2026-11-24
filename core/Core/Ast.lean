module

public import Core.Ast.Grammar
public import Core.Ast.Inventory
public import Core.Ast.Registry
public import Core.Ast.Surface

/-!
# Adding one inventory form

`Tree` defines the reference families. `Ty` is indexed by kind, `Expr` by incoming scope and result
type, and `Stmt`, `Block`, `Decl` and `UnitBody` by incoming and outgoing scopes. A `Binding` holds its
written name, value type and mutability. The newest binding is first and `Local` is its typed de Bruijn
index. A local occurrence production must prove that its written name resolves to that index under
the language's shadowing rules. Read the initializer in the incoming scope, then extend the outgoing
scope. A block's outgoing index describes the end of its body. A scope-delimiting statement chooses
which bindings are visible outside it. A whole unit starts with the empty scope.

A fragment reader fixes its incoming scope and, for expressions, the expected result type. An
uncontextualized numeral belongs to the unbounded source integer domain. M6 elaboration determines
its machine type. The current binding production implements the immutable unannotated spelling.
The empty unit and braced blocks have complete productions. The first declared type or declaration
will provide its concrete surface syntax using the same token grammar interface.

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
   on its leading token and return the tree and suffix equalities. Use `cases read` and apply
   each child's deterministic theorem in token order. Add its case to `ExprReads.deterministic`
   and `ExprReads.consumes` using the inversion and the existing suffix lemmas. For a fixed
   statement keyword, add the corresponding `StmtReads` cases. For `let` variants with the same
   header, append to `LetTailReads` and invert at the discriminator after the initializer.
   For an operator with the existing arithmetic signature, append to `Arith`, provide its
   spelling and precedence, and extend the spelling injectivity and delimiter disjointness
   proofs. The recursive right operand uses the operator precedence plus one for left
   associativity. When leading tokens overlap, use the common prefix once and dispatch at
   the first unequal token, or prove that the competing positions have disjoint type indices.
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

The three `Surface.Rule.Entry` proofs cover syntax. The machine elaboration relation,
source occurrence realization, acceptance rule, ideal rule with units and commutation,
implementation rule, preservation, and joint satisfiability remain open for M6 for
each constructor. For each M6 entry, define those propositions over the same typed case
and its premises. Supply `Elaboriert` and `Realisiert` proofs for a surface form, or the
checked elaboration or runtime origin for a core-only form. Use the syntax entry to
supply the raw `Parse` proof for the surface case. Prove the semantic premise bundle
jointly in `NAME_erfuellbar` and supply all fields of the strict `RegistryEntry`.

In `Core/Waechter/Check.lean` the strict registry configuration takes the actual inductive
name, its `RegistrySchema` function, and constructor-to-entry constant pairs. Activate a
family with all its existing constructors covered. After activation each new constructor
and its complete typed entry land together. The syntax entries here are separate from
that strict configuration. Unfolding `Ast.Bezeichnet` shows the concrete source rules
composed with the elaboration relation that M6 supplies.

## Worked syntax diff for the next leaf

This diff adds the inventoried `true` literal and introduces its Boolean result type.
The syntax modules and pins in the diff were checked with the pinned Lean toolchain.
The M6 semantic additions above are still required to admit this form to the full model.

```diff
diff --git a/core/Core/Ast/Tree.lean b/core/Core/Ast/Tree.lean
index 6d2db7918..e354c7fa0 100644
--- a/core/Core/Ast/Tree.lean
+++ b/core/Core/Ast/Tree.lean
@@ -20,6 +20,8 @@ inductive Ty : Kind → Type where
   /-- The unbounded integer domain of unsuffixed source numerals and their arithmetic.
       Elaboration will supply the contextual machine type. -/
   | integer : Ty .value
+  /-- The type of source truth values. -/
+  | boolean : Ty .value

 structure Binding where
   name : Identifier
@@ -45,6 +47,8 @@ inductive Expr : Scope → Ty .value → Type where
   | lit (value : Nat) : Expr scope .integer
   /-- Left-associative arithmetic. Both operands must have the operator's input type. -/
   | binary (op : Arith) (left right : Expr scope .integer) : Expr scope .integer
+  /-- The written Boolean literal `true`. -/
+  | trueLit : Expr scope .boolean

 inductive Stmt : Scope → Scope → Type where
   /-- `let name = value;`. The name enters scope after the initializer. -/
diff --git a/core/Core/Ast/Expression.lean b/core/Core/Ast/Expression.lean
index 05fd0f14f..baeacf483 100644
--- a/core/Core/Ast/Expression.lean
+++ b/core/Core/Ast/Expression.lean
@@ -58,6 +58,7 @@ inductive AtomReads (scope : Scope) :
   | lit : AtomReads scope (.natural value :: rest) (.lit value) rest
   | grouped : ExprReads scope 0 input tree (closeParen :: rest) →
       AtomReads scope (openParen :: input) tree rest
+  | trueLit : AtomReads scope (.word ['t', 'r', 'u', 'e'] :: rest) .trueLit rest

 /-- Higher-precedence operators stay in the right operand. A same-precedence operator
     belongs to the outer continuation, giving left associativity. -/
@@ -78,6 +79,12 @@ theorem AtomReads.lit_inversion
   cases read
   exact ⟨rfl, rfl⟩

+theorem AtomReads.trueLit_inversion
+    (read : AtomReads scope (.word ['t', 'r', 'u', 'e'] :: rest) tree suffix) :
+    tree = .trueLit ∧ suffix = rest := by
+  cases read
+  exact ⟨rfl, rfl⟩
+
 /-- One precedence proof for all registered infix operators. Adding an operator
     only extends the token and precedence tables and the token injectivity proof. -/
 theorem ExprReads.deterministic (left : ExprReads scope minimum input a rest)
@@ -90,7 +97,7 @@ theorem ExprReads.deterministic (left : ExprReads scope minimum input a rest)
       ∀ {b rest'}, AtomReads scope input b rest' → a = b ∧ rest = rest')
     (motive_3 := fun min _ first input a rest _ =>
       ∀ {b rest'}, ExprTail scope min first input b rest' → a = b ∧ rest = rest')
-    ?_ ?_ ?_ ?_ ?_ left
+    ?_ ?_ ?_ ?_ ?_ ?_ left
   · intro _ _ _ _ _ _ _ _ _ atomDet tailDet _ _ other
     cases other with
     | atom atom tail =>
@@ -104,6 +111,9 @@ theorem ExprReads.deterministic (left : ExprReads scope minimum input a rest)
     | grouped inside =>
       obtain ⟨same, suffix⟩ := insideDet inside
       exact ⟨same, (List.cons.inj suffix).2⟩
+  · intro _ _ _ other
+    obtain ⟨rfl, rfl⟩ := other.trueLit_inversion
+    exact ⟨rfl, rfl⟩
   · intro _ _ _ _ blocked _ _ other
     cases other with
     | stop => exact ⟨rfl, rfl⟩
@@ -124,13 +134,15 @@ theorem ExprReads.consumes (read : ExprReads scope minimum input tree rest) : re
     (motive_1 := fun _ input _ _ rest _ => rest <:+ input)
     (motive_2 := fun input _ _ rest _ => rest <:+ input)
     (motive_3 := fun _ _ _ input _ rest _ => rest <:+ input)
-    ?_ ?_ ?_ ?_ ?_ read
+    ?_ ?_ ?_ ?_ ?_ ?_ read
   · intro _ _ _ _ _ _ _ _ _ atom tail
     exact tail.trans atom
   · intro _ _
     exact List.suffix_cons _ _
   · intro input _ _ rest _ child
     exact ((List.suffix_cons closeParen rest).trans child).trans (List.suffix_cons openParen input)
+  · intro _
+    exact List.suffix_cons _ _
   · intro _ rest _ _ _
     exact List.suffix_refl rest
   · intro _ input _ _ _ _ _ op _ _ _ operand tail
diff --git a/core/Core/Ast/Print.lean b/core/Core/Ast/Print.lean
index b460f502f..7df278539 100644
--- a/core/Core/Ast/Print.lean
+++ b/core/Core/Ast/Print.lean
@@ -94,12 +94,22 @@ def letName : Identifier := ⟨['l', 'e', 't'], 'l', ['e', 't'], rfl, by
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
@@ -121,6 +131,7 @@ theorem Expr.printAtom (tree : Expr scope type) (rest : List Token) :
     apply ExprReads.atom (leftIH (op.token :: right.printTokens ++ closeParen :: rest))
     exact .binary op (Nat.zero_le _) (.atom (rightIH (closeParen :: rest))
       (.stop noOperatorAtClose)) (.stop noOperatorAtClose)
+  | trueLit => exact .trueLit

 theorem Expr.printReads (tree : Expr scope type) (blocked : ¬ Continues minimum rest) :
     ExprReads scope minimum (tree.printTokens ++ rest) tree rest :=
diff --git a/core/Core/Ast/Surface.lean b/core/Core/Ast/Surface.lean
index 298a28ffa..4426c79fd 100644
--- a/core/Core/Ast/Surface.lean
+++ b/core/Core/Ast/Surface.lean
@@ -147,4 +147,26 @@ theorem letValue_entry (scope : Scope) : (letValue scope).Entry where
   prints := letValue_print
   erfuellbar := letValue_erfuellbar scope

+/-- Inventory key `surface.SExpr.tru`. -/
+def trueLiteral (scope : Scope) : Rule (.expression scope .boolean) PUnit where
+  tree := fun _ => .trueLit
+  production := fun _ tokens => tokens = [.word ['t', 'r', 'u', 'e']]
+
+theorem trueLiteral_print (scope : Scope) :
+    (trueLiteral scope).production PUnit.unit
+      (((Category.expression scope .boolean).printPieces .trueLit).map PrintedToken.value) :=
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
diff --git a/core/Core/Waechter/Check.lean b/core/Core/Waechter/Check.lean
index db98b8c1b..cb7599d2e 100644
--- a/core/Core/Waechter/Check.lean
+++ b/core/Core/Waechter/Check.lean
@@ -12,16 +12,16 @@ open Lean Elab Command
 namespace Gabbro.Core.Waechter

 private meta def pins : Array (Name × UInt64) := #[
-  (`Gabbro.Core.Ast.Ty, 12782873945396265670),
-  (`Gabbro.Core.Ast.Local, 3790732133586003643),
-  (`Gabbro.Core.Ast.Expr, 9528347216282307943),
-  (`Gabbro.Core.Ast.Stmt, 5262650281051958971),
-  (`Gabbro.Core.Ast.Block, 554026736110315180),
-  (`Gabbro.Core.Ast.Decl, 7135683955101088422),
-  (`Gabbro.Core.Ast.UnitBody, 12910938552000479105),
-  (`Gabbro.Core.Ast.Unit, 8561659821477951161),
-  (`Gabbro.Core.Ast.Parse, 7662161646515821401),
-  (`Gabbro.Core.Ast.Bezeichnet, 17783779404160999950),
+  (`Gabbro.Core.Ast.Ty, 16267350856571732080),
+  (`Gabbro.Core.Ast.Local, 2823048309132892569),
+  (`Gabbro.Core.Ast.Expr, 15284502278999404801),
+  (`Gabbro.Core.Ast.Stmt, 12369416387397553265),
+  (`Gabbro.Core.Ast.Block, 14965519469628557294),
+  (`Gabbro.Core.Ast.Decl, 8984746402279208916),
+  (`Gabbro.Core.Ast.UnitBody, 9067649122551861143),
+  (`Gabbro.Core.Ast.Unit, 1392324911477459259),
+  (`Gabbro.Core.Ast.Parse, 17481635787039456365),
+  (`Gabbro.Core.Ast.Bezeichnet, 14274575155168311886),
   (`Gabbro.Core.Ziel.Rahmen, 11884202126975013255),
   (`Gabbro.Core.Ziel.NichtLeer, 3734935478639616152),
   (`Gabbro.Core.Ziel.Verfeinert, 6262184474930089844),
```
-/
