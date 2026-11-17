module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Scope

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open Elim Elim.Korrekt

/-- A view reuses immutable keys; it never reads memory or chooses an inhabitant. -/
structure ValueView (symbols : SymEnv D Nat Γ) (expression : Expr D Γ Λ kind) where
  symbol : SymValue D Nat kind
  bounded : ∀ next, symbols.Bounded next → symbol.Bounded next
  realizes : ∀ valuation old world actual, symbols.Realizes valuation world actual →
    symbol.Realizes valuation world (eval old expression world actual)

/-- Nested product projections preserve their original component observations. -/
def valueView? (expression : Expr D Γ Λ kind) (symbols : SymEnv D Nat Γ) :
    Option (ValueView symbols expression) :=
  match expression with
  | .var name => some {
      symbol := symbols.get name
      bounded := fun next bounded => symbols.bounded_get next bounded name
      realizes := fun valuation _ world actual realized => symbols.realizes_get actual valuation world name realized }
  | .prodGet body field => do
      let parent ← valueView? body symbols
      return {
        symbol := parent.symbol.field field
        bounded := fun next bounded => parent.symbol.bounded_field next (parent.bounded next bounded) field
        realizes := fun valuation old world actual realized =>
          parent.symbol.realizes_field field valuation world (eval old body world actual)
            (parent.realizes valuation old world actual realized) }
  | _ => none

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
