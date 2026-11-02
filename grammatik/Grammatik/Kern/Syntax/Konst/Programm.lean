module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm

@[expose] public section

namespace Gabbro.Grammatik

/-- The closed declaration universe used by compile-time blocks.
    This adds no execution semantics and does not change the goal statement. -/
structure ConstProgram where
  D : Deklaration
  P : Programm D
  functions : List D.Fn
  functions_complete : ∀ f, f ∈ functions
  sourceId : D.Fn → Nat
  sourceId_injective : ∀ f g, sourceId f = sourceId g → f = g
  noGlobals : D.Glob → False
  noOracles : D.Ax → False
  noRegisters : D.Reg → False
  noLocks : D.Lock → False
  noMarks : D.Marke → False
  noInvariants : D.Inv → False
  domains : List D.Tab
  domains_complete : ∀ t, t ∈ domains
  noFields : ∀ t, D.Feld t → False
  count_nonnegative : ∀ t, 0 ≤ D.count t
  domains_closed : ∀ t, D.offen t = false
  noReasons : ∀ f, D.gruende f = 0
  emptyEntry : ∀ f, Signatur.anfang D (D.signatur f) = []
  emptyExit : ∀ f, (vertragVon D f).ende = []

/-- Final resolved scope metadata; values remain typed canonical expressions.
    Wrapper identities are resolved source declaration identities. -/
structure ConstScope (D : Deklaration) where
  bindings : List (String × (Sigma fun τ => Expr D [] [] τ))
  aliases : List (String × Ty)
  wrappers : List (String × Nat)
  declarations : List (String × Nat)

end Gabbro.Grammatik
