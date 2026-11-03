module

public import Grammatik.Kern.Syntax.Syntax.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-! ## 2. Sichtbereich und Variablen -/

/-- C11 scoped-return evidence (`RueckRessourcen`): the exact residual
    `V.ende` plus the list of locally acquired scopes to close, innermost
    first. Exact return is the empty-cleanup case (`scopes = []`); one
    return API is kept by the new `retScoped` constructors beside the old
    `ret`. Calls inherit held resources but never acquire permission to
    release the caller's signature locks; owner marks are never cleanup and
    a returned capability never borrows a scope about to end. The check that
    `scopes` is exactly the crossed lexical scopes in reverse order lives in
    `AkzeptiertSpec(X)`/`Akzeptiert` and is OPEN, as is the scope-indexed
    `cleanupB` traversal. -/
structure RueckRessourcen (D : Deklaration) (V : Vertrag D) (Λ : List (Res D)) where
  scopes : List D.Lock
  genau : Λ.Perm (V.ende ++ scopes.map Res.held)

abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | here : Var (τ :: Γ) τ
  | there : Var Γ τ → Var (σ :: Γ) τ

def ArmCtx (Γ : Ctx) : Option Ty → Ctx
  | none => Γ
  | some τ => τ :: Γ

/-! ## 3. Ausdruecke -- `expr`, `pred`

    Jeder Konstruktor traegt den Bereich seines Ergebnisses im Typ. Was `M104` rechnet,
    steht hier als Index; was `M102`/`M103`/`M137` verlangen, steht als Argument. -/

/-- Resolve a table capability only in its registered nominal space. Equal space names
    grant no access to a different table and establish no physical separation. -/
def Deklaration.capTab (D : Deklaration) (space number : Nat) : Option D.Tab :=
  match D.tabNr number with
  | none => none
  | some t => if space = D.tableSpace t ∧ space < D.dataSpaces.length then some t else none

theorem Deklaration.capTab_sound {D : Deklaration} {space number : Nat} {t : D.Tab}
    (h : D.capTab space number = some t) :
    D.tabNr number = some t ∧ space = D.tableSpace t ∧ space < D.dataSpaces.length := by
  cases hn : D.tabNr number with
  | none => simp [Deklaration.capTab, hn] at h
  | some t' =>
    simp only [Deklaration.capTab, hn] at h
    split at h
    next hs => cases h; exact ⟨rfl, hs⟩
    next => cases h

theorem Deklaration.capTab_of {D : Deklaration} {space number : Nat} {t : D.Tab}
    (hn : D.tabNr number = some t) (hs : space = D.tableSpace t)
    (hb : space < D.dataSpaces.length) : D.capTab space number = some t := by
  subst hs
  simp only [Deklaration.capTab, hn, hb, and_self, if_true]

end Gabbro.Grammatik
