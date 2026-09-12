/-
  File:      Grammatik/Bibliothek.lean
  Subject:   LIBRARY CALLS (lane E2, PLAN-ERWEITUNG.md section 6) -- a
             run-time library function is an `Ax` whose parameter list is
             the ordinary parameters with the payload type appended.
             No new statement constructor: the call IS an `axiomCall`.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

/-- A run-time library function (PLAN-ERWEITUNG.md section 6, lane E2):
    ordinary parameters, a payload type (a table or tree type on the
    checker side; one more parameter here), an optional result, and
    declared effects. -/
structure BibliotheksFunktion (D : Deklaration) where
  params : List Ty
  nutzlast : Ty
  erg : Option Ty
  schreibt : D.Tab → Bool
  gschreibt : D.Glob → Bool

/-- The axiom serving a library function: its parameter list is the
    ordinary parameters with the payload appended, its result is the
    declared one, and its declared effects agree with the library
    function's. -/
def DientBibliothek (D : Deklaration) (L : BibliotheksFunktion D)
    (a : D.Ax) : Prop :=
  D.aparams a = L.params ++ [L.nutzlast] ∧ D.aerg a = L.erg ∧
  (∀ t, D.aschreibt a t = L.schreibt t) ∧
  ∀ g, D.agschreibt a g = L.gschreibt g

/-! ## 1. Argument lists split at the payload -/

/-- Appending the payload argument to the ordinary arguments gives
    arguments for the axiom's full parameter list. Both append equations
    hold by computation (`rfl`); the `have` names them so the cast reads. -/
def args_snoc (D : Deklaration) {Γ : Ctx} {Λ : List (Res D)}
    {ps : List Ty} {p : Ty} :
    Args D Γ Λ ps → Expr D Γ Λ p → Args D Γ Λ (ps ++ [p])
  | .nil, last =>
    have h : ([] : List Ty) ++ [p] = [p] := rfl
    h ▸ Args.cons last .nil
  | .cons e rest, last =>
    have h : ∀ (τ : Ty) (qs : List Ty) (q : Ty),
        (τ :: qs) ++ [q] = τ :: (qs ++ [q]) := fun _ _ _ => rfl
    h _ _ _ ▸ Args.cons e (args_snoc D rest last)

/-- Splitting arguments for the full list into the ordinary arguments
    and the payload argument. Induction on the ordinary parameters; at
    each step the append equation is named (`rfl`) and the impossible
    `nil` case is closed by the tactic from index unification. -/
theorem args_unsnoc (D : Deklaration) {Γ : Ctx} {Λ : List (Res D)}
    (ps : List Ty) (p : Ty) (args : Args D Γ Λ (ps ++ [p])) :
    ∃ (rest : Args D Γ Λ ps) (last : Expr D Γ Λ p), True := by
  revert args
  induction ps with
  | nil =>
    intro args
    have h : ([] : List Ty) ++ [p] = [p] := rfl
    rw [h] at args
    cases args
    case cons last rest => exact ⟨rest, last, trivial⟩
  | cons t ps ih =>
    intro args
    have h : (t :: ps) ++ [p] = t :: (ps ++ [p]) := rfl
    rw [h] at args
    cases args
    case cons e rest =>
      obtain ⟨r, l, _⟩ := ih rest
      exact ⟨Args.cons e r, l, trivial⟩

/-! ## 2. The call obligations are the `axiomCall` obligations -/

/-- A library call is an `Ax` whose parameter list includes the payload
    (PLAN-ERWEITUNG.md section 6, lane E2): the typing obligation (the
    full argument list) together with the effect obligations (callee
    effects inside the caller's contract, accesses guarded) -- checked
    as ordinary arguments plus the payload argument against the declared
    library function -- are exactly the `Stmt.axiomCall` premises for
    the serving axiom. Both directions use the whole bridge `hDient`:
    `hap` transports the argument list, `herg` the result, `hschw` and
    `hgschw` the four effect premises. -/
theorem bibliotheksruf_ist_ax (D : Deklaration) (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (L : BibliotheksFunktion D) (a : D.Ax)
    (hDient : DientBibliothek D L a) :
    (∃ (args : Args D Γ Λ (D.aparams a)),
      D.aerg a = none ∧
      (∀ t, D.aschreibt a t = true → V.schreibt t = true) ∧
      (∀ g, D.agschreibt a g = true → V.gschreibt g = true) ∧
      (∀ t, D.aschreibt a t = true → darf D t Λ) ∧
      (∀ g, D.agschreibt a g = true → gdarf D g Λ)) ↔
    (∃ (args : Args D Γ Λ L.params) (last : Expr D Γ Λ L.nutzlast),
      L.erg = none ∧
      (∀ t, L.schreibt t = true → V.schreibt t = true) ∧
      (∀ g, L.gschreibt g = true → V.gschreibt g = true) ∧
      (∀ t, L.schreibt t = true → darf D t Λ) ∧
      (∀ g, L.gschreibt g = true → gdarf D g Λ)) := by
  obtain ⟨hap, herg, hschw, hgschw⟩ := hDient
  constructor
  · rintro ⟨args, hno, hw, hg, hd, hgd⟩
    rw [hap] at args
    obtain ⟨rest, last, _⟩ := args_unsnoc D L.params L.nutzlast args
    refine ⟨rest, last, herg ▸ hno, ?_, ?_, ?_, ?_⟩
    · intro t ht
      apply hw t
      rw [hschw t]
      exact ht
    · intro g hg'
      apply hg g
      rw [hgschw g]
      exact hg'
    · intro t ht
      apply hd t
      rw [hschw t]
      exact ht
    · intro g hg'
      apply hgd g
      rw [hgschw g]
      exact hg'
  · rintro ⟨rest, last, hno, hw, hg, hd, hgd⟩
    refine ⟨hap.symm ▸ args_snoc D rest last, ?_, ?_, ?_, ?_, ?_⟩
    · rw [herg]
      exact hno
    · intro t ht
      rw [hschw t] at ht
      exact hw t ht
    · intro g hg'
      rw [hgschw g] at hg'
      exact hg g hg'
    · intro t ht
      rw [hschw t] at ht
      exact hd t ht
    · intro g hg'
      rw [hgschw g] at hg'
      exact hgd g hg'

/-!
CUTS:
- Only the declaration shape above; the obligation equivalence
  (`bibliotheksruf_ist_ax`) and its rule-13 witness are still owed.
-/

end Gabbro.Grammatik
