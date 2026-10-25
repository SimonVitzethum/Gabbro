import Grammatik.Logik.WP.Ruf
import Grammatik.Kern.Syntax.Koernung
import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt

/-!
# GabbroV over machine G: witnesses

`fuellen N`: a table of ANY size `N` and the body `traverse k over slots of T { T.slots[k].x = 7; } return;`.
`fuellen_korrekt` proves, for every `N`, every oracle, budget and call meaning, that the body returns and every slot
holds `7` afterwards -- through the `traverse` rule with an invariant (no evaluation: `N` is a variable).
-/

namespace Gabbro.Grammatik.WP.Zeuge

open Gabbro.Grammatik Gabbro.Grammatik.WP

/-- One table of `N` slots with one field in `0 .. 10`; one function that writes it. -/
@[reducible] def fD (N : Nat) : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => (N : Int)
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => true
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun _ => false
  ggeteilt := fun g => g.elim
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun _ => []
  gbraucht := fun g => g.elim
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => ⟨[], none, 0, [], fun _ => true, fun g => g.elim, [], [], none⟩
  eigner_nie_erzeugt := fun _ _ _ _ h => nomatch h
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Empty
  aparams := fun a => a.elim
  aerg := fun a => a.elim
  aschreibt := fun a => a.elim
  agschreibt := fun a => a.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => nomatch h
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g => g.elim

abbrev fV (N : Nat) : Vertrag (fD N) := vertragVon (fD N) ()

theorem recht (N : Nat) : darf (fD N) () [] := fun _ h => nomatch h

/-- `T.slots[k].x = 7;` -/
def koerper (N : Nat) : Block (fD N) (fV N) true [.index ((fD N).count ())] [] [] :=
  .cons (.assignSlot () () (.var .here) (.widen (by decide) (by decide) (.lit 7)) rfl (recht N)) .nil

/-- `traverse k over slots of T { T.slots[k].x = 7; } return;` -/
def rumpf (N : Nat) : Endblock (fD N) (fV N) false [] [] :=
  .cons (.traverse () .tru (koerper N)) (.ret .empty (List.Perm.refl _))

/-! ## The indices of a table of `N` slots -/

/-- Every slot number of the table is among the indices `traverse` visits. -/
theorem alleIndizes_voll (N : Nat) (j : Int) (h0 : 0 ≤ j) (hN : j < N) :
    ∃ k ∈ alleIndizes (N : Int), k.n = j := by
  refine ⟨⟨j, h0, by omega⟩, ?_, rfl⟩
  unfold alleIndizes
  rw [List.mem_filterMap]
  refine ⟨j.toNat, ?_, ?_⟩
  · simp only [List.mem_range]; omega
  · have h1 : ((j.toNat : Nat) : Int) = j := Int.toNat_of_nonneg h0
    have h2 : ((j.toNat : Nat) : Int) ≤ (N : Int) - 1 := by omega
    simp only [h2, dite_true, Option.some.injEq]
    congr 1 <;> simp [h1]

/-! ## The proof, through the `traverse` rule -/

section Beweis

variable (N : Nat) (O : Orakel (fD N)) (passes : Nat)
  (R : ∀ f : (fD N).Fn, World (fD N) → Env (fD N) ((fD N).params f) → RufAusgang f)

/-- The loop invariant: every slot no longer among the indices to visit holds `7`. -/
def Inv (ks : List (Wert (fD N) (.index ((fD N).count ())))) (σ : World (fD N)) (_ : Env (fD N) []) : Prop :=
  ∀ j : Int, 0 ≤ j → j < N → (∀ k ∈ ks, k.n ≠ j) → (σ.slots () j ()).n = 7

/-- The postcondition of the loop: it ends normally and every slot holds `7`. -/
def Nach (o : Ausgang (fV N) false []) : Prop :=
  ∃ σ', o = .ok σ' .nil ∧ ∀ j : Int, 0 ≤ j → j < N → (σ'.slots () j ()).n = 7

/-- **The loop, through `traverse_regel`.** -/
theorem schleife (σ : World (fD N)) :
    Nach N (execStmt O passes R (.traverse (V := fV N) (l := false) () .tru (koerper N)) σ .nil) := by
  show Nach N (traverseLauf (fun σ ρ => execBlock O passes R (koerper N) σ ρ)
    (fun σ ρ => let σ := σ.lese [] (Expr.tru (D := fD N) (Γ := []) (Λ := [])).orte;
      (σ, wahr? (eval σ (Expr.tru (D := fD N) (Γ := []) (Λ := [])) σ ρ)))
    (alleIndizes ((fD N).count ())) σ .nil)
  refine traverse_regel _ _ (Nach N) (Inv N) ?ende ?bruch ?schritt _ σ .nil ?start
  case start =>
    intro j h0 hN hnot
    obtain ⟨k, hk, hkj⟩ := alleIndizes_voll N j h0 hN
    exact absurd hkj (hnot k hk)
  case ende =>
    intro σ ρ h
    cases ρ
    refine ⟨_, rfl, fun j h0 hN => ?_⟩
    exact h j h0 hN (fun k hk => by cases hk)
  case bruch =>
    intro k ks σ ρ _ hc
    exact absurd hc (by simp [wahr?, eval])
  case schritt =>
    intro k ks σ ρ h _
    cases ρ
    simp only [TraverseSchritt, koerper, execBlock, execStmt]
    intro j h0 hN hnot
    by_cases hj : j = k.n
    · subst hj
      erw [schreibSlot_slots_same]
      rfl
    · erw [schreibSlot_slots_other _ _ _ _ _ _ _ hj]
      refine h j h0 hN (fun k' hk' => ?_)
      rcases List.mem_cons.1 hk' with rfl | hk''
      · exact fun he => hj he.symm
      · exact hnot k' hk''

/-- **The body is correct, for a table of any size**: it returns, and every slot holds `7`. -/
theorem fuellen_korrekt (σ : World (fD N)) :
    ∃ σ', execEnd O passes R (rumpf N) σ .nil = .zurueck σ' () ∧
      ∀ j : Int, 0 ≤ j → j < N → (σ'.slots () j ()).n = 7 := by
  obtain ⟨σ1, h1, hall⟩ := schleife N O passes R σ
  refine ⟨σ1.lese [] [], ?_, fun j h0 hN => hall j h0 hN⟩
  simp only [rumpf, execEnd, h1]
  rfl

end Beweis

#print axioms fuellen_korrekt

end Gabbro.Grammatik.WP.Zeuge
