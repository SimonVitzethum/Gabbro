/-
   File:      Grammatik/GabbroV/GvLauf.lean
   Subject:   Agent 04 task V-04b: thread N world-steps into one WORLD RUN.

   A run is `N` worlds with per-step contracts on the counter cell
   (`zellenLesen` from `GvStore`): each step moves the cell per
   `zahlNach` when `zahlVor` holds. Proved generically: (1) the
   projected run equals the abstract `rufLauf` run (`rufLauf_letzter`
   in `GvKetten` unfolds the last step); (2) the invariant holds on
   the final world by composing (1) with `rufKette_invariant` and
   `zahl_tick_vertrag` -- the 147/148 conditional discharges become
   unconditional given only the per-call contracts and the
   initial-state premise. Witness: a real 2-step run on `kettenWelt`;
   planted failure: a contract-violating run is not covered. The full
   `TreeState` projection (needs a `benutzt` bool cell) stays open.
-/
import Grammatik.GabbroV.GvStore

namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## Agreement: the projected run is the abstract run -/

/-- Extensionality for `Zahl`: same number, same value (proof
    irrelevance closes the bounds). -/
theorem zahl_ext {lo hi : Int} (a b : Zahl lo hi) (h : a.n = b.n) :
    a = b := by
  cases a with
  | mk an alo ahi =>
    cases b with
    | mk bn blo bhi =>
      simp at h
      subst h
      rfl

/-- Projection-run agreement: after `i` contract steps (of `n`) the
    cell reads as the abstract `rufLauf` run of the projected initial
    state. Induction on the steps; the successor case unfolds the
    abstract last step (`rufLauf_letzter`). -/
theorem weltLauf_uebereinstimmung
    (t_c : D.Tab) (kc : Int) (f_c : D.Feld t_c)
    (hf : D.typ t_c f_c = .int 0 255)
    (lauf : Nat → World D) (n : Nat)
    (hschritt : ∀ i, i < n → zahlVor i (zellenLesen t_c kc f_c hf (lauf i)) = true →
      zellenLesen t_c kc f_c hf (lauf (i + 1))
        = zahlNach i (zellenLesen t_c kc f_c hf (lauf i)))
    (hvor : ∀ i, i < n → zahlVor i (zellenLesen t_c kc f_c hf (lauf i)) = true)
    (i : Nat) (hi : i ≤ n) :
    zellenLesen t_c kc f_c hf (lauf i)
      = rufLauf (⟨64, zahlVor, zahlNach⟩ : RufKette (Zahl 0 255)) i 0
        (zellenLesen t_c kc f_c hf (lauf 0)) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      rfl
  | succ i ih =>
      intro hi
      have hilt : i < n := by omega
      have hstep : zellenLesen t_c kc f_c hf (lauf (i + 1))
          = zahlNach i (zellenLesen t_c kc f_c hf (lauf i)) :=
        hschritt i hilt (hvor i hilt)
      have hrun : rufLauf (⟨64, zahlVor, zahlNach⟩ : RufKette (Zahl 0 255)) (i + 1) 0
            (zellenLesen t_c kc f_c hf (lauf 0))
          = zahlNach i
            (rufLauf (⟨64, zahlVor, zahlNach⟩ : RufKette (Zahl 0 255)) i 0
              (zellenLesen t_c kc f_c hf (lauf 0))) := by
        have hletz := rufLauf_letzter
          (⟨64, zahlVor, zahlNach⟩ : RufKette (Zahl 0 255)) i 0
          (zellenLesen t_c kc f_c hf (lauf 0))
        simpa using hletz
      rw [hstep, hrun]
      have hle : i ≤ n := by omega
      exact congrArg (zahlNach i) (ih hle)

/-- The invariant holds on the final world: transfer the projected end
    state across the agreement, then apply the abstract invariant with
    the uniform tick contract. Needs only the per-call contracts and
    the initial state -- no unrolling. -/
theorem weltLauf_invariant
    (t_c : D.Tab) (kc : Int) (f_c : D.Feld t_c)
    (hf : D.typ t_c f_c = .int 0 255)
    (lauf : Nat → World D) (n : Nat) (hn : n ≤ 64)
    (hschritt : ∀ i, i < n → zahlVor i (zellenLesen t_c kc f_c hf (lauf i)) = true →
      zellenLesen t_c kc f_c hf (lauf (i + 1))
        = zahlNach i (zellenLesen t_c kc f_c hf (lauf i)))
    (hvor : ∀ i, i < n → zahlVor i (zellenLesen t_c kc f_c hf (lauf i)) = true)
    (hs0 : zahlInv (zellenLesen t_c kc f_c hf (lauf 0)) = true) :
    zahlInv (zellenLesen t_c kc f_c hf (lauf n)) = true := by
  have hagree := weltLauf_uebereinstimmung t_c kc f_c hf lauf n
    hschritt hvor n (by omega)
  have h64 : (⟨64, zahlVor, zahlNach⟩ : RufKette (Zahl 0 255)).n = 64 := rfl
  have hi64 : 0 + n ≤ (⟨64, zahlVor, zahlNach⟩ : RufKette (Zahl 0 255)).n := by
    rw [h64]
    omega
  have habs := rufKette_invariant (S := Zahl 0 255)
    (⟨64, zahlVor, zahlNach⟩ : RufKette (Zahl 0 255)) zahlInv
    zahl_tick_vertrag n 0 _ hi64 hs0
  rw [hagree]
  exact habs

/-! ## Witness: a real two-step run on `kettenWelt` -/

/-- Two-step run: the counter cell goes 0 → 1 → 2 by real writes. -/
def kettenLauf : Nat → World kettenD
  | 0 => kettenWelt
  | 1 => kettenWelt.storeSlot () 0 KettenFeld.Zaehler ⟨1, by decide, by decide⟩
  | _ => kettenWelt.storeSlot () 0 KettenFeld.Zaehler ⟨2, by decide, by decide⟩

/-- The `Zaehler` field equation of the fixture, by computation. -/
theorem hfZaehler : kettenD.typ () KettenFeld.Zaehler = .int 0 255 := rfl

/-- Step contract of the witness run: each step moves the cell per
    `zahlNach` (shown through `.n`, then lifted by `zahl_ext`). -/
theorem kettenLauf_schritt : ∀ i, i < 2 →
    zahlVor i (zellenLesen () 0 KettenFeld.Zaehler hfZaehler (kettenLauf i)) = true →
    zellenLesen () 0 KettenFeld.Zaehler hfZaehler (kettenLauf (i + 1))
      = zahlNach i (zellenLesen () 0 KettenFeld.Zaehler hfZaehler (kettenLauf i)) := by
  intro i hi _
  have hi2 : i = 0 ∨ i = 1 := by omega
  cases hi2 with
  | inl h =>
      subst h
      apply zahl_ext
      decide
  | inr h =>
      subst h
      apply zahl_ext
      decide

/-- Precondition of the witness run: the counter is below 16. -/
theorem kettenLauf_vor : ∀ i, i < 2 →
    zahlVor i (zellenLesen () 0 KettenFeld.Zaehler hfZaehler (kettenLauf i)) = true := by
  intro i hi
  have hi2 : i = 0 ∨ i = 1 := by omega
  cases hi2 with
  | inl h => subst h; decide
  | inr h => subst h; decide

/-- Witness (non-degenerate): the invariant holds after the real
    two-step run -- the per-call contracts plus the initial state,
    no unrolling. -/
theorem kettenLauf_invariant_zeuge :
    zahlInv (zellenLesen () 0 KettenFeld.Zaehler hfZaehler (kettenLauf 2)) = true :=
  weltLauf_invariant () 0 KettenFeld.Zaehler hfZaehler kettenLauf 2 (by omega)
    kettenLauf_schritt kettenLauf_vor (by decide)

/-- Failing run: step 1 jumps the counter out (99). -/
def laufF : Nat → World kettenD
  | 0 => kettenWelt
  | 1 => kettenWelt.storeSlot () 0 KettenFeld.Zaehler ⟨1, by decide, by decide⟩
  | _ => kettenWelt.storeSlot () 0 KettenFeld.Zaehler ⟨99, by decide, by decide⟩

/-- Planted failure: a run whose step violates the contract is not
    covered -- the counter ends at 99, outside the invariant. The step
    premise fails here (`1 → 99` is no `nach`), so neither lemma says
    anything: checked equation, not a counterexample. -/
theorem weltLauf_ohne_vertrag_bricht :
    zahlInv (zellenLesen () 0 KettenFeld.Zaehler hfZaehler (laufF 2)) = false := by
  decide

/-
   CUTS: what is not proved.
   - Proved: `zahl_ext`; the projection-run agreement
     (`weltLauf_uebereinstimmung`, by step induction via
     `rufLauf_letzter`); the final invariant (`weltLauf_invariant`,
     agreement plus the abstract invariant -- per-call contracts and
     initial state only); the 2-step witness on `kettenWelt`
     (`kettenLauf_invariant_zeuge`) and the contract-violating failure
     (`weltLauf_ohne_vertrag_bricht`).
   - Only stated: `kettenLauf`/`laufF` as fixture runs.
   - Not modelled: runs longer than the contract bound in one go
     (iterate the invariant); the full `TreeState` projection (needs a
     `benutzt` bool cell plus the three edge fields on one fixture --
     precisely: extend `kettenD` by `Vorgaenger`/`Kind`/`Naechstes` edge
     fields and a `Belegt` bool field, prove per-field commutation on
     the same pattern as `kantenBild_slotfeld_anders`, then lift
     `elternKonsistent`/`lokalBenutzt` along the run);
     `GvTraversal`/`GvSplits`/`GvParserFragment` reconciliation.
   - No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere; every
     premise is used; no premise has type `Prop` itself.
-/

#print axioms weltLauf_uebereinstimmung
#print axioms weltLauf_invariant
#print axioms kettenLauf_invariant_zeuge

end Gabbro.Grammatik.GabbroV
