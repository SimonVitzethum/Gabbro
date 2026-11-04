/-
  File:      Grammatik/Gen/Zeugen/Reset.lean
  Subject:   Nondegenerate reset cells through the ordinary declaration and generator-space APIs.
-/
module
public import Grammatik.Gen.Zeugen.Erreicht
@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Reset

open Gabbro.Grammatik Gabbro.Grammatik.Gen

namespace Good

abbrev z : Spez := ({ globs := [{ typ := .arr (.int 0 1) 1 }] } : Spez).einzeln

theorem member : mitglieder.getD 371 {} = z := by decide +kernel

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ := .ret .empty (List.Perm.refl _)

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨n + 1, h⟩ => absurd h (by change n + 1 < 1 at h; omega)

def h0 : Haut z.deklaration := ⟨r, fun _ => false⟩

def P : Programm z.deklaration := h0.programm

def ws : List z.deklaration.Fn := [⟨0, by decide⟩]

def e : Einsatz := z.einsatz P ws (by decide) (by decide)

theorem e_gueltig : e.gueltig = true := by decide

theorem e_hat : e.Hat ⟨10, 0, true, [true]⟩ := by decide

/-- The reset atom is the canonical verdict of the actual unused static-array carrier. -/
theorem carrier : @Gabbro.Grammatik.resetCarrierB z.deklaration (.inr ⟨0, by decide⟩) = true := by decide

theorem zellen : RaumGut ncZiel ⟨10, 0, true, [true]⟩ := by
  refine ⟨371, by rw [mitglieder_laenge]; decide, ?_⟩
  rw [member]
  exact raumGutIn_aus z (grenzenVon 371).1 (grenzenVon 371).2 ncZiel h0
    (fun f => (by decide : ∀ f : Fin z.fns.length,
      @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ (grenzenVon 371).1) f)
    (by decide) (by decide) List.mem_cons_self (ws := ws) (by decide) (by decide) (by decide)
    (by decide) e_hat

end Good

namespace Bad

abbrev z : Spez := ({ globs := [{ typ := .arr (.int 1 1) 1 }] } : Spez).einzeln

theorem member : mitglieder.getD 372 {} = z := by decide +kernel

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ := .ret .empty (List.Perm.refl _)

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨n + 1, h⟩ => absurd h (by change n + 1 < 1 at h; omega)

def h0 : Haut z.deklaration := ⟨r, fun _ => false⟩

def P : Programm z.deklaration := h0.programm

def ws : List z.deklaration.Fn := [⟨0, by decide⟩]

def e : Einsatz := z.einsatz P ws (by decide) (by decide)

def bnoetig : List Zelle := [⟨10, 0, true, [false]⟩]

theorem e_gueltig : e.gueltig = false := by decide

theorem e_hat : e.Hat ⟨10, 0, true, [false]⟩ := by decide

/-- Zero-less elements really refuse reset; the atom is not a synthetic summary bit. -/
theorem carrier : @Gabbro.Grammatik.resetCarrierB z.deklaration (.inr ⟨0, by decide⟩) = false := by decide

theorem e_gedeckt : gedeckt erreicht bnoetig e.zellen = true := by decide

theorem zellen : RaumSchlecht ncZiel erreicht bnoetig := by
  refine ⟨372, by rw [mitglieder_laenge]; decide, ?_⟩
  rw [member]
  exact raumSchlechtIn_aus z (grenzenVon 372).1 (grenzenVon 372).2 ncZiel h0
    (fun f => (by decide : ∀ f : Fin z.fns.length,
      @groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f) ≤ (grenzenVon 372).1) f)
    (by decide) (by decide) List.mem_cons_self (ws := ws) (by decide) (by decide) (by decide)
    (by decide) e_gedeckt

end Bad

end Gabbro.Grammatik.Gen.Zeugen.Reset
