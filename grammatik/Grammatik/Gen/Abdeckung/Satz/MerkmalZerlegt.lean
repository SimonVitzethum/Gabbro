/-
  File:      Grammatik/Gen/Abdeckung/Satz/MerkmalZerlegt.lean
  Subject:   a lock-only and a call-only feature set decompose into one probe per lock and per callee
             (part of step 1, `ZellenSatz.lean`).
-/
import Grammatik.Gen.Abdeckung.Satz.MerkmalUnd

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

/-! ## Decomposing a lock-only and a call-only feature set -/

/-- The probe "does not take `L`". -/
def ohneSperre (L : D.Lock) : Merkmal D := ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩

/-- **A lock-only feature set** is the conjunction over a complete list of locks of "does not take `L`" for every lock
    it refuses. -/
theorem sperrMerkmal_zerlegt (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls) (Sp : D.Lock → Bool)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    mE ⟨fun _ => true, fun _ => true, Sp⟩ e = ls.all fun L => Sp L || mE (ohneSperre L) e := by
  have hA : (⟨fun _ => true, fun _ => true, Sp⟩ : Merkmal D) =
      Merkmal.alle (ls.map fun L => if Sp L then Merkmal.top else ohneSperre L) := by
    apply Merkmal.gleich
    · intro g; rw [alle_ruf]; simp only [List.all_map]
      symm; apply List.all_eq_true.2; intro L _; simp only [Function.comp_def]; split <;> rfl
    · intro n; rw [alle_ind]; simp only [List.all_map]
      symm; apply List.all_eq_true.2; intro L _; simp only [Function.comp_def]; split <;> rfl
    · intro L'
      rw [alle_sperre]; simp only [List.all_map, Function.comp_def]
      apply Bool.eq_iff_iff.2
      simp only [List.all_eq_true]
      constructor
      · intro h L _
        split
        · rfl
        · rename_i hL
          show (!(decide (L' = L))) = true
          by_cases he : L' = L
          · subst he; exact absurd h hL
          · simp [he]
      · intro h
        have := h L' (hls L')
        split at this
        · assumption
        · simp [ohneSperre] at this
  rw [hA, mE_alle, List.all_map]
  apply congrArg (List.all ls); funext L
  simp only [Function.comp_def]
  split
  · rename_i h; rw [h, mE_top]; rfl
  · rename_i h; simp [h]

/-- The probe "does not call `g`, not even through `g`'s signature" (the probe of `ruftB`). -/
def ohneRuf (g : D.Fn) : Merkmal D :=
  ⟨fun h => !(decide (h = g)), fun n => !(decide (n = D.sig g)), fun _ => true⟩

/-- **The call graph feature set** `rufM fs Z` is the conjunction, over the complete function list, of "does not call
    `g`" for every `g` outside `Z`. -/
theorem rufM_zerlegt (fs : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs) (Z : D.Fn → Bool)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    mE (rufM fs Z) e = fs.all fun g => Z g || mE (ohneRuf g) e := by
  have hA : rufM fs Z = Merkmal.alle (fs.map fun g => if Z g then Merkmal.top else ohneRuf g) := by
    apply Merkmal.gleich
    · intro h
      rw [alle_ruf]; simp only [List.all_map, Function.comp_def]
      show Z h = _
      apply Bool.eq_iff_iff.2
      simp only [List.all_eq_true]
      constructor
      · intro hz g _
        split
        · rfl
        · rename_i hg
          show (!(decide (h = g))) = true
          by_cases he : h = g
          · subst he; exact absurd hz hg
          · simp [he]
      · intro hh
        have := hh h (hvoll h)
        split at this
        · assumption
        · simp [ohneRuf] at this
    · intro n
      rw [alle_ind]; simp only [List.all_map, Function.comp_def]
      show (fs.all fun g => !(decide (D.sig g = n)) || Z g) = _
      apply congrArg (List.all fs); funext g
      split
      · rename_i h; simp [h, Merkmal.top]
      · rename_i h
        simp only [h, ohneRuf, Bool.or_false]
        by_cases he : D.sig g = n
        · subst he; simp
        · simp [he, Ne.symm he]
    · intro L
      rw [alle_sperre]; simp only [List.all_map, Function.comp_def]
      symm; apply List.all_eq_true.2; intro g _; split <;> rfl
  rw [hA, mE_alle, List.all_map]
  apply congrArg (List.all fs); funext g
  simp only [Function.comp_def]
  split
  · rename_i h; rw [h, mE_top]; rfl
  · rename_i h; simp [h]

theorem nimmtB_eq (P : Programm D) (f : D.Fn) (L : D.Lock) : nimmtB P f L = !(mE (ohneSperre L) (P.rumpf f)) := rfl

theorem ruftB_eq (P : Programm D) (f g : D.Fn) : ruftB P f g = !(mE (ohneRuf g) (P.rumpf f)) := rfl

end Gabbro.Grammatik.Gen
