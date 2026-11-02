module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Logik.Vertraege.EinpassenVoll.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- A `tagged` case has a payload value: a bare case always, a payload case when its range
    is not empty. -/
def nutzBar : Option Ty → Bool
  | none => true
  | some (.int lo hi) => decide (lo ≤ hi)
  | some _ => false

theorem nutzBar_iff : ∀ c : Option Ty,
    nutzBar c = true ↔ ∃ x : Nutzlast D.Fn D.passt c, nutzWort c
  | none => ⟨fun _ => ⟨(), trivial⟩, fun _ => rfl⟩
  | some τ => by
      cases τ <;> try simp only [nutzBar, nutzWort, Bool.false_eq_true, exists_false]
      rename_i lo hi
      simp only [nutzBar, nutzWort, decide_eq_true_eq]
      exact ⟨fun h => ⟨(⟨lo, Int.le_refl _, h⟩ : Zahl lo hi), trivial⟩,
        fun ⟨z, _⟩ => Int.le_trans z.lo_le z.le_hi⟩

/-- **A type has an answer, decided** over the program's function list `fs` (a function
    pointer's type is inhabited exactly by the functions of its signature). -/
def antwortTyB (fs : List D.Fn) : Ty → Bool
  | .int lo hi => decide (lo ≤ hi)
  | .bool => true
  | .opt _ => true
  | .sum cs => sumWort cs && cs.any nutzBar
  | .why n => decide (n ≠ 0)
  | .never => false
  | .fl lo hi => gleitBarB lo hi
  | .fnptr m => fs.any fun f => D.passt f m
  | .ptr _ => true
  | .ref _ => true
  | .arr _ _ => false
  | .str _ => false

/-- An answer class is not empty, decided (a call without a result always answers). -/
def antwortB (fs : List D.Fn) : Option Ty → Bool
  | Option.none => true
  | Option.some τ => antwortTyB fs τ

theorem antwortTyB_iff {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) :
    ∀ τ : Ty, antwortTyB fs τ = true ↔ ∃ v : Wert D τ, WertOk τ v
  | .int lo hi => by
      simp only [antwortTyB, decide_eq_true_eq]
      exact ⟨fun h => ⟨(⟨lo, Int.le_refl _, h⟩ : Zahl lo hi), trivial⟩,
        fun ⟨z, _⟩ => Int.le_trans (z : Zahl lo hi).lo_le (z : Zahl lo hi).le_hi⟩
  | .bool => ⟨fun _ => ⟨(true : Bool), trivial⟩, fun _ => rfl⟩
  | .opt _ => ⟨fun _ => ⟨(Option.none : Option (Zahl _ _)), trivial⟩, fun _ => rfl⟩
  | .sum cs => by
      simp only [antwortTyB, Bool.and_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨hs, c, hc, hb⟩
        obtain ⟨i, rfl⟩ := List.get_of_mem hc
        obtain ⟨x, _⟩ := (nutzBar_iff _).mp hb
        exact ⟨(⟨i, x⟩ : Wert D (.sum cs)), hs⟩
      · rintro ⟨⟨i, x⟩, hs⟩
        exact ⟨hs, cs.get i, List.get_mem cs i,
          (nutzBar_iff _).mpr ⟨x, sumWort_get cs hs i⟩⟩
  | .why n => by
      simp only [antwortTyB, decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨(⟨0, Nat.pos_of_ne_zero h⟩ : Fin n), trivial⟩
      · rintro ⟨r, _⟩ h
        subst h
        exact (r : Fin 0).elim0
  | .never => ⟨fun h => absurd h (by simp only [antwortTyB, Bool.false_eq_true, not_false_eq_true]), fun h => by
      obtain ⟨v, _⟩ := h
      exact (v : Empty).elim⟩
  | .fl lo hi => by
      simp only [antwortTyB]
      rw [gleitBarB_iff]
      exact ⟨fun ⟨v, hv⟩ => ⟨v, hv⟩, fun ⟨v, hv⟩ => ⟨v, hv⟩⟩
  | .fnptr m => by
      simp only [antwortTyB, List.any_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨f, _, hf⟩ => ⟨(⟨f, hf⟩ : {f : D.Fn // D.passt f m = true}), trivial⟩,
        fun ⟨v, _⟩ => ⟨(v : {f : D.Fn // D.passt f m = true}).1, hvoll _, v.2⟩⟩
  | .ptr _ => ⟨fun _ => ⟨(() : Unit), trivial⟩, fun _ => rfl⟩
  | .ref _ => ⟨fun _ => ⟨(Val.vonZelle 0 : Wert D (.ref _)), trivial⟩, fun _ => rfl⟩
  | .arr _ _ => ⟨fun h => absurd h (by simp only [antwortTyB, Bool.false_eq_true, not_false_eq_true]), fun ⟨_, h⟩ => h.elim⟩
  | .str _ => ⟨fun h => absurd h (by simp only [antwortTyB, Bool.false_eq_true, not_false_eq_true]), fun ⟨_, h⟩ => h.elim⟩

/-- **The answer class, decided exactly** (W1): given the complete function list, the Bool
    says "answerable" exactly when the class is not empty (`antwortLeer_iff`). -/
theorem antwortB_iff {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (e : Option Ty) :
    antwortB fs e = true ↔ ¬ AntwortLeer D e := by
  cases e with
  | none => exact ⟨fun _ => antwortLeer_keinErg, fun _ => rfl⟩
  | some τ =>
      show antwortTyB fs τ = true ↔ _
      rw [antwortTyB_iff hvoll τ, antwortLeer_iff]
      constructor
      · rintro ⟨v, hv⟩ h
        exact h v hv
      · intro h
        exact Classical.byContradiction fun hn => h fun v hv => hn ⟨v, hv⟩

#print axioms Gabbro.Grammatik.flt_trans_endlich
#print axioms Gabbro.Grammatik.gleitBarB_iff
#print axioms Gabbro.Grammatik.antwortB_iff
#print axioms Gabbro.Grammatik.summePasst_voll
#print axioms Gabbro.Grammatik.gleitWortPasst_voll
#print axioms Gabbro.Grammatik.einpassen_voll
#print axioms Gabbro.Grammatik.antwortLeer_iff

end Gabbro.Grammatik
