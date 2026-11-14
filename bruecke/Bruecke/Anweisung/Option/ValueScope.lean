module
public import Bruecke.Anweisung.Option.Scope
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- A by-value option local has the same exact type in the source and runtime scope views. -/
theorem Sicht.bindOptionValue {fT fn : UFn} (h : Sicht u fT fn) (x : String) (cnt : Int) :
    Sicht u (fT.mitWert x (.opt cnt)) (fn.mitWert x (.opt cnt)) := by
  refine ⟨fun p => ?_, fun p => ?_, fun t => ?_, fun p => ?_, fun p => ?_⟩
  · by_cases hp : (x == p) = true
    · simp [numericParam, UFn.mitWert, hp]
    · have hp' : (x == p) = false := Bool.eq_false_iff.mpr hp
      simpa only [numericParam, UFn.mitWert, List.find?_cons, hp', Bool.false_eq_true,
        ↓reduceIte] using h.1 p
  · by_cases hp : (x == p) = true
    · simp [ptrTab, UFn.mitWert, hp]
    · have hp' : (x == p) = false := Bool.eq_false_iff.mpr hp
      simpa only [ptrTab, UFn.mitWert, List.find?_cons, hp', Bool.false_eq_true,
        ↓reduceIte] using h.2.1 p
  · simpa only [ptrParam, UFn.mitWert, List.filter_cons, Bool.false_eq_true, ↓reduceIte] using h.2.2.1 t
  · change paramPos ((x, .opt cnt) :: fT.params) p = paramPos ((x, .opt cnt) :: fn.params) p
    unfold paramPos
    rw [h.2.2.2.1 p]
  · by_cases hp : (x == p) = true
    · simp [valueParamTy, UFn.mitWert, hp]
    · have hp' : (x == p) = false := Bool.eq_false_iff.mpr hp
      simpa only [valueParamTy, UFn.mitWert, List.find?_cons, hp', Bool.false_eq_true,
        ↓reduceIte] using h.2.2.2.2 p

theorem artStimmt_mitOptionValue {fn : UFn} {x : String} (cnt : Int)
    (h : ArtStimmt fn) (hx : x ≠ "#erg") : ArtStimmt (fn.mitWert x (.opt cnt)) := by
  refine ⟨fun j num wb hk => ?_, fun k hk => ?_, fun q hq => ?_⟩
  · cases j with
    | zero => simp [UFn.mitWert, uArtVon] at hk
    | succ j =>
        have hk' : fn.kinds[j]? = some (.ptr (.table num (true, wb))) := hk
        obtain ⟨w', hw'⟩ := h.1 j num wb hk'
        exact ⟨w', hw'⟩
  · simp only [UFn.mitWert, List.mem_cons] at hk
    rcases hk with rfl | hk
    · rfl
    · exact h.2.1 k hk
  · simp only [UFn.mitWert, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp [ParamSchlicht, TySchlicht, hx]
    · exact h.2.2 q hq

/-- Option locals are ordinary by-value locals. Only capability names are protected. -/
theorem UmfangB.bindOptionValue {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {x : String} (hx : NameFrisch (protectedNames fn.params fn.kinds) x) (cnt : Int) :
    UmfangB (.opt cnt :: Γ) (fn.mitWert x (.opt cnt)) (ns.push x) := by
  have hn := BodyNames.valid_push h.valid x
  refine ⟨?_, artStimmt_mitOptionValue cnt h.art hx.2.2.1, hn.1,
    congrArg Nat.succ h.length, hn.2, ?_⟩
  · exact congrArg (List.cons _) h.ctx
  · intro j y cap hj
    cases j with
    | zero => cases hj
    | succ j =>
        have ht : fn.params[j]? = some (y, .ptr cap) := hj
        have hxy : x ≠ y := by
          intro he
          apply hx.1
          rw [he]
          exact pointer_mem_protected fn.params fn.kinds j y cap ht
        change paramPos ((x, .opt cnt) :: fn.params) y = .ok (j + 1)
        simp only [paramPos, beq_iff_eq, hxy, ↓reduceIte, h.pointer j y cap ht]

/-- The runtime relation already stores arbitrary typed values; only the source-scope
    header differs from the numeric push theorem. -/
theorem PositionalLRel.pushOptionValue {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    (x name : String) (cnt : Int) (hi : name ∉ ids) (v : Wert D (.opt cnt)) :
    PositionalLRel (fn.mitWert x (.opt cnt)) (name :: ids) 0 (Env.cons v ρ)
      (Gabbro.Body.bindLocal β name (valOf (.opt cnt) v)) := by
  have hp := h.push x name (0, 0) hi v
  exact ⟨hp.length, hp.distinct, hp.values⟩

end Gabbro.Bruecke
