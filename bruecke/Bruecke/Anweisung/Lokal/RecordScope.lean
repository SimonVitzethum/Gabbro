module
public import Bruecke.Anweisung.Lokal.BoolScope
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- A record local has the same exact type in the source and runtime scope views. -/
theorem Sicht.bindRecord {fT fn : UFn} (h : Sicht u fT fn) (x : String) (id : Nat) (fs : List Ty) :
    Sicht u (fT.mitWert x (.prod id fs)) (fn.mitWert x (.prod id fs)) := by
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
  · change paramPos ((x, .prod id fs) :: fT.params) p = paramPos ((x, .prod id fs) :: fn.params) p
    unfold paramPos
    rw [h.2.2.2.1 p]
  · by_cases hp : (x == p) = true
    · simp [valueParamTy, UFn.mitWert, hp]
    · have hp' : (x == p) = false := Bool.eq_false_iff.mpr hp
      simpa only [valueParamTy, UFn.mitWert, List.find?_cons, hp', Bool.false_eq_true,
        ↓reduceIte] using h.2.2.2.2 p

theorem artStimmt_mitRecord {fn : UFn} {x : String} (id : Nat) (fs : List Ty)
    (h : ArtStimmt fn) (hx : x ≠ "#erg") : ArtStimmt (fn.mitWert x (.prod id fs)) := by
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

/-- Record locals are ordinary by-value locals. Only capability names are protected. -/
theorem UmfangB.bindRecord {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {x : String} (hx : NameFrisch (protectedNames fn.params fn.kinds) x) (id : Nat) (fs : List Ty) :
    UmfangB (.prod id fs :: Γ) (fn.mitWert x (.prod id fs)) (ns.push x) := by
  have hn := BodyNames.valid_push h.valid x
  refine ⟨?_, artStimmt_mitRecord id fs h.art hx.2.2.1, hn.1,
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
        change paramPos ((x, .prod id fs) :: fn.params) y = .ok (j + 1)
        simp only [paramPos, beq_iff_eq, hxy, ↓reduceIte, h.pointer j y cap ht]

/-- The runtime relation already stores arbitrary typed values; only the source-scope
    header differs from the numeric push theorem. -/
theorem PositionalLRel.pushRecord {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    (x name : String) (id : Nat) (fs : List Ty) (hi : name ∉ ids) (v : Wert D (.prod id fs)) :
    PositionalLRel (fn.mitWert x (.prod id fs)) (name :: ids) 0 (Env.cons v ρ)
      (Gabbro.Body.bindLocal β name (valOf (.prod id fs) v)) := by
  have hp := h.push x name (0, 0) hi v
  exact ⟨hp.length, hp.distinct, hp.values⟩

end Gabbro.Bruecke
