module
public import Bruecke.Anweisung.Lokal.Position
public import Bruecke.Anweisung.Lokal.Benannt
@[expose] public section

/-! # Bool scopes use the same positional identifiers as numeric scopes -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

theorem mitBindungB_ctx (fn : UFn) (x : String) :
    (fn.mitBindungB x).params.map (·.2) = .bool :: fn.params.map (·.2) := rfl

theorem Sicht.bindB {fT fn : UFn} (h : Sicht u fT fn) (x : String) :
    Sicht u (fT.mitBindungB x) (fn.mitBindungB x) := by
  refine ⟨fun p => ?_, fun p => ?_, fun t => ?_, fun p => ?_, fun p => ?_⟩
  · by_cases hx : (x == p) = true
    · simp only [numericParam, UFn.mitBindungB, List.find?_cons, hx, ↓reduceIte]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [numericParam, UFn.mitBindungB, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.1 p
  · by_cases hx : (x == p) = true
    · simp only [ptrTab, UFn.mitBindungB, List.find?_cons, hx, ↓reduceIte]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [ptrTab, UFn.mitBindungB, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.2.1 p
  · exact h.2.2.1 t
  · change paramPos ((x, .bool) :: fT.params) p = paramPos ((x, .bool) :: fn.params) p
    unfold paramPos
    rw [h.2.2.2.1 p]
  · by_cases hx : (x == p) = true
    · simp [valueParamTy, UFn.mitBindungB, hx]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [valueParamTy, UFn.mitBindungB, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.2.2.2.2 p

theorem artStimmt_mitBindungB {fn : UFn} {x : String}
    (h : ArtStimmt fn) (hx : x ≠ "#erg") : ArtStimmt (fn.mitBindungB x) := by
  refine ⟨fun j num wb hk => ?_, fun k hk => ?_, fun q hq => ?_⟩
  · cases j with
    | zero => simp [UFn.mitBindungB] at hk
    | succ j =>
      have hk' : fn.kinds[j]? = some (.ptr (.table num (true, wb))) := hk
      obtain ⟨w', hw'⟩ := h.1 j num wb hk'
      exact ⟨w', hw'⟩
  · simp only [UFn.mitBindungB, List.mem_cons] at hk
    rcases hk with rfl | hk
    · rfl
    · exact h.2.1 k hk
  · simp only [UFn.mitBindungB, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp [ParamSchlicht, TySchlicht, hx]
    · exact h.2.2 q hq

theorem UmfangB.bindB {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {x : String} (hx : NameFrisch (protectedNames fn.params fn.kinds) x) :
    UmfangB (.bool :: Γ) (fn.mitBindungB x) (ns.push x) := by
  have hn := BodyNames.valid_push h.valid x
  refine ⟨?_, artStimmt_mitBindungB h.art hx.2.2.1, hn.1,
    congrArg Nat.succ h.length, hn.2, ?_⟩
  · rw [h.ctx, mitBindungB_ctx]
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
      change paramPos ((x, .bool) :: fn.params) y = .ok (j + 1)
      simp only [paramPos, beq_iff_eq, hxy, ↓reduceIte, h.pointer j y cap ht]

theorem PositionalLRel.pushB {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    (x id : String) (hi : id ∉ ids) (v : Wert D .bool) :
    PositionalLRel (fn.mitBindungB x) (id :: ids) 0 (Env.cons v ρ)
      (Gabbro.Body.bindLocal β id (valOf .bool v)) := by
  have hp := h.push (τ := .bool) x id (0, 0) hi v
  exact ⟨hp.length, hp.distinct, hp.values⟩

theorem PositionalLRel.tailB {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {id x : String} {ρ : Env D (.bool :: Γ)} {β : Gabbro.Body.Binding}
    (h : PositionalLRel (fn.mitBindungB x) (id :: ids) 0 ρ β) :
    PositionalLRel fn ids 0 ρ.tail β := by
  have hn : PositionalLRel (fn.mitBindung x (0, 0)) (id :: ids) 0 ρ β :=
    ⟨h.length, h.distinct, h.values⟩
  exact hn.tail

end Gabbro.Bruecke
