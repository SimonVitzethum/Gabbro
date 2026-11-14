module
public import Bruecke.Anweisung.Lokal.Position
public import Bruecke.Anweisung.Lokal.Benannt
@[expose] public section

/-! # Optional indices retain their table identity in source scopes -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

theorem mitOpt_ctx (fn : UFn) (x : String) (num : Nat) (cnt : Int) :
    (fn.mitOpt x num cnt).params.map (·.2) = (.opt cnt) :: fn.params.map (·.2) := rfl

theorem Sicht.bindOpt {fT fn : UFn} (h : Sicht u fT fn) (x : String) (num : Nat) (cnt : Int) :
    Sicht u (fT.mitOpt x num cnt) (fn.mitOpt x num cnt) := by
  refine ⟨fun p => ?_, fun p => ?_, fun t => ?_, fun p => ?_, fun p => ?_⟩
  · by_cases hx : (x == p) = true
    · simp only [numericParam, UFn.mitOpt, List.find?_cons, hx, ↓reduceIte]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [numericParam, UFn.mitOpt, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.1 p
  · by_cases hx : (x == p) = true
    · simp only [ptrTab, UFn.mitOpt, List.find?_cons, hx, ↓reduceIte]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [ptrTab, UFn.mitOpt, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.2.1 p
  · exact h.2.2.1 t
  · change paramPos ((x, (.opt cnt)) :: fT.params) p = paramPos ((x, (.opt cnt)) :: fn.params) p
    unfold paramPos
    rw [h.2.2.2.1 p]
  · by_cases hx : (x == p) = true
    · simp [valueParamTy, UFn.mitOpt, hx]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [valueParamTy, UFn.mitOpt, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.2.2.2.2 p

theorem artStimmt_mitOpt {fn : UFn} {x : String}
    (num : Nat) (cnt : Int) (h : ArtStimmt fn) (hx : x ≠ "#erg") : ArtStimmt (fn.mitOpt x num cnt) := by
  refine ⟨fun j num wb hk => ?_, fun k hk => ?_, fun q hq => ?_⟩
  · cases j with
    | zero => simp [UFn.mitOpt] at hk
    | succ j =>
      have hk' : fn.kinds[j]? = some (.ptr (.table num (true, wb))) := hk
      obtain ⟨w', hw'⟩ := h.1 j num wb hk'
      exact ⟨w', hw'⟩
  · simp only [UFn.mitOpt, List.mem_cons] at hk
    rcases hk with rfl | hk
    · rfl
    · exact h.2.1 k hk
  · simp only [UFn.mitOpt, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp [ParamSchlicht, TySchlicht, hx]
    · exact h.2.2 q hq

theorem UmfangB.bindOpt {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {x : String} (num : Nat) (cnt : Int) (hx : NameFrisch (protectedNames fn.params fn.kinds) x) :
    UmfangB ((.opt cnt) :: Γ) (fn.mitOpt x num cnt) (ns.push x) := by
  have hn := BodyNames.valid_push h.valid x
  refine ⟨?_, artStimmt_mitOpt num cnt h.art hx.2.2.1, hn.1,
    congrArg Nat.succ h.length, hn.2, ?_⟩
  · rw [h.ctx, mitOpt_ctx]
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
      change paramPos ((x, (.opt cnt)) :: fn.params) y = .ok (j + 1)
      simp only [paramPos, beq_iff_eq, hxy, ↓reduceIte, h.pointer j y cap ht]

theorem PositionalLRel.pushOpt {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    (x id : String) (num : Nat) (cnt : Int) (hi : id ∉ ids) (v : Wert D (.opt cnt)) :
    PositionalLRel (fn.mitOpt x num cnt) (id :: ids) 0 (Env.cons v ρ)
      (Gabbro.Body.bindLocal β id (valOf (.opt cnt) v)) := by
  have hp := h.push (τ := (.opt cnt)) x id (0, 0) hi v
  exact ⟨hp.length, hp.distinct, hp.values⟩

theorem PositionalLRel.tailOpt {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {id x : String} {num : Nat} {cnt : Int} {ρ : Env D ((.opt cnt) :: Γ)} {β : Gabbro.Body.Binding}
    (h : PositionalLRel (fn.mitOpt x num cnt) (id :: ids) 0 ρ β) :
    PositionalLRel fn ids 0 ρ.tail β := by
  have hn : PositionalLRel (fn.mitBindung x (0, 0)) (id :: ids) 0 ρ β :=
    ⟨h.length, h.distinct, h.values⟩
  exact hn.tail

end Gabbro.Bruecke
