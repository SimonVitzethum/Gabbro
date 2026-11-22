module
public import Bruecke.Anweisung.Lokal.Position
public import Bruecke.Anweisung.Lokal.Benannt
@[expose] public section

/-! # Bare tagged locals keep their declared type in source scopes

`let x = T::C;` (or a copy of a tagged local) binds `x` to a value of the bare tagged type `T`:
every case of `T` without payload. The scope after it (`UFn.mitSum`) keeps every visibility fact of
the bridge, as for option locals (`Option/Scope.lean`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

theorem mitSum_ctx (fn : UFn) (x : String) (num : Nat) (cs : List (Option Ty)) :
    (fn.mitSum x num cs).params.map (·.2) = (.sum cs) :: fn.params.map (·.2) := rfl

theorem protectedNames_mitSum (fn : UFn) (x : String) (num : Nat) (cs : List (Option Ty)) :
    protectedNames (fn.mitSum x num cs).params (fn.mitSum x num cs).kinds =
      protectedNames fn.params fn.kinds := by
  simp only [UFn.mitSum, protectedNames]

theorem Sicht.bindSum {fT fn : UFn} (h : Sicht u fT fn) (x : String) (num : Nat) (cs : List (Option Ty)) :
    Sicht u (fT.mitSum x num cs) (fn.mitSum x num cs) := by
  refine ⟨fun p => ?_, fun p => ?_, fun t => ?_, fun p => ?_, fun p => ?_⟩
  · by_cases hx : (x == p) = true
    · simp only [numericParam, UFn.mitSum, List.find?_cons, hx, ↓reduceIte]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [numericParam, UFn.mitSum, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.1 p
  · by_cases hx : (x == p) = true
    · simp only [ptrTab, UFn.mitSum, List.find?_cons, hx, ↓reduceIte]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [ptrTab, UFn.mitSum, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.2.1 p
  · exact h.2.2.1 t
  · change paramPos ((x, (.sum cs)) :: fT.params) p = paramPos ((x, (.sum cs)) :: fn.params) p
    unfold paramPos
    rw [h.2.2.2.1 p]
  · by_cases hx : (x == p) = true
    · simp [valueParamTy, UFn.mitSum, hx]
    · have hx' : (x == p) = false := Bool.eq_false_iff.mpr hx
      simpa only [valueParamTy, UFn.mitSum, List.find?_cons, hx', Bool.false_eq_true,
        ↓reduceIte] using h.2.2.2.2 p

theorem artStimmt_mitSum {fn : UFn} {x : String} (num : Nat) {cs : List (Option Ty)}
    (hb : cs.all Option.isNone = true) (h : ArtStimmt fn) (hx : x ≠ "#erg") :
    ArtStimmt (fn.mitSum x num cs) := by
  refine ⟨fun j n wb hk => ?_, fun k hk => ?_, fun q hq => ?_⟩
  · cases j with
    | zero => simp [UFn.mitSum] at hk
    | succ j =>
      have hk' : fn.kinds[j]? = some (.ptr (.table n (true, wb))) := hk
      obtain ⟨w', hw'⟩ := h.1 j n wb hk'
      exact ⟨w', hw'⟩
  · simp only [UFn.mitSum, List.mem_cons] at hk
    rcases hk with rfl | hk
    · rfl
    · exact h.2.1 k hk
  · simp only [UFn.mitSum, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp [ParamSchlicht, TySchlicht, hx, hb]
    · exact h.2.2 q hq

theorem UmfangB.bindSum {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {x : String} (num : Nat) {cs : List (Option Ty)} (hb : cs.all Option.isNone = true)
    (hx : NameFrisch (protectedNames fn.params fn.kinds) x) :
    UmfangB ((.sum cs) :: Γ) (fn.mitSum x num cs) (ns.push x) := by
  have hn := BodyNames.valid_push h.valid x
  refine ⟨?_, artStimmt_mitSum num hb h.art hx.2.2.1, hn.1,
    congrArg Nat.succ h.length, hn.2, ?_⟩
  · rw [h.ctx, mitSum_ctx]
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
      change paramPos ((x, (.sum cs)) :: fn.params) y = .ok (j + 1)
      simp only [paramPos, beq_iff_eq, hxy, ↓reduceIte, h.pointer j y cap ht]

theorem PositionalLRel.pushSum {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    (x id : String) (num : Nat) (cs : List (Option Ty)) (hi : id ∉ ids) (v : Wert D (.sum cs)) :
    PositionalLRel (fn.mitSum x num cs) (id :: ids) 0 (Env.cons v ρ)
      (Gabbro.Body.bindLocal β id (valOf (.sum cs) v)) := by
  have hp := h.push (τ := (.sum cs)) x id (0, 0) hi v
  exact ⟨hp.length, hp.distinct, hp.values⟩

theorem PositionalLRel.tailSum {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {id x : String} {num : Nat} {cs : List (Option Ty)} {ρ : Env D ((.sum cs) :: Γ)}
    {β : Gabbro.Body.Binding}
    (h : PositionalLRel (fn.mitSum x num cs) (id :: ids) 0 ρ β) :
    PositionalLRel fn ids 0 ρ.tail β := by
  have hn : PositionalLRel (fn.mitBindung x (0, 0)) (id :: ids) 0 ρ β :=
    ⟨h.length, h.distinct, h.values⟩
  exact hn.tail

end Gabbro.Bruecke
