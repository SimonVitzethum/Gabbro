module
public import Bruecke.Teil.Quelle
public import Bruecke.Anweisung.Lokal.QuelleB
@[expose] public section

/-!
# Partial bridge duties for bodies with local bindings

The carried call-closed set owes binder freshness and Body duties over `zuBodyB`.
Open body, interface and start duties are exactly those of the partial bridge.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Carried functions satisfy the partial shape conditions and have fresh local binders. -/
structure GetragenB (u : UProg) (C : Fin u.fns.length → Prop) : Prop extends Getragen u C where
  frisch : ∀ c, C c → BindFrisch (fnAt u c)

/-- Partial source duties, with Body translation through local bindings. -/
def PflichtenTeilB (src : String) {u : UProg} (C : Fin u.fns.length → Prop) : Prop :=
  uOf src = some u ∧ nullB u = true ∧ GetragenB u C ∧ rangB u (rangAuto u) = true ∧
    SchnittstellenPflichtTeil u C ∧
    (∀ c, C c → ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) ∧ OffenePflicht u C

/-- Binder-free partial duties already establish the freshness of every carried body. -/
theorem getragenB_of_getragen {u : UProg} {C : Fin u.fns.length → Prop}
    (S : Getragen u C)
    (hZ : ∀ c, C c → ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) : GetragenB u C := by
  refine { toGetragen := S, frisch := fun c hc => ?_ }
  obtain ⟨body, hbody, _⟩ := hZ c hc
  apply bindFrischB_ok
  rw [zuBody_eq] at hbody
  cases hs : stmtsBody u (fnAt u c) (fnAt u c).body with
  | none => rw [hs] at hbody; cases hbody
  | some bs => exact bindFrischLB_ohne _ _ bs hs

/-- The previous partial duties imply the binding-aware duties for the same carried set. -/
theorem pflichtenTeilB_of_pflichtenTeil {src : String} {u : UProg}
    {C : Fin u.fns.length → Prop} (hp : PflichtenTeil src C) : PflichtenTeilB src C := by
  obtain ⟨hu, hn, S, hr, hPtr, hZ, hOpen⟩ := hp
  refine ⟨hu, hn, getragenB_of_getragen S hZ, hr, hPtr, fun c hc => ?_, hOpen⟩
  obtain ⟨body, hbody, hm⟩ := hZ c hc
  exact ⟨body, zuBodyB_of_zuBody hbody, hm⟩

end Gabbro.Bruecke
