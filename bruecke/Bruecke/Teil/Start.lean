module
public import Bruecke.Teil.Pflichten
@[expose] public section

/-!
# The explicit initial requirement of open starts

Carried functions have empty `needs`; open functions owe their actual lowered requirement at
all declared starts. Body duties never establish an initial requirement by assuming it.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The lowering's trivial requirement fact needs only this function's empty `needs`. -/
theorem requires_tru_of_needs_leer {u : UProg} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (h : lowerAllg u = .ok (P, fs))
    (c : Fin u.fns.length) (hn : (fnAt u c).needs = []) : P.requires c = .tru := by
  unfold lowerAllg at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · obtain ⟨rfl, -⟩ := Gabbro.Grammatik.Parser.Measures.checkedProgram_eq h
        simp only [progOfFn, reqOf, hn, ↓reduceIte]
      · cases h

/-- Open roots owe their requirement at the unit's actual initial world and arguments. -/
def OffeneStartPflicht (u : UProg) (C : Fin u.fns.length → Prop)
    (P : Programm (declOf u)) (hn : nullB u = true) : Prop :=
  ∀ a ∈ (einheitAllg u P hn).starts ++ (einheitAllg u P hn).gestartet,
    ¬ C a.1 → ReqAmEintritt P a.1 ((einheitAllg u P hn).sp0.welt []) a.2

/-- The open-root duty and the carried empty requirements supply the whole start duty. -/
theorem startPflicht_teil {u : UProg} {C : Fin u.fns.length → Prop}
    {P : Programm (declOf u)} {fs : List (declOf u).Fn} {hn : nullB u = true}
    (hlow : lowerAllg u = .ok (P, fs)) (S : Getragen u C)
    (hO : OffeneStartPflicht u C P hn) :
    Zielsatz.StartPflicht (einheitAllg u P hn) := by
  classical
  refine ⟨fun _ => rfl, fun a ha => ?_⟩
  by_cases hc : C a.1
  · unfold ReqAmEintritt
    show wahr? (eval _ (P.requires a.1) _ a.2) = true
    rw [requires_tru_of_needs_leer hlow a.1 (S.ohneReq a.1 hc)]
    rfl
  · exact hO a ha hc

/-- A single open start with an impossible requirement refutes the new duty. -/
theorem offeneStartPflicht_refused_teil {u : UProg} {C : Fin u.fns.length → Prop}
    {P : Programm (declOf u)} {hn : nullB u = true}
    (a : Σ c : (declOf u).Fn, Env (declOf u) ((declOf u).params c))
    (ha : a ∈ (einheitAllg u P hn).starts ++ (einheitAllg u P hn).gestartet)
    (hc : ¬ C a.1)
    (hreq : ¬ ReqAmEintritt P a.1 ((einheitAllg u P hn).sp0.welt []) a.2) :
    ¬ OffeneStartPflicht u C P hn :=
  fun h => hreq (h a ha hc)

end Gabbro.Bruecke
