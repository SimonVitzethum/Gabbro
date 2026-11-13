module
public import Bruecke.Quelle
@[expose] public section

/-!
# Carried shape and explicit open duties

`Getragen` restricts function shape conditions to a call-closed carried set. The global table,
invariant and static conditions remain unchanged. `OffenePflicht` supplies canonical body
and interface duties for its complement; `Teil/Start` states the separate open-root duty.
`Kette/` assembles those duties with the carried Body simulation.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The old structural conditions, restricted to carried functions, except for the unchanged
    global table, invariant and static conditions. Successful Body reading resolves calls;
    closure here requires every resolved direct callee to be carried. -/
structure Getragen (u : UProg) (C : Fin u.fns.length → Prop) : Prop where
  geschlossen : ∀ c, C c → ∀ n ∈ calleesOf (fnAt u c), ∀ d,
    fnSuch u n = some (fnAt u d) → C d
  boolTab : ∀ t : Fin u.tabs.length,
    (tabAt u t).bools = [] ∧ (tabAt u t).opts = [] ∧ (tabAt u t).werte = []
  boolErg : ∀ c, C c → ErgSchlicht (fnAt u c)
  tab : TabEindeutig u
  art : ∀ c, C c → ArtStimmt (fnAt u c)
  namen : ∀ c, C c → NamenEindeutig (fnAt u c)
  frei : ∀ c, C c → NamenFrei (fnAt u c)
  olds : ∀ c, C c → OldsKurz u (fnAt u c)
  post : ∀ c, C c → PostDef u (fnAt u c)
  schreibt : ∀ c, C c → ∀ w ∈ (fnAt u c).puts, ∃ t, (tabAt u t).name = w
  gschreibt : ∀ c, C c → ∀ w ∈ (fnAt u c).gputs, ∃ g, (globAt u g).name = w
  ohneReq : ∀ c, C c → (fnAt u c).needs = []
  ohneGrund : ∀ c, C c → (fnAt u c).gruende = 0
  ohneInv : u.invs = []
  statics : NumericStatics u
  ohneTransition : ∀ c, C c → transitionOfFn u c = none

/-- O43 for carried targets. The complementary targets owe the very same canonical
    `PtrZielVerfeinert`, in `OffenePflicht`. -/
def SchnittstellenPflichtTeil (u : UProg) (C : Fin u.fns.length → Prop) : Prop :=
  ∀ (P : Programm (declOf u)) (fs : List (declOf u).Fn), lowerAllg u = .ok (P, fs) →
    ∀ c, C c → ∀ n (hf : (declOf u).passt c n = true), PtrZielVerfeinert P c n hf

/-- Exactly the nonautomatic function components of `LogikPflicht` for open functions.
    Both invariant-return components follow from the unchanged `u.invs = []`, including reason
    returns; no assumption about the open functions' reason channels is needed for those.
    This is a logic duty, not the missing initial-memory duty for an open declared root. -/
def OffenePflicht (u : UProg) (C : Fin u.fns.length → Prop) : Prop :=
  ∀ c, ¬ C c → ∀ (P : Programm (declOf u)) (fs : List (declOf u).Fn),
    lowerAllg u = .ok (P, fs) →
      (∀ passes, KoerperGutS P passes (axWahr (declOf u)) (SperrInv.leer (declOf u)) c) ∧
      ∀ n (hf : (declOf u).passt c n = true), PtrZielVerfeinert P c n hf

/-- Reassemble O43 without imposing carried-target duties on open targets. -/
theorem schnittstellen_aus_teil {u : UProg} {C : Fin u.fns.length → Prop}
    (hC : SchnittstellenPflichtTeil u C) (hO : OffenePflicht u C) :
    SchnittstellenPflicht u := by
  classical
  intro P fs hlow c n hf
  by_cases hc : C c
  · exact hC P fs hlow c hc n hf
  · exact (hO c hc P fs hlow).2 n hf

/-- Empty declared invariants discharge BOTH return-invariant components for EVERY function.
    In particular, open reason channels need no extra invariant premise. -/
theorem invPflichten_teil {u : UProg} {C : Fin u.fns.length → Prop} (S : Getragen u C)
    (P : Programm (declOf u)) (passes : Nat) (c : (declOf u).Fn) :
    InvGutS P passes (axWahr (declOf u)) (SperrInv.leer (declOf u)) c ∧
    Zielsatz.InvGutGrund P passes (axWahr (declOf u)) (SperrInv.leer (declOf u)) c := by
  have hi : List.finRange u.invs.length = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, S.ohneInv]; rfl)
  refine ⟨invGutS_leer hi c, ?_⟩
  intro O hR hL hQ U hU R hRR hOV σ ρ hreq σ' r hrun i him
  have him' : i ∈ List.finRange u.invs.length := him
  rw [hi] at him'
  cases him'

/-- Assemble the logic part once the carried Body-to-G simulation has supplied its per-function
    body component. This lemma makes no claim to supply that missing simulation. -/
theorem logik_aus_teilpflichten {u : UProg} {C : Fin u.fns.length → Prop}
    (S : Getragen u C) (hC : SchnittstellenPflichtTeil u C) (hO : OffenePflicht u C)
    {P : Programm (declOf u)} {fs : List (declOf u).Fn} (hlow : lowerAllg u = .ok (P, fs))
    (hK : ∀ passes c, C c →
      KoerperGutS P passes (axWahr (declOf u)) (SperrInv.leer (declOf u)) c) :
    Zielsatz.LogikPflicht P (SperrInv.leer (declOf u)) (axWahr (declOf u)) := by
  classical
  refine ⟨fun passes c => ⟨?_, invPflichten_teil S P passes c⟩,
    fun _ _ _ _ => rfl, axEnsLokal_wahr, schnittstellen_aus_teil hC hO P fs hlow⟩
  by_cases hc : C c
  · exact hK passes c hc
  · exact (hO c hc P fs hlow).1 passes

end Gabbro.Bruecke
