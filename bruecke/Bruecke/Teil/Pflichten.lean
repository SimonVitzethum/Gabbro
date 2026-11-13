module
public import Bruecke.Quelle
@[expose] public section

/-!
# Per-function bridge duties

This is the duty-definition checkpoint of the partial bridge. The function predicate is tied
explicitly to the elaborated unit by `uOf src = some u`. Shape checks for tables, invariants,
statics and the rank remain global. Pointer refinement is split by the same function predicate.

These duties do NOT yet imply `NutzerPflicht`: an open declared root can have a nontrivial
`requires`. Its body duty assumes that predicate and cannot establish it at startup. A complete
partial bridge needs an additional start duty for open roots (or a restriction on the roots).
No source-to-`NutzerPflicht` theorem is claimed here.
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
  ohneReq : ∀ c, C c → (fnAt u c).needs = []
  ohneGrund : ∀ c, C c → (fnAt u c).gruende = 0
  ohneInv : u.invs = []
  ohneGlob : u.globs = []
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

/-- Source duties with Body proofs only on the carried call-closed set. Unlike `Pflichten`,
    the dependent unit is an implicit parameter; the first conjunct fixes it to the source's
    actual elaboration. This checkpoint still lacks the open-root part of `StartPflicht`. -/
def PflichtenTeil (src : String) {u : UProg} (C : Fin u.fns.length → Prop) : Prop :=
  uOf src = some u ∧ nullB u = true ∧ Getragen u C ∧ rangB u (rangAuto u) = true ∧
    SchnittstellenPflichtTeil u C ∧
    (∀ c, C c → ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) ∧ OffenePflicht u C

/-- Taking every function preserves all structural checks of the existing bridge. -/
theorem getragen_of_stimmig {u : UProg} (S : Stimmig u) :
    Getragen u (fun _ => True) where
  geschlossen := fun _ _ _ _ _ _ => True.intro
  boolTab := S.boolTab
  boolErg := fun c _ => S.boolErg c
  tab := S.tab
  art := fun c _ => S.art c
  namen := fun c _ => S.namen c
  frei := fun c _ => S.frei c
  olds := fun c _ => S.olds c
  post := fun c _ => S.post c
  schreibt := fun c _ => S.schreibt c
  ohneReq := fun c _ => S.ohneReq c
  ohneGrund := fun c _ => S.ohneGrund (fnAt u c) (List.get_mem _ _)
  ohneInv := S.ohneInv
  ohneGlob := S.ohneGlob
  ohneTransition := fun c _ => S.ohneTransition c

/-- Existing source duties imply the all-carried partial duties, for the very same elaboration. -/
theorem pflichtenTeil_of_pflichten {src : String} (hp : Pflichten src) :
    ∃ u : UProg, PflichtenTeil src (u := u) (fun _ => True) := by
  obtain ⟨u, hu, hn, hs, hr, hPlain, hPtr, hz⟩ := hp
  refine ⟨u, hu, hn, getragen_of_stimmig (stimmig_of hs hPlain), hr, ?_,
    fun c _ => hz c, ?_⟩
  · intro P fs hlow c _ n hf
    exact hPtr P fs hlow c n hf
  · intro c hc
    exact (hc True.intro).elim

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
