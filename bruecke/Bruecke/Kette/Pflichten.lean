module
public import Bruecke.Teil.Pflichten
public import Bruecke.Anweisung.Lokal.Kopf
public import Bruecke.Anweisung.Zweig.Benannt
public import Bruecke.Anweisung.Lokal.SimulationB
public import Bruecke.Kette.Mass.Pflicht
@[expose] public section

/-!
# One carried chain: local bindings and structured branches

The carried set is closed over the whole flat body, including both branch arms. Integer and
bool source names may repeat; capability and other protected names retain their freshness.
The readers allocate distinct Body identifiers and retain the history across all arms.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Carried shape and call closure, with kind-sensitive local admission. -/
structure GetragenG (u : UProg) (C : Fin u.fns.length → Prop) : Prop extends Getragen u C where
  frisch : ∀ c, C c → BindFrisch (fnAt u c)

/-- Source duties for the carried functions over the branch-aware Body translation.
    Open functions retain their explicit canonical G duties. -/
def PflichtenTeilG (src : String) {u : UProg} (C : Fin u.fns.length → Prop) : Prop :=
  uOf src = some u ∧ nullB u = true ∧ GetragenG u C ∧ rangB u (rangAuto u) = true ∧
    (∀ c, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body) ∧ OffenePflicht u C

/-- Per-unit duties through the consolidated branch-aware translation. All structural
    conditions are Boolean checks; pointer refinement is no user duty (owner, 2026-11-20). -/
def PflichtenAlle (src : String) : Prop :=
  ∃ u : UProg, uOf src = some u ∧ nullB u = true ∧ stimmigB u = true ∧
    bindFrischAllB u = true ∧ rangB u (rangAuto u) = true ∧ ohneTransitionB u = true ∧
    ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body

/-- Decided per-unit checks supply the all-carried shape and freshness conditions. -/
theorem getragenG_of_bools {u : UProg} (hs : stimmigB u = true)
    (hPlain : ohneTransitionB u = true) (hf : bindFrischAllB u = true) :
    GetragenG u (fun _ => True) := by
  simp only [stimmigB, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨hk, ht⟩, hq⟩, hi⟩, hg⟩, hfn⟩ := hs
  have hc : ∀ c : Fin u.fns.length, (artB (fnAt u c) && namenB (fnAt u c) && freiB (fnAt u c) &&
      oldsB u (fnAt u c) && postB u (fnAt u c) && schreibtB u (fnAt u c)) = true :=
    fun c => List.all_eq_true.mp hfn _ (List.get_mem _ _)
  simp only [Bool.and_eq_true] at hc
  refine { toGetragen := {
    geschlossen := fun _ _ _ _ _ _ => True.intro
    boolTab := (keinBoolB_ok hk).1
    boolErg := fun c _ => (keinBoolB_ok hk).2 c
    tab := tabB_ok ht
    art := fun c _ => artB_ok (hc c).1.1.1.1.1
    namen := fun c _ => (of_decide_eq_true (hc c).1.1.1.1.2 :
      ((fnAt u c).params.map (·.1)).Nodup)
    frei := fun c _ => freiB_ok (hc c).1.1.1.2
    olds := fun c _ => oldsB_ok (hc c).1.1.2
    post := fun c _ => postB_ok (hc c).1.2
    schreibt := fun c _ => schreibtB_ok (hc c).2
    gschreibt := fun c _ => gschreibtB_ok (hc c).2
    ohneReq := fun c _ => ?_
    ohneInv := List.isEmpty_iff.mp hi
    statics := staticsB_ok hg
    ohneTransition := fun c _ => ohneTransitionB_ok hPlain c }
           frisch := fun c _ => bindFrischAllB_ok hf c }
  · have h := List.all_eq_true.mp hq (fnAt u c) (List.get_mem _ _)
    exact List.isEmpty_iff.mp h

/-- Per-unit duties are the all-carried instance of the consolidated duties. -/
theorem pflichtenTeilG_of_alle {src : String} (hp : PflichtenAlle src) :
    ∃ u : UProg, PflichtenTeilG src (u := u) (fun _ => True) := by
  obtain ⟨u, hu, hn, hs, hf, hr, hPlain, hZ⟩ := hp
  refine ⟨u, hu, hn, getragenG_of_bools hs hPlain hf, hr, fun c _ => hZ c, ?_⟩
  intro c hc
  exact (hc True.intro).elim

/-! ## Recursive units: the measure duties

The rank conjunct `rangB u (rangAuto u) = true` of `PflichtenTeilG`/`PflichtenAlle` is the one
unit gate that refuses every recursive unit. The measure forms below drop it: each carried
function owes `meetsUM` under one well-founded measure of the person's choice, which admits
recursion and mutual recursion. The rank forms are instances (`pflichtenTeilM_of_G`,
`pflichtenAlleM_of_alle`), so every existing acyclic duty proof carries over unchanged. -/

/-- Source duties for the carried functions under a measure; no call-graph rank. -/
def PflichtenTeilM (src : String) {u : UProg} (C : Fin u.fns.length → Prop) : Prop :=
  uOf src = some u ∧ nullB u = true ∧ GetragenG u C ∧
    (∃ M : MassU, MassPflichtU u C M) ∧ OffenePflicht u C

/-- Per-unit duties under a measure, every function carried; no call-graph rank. -/
def PflichtenAlleM (src : String) : Prop :=
  ∃ u : UProg, uOf src = some u ∧ nullB u = true ∧ stimmigB u = true ∧
    bindFrischAllB u = true ∧ ohneTransitionB u = true ∧
    ∃ M : MassU, MassPflichtU u (fun _ => True) M

/-- The rank duties are measure duties under the rank. -/
theorem pflichtenTeilM_of_G {src : String} {u : UProg} {C : Fin u.fns.length → Prop}
    (hp : PflichtenTeilG src C) : PflichtenTeilM src C := by
  obtain ⟨hu, hn, S, hr, hZ, hOpen⟩ := hp
  exact ⟨hu, hn, S, ⟨_, massPflichtU_of_rang (rang_of hr) hZ⟩, hOpen⟩

theorem pflichtenAlleM_of_alle {src : String} (hp : PflichtenAlle src) : PflichtenAlleM src := by
  obtain ⟨u, hu, hn, hs, hf, hr, hPlain, hZ⟩ := hp
  exact ⟨u, hu, hn, hs, hf, hPlain, _,
    massPflichtU_of_rang (C := fun _ => True) (rang_of hr) (fun c _ => hZ c)⟩

/-- Per-unit measure duties are the all-carried instance of the measure duties. -/
theorem pflichtenTeilM_of_alleM {src : String} (hp : PflichtenAlleM src) :
    ∃ u : UProg, PflichtenTeilM src (u := u) (fun _ => True) := by
  obtain ⟨u, hu, hn, hs, hf, hPlain, M, hZ⟩ := hp
  refine ⟨u, hu, hn, getragenG_of_bools hs hPlain hf, ⟨M, hZ⟩, ?_⟩
  intro c hc
  exact (hc True.intro).elim

end Gabbro.Bruecke
