module
public import Bruecke.Kette.Mass.Pflicht
public import Bruecke.Kette.Rahmen
public import Bruecke.Teil.Abschluss
public import Bruecke.Anweisung.Zweig.Realisierung
@[expose] public section

/-!
# One Body environment for recursive units

`massEnv u` answers every entry `(n, t)` with an answer that keeps the frame of `n` and meets
its contract, wherever such an answer exists, and leaves the state unchanged otherwise. It
depends on nothing but the unit: no rank, no layering, no fixed point.

`massEnv_antwort` shows, by well-founded induction over the measure, that a good answer exists
at every entry of a carried function that satisfies its precondition: the function's
`meetsUM` duty, applied to `massEnv u` itself, needs the callee contracts only strictly below
the entry value, and those come from the induction hypothesis. A recursive or mutually
recursive callee is therefore discharged exactly like any other. The result is the old
conclusion of `realisiert_alle_G` -- full contracts and frames of every carried function in
ONE environment -- now without a call-graph rank.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The answer `out` to an entry of `n` at `t` keeps the frame of `n`. -/
def RahmenOK (u : UProg) (n : String) (t : Gabbro.Body.State)
    (out : Gabbro.Body.State × Option Gabbro.Body.Value) : Prop :=
  ∀ gf, fnSuch u n = some gf →
    ∀ p : Gabbro.Body.Place, p.carrier ∉ writesU gf → out.1.world p = t.world p

/-- The answer `out` to an entry of `n` at `t` meets the contract of `n`. -/
def VertragOK (u : UProg) (n : String) (t : Gabbro.Body.State)
    (out : Gabbro.Body.State × Option Gabbro.Body.Value) : Prop :=
  ∀ gf, fnSuch u n = some gf → preProp (wfU u) gf t → postP u gf t out.1 out.2

/-- A good answer: frame and contract. -/
def AntwortGut (u : UProg) (n : String) (t : Gabbro.Body.State)
    (out : Gabbro.Body.State × Option Gabbro.Body.Value) : Prop :=
  RahmenOK u n t out ∧ VertragOK u n t out

/-- **The environment of a unit**: a good answer where one exists, else the entry unchanged. -/
noncomputable def massEnv (u : UProg) : Gabbro.Body.Env := fun n t =>
  haveI := Classical.propDecidable (∃ out, AntwortGut u n t out)
  if h : ∃ out, AntwortGut u n t out then Classical.choose h else (t, none)

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem massEnv_gut {n : String} {t : Gabbro.Body.State} (hex : ∃ out, AntwortGut u n t out) :
    AntwortGut u n t (massEnv u n t) := by
  simp only [massEnv, dif_pos hex]
  exact Classical.choose_spec hex

theorem massEnv_sonst {n : String} {t : Gabbro.Body.State} (hex : ¬ ∃ out, AntwortGut u n t out) :
    massEnv u n t = (t, none) := by
  simp only [massEnv, dif_neg hex]

/-- Every name keeps its frame under `massEnv`, carried or not. -/
theorem massEnv_rahmen (n : String) (gf : UFn) (hgf : fnSuch u n = some gf) :
    Gabbro.Body.Frame (massEnv u) n (writesU gf) := by
  intro t p hp
  by_cases hex : ∃ out, AntwortGut u n t out
  · exact (massEnv_gut hex).1 gf hgf p hp
  · simp only [massEnv_sonst hex]

theorem massEnv_vertrag {n : String} {t : Gabbro.Body.State} {gf : UFn}
    (hgf : fnSuch u n = some gf) (hex : ∃ out, AntwortGut u n t out)
    (hpre : preProp (wfU u) gf t) : postP u gf t (massEnv u n t).1 (massEnv u n t).2 :=
  (massEnv_gut hex).2 gf hgf hpre

/-- **A good answer exists at every entry of a carried function**, by well-founded induction
    over the measure. -/
theorem massEnv_antwort (S : Getragen u C) (M : MassU) (hZ : MassPflichtU u C M)
    (hlow : ∀ c : Fin u.fns.length, C c → ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (a : M.Wert) : ∀ (n : String) (c : Fin u.fns.length) (t : Gabbro.Body.State), C c →
      fnSuch u n = some (fnAt u c) → M.mass n t = a → preProp (wfU u) (fnAt u c) t →
      ∃ out, AntwortGut u n t out := by
  refine WellFounded.induction M.wf (C := fun a => ∀ (n : String) (c : Fin u.fns.length)
    (t : Gabbro.Body.State), C c → fnSuch u n = some (fnAt u c) → M.mass n t = a →
      preProp (wfU u) (fnAt u c) t → ∃ out, AntwortGut u n t out) a ?_
  intro a IH n c t hc hgf ha hpre
  have hname : (fnAt u c).name = n := by simpa using List.find?_some hgf
  obtain ⟨body, hbody, hmeets⟩ := hZ c hc
  obtain ⟨b0, hb0⟩ := hlow c hc
  have hm := hmeets (massEnv u) t hpre.1 hpre.2
  obtain ⟨s', hs', hpost⟩ := hypsM_elim (wfU u) (massEnv u) _ (calleesOf (fnAt u c)) _
    (fun g hg => by
      obtain ⟨args, hm'⟩ := mem_calleesOf hg
      obtain ⟨gf', hgf'⟩ := callee_gefundenZ hbody g args hm'
      obtain ⟨d, rfl, _⟩ := fnSuch_mem hgf'
      have hd : C d := callee_getragen_calls S hc hm' hgf'
      refine ⟨fnAt u d, hgf', fun t' ht' => ?_, massEnv_rahmen g _ hgf'⟩
      have hlt : M.lt (M.mass g t') (M.mass (fnAt u c).name t) := ht'.1
      rw [hname, ha] at hlt
      exact massEnv_vertrag hgf' (IH _ hlt g d t' hd hgf' rfl ht'.2) ht'.2) hm
  refine ⟨(s', Gabbro.Body.finalValue (Gabbro.Body.exec (massEnv u) body t)), ?_, ?_⟩
  · intro gf hgf2 p hp
    rw [hgf] at hgf2
    cases hgf2
    exact exec_rahmen_G S c hc (massEnv u) (fnAt u c).ret ((fnAt u c).body.length + 1)
      ((fnAt u c).body.length + 1) (fnAt u c).body (fnAt u c) (fnAt u c)
      (BodyNames.start (fnAt u c)) b0 body rfl (Sicht.refl _) (fun _ hm => hm) hb0 hbody
      (fun cn gf' hgf' _ => massEnv_rahmen cn gf' hgf') t s' hs' p hp
  · intro gf hgf2 _
    rw [hgf] at hgf2
    cases hgf2
    exact hpost

/-- **The realisation under a measure**: contracts and frames of every carried function in
    the one environment `massEnv u`. Recursion and mutual recursion included. -/
theorem realisiert_mass_G (S : Getragen u C) (M : MassU) (hZ : MassPflichtU u C M)
    (hlow : ∀ c : Fin u.fns.length, C c → ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0) :
    ∀ n c, C c → fnSuch u n = some (fnAt u c) →
      Gabbro.Body.Contract (massEnv u) n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧
      Gabbro.Body.Frame (massEnv u) n (writesU (fnAt u c)) :=
  fun n c hc hgf =>
    ⟨fun t ht => massEnv_vertrag hgf (massEnv_antwort S M hZ hlow _ n c t hc hgf rfl ht) ht,
      massEnv_rahmen n _ hgf⟩

/-- The existential shape of `realisiert_alle_G`, under a measure instead of a rank. -/
theorem realisiert_alle_mass_G (S : Getragen u C) (M : MassU) (hZ : MassPflichtU u C M)
    (hlow : ∀ c : Fin u.fns.length, C c → ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0) :
    ∃ ρ : Gabbro.Body.Env, ∀ n c, C c → fnSuch u n = some (fnAt u c) →
      Gabbro.Body.Contract ρ n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧
      Gabbro.Body.Frame ρ n (writesU (fnAt u c)) :=
  ⟨massEnv u, realisiert_mass_G S M hZ hlow⟩

end Gabbro.Bruecke
