module
public import Bruecke.Kette.Rahmen
public import Bruecke.Teil.Realisierung
public import Bruecke.Anweisung.Zweig.Realisierung
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem realisiert_G (S : Getragen u C)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, C c → ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) : ∀ k, ∃ ρ, RealisiertC u C rk k ρ
  | 0 => ⟨fun _ t => (t, none), fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
      classical
      obtain ⟨ρk, hk⟩ := realisiert_G S hZ hlow rk hR k
      let ant : UFn → Gabbro.Body.State → Gabbro.Body.State × Option Gabbro.Body.Value :=
        fun gf t =>
          if preProp (wfU u) gf t then
            match Gabbro.Body.finalState (Gabbro.Body.exec ρk ((zuBodyZ u gf).getD []) t) with
            | some s' => (s', Gabbro.Body.finalValue (Gabbro.Body.exec ρk ((zuBodyZ u gf).getD []) t))
            | none => (t, none)
          else (t, none)
      let ρ' : Gabbro.Body.Env := fun n t =>
        if rk n = k then
          match fnSuch u n with
          | some gf => ant gf t
          | none => ρk n t
        else ρk n t
      refine ⟨ρ', fun n c hc hgf hlt => ?_⟩
      by_cases hkn : rk n = k
      · have hρ' : ∀ t, ρ' n t = ant (fnAt u c) t := fun t => by simp only [ρ', hkn, ↓reduceIte, hgf]
        have hname : (fnAt u c).name = n := by simpa using List.find?_some hgf
        obtain ⟨body, hbody, hmeets⟩ := hZ c hc
        obtain ⟨b0, hb0⟩ := hlow c hc
        -- the callees: found, of smaller rank, so kept by `ρk`
        have hcallee : ∀ cn gf', fnSuch u cn = some gf' →
            (∃ args, CallsIn (fnAt u c).body cn args) →
            Gabbro.Body.Contract ρk cn (preProp (wfU u) gf') (postP u gf') ∧
            Gabbro.Body.Frame ρk cn (writesU gf') := by
          intro cn gf' hgf' ⟨args, hm⟩
          obtain ⟨d, rfl, _⟩ := fnSuch_mem hgf'
          exact hk cn d (callee_getragen_calls S hc hm hgf') hgf'
            (by have := hR c cn args hm; rw [hname] at this; omega)
        constructor
        · intro t hpre
          rw [hρ' t]
          simp only [ant, hpre, ↓reduceIte, hbody, Option.getD_some]
          have hm := hmeets ρk t hpre.1 hpre.2
          obtain ⟨s', hs', hpost⟩ := hyps_elim (wfU u) ρk (calleesOf (fnAt u c)) _ (fun g hg => by
            obtain ⟨args, hm'⟩ := mem_calleesOf hg
            obtain ⟨gf', hgf'⟩ := callee_gefundenZ hbody g args hm'
            exact ⟨gf', hgf', hcallee g gf' hgf' ⟨args, hm'⟩⟩) hm
          rw [hs']
          exact hpost
        · intro t p hp
          rw [hρ' t]
          simp only [ant]
          split
          · rw [hbody, Option.getD_some]
            split
            · rename_i s' hs'
              exact exec_rahmen_G S c hc ρk (fnAt u c).ret ((fnAt u c).body.length + 1)
                ((fnAt u c).body.length + 1) (fnAt u c).body (fnAt u c) (fnAt u c) (BodyNames.start (fnAt u c)) b0 body rfl (Sicht.refl _) (fun _ hm => hm) hb0 hbody
                (fun cn gf' hgf' hm => (hcallee cn gf' hgf' hm).2) t s' hs' p hp
            · rfl
          · rfl
      · obtain ⟨hc, hf⟩ := hk n c hc hgf (by omega)
        refine ⟨fun t ht => ?_, fun t p hp => ?_⟩
        · simp only [ρ', if_neg hkn]; exact hc t ht
        · simp only [ρ', if_neg hkn]; exact hf t p hp

theorem realisiert_alle_G (S : Getragen u C)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, C c → ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) :
    ∃ ρ : Gabbro.Body.Env, ∀ n c, C c → fnSuch u n = some (fnAt u c) →
      Gabbro.Body.Contract ρ n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧
      Gabbro.Body.Frame ρ n (writesU (fnAt u c)) := by
  let K := (u.fns.map (fun f => rk f.name)).foldr max 0 + 1
  obtain ⟨ρ, hρ⟩ := realisiert_G S hZ hlow rk hR K
  refine ⟨ρ, fun n c hc hgf => hρ n c hc hgf ?_⟩
  have hname : (fnAt u c).name = n := by simpa using List.find?_some hgf
  have hmem : rk n ∈ u.fns.map (fun f => rk f.name) := by
    rw [List.mem_map]
    exact ⟨fnAt u c, List.get_mem _ _, by rw [hname]⟩
  have : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr max 0 := by
    intro l x hx
    induction l with
    | nil => cases hx
    | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)
  have := this _ _ hmem
  omega

end Gabbro.Bruecke
