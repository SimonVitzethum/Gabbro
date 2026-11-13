module
public import Bruecke.Teil.Rahmen
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Only carried functions of rank below `k` must have realizations. -/
def RealisiertC (u : UProg) (C : Fin u.fns.length → Prop)
    (rk : String → Nat) (k : Nat) (ρ : Gabbro.Body.Env) : Prop :=
  ∀ n c, C c → fnSuch u n = some (fnAt u c) → rk n < k →
    Gabbro.Body.Contract ρ n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧
    Gabbro.Body.Frame ρ n (fnAt u c).puts

theorem realisiert_teil (S : Getragen u C)
    (hZ : ∀ c : Fin u.fns.length, C c → ∃ body, zuBody u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, C c → ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) : ∀ k, ∃ ρ, RealisiertC u C rk k ρ
  | 0 => ⟨fun _ t => (t, none), fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
      classical
      obtain ⟨ρk, hk⟩ := realisiert_teil S hZ hlow rk hR k
      let ant : UFn → Gabbro.Body.State → Gabbro.Body.State × Option Gabbro.Body.Value :=
        fun gf t =>
          if preProp (wfU u) gf t then
            match Gabbro.Body.finalState (Gabbro.Body.exec ρk ((zuBody u gf).getD []) t) with
            | some s' => (s', Gabbro.Body.finalValue (Gabbro.Body.exec ρk ((zuBody u gf).getD []) t))
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
        rw [zuBody_eq] at hbody
        cases hbs : stmtsBody u (fnAt u c) (fnAt u c).body with
        | none => rw [hbs] at hbody; cases hbody
        | some bs =>
          rw [hbs] at hbody
          cases heB : endBody u (fnAt u c) (fnAt u c).ret with
          | none => rw [heB] at hbody; cases hbody
          | some eB =>
            rw [heB] at hbody
            simp only [Option.map_some, Option.some.injEq] at hbody
            have hz : zuBody u (fnAt u c) = some (bs ++ eB) := by
              rw [zuBody_eq, hbs, heB]; rfl
            -- the callees: found, of smaller rank, so kept by `ρk`
            have hcallee : ∀ cn gf', fnSuch u cn = some gf' →
                (∃ args, UStmt.call cn args ∈ (fnAt u c).body) →
                Gabbro.Body.Contract ρk cn (preProp (wfU u) gf') (postP u gf') ∧
                Gabbro.Body.Frame ρk cn gf'.puts := by
              intro cn gf' hgf' ⟨args, hm⟩
              obtain ⟨d, rfl, _⟩ := fnSuch_mem hgf'
              exact hk cn d (callee_getragen_teil S hc hm hgf') hgf'
                (by have := hR c cn args hm; rw [hname] at this; omega)
            have heBr : ∀ x ∈ eB, ∃ e, x = .ret (some e) := by
              intro x hx
              cases hr : (fnAt u c).ret
              case empty => rw [hr] at heB; simp [endBody] at heB; subst heB; cases hx
              case val v =>
                rw [hr] at heB
                simp only [endBody] at heB
                cases hs : sideExpr u (fnAt u c) v with
                | none => rw [hs] at heB; cases heB
                | some e =>
                  rw [hs] at heB
                  simp only [Option.map_some, Option.some.injEq] at heB
                  subst heB
                  simp at hx; exact ⟨e, hx⟩
              all_goals (rw [hr] at heB; simp [endBody] at heB)
            constructor
            · intro t hpre
              rw [hρ' t]
              simp only [ant, hpre, ↓reduceIte, hz, Option.getD_some]
              have hm := hmeets ρk t hpre.1 hpre.2
              subst hbody
              obtain ⟨s', hs', hpost⟩ := hyps_elim (wfU u) ρk (calleesOf (fnAt u c)) _ (fun g hg => by
                obtain ⟨args, hm'⟩ := mem_calleesOf hg
                obtain ⟨gf', hgf'⟩ := callee_gefunden hbs hm'
                exact ⟨gf', hgf', hcallee g gf' hgf' ⟨args, hm'⟩⟩) hm
              rw [hs']
              exact hpost
            · intro t p hp
              rw [hρ' t]
              simp only [ant]
              split
              · rw [hz, Option.getD_some]
                split
                · rename_i s' hs'
                  exact exec_rahmen_teil S c hc ρk eB heBr _ bs (fun _ hm => hm)
                    (lowBody_stmts c _ _ (resOf u c) b0 (stmtsBody_isSome hbs) hb0) hbs
                    (fun cn gf' hgf' hm => (hcallee cn gf' hgf' hm).2) t s' hs' p hp
                · rfl
              · rfl
      · obtain ⟨hc, hf⟩ := hk n c hc hgf (by omega)
        refine ⟨fun t ht => ?_, fun t p hp => ?_⟩
        · simp only [ρ', if_neg hkn]; exact hc t ht
        · simp only [ρ', if_neg hkn]; exact hf t p hp

end Gabbro.Bruecke
