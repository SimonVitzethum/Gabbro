module
public import Bruecke.Anweisung.Lokal.Rahmen
@[expose] public section

/-!
# C5, part 4: the environment that keeps every contract, for bodies with local bindings

`realisiert` (`Realisierung.lean`) runs each body `zuBody` computes; `realisiertB` runs the bodies
`zuBodyB` computes, rank by rank, with the frame `exec_rahmenB`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- **The environment exists, rank by rank** -- for the bodies with local bindings. -/
theorem realisiertB (S : Stimmig u)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) : ∀ k, ∃ ρ, Realisiert u rk k ρ
  | 0 => ⟨fun _ t => (t, none), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
      classical
      obtain ⟨ρk, hk⟩ := realisiertB S hZ hlow rk hR k
      let ant : UFn → Gabbro.Body.State → Gabbro.Body.State × Option Gabbro.Body.Value :=
        fun gf t =>
          if preProp (wfU u) gf t then
            match Gabbro.Body.finalState (Gabbro.Body.exec ρk ((zuBodyB u gf).getD []) t) with
            | some s' => (s', Gabbro.Body.finalValue (Gabbro.Body.exec ρk ((zuBodyB u gf).getD []) t))
            | none => (t, none)
          else (t, none)
      let ρ' : Gabbro.Body.Env := fun n t =>
        if rk n = k then
          match fnSuch u n with
          | some gf => ant gf t
          | none => ρk n t
        else ρk n t
      refine ⟨ρ', fun n gf hgf hlt => ?_⟩
      by_cases hkn : rk n = k
      · have hρ' : ∀ t, ρ' n t = ant gf t := fun t => by simp only [ρ', hkn, ↓reduceIte, hgf]
        obtain ⟨c, rfl, hname⟩ := fnSuch_mem hgf
        obtain ⟨body, hbody, hmeets⟩ := hZ c
        obtain ⟨b0, hb0⟩ := hlow c
        -- the callees: found, of smaller rank, so kept by `ρk`
        have hcallee : ∀ cn gf', fnSuch u cn = some gf' →
            (∃ args, UStmt.call cn args ∈ (fnAt u c).body) →
            Gabbro.Body.Contract ρk cn (preProp (wfU u) gf') (postP u gf') ∧
            Gabbro.Body.Frame ρk cn gf'.puts := fun cn gf' hgf' ⟨args, hm⟩ =>
          hk cn gf' hgf' (by have := hR c cn args hm; rw [hname] at this; omega)
        constructor
        · intro t hpre
          rw [hρ' t]
          simp only [ant, hpre, ↓reduceIte, hbody, Option.getD_some]
          have hm := hmeets ρk t hpre.1 hpre.2
          obtain ⟨s', hs', hpost⟩ := hyps_elim (wfU u) ρk (calleesOf (fnAt u c)) _ (fun g hg => by
            obtain ⟨args, hm'⟩ := mem_calleesOf hg
            obtain ⟨gf', hgf'⟩ := callee_gefundenB (fnAt u c).ret (fnAt u c) (fnAt u c).body body
              hbody g args hm'
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
              exact exec_rahmenB S c ρk (fnAt u c).ret ((fnAt u c).body.length + 1)
                (fnAt u c).body (fnAt u c) (fnAt u c) b0 body rfl (Sicht.refl _) hb0 hbody
                (fun cn gf' hgf' hm => (hcallee cn gf' hgf' hm).2) t s' hs' p hp
            · rfl
          · rfl
      · obtain ⟨hc, hf⟩ := hk n gf hgf (by omega)
        refine ⟨fun t ht => ?_, fun t p hp => ?_⟩
        · simp only [ρ', if_neg hkn]; exact hc t ht
        · simp only [ρ', if_neg hkn]; exact hf t p hp

theorem realisiert_alleB (S : Stimmig u)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyB u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) :
    ∃ ρ : Gabbro.Body.Env, ∀ n gf, fnSuch u n = some gf →
      Gabbro.Body.Contract ρ n (preProp (wfU u) gf) (postP u gf) ∧ Gabbro.Body.Frame ρ n gf.puts := by
  let K := (u.fns.map (fun f => rk f.name)).foldr max 0 + 1
  obtain ⟨ρ, hρ⟩ := realisiertB S hZ hlow rk hR K
  refine ⟨ρ, fun n gf hgf => hρ n gf hgf ?_⟩
  obtain ⟨c, rfl, hname⟩ := fnSuch_mem hgf
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
