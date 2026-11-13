module
public import Bruecke.Anweisung.Zweig.Rahmen
public import Bruecke.Anweisung.Lokal.RealisierungB
@[expose] public section

/-!
# C6, part 8: the environment that keeps every contract, for bodies with conditionals

`realisiertB` for the bodies `zuBodyZ` computes, rank by rank, with the frame `exec_rahmenZ`.
Every call of a body the translation carries finds its callee (`callee_gefundenZ`), in a branch
as well: the translation reads every statement of the flat body.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. Every call finds its callee -/

theorem callee_of_schrittB {fn : UFn} {g : String} {args : List UArg} {p : Gabbro.Body.Stmt × UFn}
    (hs : schrittB u fn (.call g args) = some p) : ∃ gf, fnSuch u g = some gf := by
  have hs' : (stmtBody u fn (.call g args)).map (fun b => (b, fn)) = some p := hs
  cases hb : stmtBody u fn (.call g args) with
  | none => rw [hb] at hs'; cases hs'
  | some x =>
    simp only [stmtBody] at hb
    split at hb
    · rename_i gf es hgf _
      exact ⟨gf, hgf⟩
    · cases hb

theorem mem_tail_of_ne {a b : UStmt} {l : List UStmt} (h : a ∈ b :: l) (hne : a ≠ b) : a ∈ l := by
  rcases List.mem_cons.mp h with h' | h'
  · exact absurd h' hne
  · exact h'

/-- A call the block reader reads finds its callee, or it lies in what is left. -/
theorem seqZ_callee : ∀ (k : Nat) (fn : UFn) (ss : List UStmt) (t : List Gabbro.Body.Stmt)
    (rest : List UStmt), seqZ u k fn ss = some (t, rest) → ∀ (g : String) (args : List UArg),
      UStmt.call g args ∈ ss → (∃ gf, fnSuch u g = some gf) ∨ UStmt.call g args ∈ rest
  | 0, _, _, _, _, h, _, _, _ => by simp [seqZ] at h
  | k + 1, _, [], _, _, _, _, _, hm => absurd hm List.not_mem_nil
  | k + 1, fn, s0 :: ss, t, rest, h, g, args, hm => by
      cases s0
      case blkEnd | ifElse =>
        simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact .inr hm
      case ifBeg cnd | ifEnde cnd =>
        obtain ⟨ce, tt, te, r1, r2, ys, _, hT, hE, hY, _⟩ :=
          seqZ_wenn_some (cnd := cnd) h (by first | exact .inl rfl | exact .inr rfl)
        have hm' := mem_tail_of_ne hm (by intro h'; cases h')
        rcases seqZ_callee k fn ss tt _ hT g args hm' with hf | hm1
        · exact .inl hf
        · rcases seqZ_callee k fn r1 te _ hE g args (mem_tail_of_ne hm1 (by intro h'; cases h'))
            with hf | hm2
          · exact .inl hf
          · exact seqZ_callee k fn r2 ys rest hY g args (mem_tail_of_ne hm2 (by intro h'; cases h'))
      case ret r0 =>
        obtain ⟨b, ys, _, hY, _⟩ := seqZ_ret_some h
        exact seqZ_callee k fn ss ys rest hY g args (mem_tail_of_ne hm (by intro h'; cases h'))
      case call g' args' =>
        obtain ⟨b, fn', ys, hs, hY, _⟩ := seqZ_schritt_some h (by exact True.intro)
        rcases List.mem_cons.mp hm with h' | h'
        · cases h'
          exact .inl (callee_of_schrittB hs)
        · exact seqZ_callee k fn' ss ys rest hY g args h'
      case bind | bindMut | setVar | assign | assignTab =>
        obtain ⟨b, fn', ys, hs, hY, _⟩ := seqZ_schritt_some h (by exact True.intro)
        exact seqZ_callee k fn' ss ys rest hY g args (mem_tail_of_ne hm (by intro h'; cases h'))
      all_goals exact absurd h (by simp [seqZ, schrittB, stmtBody])

/-- A call of a body the body reader reads finds its callee. -/
theorem stmtsBodyZ_callee (r : URet) : ∀ (k : Nat) (fn : UFn) (ss : List UStmt)
    (bs : List Gabbro.Body.Stmt), stmtsBodyZ u k fn ss r = some bs →
    ∀ (g : String) (args : List UArg), UStmt.call g args ∈ ss → ∃ gf, fnSuch u g = some gf
  | 0, _, _, _, h, _, _, _ => by simp [stmtsBodyZ] at h
  | k + 1, _, [], _, _, _, _, hm => absurd hm List.not_mem_nil
  | k + 1, fn, s0 :: ss, bs, h, g, args, hm => by
      cases s0
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', _, hT, hE, hY, _⟩ := stmtsBodyZ_ifBeg_some h
        have hm' := mem_tail_of_ne hm (by intro h'; cases h')
        rcases seqZ_callee k fn ss tt _ hT g args hm' with hf | hm1
        · exact hf
        · rcases seqZ_callee k fn r1 te _ hE g args (mem_tail_of_ne hm1 (by intro h'; cases h'))
            with hf | hm2
          · exact hf
          · exact stmtsBodyZ_callee r k fn r2 bs' hY g args
              (mem_tail_of_ne hm2 (by intro h'; cases h'))
      case call g' args' =>
        obtain ⟨b, fn', bs', hs, hY, _⟩ := stmtsBodyZ_schritt_some h (by exact True.intro)
        rcases List.mem_cons.mp hm with h' | h'
        · cases h'
          exact callee_of_schrittB hs
        · exact stmtsBodyZ_callee r k fn' ss bs' hY g args h'
      case bind | bindMut | setVar | assign | assignTab =>
        obtain ⟨b, fn', bs', hs, hY, _⟩ := stmtsBodyZ_schritt_some h (by exact True.intro)
        exact stmtsBodyZ_callee r k fn' ss bs' hY g args (mem_tail_of_ne hm (by intro h'; cases h'))
      all_goals exact absurd h (by simp [stmtsBodyZ, schrittB, stmtBody])

theorem callee_gefundenZ {f : UFn} {body : List Gabbro.Body.Stmt} (h : zuBodyZ u f = some body)
    (g : String) (args : List UArg) (hm : UStmt.call g args ∈ f.body) :
    ∃ gf, fnSuch u g = some gf :=
  stmtsBodyZ_callee f.ret _ f f.body body h g args hm

/-! ## 2. The environment -/

/-- **The environment exists, rank by rank** -- for the bodies with conditionals. -/
theorem realisiertZ (S : Stimmig u)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) : ∀ k, ∃ ρ, Realisiert u rk k ρ
  | 0 => ⟨fun _ t => (t, none), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
      classical
      obtain ⟨ρk, hk⟩ := realisiertZ S hZ hlow rk hR k
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
      refine ⟨ρ', fun n gf hgf hlt => ?_⟩
      by_cases hkn : rk n = k
      · have hρ' : ∀ t, ρ' n t = ant gf t := fun t => by simp only [ρ', hkn, ↓reduceIte, hgf]
        obtain ⟨c, rfl, hname⟩ := fnSuch_mem hgf
        obtain ⟨body, hbody, hmeets⟩ := hZ c
        obtain ⟨b0, hb0⟩ := hlow c
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
              exact exec_rahmenZ S c ρk (fnAt u c).ret ((fnAt u c).body.length + 1)
                ((fnAt u c).body.length + 1) (fnAt u c).body (fnAt u c) (fnAt u c) b0 body rfl
                (Sicht.refl _) hb0 hbody (fun cn gf' hgf' hm => (hcallee cn gf' hgf' hm).2)
                t s' hs' p hp
            · rfl
          · rfl
      · obtain ⟨hc, hf⟩ := hk n gf hgf (by omega)
        refine ⟨fun t ht => ?_, fun t p hp => ?_⟩
        · simp only [ρ', if_neg hkn]; exact hc t ht
        · simp only [ρ', if_neg hkn]; exact hf t p hp

theorem realisiert_alleZ (S : Stimmig u)
    (hZ : ∀ c : Fin u.fns.length, ∃ body, zuBodyZ u (fnAt u c) = some body ∧
      meetsU u (wfU u) (fnAt u c) body)
    (hlow : ∀ c : Fin u.fns.length, ∃ b0, lowBody u c (fnAt u c).body (fnAt u c).ret = .ok b0)
    (rk : String → Nat) (hR : Rang u rk) :
    ∃ ρ : Gabbro.Body.Env, ∀ n gf, fnSuch u n = some gf →
      Gabbro.Body.Contract ρ n (preProp (wfU u) gf) (postP u gf) ∧
        Gabbro.Body.Frame ρ n gf.puts := by
  let K := (u.fns.map (fun f => rk f.name)).foldr max 0 + 1
  obtain ⟨ρ, hρ⟩ := realisiertZ S hZ hlow rk hR K
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
