module
public import Bruecke.Teil.Lokal.Rahmen
public import Bruecke.Anweisung.Zweig.Rahmen
public import Bruecke.Anweisung.Zweig.Lesen
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem statisch_schritt_G {loopMode : Bool} (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env)
    {Γ : Ctx} {fn : UFn} {ns : BodyNames} (hΓ : Γ = fn.params.map (·.2)) (st : UStmt) (ss : List UStmt)
    {Λ Λ' : List (Res (declOf u))} {g : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (hmem : st ∈ (fnAt u c).body) (hgst : lowStmtL (l := loopMode) u c Γ fn Λ st = .ok ⟨Λ', g⟩) {bB : Gabbro.Body.Stmt}
    (hx : namedStmt u fn ns st = some bB)
    (hF : ∀ cname gf, fnSuch u cname = some gf → (∃ args, CallsIn (st :: ss) cname args) →
      Gabbro.Body.Frame ρB cname (writesU gf))
    {bs' : List Gabbro.Body.Stmt} (IH : Statisch ρB (writesU (fnAt u c)) bs') :
    Statisch ρB (writesU (fnAt u c)) (bB :: bs') := by
  obtain ⟨raw, hx, hn⟩ := namedStmt_some hx
  rcases stmt_statisch_teilB S c hc hΓ st hmem hgst hx with ⟨cn, idx, fld, ve, rfl, hcn⟩ |
      ⟨n, ve, rfl, hnwrite⟩ | ⟨cname, ps, es, pre, gf, rfl, hgf, hsub⟩
  · simp only [renameStep] at hn
    split at hn
    · rename_i idx' ve' hi hv
      cases hn
      exact .assign _ _ _ _ _ (List.mem_append_left _ hcn) IH
    · cases hn
  · simp only [renameStep] at hn
    cases he : renameScalar (ns.lookup fn) ve with
    | none => rw [he] at hn; cases hn
    | some ve' =>
      rw [he] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst bB
      exact .assignGlobal _ _ _ (writesU_global hnwrite) IH
  · have hcall : ∃ args, CallsIn (st :: ss) cname args := by
      cases st
      case call =>
        simp only [stmtBody] at hx
        split at hx
        · simp only [Option.some.injEq] at hx
          cases hx
          exact ⟨_, CallsIn.discard (List.mem_cons_self ..)⟩
        · cases hx
      case assign b f ix v =>
        simp only [stmtBody] at hx
        split at hx
        · simp only [Option.some.injEq] at hx; cases hx
        · cases hx
      case assignTab b f ix v _ =>
        simp only [stmtBody] at hx
        cases hsv : sideExprG u fn v with
        | none => rw [hsv] at hx; cases hx
        | some ve => rw [hsv] at hx; simp at hx
      case assignGlob n v _ =>
        simp only [stmtBody] at hx
        cases he : sideExprG u fn v with
        | none => rw [he] at hx; cases hx
        | some e => rw [he] at hx; cases hx
      all_goals simp only [stmtBody, reduceCtorEq] at hx
    simp only [renameStep] at hn
    cases hr : renameStep.renameScalars (ns.lookup fn) es with
    | none => rw [hr] at hn; cases hn
    | some es' =>
      rw [hr] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst bB
      exact .call _ _ _ _ _ (fun t p hp => hF cname gf hgf hcall t p (fun hm => hp (hsub _ hm))) IH

end Gabbro.Bruecke
