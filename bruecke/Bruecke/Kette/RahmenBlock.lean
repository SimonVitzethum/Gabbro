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

theorem statisch_schritt_G (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env)
    {Γ : Ctx} {fn : UFn} {ns : BodyNames} (hΓ : Γ = fn.params.map (·.2)) (st : UStmt) (ss : List UStmt)
    {Λ Λ' : List (Res (declOf u))} {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ'}
    (hmem : st ∈ (fnAt u c).body) (hgst : lowStmtL (l := false) u c Γ fn Λ st = .ok ⟨Λ', g⟩) {bB : Gabbro.Body.Stmt}
    (hx : namedStmt u fn ns st = some bB)
    (hF : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ st :: ss) →
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
      exact .assignGlobal _ _ _ (List.mem_append_right _ hnwrite) IH
  · have hcall : ∃ args, UStmt.call cname args ∈ st :: ss := by
      cases st
      case call =>
        simp only [stmtBody] at hx
        split at hx
        · simp only [Option.some.injEq] at hx
          cases hx
          exact ⟨_, List.mem_cons_self ..⟩
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

theorem statischSeq_G (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ')
      (rest : List UStmt) (t : List Gabbro.Body.Stmt) (restZ : List UStmt) (used : List String),
      Γ = fn.params.map (·.2) → Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowSeqL (l := false) u c Γ fn n Λ [] ss = .ok (p, rest) →
      seqZ u k fT ns ss = some (t, restZ, used) →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρB cname (writesU gf)) →
      restZ = rest ∧ rest <:+ ss ∧ Statisch ρB (writesU (fnAt u c)) t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k ss Γ fn fT ns Λ p rest t restZ used hΓ hS hmem hlow hbs hF
    obtain _ | n := n
    · rw [lowSeqL_zero] at hlow; cases hlow
    obtain _ | k := k
    · exact absurd hbs (by simp only [seqZ, reduceCtorEq, not_false_eq_true])
    obtain _ | ⟨s0, ss⟩ := ss
    · rw [lowSeq_nil] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl, _⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, .nil⟩
    have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
      fun st hm => hmem st (List.mem_cons_of_mem _ hm)
    have hhead : s0 ∈ (fnAt u c).body := hmem s0 (List.mem_cons_self ..)
    have hFss : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρB cname (writesU gf) :=
      fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, List.mem_cons_of_mem _ hm⟩
    cases s0
    case blkEnd | ifElse =>
      first
        | rw [lowSeq_blkEnd] at hlow
        | rw [lowSeq_ifElse] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl, _⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, .nil⟩
    case bind x d v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind hstepT
      obtain ⟨ls, q, hls, hq, rfl⟩ := lowSeq_bind_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x ls.range)
        (fT.mitBindung x (0, 0)) (ns.push x) q rest ys restZ used
        (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
        (hS.bind x (0, 0) ls.range) hmemss hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case bindMut x lo hi v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut hstepT
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindMut_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used
        (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
        (hS.bind x (lo, hi) (lo, hi)) hmemss hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case setVar x v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨-, id, eT, -, -, rfl, rfl, rfl⟩ := schrittB_setVar hstepT
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hΓ hS hmemss hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case assign | assignTab | assignGlob | call =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hstepN, rfl, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
      obtain ⟨hx, -, -⟩ := schrittB_stmt hstepN (fun _ _ _ h => by cases h)
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hΓ hS hmemss hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _),
        statisch_schritt_G S c hc ρB hΓ _ ss hhead hst hx hF IH.2.2⟩
    case ret r0 =>
      obtain ⟨bst, ys, hbT, hys, rfl⟩ := seqZ_ret_some hbs
      obtain ⟨st, q, hst, hq, rfl⟩ := lowSeq_ret_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ ns q rest ys restZ used hΓ hS hmemss hq hys hFss
      have hret : ∃ e, bst = .ret e := by
        cases r0
        case empty =>
          simp only [retZ, Option.some.injEq] at hbT
          exact ⟨_, hbT.symm⟩
        case val sd =>
          simp only [retZ] at hbT
          cases hse : namedSide u fT ns sd with
          | none => rw [hse] at hbT; cases hbT
          | some e =>
            rw [hse] at hbT
            simp only [Option.map_some, Option.some.injEq] at hbT
            exact ⟨_, hbT.symm⟩
        all_goals simp [retZ] at hbT
      obtain ⟨e, rfl⟩ := hret
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .ret _ _ IH.2.2⟩
    case ifBeg cnd | ifEnde cnd =>
      obtain ⟨Λ₁, st, rest', q, hst, hq, rfl⟩ :=
        lowSeq_wenn_ok (cnd := cnd) hlow (by first | exact .inl rfl | exact .inr rfl)
      obtain ⟨ce, tt, te, r1, r2, ys, used1, used2, hce, hTZ, hEZ, hYZ, rfl⟩ :=
        seqZ_wenn_some (cnd := cnd) hbs (by first | exact .inl rfl | exact .inr rfl)
      obtain _ | m := n
      · rw [lowStructL_zero] at hst; cases hst
      obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
      obtain ⟨hr1, hsuf1, hSt⟩ := ih m (by omega) k ss fn _ ns ⟨Λ₁, tb⟩ (.ifElse :: rest1) tt
        (.ifElse :: r1) used1 hΓ hS hmemss hT hTZ hFss
      have h1 : r1 = rest1 := (List.cons.inj hr1).2
      rw [h1] at hEZ
      have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
      obtain ⟨hr2, hsuf2, hSe⟩ := ih m (by omega) k rest1 fn _ (ns.resume used1) ⟨Λ₁, eb⟩ (.blkEnd :: rest') te
        (.blkEnd :: r2) used2 hΓ hS (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) hE hEZ
        (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, mem_of_suffix hsuf1' hm⟩)
      have h2 : r2 = rest' := (List.cons.inj hr2).2
      rw [h2] at hYZ
      have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hSc⟩ := ih (m + 1) (by omega) k rest' fn _ (ns.resume used2) q rest ys restZ used hΓ hS (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hq hYZ
        (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, mem_of_suffix hsuf2' hm⟩)
      exact ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), .ite _ _ _ _ hSt hSe hSc⟩
    all_goals exact absurd hbs (by simp only [seqZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

end Gabbro.Bruecke
