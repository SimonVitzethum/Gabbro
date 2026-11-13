module
public import Bruecke.Anweisung.Zweig.Block
public import Bruecke.Anweisung.Lokal.Rahmen
@[expose] public section

/-!
# C6, part 7: the Body frame of a body with conditionals

`exec_rahmenB` for the bodies `stmtsBodyZ` computes. The static half is a property of the Body
program (`Statisch`): every slot write writes a carrier of the function, every call keeps what the
function does not declare, the arms of every `ite` again so. `exec_statisch` proves the frame
from it, by induction on the derivation; `statischSeq`/`statischZ` derive it along the lowering
(the static facts of a lowered statement are `stmt_statischB`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The static frame of a Body program -/

/-- Every slot write writes a carrier of `puts`; every call keeps every place outside `puts`. -/
inductive Statisch (ρB : Gabbro.Body.Env) (puts : List String) : List Gabbro.Body.Stmt → Prop where
  | nil : Statisch ρB puts []
  | assign (cn : String) (i : Gabbro.Body.Expr) (f : String) (e : Gabbro.Body.Expr)
      (xs : List Gabbro.Body.Stmt) :
      cn ∈ puts → Statisch ρB puts xs → Statisch ρB puts (.assign cn i f e :: xs)
  | bindName (x : String) (e : Gabbro.Body.Expr) (xs : List Gabbro.Body.Stmt) :
      Statisch ρB puts xs → Statisch ρB puts (.bindName x e :: xs)
  | ret (e : Option Gabbro.Body.Expr) (xs : List Gabbro.Body.Stmt) :
      Statisch ρB puts xs → Statisch ρB puts (.ret e :: xs)
  | call (cn : String) (ps : List String) (es : List Gabbro.Body.Expr) (pre : Gabbro.Body.Expr)
      (xs : List Gabbro.Body.Stmt) :
      (∀ t p, p.carrier ∉ puts → (ρB cn t).1.world p = t.world p) →
      Statisch ρB puts xs → Statisch ρB puts (.call cn ps es pre :: xs)
  | ite (ce : Gabbro.Body.Expr) (tb te xs : List Gabbro.Body.Stmt) :
      Statisch ρB puts tb → Statisch ρB puts te → Statisch ρB puts xs →
      Statisch ρB puts (.ite ce tb te :: xs)

/-- A branch that runs, then the rest: each keeps the places outside `puts`. -/
theorem rahmen_zweig {ρB : Gabbro.Body.Env} {puts : List String} {x : Gabbro.Body.Stmt}
    {tb xs : List Gabbro.Body.Stmt} {t s' : Gabbro.Body.State}
    (hs : Gabbro.Body.step ρB x t = Gabbro.Body.exec ρB tb t)
    (hb : ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB tb t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p)
    (hxs : ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB xs t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p)
    (h : Gabbro.Body.finalState (Gabbro.Body.exec ρB (x :: xs) t) = some s') :
    ∀ p, p.carrier ∉ puts → s'.world p = t.world p := by
  intro p hp
  cases hx : Gabbro.Body.exec ρB tb t with
  | running t1 =>
    have h' : Gabbro.Body.finalState (Gabbro.Body.exec ρB xs t1) = some s' := by
      rw [exec_cons_running ρB x xs t t1 (hs.trans hx)] at h
      exact h
    rw [hxs t1 s' h' p hp]
    exact hb t t1 (by simp only [hx, Gabbro.Body.finalState]) p hp
  | returned t1 v =>
    have h' : Gabbro.Body.exec ρB (x :: xs) t = .returned t1 v := by
      simp only [Gabbro.Body.exec, hs, hx]
    rw [h'] at h
    exact hb t s' (by rw [hx]; exact h) p hp
  | exited t1 =>
    have h' : Gabbro.Body.exec ρB (x :: xs) t = .exited t1 := by
      simp only [Gabbro.Body.exec, hs, hx]
    rw [h'] at h
    exact hb t s' (by rw [hx]; exact h) p hp
  | left t1 =>
    have h' : Gabbro.Body.exec ρB (x :: xs) t = .left t1 := by
      simp only [Gabbro.Body.exec, hs, hx]
    rw [h'] at h
    exact hb t s' (by rw [hx]; exact h) p hp
  | stuck =>
    have h' : Gabbro.Body.exec ρB (x :: xs) t = .stuck := by
      simp only [Gabbro.Body.exec, hs, hx]
    rw [h'] at h
    simp [Gabbro.Body.finalState] at h

/-- **A static Body program keeps every place outside `puts`.** -/
theorem exec_statisch {ρB : Gabbro.Body.Env} {puts : List String} {bs : List Gabbro.Body.Stmt}
    (h : Statisch ρB puts bs) : ∀ t s',
      Gabbro.Body.finalState (Gabbro.Body.exec ρB bs t) = some s' →
      ∀ p, p.carrier ∉ puts → s'.world p = t.world p := by
  induction h with
  | nil =>
    intro t s' h p _
    simp only [Gabbro.Body.exec, Gabbro.Body.finalState, Option.some.injEq] at h
    rw [h]
  | assign cn i f e xs hcn _ ih =>
    intro t s' h p hp
    rcases step_assign ρB cn i f e t with hs | ⟨k, v, hs⟩
    · simp [Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
    · simp only [Gabbro.Body.exec, hs] at h
      rw [ih _ s' h p hp]
      apply Gabbro.Body.store_elsewhere
      intro e'
      apply hp
      rw [e']
      exact hcn
  | bindName x e xs _ ih =>
    intro t s' h p hp
    rcases step_bindName ρB x e t with hs | ⟨v, hs⟩
    · simp [Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
    · simp only [Gabbro.Body.exec, hs] at h
      exact ih _ s' h p hp
  | ret e xs _ _ =>
    intro t s' h p _
    cases e with
    | none =>
      simp only [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.finalState,
        Option.some.injEq] at h
      rw [h]
    | some e' =>
      simp only [Gabbro.Body.exec, Gabbro.Body.step] at h
      cases hv : Gabbro.Body.eval t e' with
      | none => simp [hv, Gabbro.Body.finalState] at h
      | some v =>
        simp only [hv, Gabbro.Body.finalState, Option.some.injEq] at h
        rw [h]
  | call cn ps es pre xs hfr _ ih =>
    intro t s' h p hp
    rcases step_call ρB cn ps es pre t with hs | ⟨t', ht', hs⟩
    · simp [Gabbro.Body.exec, hs, Gabbro.Body.finalState] at h
    · simp only [Gabbro.Body.exec, hs] at h
      rw [ih _ s' h p hp]
      show (ρB cn t').1.world p = t.world p
      rw [hfr t' p hp, ht']
  | ite ce tb te xs _ _ _ ihb ihe ihx =>
    intro t s' h
    rcases step_ite_cases ρB ce tb te t with hs | hs | hs
    · exact rahmen_zweig hs ihb ihx h
    · exact rahmen_zweig hs ihe ihx h
    · have h' : Gabbro.Body.exec ρB (.ite ce tb te :: xs) t = .stuck := by
        simp only [Gabbro.Body.exec, hs]
      rw [h'] at h
      simp [Gabbro.Body.finalState] at h

theorem statisch_rets {ρB : Gabbro.Body.Env} {puts : List String} :
    ∀ (eB : List Gabbro.Body.Stmt), (∀ x ∈ eB, ∃ e, x = .ret (some e)) → Statisch ρB puts eB
  | [], _ => .nil
  | x :: rest, hx => by
      obtain ⟨e, rfl⟩ := hx x (List.mem_cons_self ..)
      exact .ret _ _ (statisch_rets rest (fun y hy => hx y (List.mem_cons_of_mem _ hy)))

/-- A lowered slot write or call, then a static rest. -/
theorem statisch_schritt (S : Stimmig u) (c : Fin u.fns.length) (ρB : Gabbro.Body.Env)
    {Γ : Ctx} {fn : UFn} (hΓ : Γ = fn.params.map (·.2)) (st : UStmt) (ss : List UStmt)
    {Λ Λ' : List (Res (declOf u))} {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ'}
    (hgst : lowStmtL (l := false) u c Γ fn Λ st = .ok ⟨Λ', g⟩) {bB : Gabbro.Body.Stmt}
    (hx : stmtBody u fn st = some bB)
    (hF : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ st :: ss) →
      Gabbro.Body.Frame ρB cname gf.puts)
    {bs' : List Gabbro.Body.Stmt} (IH : Statisch ρB (fnAt u c).puts bs') :
    Statisch ρB (fnAt u c).puts (bB :: bs') := by
  rcases stmt_statischB S c hΓ st hgst hx with ⟨cn, idx, fld, ve, rfl, hcn⟩ |
      ⟨cname, ps, es, pre, gf, rfl, hgf, hsub⟩
  · exact .assign _ _ _ _ _ hcn IH
  · have hcall : ∃ args, UStmt.call cname args ∈ st :: ss := by
      cases st
      case call cn args =>
        simp only [stmtBody] at hx
        split at hx
        · rename_i gf' es' _ _
          simp only [Option.some.injEq] at hx
          cases hx
          exact ⟨args, List.mem_cons_self ..⟩
        · cases hx
      case assign b f ix v =>
        simp only [stmtBody] at hx
        split at hx
        · simp only [Option.some.injEq] at hx; cases hx
        · cases hx
      case assignTab b f ix v =>
        simp only [stmtBody] at hx
        cases hsv : sideExpr u fn v with
        | none => rw [hsv] at hx; cases hx
        | some ve => rw [hsv] at hx; simp at hx
      all_goals simp [stmtBody] at hx
    exact .call _ _ _ _ _ (fun t p hp => hF cname gf hgf hcall t p (fun hm => hp (hsub _ hm))) IH

/-! ## 2. The static frame along the lowering -/

/-- **A lowered block's translation is static**, given the frames of the functions it calls. -/
theorem statischSeq (S : Stimmig u) (c : Fin u.fns.length) (ρB : Gabbro.Body.Env) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) {Λ : List (Res (declOf u))}
      (p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ')
      (rest : List UStmt) (t : List Gabbro.Body.Stmt) (restZ : List UStmt),
      Γ = fn.params.map (·.2) → Sicht u fT fn →
      lowSeqL (l := false) u c Γ fn n Λ [] ss = .ok (p, rest) →
      seqZ u k fT ss = some (t, restZ) →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρB cname gf.puts) →
      restZ = rest ∧ rest <:+ ss ∧ Statisch ρB (fnAt u c).puts t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k ss Γ fn fT Λ p rest t restZ hΓ hS hlow hbs hF
    obtain _ | n := n
    · rw [lowSeqL_zero] at hlow; cases hlow
    obtain _ | k := k
    · exact absurd hbs (by simp [seqZ])
    obtain _ | ⟨s0, ss⟩ := ss
    · rw [lowSeq_nil] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, .nil⟩
    have hFss : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρB cname gf.puts :=
      fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, List.mem_cons_of_mem _ hm⟩
    cases s0
    case blkEnd | ifElse =>
      first
        | rw [lowSeq_blkEnd] at hlow
        | rw [lowSeq_ifElse] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, .nil⟩
    case bind x d v =>
      obtain ⟨bT, fT', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bind hstepT
      obtain ⟨ls, q, hls, hq, rfl⟩ := lowSeq_bind_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x ls.range)
        (fT.mitBindung x (0, 0)) q rest ys restZ
        (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
        (hS.bind x (0, 0) ls.range) hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case bindMut x lo hi v =>
      obtain ⟨bT, fT', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bindMut hstepT
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindMut_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) q rest ys restZ
        (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
        (hS.bind x (lo, hi) (lo, hi)) hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case setVar x v =>
      obtain ⟨bT, fT', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨-, eT, -, rfl, rfl⟩ := schrittB_setVar hstepT
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ q rest ys restZ hΓ hS hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case assign | assignTab | call =>
      obtain ⟨bT, fT', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hstepN, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
      obtain ⟨hx, -⟩ := schrittB_stmt hstepN (fun _ _ _ h => by cases h)
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ q rest ys restZ hΓ hS hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _),
        statisch_schritt S c ρB hΓ _ ss hst hx hF IH.2.2⟩
    case ret r0 =>
      obtain ⟨bst, ys, hbT, hys, rfl⟩ := seqZ_ret_some hbs
      obtain ⟨st, q, hst, hq, rfl⟩ := lowSeq_ret_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ q rest ys restZ hΓ hS hq hys hFss
      have hret : ∃ e, bst = .ret e := by
        cases r0
        case empty =>
          simp only [retZ, Option.some.injEq] at hbT
          exact ⟨_, hbT.symm⟩
        case val sd =>
          simp only [retZ] at hbT
          cases hse : sideExpr u fT sd with
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
      obtain ⟨ce, tt, te, r1, r2, ys, hce, hTZ, hEZ, hYZ, rfl⟩ :=
        seqZ_wenn_some (cnd := cnd) hbs (by first | exact .inl rfl | exact .inr rfl)
      obtain _ | m := n
      · rw [lowStructL_zero] at hst; cases hst
      obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
      obtain ⟨hr1, hsuf1, hSt⟩ := ih m (by omega) k ss fn _ ⟨Λ₁, tb⟩ (.ifElse :: rest1) tt
        (.ifElse :: r1) hΓ hS hT hTZ hFss
      have h1 : r1 = rest1 := (List.cons.inj hr1).2
      rw [h1] at hEZ
      have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
      obtain ⟨hr2, hsuf2, hSe⟩ := ih m (by omega) k rest1 fn _ ⟨Λ₁, eb⟩ (.blkEnd :: rest') te
        (.blkEnd :: r2) hΓ hS hE hEZ
        (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, mem_of_suffix hsuf1' hm⟩)
      have h2 : r2 = rest' := (List.cons.inj hr2).2
      rw [h2] at hYZ
      have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hSc⟩ := ih (m + 1) (by omega) k rest' fn _ q rest ys restZ hΓ hS hq hYZ
        (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, mem_of_suffix hsuf2' hm⟩)
      exact ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), .ite _ _ _ _ hSt hSe hSc⟩
    all_goals exact absurd hbs (by simp [seqZ, schrittB, stmtBody])

/-- **A lowered body's translation is static**, given the frames of the functions it calls. -/
theorem statischZ (S : Stimmig u) (c : Fin u.fns.length) (ρB : Gabbro.Body.Env) (r : URet) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt),
      Γ = fn.params.map (·.2) → Sicht u fT fn →
      lowBodyF u c Γ fn n Λ ss r = .ok b0 → stmtsBodyZ u k fT ss r = some bs →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρB cname gf.puts) →
      Statisch ρB (fnAt u c).puts bs
  | 0, k, ss, Γ, fn, fT, Λ, b0, bs, hΓ, hS, hlow, hbs, hF => by
      simp only [lowBodyF] at hlow <;> cases hlow
  | n + 1, 0, ss, Γ, fn, fT, Λ, b0, bs, hΓ, hS, hlow, hbs, hF => by
      exact absurd hbs (by simp [stmtsBodyZ])
  | n + 1, k + 1, [], Γ, fn, fT, Λ, b0, bs, hΓ, hS, hlow, hbs, hF => by
      simp only [stmtsBodyZ] at hbs
      exact statisch_rets bs (endBody_rets (fn := fT) (r := r) hbs)
  | n + 1, k + 1, s0 :: ss, Γ, fn, fT, Λ, b0, bs, hΓ, hS, hlow, hbs, hF => by
      have hFss : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
          Gabbro.Body.Frame ρB cname gf.puts :=
        fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, List.mem_cons_of_mem _ hm⟩
      cases s0
      case bind x d v =>
        obtain ⟨bB, fT', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bind hstep0
        obtain ⟨ls, rest, hls, hrest, rfl⟩ := lowBodyF_bind_ok c hlow
        exact .bindName _ _ _ (statischZ S c ρB r n k ss (fn.mitBindung x ls.range)
          (fT.mitBindung x (0, 0)) rest bs'
          (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bind x (0, 0) ls.range) hrest hbs' hFss)
      case bindMut x lo hi v =>
        obtain ⟨bB, fT', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bindMut hstep0
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindMut_ok c hlow
        exact .bindName _ _ _ (statischZ S c ρB r n k ss (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) rest bs'
          (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bind x (lo, hi) (lo, hi)) hrest hbs' hFss)
      case setVar x v =>
        obtain ⟨bB, fT', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨-, eT, -, rfl, rfl⟩ := schrittB_setVar hstep0
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.setVar x v) ss trivial hlow
        exact .bindName _ _ _ (statischZ S c ρB r n k ss fn _ rest bs' hΓ hS hrest hbs' hFss)
      case assign | assignTab | call =>
        obtain ⟨bB, fT', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨hstepN, rfl⟩ := schrittB_einzeln_sicht hS hstep0 (by exact True.intro)
        obtain ⟨hx, -⟩ := schrittB_stmt hstepN (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r _ ss (by exact True.intro) hlow
        exact statisch_schritt S c ρB hΓ _ ss hgst hx hF
          (statischZ S c ρB r n k ss fn _ rest bs' hΓ hS hrest hbs' hFss)
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', hce, hTZ, hEZ, hbs', rfl⟩ := stmtsBodyZ_ifBeg_some hbs
        obtain ⟨Λ₁, st, rest', e, hst, hrest, rfl⟩ := lowBodyF_ifBeg_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hSt⟩ := statischSeq S c ρB m k ss fn _ ⟨Λ₁, tb⟩ (.ifElse :: rest1)
          tt (.ifElse :: r1) hΓ hS hT hTZ hFss
        have h1 : r1 = rest1 := (List.cons.inj hr1).2
        rw [h1] at hEZ
        have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hSe⟩ := statischSeq S c ρB m k rest1 fn _ ⟨Λ₁, eb⟩
          (.blkEnd :: rest') te (.blkEnd :: r2) hΓ hS hE hEZ
          (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, mem_of_suffix hsuf1' hm⟩)
        have h2 : r2 = rest' := (List.cons.inj hr2).2
        rw [h2] at hbs'
        have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        exact .ite _ _ _ _ hSt hSe (statischZ S c ρB r n k rest' fn _ e bs' hΓ hS hrest hbs'
          (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, mem_of_suffix hsuf2' hm⟩))
      all_goals exact absurd hbs (by simp [stmtsBodyZ, schrittB, stmtBody])

/-- **A body with local bindings and conditionals changes only the carriers its function
    declares** -- given the frames of the functions it calls. -/
theorem exec_rahmenZ (S : Stimmig u) (c : Fin u.fns.length) (ρB : Gabbro.Body.Env) (r : URet)
    (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) {Λ : List (Res (declOf u))}
    (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt)
    (hΓ : Γ = fn.params.map (·.2)) (hS : Sicht u fT fn)
    (hlow : lowBodyF u c Γ fn n Λ ss r = .ok b0) (hbs : stmtsBodyZ u k fT ss r = some bs)
    (hF : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
      Gabbro.Body.Frame ρB cname gf.puts) :
    ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB bs t) = some s' →
      ∀ p, p.carrier ∉ (fnAt u c).puts → s'.world p = t.world p :=
  exec_statisch (statischZ S c ρB r n k ss fn _ b0 bs hΓ hS hlow hbs hF)

end Gabbro.Bruecke
