module
public import Bruecke.Kette.Formen.StatischSchritt
public import Bruecke.Anweisung.Zweig.Rahmen
public import Bruecke.Anweisung.Zweig.Lesen
public import Bruecke.Anweisung.Bereich.Rahmen
public import Bruecke.Anweisung.Schleife.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem statischSeq_G (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env) :
    ∀ (n : Nat) {loopMode : Bool} (k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) loopMode Γ Λ Λ')
      (rest : List UStmt) (t : List Gabbro.Body.Stmt) (restZ : List UStmt) (used : List String),
      Γ = fn.params.map (·.2) → Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowSeqL (l := loopMode) u c Γ fn n Λ [] ss = .ok (p, rest) →
      seqZ u k fT ns ss = some (t, restZ, used) →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, CallsIn ss cname args) →
        Gabbro.Body.Frame ρB cname (writesU gf)) →
      restZ = rest ∧ rest <:+ ss ∧ Statisch ρB (writesU (fnAt u c)) t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro loopMode k ss Γ fn fT ns Λ p rest t restZ used hΓ hS hmem hlow hbs hF
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
    have hFss : ∀ cname gf, fnSuch u cname = some gf → (∃ args, CallsIn ss cname args) →
        Gabbro.Body.Frame ρB cname (writesU gf) :=
      fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, hm.cons _⟩
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
    case bindB x v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB hstepT
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindB_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindungB x)
        (fT.mitBindungB x) (ns.push x) q rest ys restZ used
        (by rw [mitBindungB_ctx]; exact congrArg (List.cons _) hΓ)
        (hS.bindB x) hmemss hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case loopBeg x tab inv =>
      obtain ⟨rfl, hg, tZ, bodyB, tailZ, allocated, ys, htZ, hBodyZ, hTailZ, rfl⟩ := seqZ_loop_some hbs
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowSeq_loop_ok hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨t, bodyG, ht, hBodyG, hΛ, hst⟩ := lowStruct_loop_ok hStruct
      subst Λ₁
      cases hst
      have htEq : tZ = t := by
        rw [ht] at htZ
        exact (Except.ok.inj htZ).symm
      subst tZ
      obtain ⟨htail, hsuf⟩ := loopWrites_rest m k ss
        (fn.mitIndex x t.val ((declOf u).count t)) (fT.mitIndex x t.val ((declOf u).count t))
        (ns.push x) bodyG tail tailZ bodyB allocated hg hBodyG hBodyZ
      subst tailZ
      have hmemTail : ∀ st ∈ tail, st ∈ (fnAt u c).body := fun st hm => hmemss st (mem_of_suffix hsuf hm)
      have hΓi : .index ((declOf u).count t) :: Γ =
          (fn.mitIndex x t.val ((declOf u).count t)).params.map (·.2) := congrArg (List.cons _) hΓ
      obtain ⟨_, _, hFrameBody⟩ := ih m (by omega) k ss
        (fn.mitIndex x t.val ((declOf u).count t)) (fT.mitIndex x t.val ((declOf u).count t))
        (ns.push x) ⟨Λ, bodyG⟩ (.blkEnd :: tail) bodyB (.blkEnd :: tail) allocated
        hΓi (hS.index x t.val ((declOf u).count t)) hmemss hBodyG hBodyZ hFss
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used hΓ hS hmemTail hQ hTailZ
        (fun g gf hgf ⟨args, hc⟩ => hFss g gf hgf ⟨args, hc.mono (fun _ hm => mem_of_suffix hsuf hm)⟩)
      exact ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), .forEach _ _ _ _ hFrameBody IH.2.2⟩
    case narrowBeg x lo hi =>
      obtain ⟨e, errorBody, tailZ, ys, hname, hEZ, hYZ, rfl⟩ := seqZ_narrow_some hbs
      obtain ⟨hn, id, hid, rfl⟩ := narrowName_some hname
      have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
      have hid' : ns.lookup fn x = some id := (BodyNames.lookup_sicht hS ns x).symm.trans hid
      obtain ⟨j, a, b, v, err, tail, q, hj, hv, hEG, hQG, rfl⟩ := lowSeq_narrow_ok hn' hlow
      have heq : tail = tailZ := (List.cons.inj (endBodyZ_rest n k ss fn fT ns err
        (.blkEnd :: tail) (.blkEnd :: tailZ) errorBody hEG hEZ)).2
      subst tailZ
      have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans (endBodyZ_suffix k fT ns ss errorBody _ hEZ)
      have hmemTail : ∀ st ∈ tail, st ∈ (fnAt u c).body := fun st hm => hmemss st (mem_of_suffix hsuf hm)
      have hErr := endBodyZ_statisch S hc ρB n k ss fn fT ns err (.blkEnd :: tail)
        errorBody hΓ hS hmemss hEG hEZ hFss
      have hΓ' : .int lo hi :: Γ = (fn.mitBindung x (lo, hi)).params.map (·.2) :=
        congrArg (List.cons _) hΓ
      have IH := ih n (Nat.lt_succ_self n) k tail (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used hΓ' (hS.bind x (lo, hi) (lo, hi))
        hmemTail hQG hYZ (fun g gf hgf ⟨args, hc⟩ => hFss g gf hgf ⟨args, hc.mono (fun _ hm => mem_of_suffix hsuf hm)⟩)
      exact ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _),
        .ite _ _ _ _ (.bindName _ _ _ .nil) hErr IH.2.2⟩
    case bindCall x g args =>
      obtain ⟨bB, fT', ns', ys, hstep, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨bt, hb, rfl, rfl⟩ := schrittB_bindCall hstep
      obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowSeq_bindCall_ok hlow
      obtain ⟨ht, sh, hsh⟩ := resultCall_type hk he hb
      subst bt
      rw [mitRuf_scalar fn x head.callee hsh] at hq
      obtain ⟨gf, raw, es, _, hgf, _, _, _, _, rfl⟩ := namedResult_some hb
      obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
      have hf : fnSuch u g = some (fnAt u head.callee) := fnIdx_find _ _ _ hi
      rw [hf] at hgf
      cases hgf
      have hctx : ty :: Γ = (fn.mitTy x ty).params.map (·.2) := by
        cases ty
        case int | bool | prod => exact congrArg (List.cons _) hΓ
        all_goals cases hsh
      have hsub := lowRufKopf_writes S hc hk (CallsIn.bind hhead)
      have hframe := hF g (fnAt u head.callee) hf ⟨args, CallsIn.bind (List.mem_cons_self ..)⟩
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitTy x ty)
        (fT.mitTy x ty) (ns.push x) q rest ys restZ used hctx (hS.bindTy x hsh) hmemss hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _),
        .bindCall _ _ _ _ _ _ (fun t p hp => hframe t p (fun hm => hp (hsub _ hm))) IH.2.2⟩
    case setVar x v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨-, id, eT, -, -, rfl, rfl, rfl⟩ := schrittB_setVar hstepT
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hΓ hS hmemss hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case setVarB x v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨id, eT, -, -, rfl, rfl, rfl⟩ := schrittB_setVarB hstepT
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hΓ hS hmemss hq hys hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case assign | assignTab | assignGlob | call =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hstepN, rfl, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
      obtain ⟨hx, -, -⟩ := schrittB_stmt hstepN (fun _ _ _ h => by cases h)
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
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
        case bool sd =>
          simp only [retZ] at hbT
          cases hse : condZ u fT ns sd with
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
        (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, hm.mono (fun _ h => mem_of_suffix hsuf1' h)⟩)
      have h2 : r2 = rest' := (List.cons.inj hr2).2
      rw [h2] at hYZ
      have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hSc⟩ := ih (m + 1) (by omega) k rest' fn _ (ns.resume used2) q rest ys restZ used hΓ hS (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hq hYZ
        (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, hm.mono (fun _ h => mem_of_suffix hsuf2' h)⟩)
      exact ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), .ite _ _ _ _ hSt hSe hSc⟩
    all_goals exact absurd hbs (by simp only [seqZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

end Gabbro.Bruecke
