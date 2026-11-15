module
public import Bruecke.Kette.RahmenBlock
public import Bruecke.Anweisung.Zweig.EndForm
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem statischEndSeq_G (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env) :
    ∀ n k ss {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (b : Endblock (declOf u) (verOf u c) false Γ Λ) rest bs restZ used,
      Γ = fn.params.map (·.2) → Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) → EndMarker rest →
      lowEndL (l := false) u c Γ fn n Λ [] ss = .ok (b, rest) →
      seqZ u k fT ns ss = some (bs, restZ, used) →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, CallsIn ss cname args) →
        Gabbro.Body.Frame ρB cname (writesU gf)) →
      restZ = rest ∧ rest <:+ ss ∧ Statisch ρB (writesU (fnAt u c)) bs := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k ss Γ fn fT ns Λ b rest bs restZ used hΓ hS hmem hm hlow hbs hF
    obtain _ | n := n
    · cases hlow
    obtain _ | k := k
    · cases hbs
    obtain _ | ⟨s0, ss⟩ := ss
    · rw [lowEndL_succ] at hlow; cases hlow
    have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
      fun st h => hmem st (List.mem_cons_of_mem _ h)
    have hhead := hmem s0 (List.mem_cons_self ..)
    have hFss : ∀ cn gf, fnSuch u cn = some gf → (∃ args, CallsIn ss cn args) →
        Gabbro.Body.Frame ρB cn (writesU gf) :=
      fun cn gf hf ⟨args, ha⟩ => hF cn gf hf ⟨args, ha.cons _⟩
    cases s0
    case blkEnd | ifElse => rw [lowEndL_succ] at hlow; cases hlow
    case leave x | next x =>
      obtain ⟨hl, _, _⟩ := (by first
        | exact lowEnd_control_ok (leave := true) hlow
        | exact lowEnd_control_ok (leave := false) hlow)
      cases hl
    case ret r =>
      obtain ⟨bst, ys, hr, hy, rfl⟩ := seqZ_ret_some hbs
      rw [lowEndL_succ] at hlow
      simp only [lowEndStep] at hlow
      cases hg : lowRetEnd (l := false) u c Γ fn Λ [] r with
      | error e => simp only [hg, Except.map] at hlow; cases hlow
      | ok e =>
        simp only [hg, Except.map] at hlow
        cases hlow
        obtain ⟨rfl, rfl, _⟩ := seqZ_marker_some hm hy
        refine ⟨rfl, List.suffix_cons _ _, ?_⟩
        have hret : ∃ e, bst = .ret e := by
          cases r <;> simp only [retZ, Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq] at hr
          case empty => exact ⟨none, hr.symm⟩
          case val | bool | wert => obtain ⟨e, _, he⟩ := hr; exact ⟨some e, he.symm⟩
          case opt v =>
            obtain ⟨e, _, he⟩ := hr; exact ⟨some e, he.symm⟩
          case why n =>
            cases hr
            exact ⟨_, rfl⟩
        obtain ⟨e, rfl⟩ := hret
        exact .ret _ _ .nil
    case bind x d v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind ht
      obtain ⟨ls, q, hls, hq, rfl⟩ := lowEndL_bind_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x ls.range)
        (fT.mitBindung x (0, 0)) (ns.push x) q rest ys restZ used
        (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
        (hS.bind x (0, 0) ls.range) hmemss hm hq hy hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case bindMut x lo hi v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut ht
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEndL_bindMut_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used
        (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
        (hS.bind x (lo, hi) (lo, hi)) hmemss hm hq hy hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case bindB x v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB ht
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEndL_bindB_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindungB x) (fT.mitBindungB x)
        (ns.push x) q rest ys restZ used (by rw [mitBindungB_ctx]; exact congrArg (List.cons _) hΓ)
        (hS.bindB x) hmemss hm hq hy hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case setVar x v | setVarB x v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      first
      | obtain ⟨-, id, eT, -, -, rfl, rfl, rfl⟩ := schrittB_setVar ht
      | obtain ⟨id, eT, -, -, rfl, rfl, rfl⟩ := schrittB_setVarB ht
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowEndL_leaf_ok (by trivial) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hΓ hS hmemss hm hq hy hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), .bindName _ _ _ IH.2.2⟩
    case assign | assignTab | assignGlob | assignGlobB | call =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨htN, rfl, rfl⟩ := schrittB_einzeln_sicht hS ht (by trivial)
      obtain ⟨hx, -, -⟩ := schrittB_stmt htN (fun _ _ _ h => by cases h)
        (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowEndL_leaf_ok (by trivial) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hΓ hS hmemss hm hq hy hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _),
        statisch_schritt_G S c hc ρB hΓ _ ss hhead hst hx hF IH.2.2⟩
    case bindCall x g args =>
      obtain ⟨bB, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨bt, hb, rfl, rfl⟩ := schrittB_bindCall ht
      obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowEndL_bindCall_ok hlow
      obtain ⟨hty, sh, hsh⟩ := resultCall_type hk he hb
      subst bt
      have hmit : mitRuf u fn x head.callee ty = fn.mitTy x ty := by
        cases ty with
        | int lo hi => exact mitRuf_int _ _ _ _ _ _
        | bool => exact mitRuf_bool _ _ _ _
        | prod id fs => rfl
        | opt n =>
          cases ho : (fnAt u head.callee).resOpt with
          | none => simp only [mitRuf, ho]
          | some entry => simp only [mitRuf, ho]
        | _ => simp only [shapeOfTy] at hsh; cases hsh
      rw [hmit] at hq
      obtain ⟨gf, raw, es, _, hgf, _, _, _, _, rfl⟩ := namedResult_some hb
      obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
      have hf : fnSuch u g = some (fnAt u head.callee) := fnIdx_find _ _ _ hi
      rw [hf] at hgf
      cases hgf
      have hctx : ty :: Γ = (fn.mitTy x ty).params.map (·.2) := by
        cases ty
        case int | bool | prod | opt => exact congrArg (List.cons _) hΓ
        all_goals cases hsh
      have hsub := lowRufKopf_writes S hc hk (CallsIn.bind hhead)
      have hframe := hF g (fnAt u head.callee) hf ⟨args, CallsIn.bind (List.mem_cons_self ..)⟩
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitTy x ty) (fT.mitTy x ty)
        (ns.push x) q rest ys restZ used hctx (hS.bindTy x hsh) hmemss hm hq hy hFss
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _),
        .bindCall _ _ _ _ _ _ (fun t p hp => hframe t p (fun ha => hp (hsub _ ha))) IH.2.2⟩
    case narrowBeg x lo hi =>
      obtain ⟨e, errorBody, tailZ, ys, hname, hEZ, hYZ, rfl⟩ := seqZ_narrow_some hbs
      obtain ⟨hn, id, hid, rfl⟩ := narrowName_some hname
      have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
      obtain ⟨j, a, b, v, err, tail, q, hj, hv, hEG, hQG, rfl⟩ := lowEndL_narrow_ok hn' hlow
      have heq : tail = tailZ := (List.cons.inj (endBodyZ_rest n k ss fn fT ns err
        (.blkEnd :: tail) (.blkEnd :: tailZ) errorBody hEG hEZ)).2
      subst tailZ
      have hsuf := (List.suffix_cons _ _).trans (endBodyZ_suffix k fT ns ss errorBody _ hEZ)
      have hErr := endBodyZ_statisch S hc ρB n k ss fn fT ns err (.blkEnd :: tail)
        errorBody hΓ hS hmemss hEG hEZ hFss
      have IH := ih n (Nat.lt_succ_self n) k tail (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used (congrArg (List.cons _) hΓ)
        (hS.bind x (lo, hi) (lo, hi)) (fun st h => hmemss st (mem_of_suffix hsuf h)) hm hQG hYZ
        (fun g gf hf ⟨args, ha⟩ => hFss g gf hf ⟨args, ha.mono (fun _ h => mem_of_suffix hsuf h)⟩)
      exact ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _),
        .ite _ _ _ _ (.bindName _ _ _ .nil) hErr IH.2.2⟩
    case loopBeg x tab inv =>
      obtain ⟨rfl, tZ, bodyB, tailZ, allocated, ys, htZ, hBodyZ, hTailZ, rfl⟩ := seqZ_loop_some hbs
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowEndL_struct_ok (.inr ⟨x, tab, rfl⟩) hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨_, bodyG, ht, hBodyG, hΛ, hst⟩ := lowStruct_loop_ok hStruct
      subst Λ₁
      cases hst
      rw [ht] at htZ
      cases htZ
      obtain ⟨hrBody, hsufBody, hFrame⟩ := statischSeq_G S c hc ρB m k ss
        (fn.mitIndex x tZ.val ((declOf u).count tZ)) (fT.mitIndex x tZ.val ((declOf u).count tZ))
        (ns.push x) ⟨Λ, bodyG⟩ (.blkEnd :: tail) bodyB (.blkEnd :: tailZ) allocated
        (congrArg (List.cons _) hΓ) (hS.index x tZ.val ((declOf u).count tZ)) hmemss hBodyG hBodyZ hFss
      have htail : tailZ = tail := (List.cons.inj hrBody).2
      subst tailZ
      have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans hsufBody
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used hΓ hS
        (fun st h => hmemss st (mem_of_suffix hsuf h)) hm hQ hTailZ
        (fun g gf hf ⟨args, ha⟩ => hFss g gf hf ⟨args, ha.mono (fun _ h => mem_of_suffix hsuf h)⟩)
      exact ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), .forEach _ _ _ _ hFrame IH.2.2⟩
    case ifBeg cnd | ifEnde cnd =>
      obtain ⟨ce, tt, te, r1, r2, ys, used1, used2, hce, hTZ, hEZ, hYZ, rfl⟩ :=
        seqZ_wenn_some (cnd := cnd) hbs (by first | exact .inl rfl | exact .inr rfl)
      have hcases : EndIfCases u c Γ fn n Λ cnd ss b rest := by
        first
        | exact lowEndL_ifEnde_cases hm hlow
        | exact Or.inr (lowEndL_struct_ok (.inl ⟨cnd, rfl⟩) hlow)
      rcases hcases with ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ |
        ⟨Λ₁, st, tail, q, hst, hq, rfl⟩
      · obtain ⟨hr1, hsuf1, hSt⟩ := ih n (Nat.lt_succ_self n) k ss fn fT ns tb
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hΓ hS hmemss True.intro hT hTZ hFss
        have h1 := (List.cons.inj hr1).2
        subst r1
        have hsuf1' := (List.suffix_cons _ _).trans hsuf1
        have hFE : ∀ cn gf, fnSuch u cn = some gf → (∃ args, CallsIn rest1 cn args) →
            Gabbro.Body.Frame ρB cn (writesU gf) :=
          fun cn gf hf ⟨args, ha⟩ => hFss cn gf hf ⟨args, ha.mono (fun _ h => mem_of_suffix hsuf1' h)⟩
        obtain ⟨hr2, hsuf2, hSe⟩ := ih n (Nat.lt_succ_self n) k rest1 fn fT (ns.resume used1) eb
          (.blkEnd :: rest) te (.blkEnd :: r2) used2 hΓ hS
          (fun st h => hmemss st (mem_of_suffix hsuf1' h)) True.intro hE hEZ hFE
        have h2 := (List.cons.inj hr2).2
        subst r2
        obtain ⟨rfl, rfl, _⟩ := seqZ_marker_some hm hYZ
        exact ⟨rfl, ((List.suffix_cons _ _).trans hsuf2).trans
          (hsuf1'.trans (List.suffix_cons _ _)), .ite _ _ _ _ hSt hSe .nil⟩
      · obtain _ | m := n
        · rw [lowStructL_zero] at hst; cases hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hSt⟩ := statischSeq_G S c hc ρB m k ss fn fT ns ⟨Λ₁, tb⟩
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hΓ hS hmemss hT hTZ hFss
        have h1 := (List.cons.inj hr1).2
        subst r1
        have hsuf1' := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hSe⟩ := statischSeq_G S c hc ρB m k rest1 fn fT (ns.resume used1)
          ⟨Λ₁, eb⟩ (.blkEnd :: tail) te (.blkEnd :: r2) used2 hΓ hS
          (fun st h => hmemss st (mem_of_suffix hsuf1' h)) hE hEZ
          (fun cn gf hf ⟨args, ha⟩ => hFss cn gf hf ⟨args, ha.mono (fun _ h => mem_of_suffix hsuf1' h)⟩)
        have h2 := (List.cons.inj hr2).2
        subst r2
        have hsuf2' := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume used2) q rest ys restZ used hΓ hS
          (fun st h => hmemss st (mem_of_suffix hsuf2' h)) hm hq hYZ
          (fun cn gf hf ⟨args, ha⟩ => hFss cn gf hf ⟨args, ha.mono (fun _ h => mem_of_suffix hsuf2' h)⟩)
        exact ⟨IH.1, (IH.2.1.trans hsuf2').trans (List.suffix_cons _ _), .ite _ _ _ _ hSt hSe IH.2.2⟩
    all_goals exact absurd hbs (by simp only [seqZ, schrittB, namedStmt, stmtBody,
      Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

end Gabbro.Bruecke
