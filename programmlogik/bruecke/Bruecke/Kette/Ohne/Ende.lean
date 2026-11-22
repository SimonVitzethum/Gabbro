module
public import Bruecke.Kette.Ohne.Seq
@[expose] public section

/-!
# Carried ending blocks lower without `locks`

The mirror of `laufEndSeq_G`: an explicit ending read by `seqZ` lowers (`lowEndL`) to an ending
block that contains no `locks` block and no scoped return.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem ende_ohne (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) :
    ∀ n k ss {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (b : Endblock (declOf u) (verOf u c) false Γ Λ) rest bs restZ used,
      Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) → EndMarker rest →
      lowEndL (l := false) u c Γ fn n Λ [] ss = .ok (b, rest) →
      seqZ u k fT ns ss = some (bs, restZ, used) →
      restZ = rest ∧ rest <:+ ss ∧ b.ohneLocks = true := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k ss Γ fn fT ns Λ b rest bs restZ used hS hmem hm hlow hbs
    obtain _ | n := n
    · cases hlow
    obtain _ | k := k
    · cases hbs
    obtain _ | ⟨s0, ss⟩ := ss
    · rw [lowEndL_succ] at hlow; cases hlow
    have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
      fun st h => hmem st (List.mem_cons_of_mem _ h)
    have hhead := hmem s0 (List.mem_cons_self ..)
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
        exact ⟨rfl, List.suffix_cons _ _, lowRetEnd_ohne hg⟩
    case bind x d v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind ht
      obtain ⟨ls, q, hls, hq, rfl⟩ := lowEndL_bind_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x ls.range)
        (fT.mitBindung x (0, 0)) (ns.push x) q rest ys restZ used
        (hS.bind x (0, 0) ls.range) hmemss hm hq hy
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Endblock.ohneLocks] using IH.2.2⟩
    case bindW x d v =>
      obtain ⟨id, fields, eT, ys, htT, heT, hy, rfl⟩ := seqZ_bindRecord_some hbs
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEnd_bindRecord_ok ((recordBinderType_sicht hS d v).symm.trans htT) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitWert x (.prod id fields))
        (fT.mitWert x (.prod id fields)) (ns.push x) q rest ys restZ used
        (hS.bindRecord x id fields) hmemss hm hq hy
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Endblock.ohneLocks] using IH.2.2⟩
    case bindMut x lo hi v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut ht
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEndL_bindMut_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used
        (hS.bind x (lo, hi) (lo, hi)) hmemss hm hq hy
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Endblock.ohneLocks] using IH.2.2⟩
    case bindB x v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB ht
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEndL_bindB_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindungB x)
        (fT.mitBindungB x) (ns.push x) q rest ys restZ used (hS.bindB x) hmemss hm hq hy
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Endblock.ohneLocks] using IH.2.2⟩
    case setVar | setVarB | setVarOpt | assign | assignTab | assignOpt | assignTabOpt | assignGlob | assignGlobB | call =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨htN, rfl, rfl⟩ := schrittB_einzeln_sicht hS ht (by trivial)
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowEndL_leaf_ok (by trivial) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hS hmemss hm hq hy
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), ?_⟩
      simp only [Endblock.ohneLocks, Bool.and_eq_true]
      exact ⟨lowStmtL_einzeln_ohne S.tab (by trivial) hst, IH.2.2⟩
    case bindOpt x num v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hn, eT, heT, rfl, rfl, rfl⟩ := schrittB_bindOpt ht
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEndL_bindOpt_ok (hn := hn) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩))
        (fT.mitOpt x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) q rest ys restZ used
        (hS.bindOpt x num ((declOf u).count ⟨num, hn⟩)) hmemss hm hq hy
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Endblock.ohneLocks] using IH.2.2⟩
    case matchWhyBeg x =>
      obtain ⟨count, e, arms, tailZ, allocated, ys, he, hAZ, hYZ, rfl⟩ := seqZ_reason_some hbs
      obtain ⟨id, ht, hid, rfl⟩ := reasonSubject_some he
      have ht' : valueParamTy fn x = some (.why count) := (hS.2.2.2.2 x).symm.trans ht
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowEndL_struct_ok (.inr (.inr (.inr (.inr ⟨x, rfl⟩)))) hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨j, v, ga, hj, hv, hAG, hΛ, hst⟩ := lowStruct_reason_ok ht' hStruct
      subst Λ₁
      cases hst
      obtain ⟨hr, hsuf, hArms⟩ := arms_ohne_with m (by
          intro fuel hlt k ss _ fn ft ns _ p tail bs tailZ used hV hm hG hB
          exact seq_ohne S c hc fuel k ss fn ft ns p tail bs tailZ used hV hm hG hB)
        m (Nat.le_refl m) count k 0 ss fn fT ns Λ ga
        (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hS hmemss hAG hAZ
      have ht : tailZ = tail := (List.cons.inj hr).2
      subst tailZ
      have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used
        hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm)) hm hQ hYZ
      refine ⟨IH.1, (IH.2.1.trans hsuf').trans (List.suffix_cons _ _), ?_⟩
      simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨hArms, IH.2.2⟩
    case matchTagBeg sidx x binders =>
      obtain ⟨cs, e, arms, tailZ, allocated, ys, hn, he, hAZ, hYZ, rfl⟩ := seqZ_tag_some hbs
      obtain ⟨id, ht, hBare, hid, rfl⟩ := tagSubject_some he
      have ht' : valueParamTy fn x = some (.sum cs) := (hS.2.2.2.2 x).symm.trans ht
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowEndL_struct_ok (.inr (.inr (.inr (.inl ⟨sidx, x, binders, rfl⟩)))) hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨j, v, tagG, hj, hv, hTagG, hΛ, hst⟩ := lowStruct_tag_ok hn ht' hStruct
      subst Λ₁
      cases hst
      obtain ⟨ga, hAG, hBareRel⟩ := lowArms_bare m fn Λ cs binders ss tagG (.blkEnd :: tail) hBare hTagG
      obtain ⟨hr, hsuf, hArms⟩ := arms_ohne_with m (by
          intro fuel hlt k ss _ fn ft ns _ p tail bs tailZ used hV hm hG hB
          exact seq_ohne S c hc fuel k ss fn ft ns p tail bs tailZ used hV hm hG hB)
        m (Nat.le_refl m) cs.length k 0 ss fn fT ns Λ ga
        (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hS hmemss hAG hAZ
      have ht : tailZ = tail := (List.cons.inj hr).2
      subst tailZ
      have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used
        hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm)) hm hQ hYZ
      refine ⟨IH.1, (IH.2.1.trans hsuf').trans (List.suffix_cons _ _), ?_⟩
      simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨hBareRel.ohne hArms, IH.2.2⟩
    case matchBeg num v x =>
      obtain ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, he, hPZ, hAZ, hYZ, rfl⟩ := seqZ_option_some hbs
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowEndL_struct_ok (.inr (.inr (.inl ⟨num, v, x, rfl⟩))) hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨ev, pG, aG, rest1, hv, hPG, hAG, rfl⟩ := lowStruct_option_ok hn hStruct
      obtain ⟨hr1, hsuf1, hP⟩ := seq_ohne S c hc m k ss
        (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩))
        (fT.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x)
        ⟨Λ₁, pG⟩ (.ifElse :: rest1) pb (.ifElse :: r1) used1
        (hS.index x num ((declOf u).count ⟨num, hn⟩)) hmemss hPG hPZ
      have h1 : r1 = rest1 := (List.cons.inj hr1).2
      subst r1
      have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
      obtain ⟨hr2, hsuf2, hA⟩ := seq_ohne S c hc m k rest1 fn fT
        (ns.resume used1) ⟨Λ₁, aG⟩ (.blkEnd :: tail) ab (.blkEnd :: r2) used2 hS
        (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) hAG hAZ
      have h2 : r2 = tail := (List.cons.inj hr2).2
      subst r2
      have hsuf2' : tail <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hRest⟩ := ih (m + 1) (by omega) k tail fn fT
        (ns.resume used2) q rest ys restZ used hS
        (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hm hQ hYZ
      refine ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), ?_⟩
      simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨⟨hP, hA⟩, hRest⟩
    case bindCall x g args =>
      obtain ⟨bB, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨bt, hbT, rfl, rfl⟩ := schrittB_bindCall ht
      obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowEndL_bindCall_ok hlow
      obtain ⟨hty, sh, hsh⟩ := resultCall_type hk he hbT
      subst bt
      obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
      have hf := fnIdx_find _ _ _ hi
      have hd := callee_getragen_calls S hc (CallsIn.bind hhead) hf
      have hType := (S.boolErg head.callee hd).1
      have IH := ih n (Nat.lt_succ_self n) k ss (mitRuf u fn x head.callee ty) (fT.mitTy x ty)
        (ns.push x) q rest ys restZ used (hS.bindRuf x head.callee hsh hType he) hmemss hm hq hy
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Endblock.ohneLocks] using IH.2.2⟩
    case narrowBeg x lo hi =>
      obtain ⟨e, errorBody, tailZ, ys, hname, hEZ, hYZ, rfl⟩ := seqZ_narrow_some hbs
      obtain ⟨hn, id, hid, rfl⟩ := narrowName_some hname
      have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
      obtain ⟨j, a, b, v, err, tail, q, hj, hv, hEG, hQG, rfl⟩ := lowEndL_narrow_ok hn' hlow
      have heq : tail = tailZ := (List.cons.inj (endBodyZ_rest n k ss fn fT ns err
        (.blkEnd :: tail) (.blkEnd :: tailZ) errorBody hEG hEZ)).2
      subst tailZ
      have hsuf := (List.suffix_cons _ _).trans (endBodyZ_suffix k fT ns ss errorBody _ hEZ)
      have hErr := endBodyZ_ohne S.tab c n k ss fn fT ns err (.blkEnd :: tail) errorBody hS hEG hEZ
      have IH := ih n (Nat.lt_succ_self n) k tail (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used
        (hS.bind x (lo, hi) (lo, hi)) (fun st h => hmemss st (mem_of_suffix hsuf h)) hm hQG hYZ
      refine ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), ?_⟩
      simp only [Endblock.ohneLocks, Bool.and_eq_true]
      exact ⟨hErr, IH.2.2⟩
    case loopBeg x tab inv =>
      obtain ⟨rfl, tZ, bodyB, tailZ, allocated, ys, htZ, hBodyZ, hTailZ, rfl⟩ := seqZ_loop_some hbs
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowEndL_struct_ok (.inr (.inl ⟨x, tab, rfl⟩)) hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨_, bodyG, ht, hBodyG, hΛ, hst⟩ := lowStruct_loop_ok hStruct
      subst Λ₁
      cases hst
      rw [ht] at htZ
      cases htZ
      obtain ⟨hrBody, hsufBody, hBody⟩ := seq_ohne S c hc m k ss
        (fn.mitIndex x tZ.val ((declOf u).count tZ)) (fT.mitIndex x tZ.val ((declOf u).count tZ))
        (ns.push x) ⟨Λ, bodyG⟩ (.blkEnd :: tail) bodyB (.blkEnd :: tailZ) allocated
        (hS.index x tZ.val ((declOf u).count tZ)) hmemss hBodyG hBodyZ
      have htail : tailZ = tail := (List.cons.inj hrBody).2
      subst tailZ
      have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans hsufBody
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used hS
        (fun st h => hmemss st (mem_of_suffix hsuf h)) hm hQ hTailZ
      refine ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), ?_⟩
      simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨hBody, IH.2.2⟩
    case ifBeg cnd | ifEnde cnd =>
      obtain ⟨ce, tt, te, r1, r2, ys, used1, used2, hce, hTZ, hEZ, hYZ, rfl⟩ :=
        seqZ_wenn_some (cnd := cnd) hbs (by first | exact .inl rfl | exact .inr rfl)
      have hcases : EndIfCases u c Γ fn n Λ cnd ss b rest := by
        first
        | exact lowEndL_ifEnde_cases hm hlow
        | exact Or.inr (lowEndL_struct_ok (.inl ⟨cnd, rfl⟩) hlow)
      rcases hcases with ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ |
        ⟨Λ₁, st, tail, q, hst, hq, rfl⟩
      · obtain ⟨hr1, hsuf1, hBt⟩ := ih n (Nat.lt_succ_self n) k ss fn fT ns tb
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hS hmemss True.intro hT hTZ
        have h1 := (List.cons.inj hr1).2
        subst r1
        have hsuf1' := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hBe⟩ := ih n (Nat.lt_succ_self n) k rest1 fn fT (ns.resume used1) eb
          (.blkEnd :: rest) te (.blkEnd :: r2) used2 hS
          (fun st h => hmemss st (mem_of_suffix hsuf1' h)) True.intro hE hEZ
        have h2 := (List.cons.inj hr2).2
        subst r2
        obtain ⟨rfl, rfl, _⟩ := seqZ_marker_some hm hYZ
        refine ⟨rfl, ((List.suffix_cons _ _).trans hsuf2).trans (hsuf1'.trans (List.suffix_cons _ _)), ?_⟩
        simp only [Endblock.ohneLocks, Bool.and_eq_true]
        exact ⟨hBt, hBe⟩
      · obtain _ | m := n
        · rw [lowStructL_zero] at hst; cases hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hBt⟩ := seq_ohne S c hc m k ss fn fT ns ⟨Λ₁, tb⟩
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hS hmemss hT hTZ
        have h1 := (List.cons.inj hr1).2
        subst r1
        have hsuf1' := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hBe⟩ := seq_ohne S c hc m k rest1 fn fT (ns.resume used1)
          ⟨Λ₁, eb⟩ (.blkEnd :: tail) te (.blkEnd :: r2) used2 hS
          (fun st h => hmemss st (mem_of_suffix hsuf1' h)) hE hEZ
        have h2 := (List.cons.inj hr2).2
        subst r2
        have hsuf2' := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume used2) q rest ys restZ used
          hS (fun st h => hmemss st (mem_of_suffix hsuf2' h)) hm hq hYZ
        refine ⟨IH.1, (IH.2.1.trans hsuf2').trans (List.suffix_cons _ _), ?_⟩
        simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
        exact ⟨⟨hBt, hBe⟩, IH.2.2⟩
    all_goals exact absurd hbs (by simp only [seqZ, schrittB, namedStmt, stmtBody,
      Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

end Gabbro.Bruecke
