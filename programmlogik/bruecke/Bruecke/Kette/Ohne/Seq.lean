module
public import Bruecke.Kette.Ohne.EndBody
@[expose] public section

/-!
# Carried block sequences lower without `locks`

Along the reader `seqZ` (and `reasonArmsZ` for the arms of a match), every lowered block of a
carried function contains no `locks` block and no scoped return. The induction follows
`laufSeq_G` and `reasonArms_G_with` case by case, without their semantic content.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- The arms of a reason or tag match, given the sequence statement below a fuel bound. -/
theorem arms_ohne_with {loopMode : Bool} {c : Fin u.fns.length} (bound : Nat)
    (hseq : ∀ fuel, fuel < bound → ∀ k ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
      {Λ : List (Res (declOf u))} (p : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ Λ')
      tail bs tailZ used,
      Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowSeqL u c Γ fn fuel Λ [] ss = .ok (p, tail) →
      seqZ u k ft ns ss = some (bs, tailZ, used) →
      tailZ = tail ∧ tail <:+ ss ∧ p.2.ohneLocks = true) :
    ∀ fuel, fuel ≤ bound → ∀ count k offset ss {Γ : Ctx} (fn ft : UFn) (ns : BodyNames)
      (Λ : List (Res (declOf u))) (ga : GrundArms (declOf u) (verOf u c) loopMode Γ Λ Λ count)
      tail bs tailZ used,
      Sicht u ft fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowGArmsL u c Γ fn fuel Λ [] count ss = .ok (ga, tail) →
      reasonArmsZ u k ft count offset ns ss = some (bs, tailZ, used) →
      tailZ = tail ∧ tail <:+ ss ∧ ga.ohneLocks = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro hbound count k offset ss Γ fn ft ns Λ ga tail bs tailZ used hV hm hG hB
    cases hG
  | succ fuel ih =>
    intro hbound count k offset ss Γ fn ft ns Λ ga tail bs tailZ used hV hm hG hB
    cases count with
    | zero =>
      change Except.ok (GrundArms.nil, ss) = .ok (ga, tail) at hG
      cases hG
      simp only [reasonArmsZ, readReasonArms, Option.some.injEq, Prod.mk.injEq] at hB
      obtain ⟨rfl, rfl, _⟩ := hB
      exact ⟨rfl, List.suffix_refl _, rfl⟩
    | succ count =>
      obtain ⟨gbody, grest, remaining, hg, hcG, rfl⟩ := lowGArms_succ hG
      obtain ⟨bbody, remainingZ, allocated, hb, hcB⟩ := reasonArmsZ_succ hB
      obtain ⟨hr, hsuf, hBody⟩ := hseq fuel (by omega) k ss fn ft ns
        ⟨Λ, gbody⟩ remaining bbody remainingZ allocated hV hm hg hb
      subst remainingZ
      rcases hcG with ⟨rfl, rfl⟩ | ⟨m, rest, rfl, hrG, hgrest⟩
      · rcases hcB with ⟨_, rfl, rfl, _⟩ | ⟨m, rest, bs, hn, _⟩
        · cases grest
          refine ⟨rfl, hsuf, ?_⟩
          simp only [GrundArms.ohneLocks, Bool.and_true]
          exact hBody
        · cases hn
      · rcases hcB with ⟨hn, _⟩ | ⟨m', restZ, bs', hn, hrB, hbrest, rfl⟩
        · cases hn
        · cases hn
          subst hrG
          cases hrB
          have hsuf' : rest <:+ ss := (List.suffix_cons _ _).trans hsuf
          obtain ⟨htail, hsufTail, hR⟩ := ih (by omega) (m + 1) k (offset + 1) rest fn ft
            (ns.resume allocated) Λ grest tail bs' tailZ used hV
            (fun st h => hm st (mem_of_suffix hsuf' h)) hgrest hbrest
          refine ⟨htail, hsufTail.trans hsuf', ?_⟩
          simp only [GrundArms.ohneLocks, Bool.and_eq_true]
          exact ⟨hBody, hR⟩

/-- **Every carried block sequence lowers without `locks`.** -/
theorem seq_ohne (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) :
    ∀ (n : Nat) {loopMode : Bool} (k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames)
      {Λ : List (Res (declOf u))}
      (p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) loopMode Γ Λ Λ')
      (rest : List UStmt) (t : List Gabbro.Body.Stmt) (restZ : List UStmt) (used : List String),
      Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowSeqL (l := loopMode) u c Γ fn n Λ [] ss = .ok (p, rest) →
      seqZ u k fT ns ss = some (t, restZ, used) →
      restZ = rest ∧ rest <:+ ss ∧ p.2.ohneLocks = true := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro loopMode k ss Γ fn fT ns Λ p rest t restZ used hS hmem hlow hbs
    obtain _ | n := n
    · rw [lowSeqL_zero] at hlow; cases hlow
    obtain _ | k := k
    · exact absurd hbs (by simp only [seqZ, reduceCtorEq, not_false_eq_true])
    obtain _ | ⟨s0, ss⟩ := ss
    · rw [lowSeq_nil] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl, _⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, rfl⟩
    have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
      fun st hm => hmem st (List.mem_cons_of_mem _ hm)
    have hhead : s0 ∈ (fnAt u c).body := hmem s0 (List.mem_cons_self ..)
    cases s0
    case blkEnd | ifElse =>
      first
        | rw [lowSeq_blkEnd] at hlow
        | rw [lowSeq_ifElse] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl, _⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, rfl⟩
    case bind x d v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind hstepT
      obtain ⟨ls, q, hls, hq, rfl⟩ := lowSeq_bind_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x ls.range)
        (fT.mitBindung x (0, 0)) (ns.push x) q rest ys restZ used
        (hS.bind x (0, 0) ls.range) hmemss hq hys
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Block.ohneLocks] using IH.2.2⟩
    case bindW x d v =>
      obtain ⟨id, fields, eT, ys, htT, heT, hys, rfl⟩ := seqZ_bindRecord_some hbs
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindRecord_ok ((recordBinderType_sicht hS d v).symm.trans htT) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitWert x (.prod id fields))
        (fT.mitWert x (.prod id fields)) (ns.push x) q rest ys restZ used
        (hS.bindRecord x id fields) hmemss hq hys
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Block.ohneLocks] using IH.2.2⟩
    case bindMut x lo hi v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut hstepT
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindMut_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used (hS.bind x (lo, hi) (lo, hi))
        hmemss hq hys
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Block.ohneLocks] using IH.2.2⟩
    case bindB x v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB hstepT
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindB_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindungB x)
        (fT.mitBindungB x) (ns.push x) q rest ys restZ used (hS.bindB x) hmemss hq hys
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Block.ohneLocks] using IH.2.2⟩
    case bindOpt x num v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hn, eT, heT, rfl, rfl, rfl⟩ := schrittB_bindOpt hstepT
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindOpt_ok (hn := hn) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩))
        (fT.mitOpt x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) q rest ys restZ used
        (hS.bindOpt x num ((declOf u).count ⟨num, hn⟩)) hmemss hq hys
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Block.ohneLocks] using IH.2.2⟩
    case bindSum x sidx v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hs, hbare, eT, heT, rfl, rfl, rfl⟩ := schrittB_bindSum hstepT
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindSum_ok (hs := hs) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec)
        (fT.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) (ns.push x) q rest ys restZ used (hS.bindSum x sidx _) hmemss hq hys
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Block.ohneLocks] using IH.2.2⟩
    case matchWhyBeg x =>
      obtain ⟨count, e, arms, tailZ, allocated, ys, he, hAZ, hYZ, rfl⟩ := seqZ_reason_some hbs
      obtain ⟨id, ht, hid, rfl⟩ := reasonSubject_some he
      have ht' : valueParamTy fn x = some (.why count) := (hS.2.2.2.2 x).symm.trans ht
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowSeq_reason_ok hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨j, v, ga, hj, hv, hAG, hΛ, hst⟩ := lowStruct_reason_ok ht' hStruct
      subst Λ₁
      cases hst
      obtain ⟨hr, hsuf, hArms⟩ := arms_ohne_with m (by
          intro fuel hlt k ss _ fn ft ns _ p tail bs tailZ used hV hm hG hB
          exact ih fuel (by omega) k ss fn ft ns p tail bs tailZ used hV hm hG hB)
        m (Nat.le_refl m) count k 0 ss fn fT ns Λ ga
        (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hS hmemss hAG hAZ
      have ht : tailZ = tail := (List.cons.inj hr).2
      subst tailZ
      have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used
        hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm)) hQ hYZ
      refine ⟨IH.1, (IH.2.1.trans hsuf').trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨hArms, IH.2.2⟩
    case matchTagBeg sidx x binders =>
      obtain ⟨cs, e, arms, tailZ, allocated, ys, hn, he, hAZ, hYZ, rfl⟩ := seqZ_tag_some hbs
      obtain ⟨id, ht, hBare, hid, rfl⟩ := tagSubject_some he
      have ht' : valueParamTy fn x = some (.sum cs) := (hS.2.2.2.2 x).symm.trans ht
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowSeq_tag_ok hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨j, v, tagG, hj, hv, hTagG, hΛ, hst⟩ := lowStruct_tag_ok hn ht' hStruct
      subst Λ₁
      cases hst
      obtain ⟨ga, hAG, hBareRel⟩ := lowArms_bare m fn Λ cs binders ss tagG (.blkEnd :: tail) hBare hTagG
      obtain ⟨hr, hsuf, hArms⟩ := arms_ohne_with m (by
          intro fuel hlt k ss _ fn ft ns _ p tail bs tailZ used hV hm hG hB
          exact ih fuel (by omega) k ss fn ft ns p tail bs tailZ used hV hm hG hB)
        m (Nat.le_refl m) cs.length k 0 ss fn fT ns Λ ga
        (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hS hmemss hAG hAZ
      have ht : tailZ = tail := (List.cons.inj hr).2
      subst tailZ
      have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used
        hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm)) hQ hYZ
      refine ⟨IH.1, (IH.2.1.trans hsuf').trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨hBareRel.ohne hArms, IH.2.2⟩
    case matchBeg num v x =>
      obtain ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, he, hPZ, hAZ, hYZ, rfl⟩ := seqZ_option_some hbs
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowSeq_option_ok hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨ev, pG, aG, rest1, hv, hPG, hAG, rfl⟩ := lowStruct_option_ok hn hStruct
      obtain ⟨hr1, hsuf1, hP⟩ := ih m (by omega) k ss
        (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩))
        (fT.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x)
        ⟨Λ₁, pG⟩ (.ifElse :: rest1) pb (.ifElse :: r1) used1
        (hS.index x num ((declOf u).count ⟨num, hn⟩)) hmemss hPG hPZ
      have h1 : r1 = rest1 := (List.cons.inj hr1).2
      subst r1
      have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
      obtain ⟨hr2, hsuf2, hA⟩ := ih m (by omega) k rest1 fn fT
        (ns.resume used1) ⟨Λ₁, aG⟩ (.blkEnd :: tail) ab (.blkEnd :: r2) used2 hS
        (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) hAG hAZ
      have h2 : r2 = tail := (List.cons.inj hr2).2
      subst r2
      have hsuf2' : tail <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hRest⟩ := ih (m + 1) (by omega) k tail fn fT
        (ns.resume used2) q rest ys restZ used hS
        (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hQ hYZ
      refine ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨⟨hP, hA⟩, hRest⟩
    case loopBeg x tab inv =>
      obtain ⟨rfl, tZ, bodyB, tailZ, allocated, ys, htZ, hBodyZ, hTailZ, rfl⟩ := seqZ_loop_some hbs
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
      obtain ⟨hrBody, hsufBody, hBody⟩ := ih m (by omega) k ss
        (fn.mitIndex x t.val ((declOf u).count t)) (fT.mitIndex x t.val ((declOf u).count t))
        (ns.push x) ⟨Λ, bodyG⟩ (.blkEnd :: tail) bodyB (.blkEnd :: tailZ) allocated
        (hS.index x t.val ((declOf u).count t)) hmemss hBodyG hBodyZ
      have htail : tailZ = tail := (List.cons.inj hrBody).2
      subst tailZ
      have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans hsufBody
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used hS
        (fun st hm => hmemss st (mem_of_suffix hsuf hm)) hQ hTailZ
      refine ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨hBody, IH.2.2⟩
    case narrowBeg x lo hi =>
      obtain ⟨e, errorBody, tailZ, ys, hname, hEZ, hYZ, rfl⟩ := seqZ_narrow_some hbs
      obtain ⟨hn, id, hid, rfl⟩ := narrowName_some hname
      have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
      obtain ⟨j, a, b, v, err, tail, q, hj, hv, hEG, hQG, rfl⟩ := lowSeq_narrow_ok hn' hlow
      have heq : tail = tailZ := (List.cons.inj (endBodyZ_rest n k ss fn fT ns err
        (.blkEnd :: tail) (.blkEnd :: tailZ) errorBody hEG hEZ)).2
      subst tailZ
      have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans (endBodyZ_suffix k fT ns ss errorBody _ hEZ)
      have hErr := endBodyZ_ohne S.tab c n k ss fn fT ns err (.blkEnd :: tail) errorBody hS hEG hEZ
      have IH := ih n (Nat.lt_succ_self n) k tail (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used
        (hS.bind x (lo, hi) (lo, hi)) (fun st hm => hmemss st (mem_of_suffix hsuf hm)) hQG hYZ
      refine ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Bool.and_eq_true]
      exact ⟨hErr, IH.2.2⟩
    case bindCall x g args =>
      obtain ⟨bB, fT', ns', ys, hstep, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨bt, hbT, rfl, rfl⟩ := schrittB_bindCall hstep
      obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowSeq_bindCall_ok hlow
      obtain ⟨ht, sh, hsh⟩ := resultCall_type hk he hbT
      subst bt
      obtain ⟨hidx, _, _⟩ := lowRufKopf_ok hk
      have hcallee : fnSuch u g = some (fnAt u head.callee) := fnIdx_find _ _ _ hidx
      have hd := callee_getragen_calls S hc (CallsIn.bind hhead) hcallee
      have hType := (S.boolErg head.callee hd).1
      have IH := ih n (Nat.lt_succ_self n) k ss (mitRuf u fn x head.callee ty)
        (fT.mitTy x ty) (ns.push x) q rest ys restZ used (hS.bindRuf x head.callee hsh hType he) hmemss hq hys
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), by simpa only [Block.ohneLocks] using IH.2.2⟩
    case setVar | setVarB | setVarOpt | assign | assignTab | assignOpt | assignTabOpt | assignGlob | assignGlobB | call =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hstepN, rfl, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hS hmemss hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Bool.and_eq_true]
      exact ⟨lowStmtL_einzeln_ohne S.tab (by exact True.intro) hst, IH.2.2⟩
    case leave x | next x =>
      obtain ⟨ys, hys, rfl⟩ := (by first
        | exact seqZ_control_some (leave := true) hbs
        | exact seqZ_control_some (leave := false) hbs)
      obtain ⟨hl, q, hq, rfl⟩ := (by first
        | exact lowSeq_control_ok (leave := true) hlow
        | exact lowSeq_control_ok (leave := false) hlow)
      have IH := ih n (Nat.lt_succ_self n) k ss fn fT ns q rest ys restZ used hS hmemss hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Bool.and_eq_true]
      exact ⟨controlStmt_ohne _ hl, IH.2.2⟩
    case ret r0 =>
      obtain ⟨bst, ys, hbT, hys, rfl⟩ := seqZ_ret_some hbs
      obtain ⟨st, q, hst, hq, rfl⟩ := lowSeq_ret_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hS hmemss hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Bool.and_eq_true]
      exact ⟨lowRetStmt_ohne hst, IH.2.2⟩
    case ifBeg cnd | ifEnde cnd =>
      obtain ⟨Λ₁, st, rest', q, hst, hq, rfl⟩ :=
        lowSeq_wenn_ok (cnd := cnd) hlow (by first | exact .inl rfl | exact .inr rfl)
      obtain ⟨ce, tt, te, r1, r2, ys, used1, used2, hce, hTZ, hEZ, hYZ, rfl⟩ :=
        seqZ_wenn_some (cnd := cnd) hbs (by first | exact .inl rfl | exact .inr rfl)
      obtain _ | m := n
      · rw [lowStructL_zero] at hst; cases hst
      obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
      obtain ⟨hr1, hsuf1, hBt⟩ := ih m (by omega) k ss fn fT ns ⟨Λ₁, tb⟩ (.ifElse :: rest1) tt
        (.ifElse :: r1) used1 hS hmemss hT hTZ
      have h1 : r1 = rest1 := (List.cons.inj hr1).2
      rw [h1] at hEZ
      have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
      obtain ⟨hr2, hsuf2, hBe⟩ := ih m (by omega) k rest1 fn fT (ns.resume used1) ⟨Λ₁, eb⟩ (.blkEnd :: rest') te
        (.blkEnd :: r2) used2 hS (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) hE hEZ
      have h2 : r2 = rest' := (List.cons.inj hr2).2
      rw [h2] at hYZ
      have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hBc⟩ := ih (m + 1) (by omega) k rest' fn fT (ns.resume used2) q rest ys restZ used hS
        (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hq hYZ
      refine ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), ?_⟩
      simp only [Block.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
      exact ⟨⟨hBt, hBe⟩, hBc⟩
    all_goals exact absurd hbs (by simp only [seqZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

end Gabbro.Bruecke
