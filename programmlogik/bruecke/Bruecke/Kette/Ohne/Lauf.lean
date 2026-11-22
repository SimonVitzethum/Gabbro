module
public import Bruecke.Kette.Ohne.Ende
@[expose] public section

/-!
# A carried function body lowers without `locks`

The mirror of `lauf_G`: along the reader `stmtsBodyZ`, the lowered body (`lowBodyF`) of a
carried function contains no `locks` block and no scoped return.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem lauf_ohne (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (r : URet) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt),
      Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowBodyF u c Γ fn n Λ ss r = .ok b0 → stmtsBodyZ u k fT ns ss r = some bs →
      b0.ohneLocks = true
  | 0, k, ss, Γ, fn, fT, ns, Λ, b0, bs, hS, hmem, hlow, hbs => by
      simp only [lowBodyF] at hlow <;> cases hlow
  | n + 1, 0, ss, Γ, fn, fT, ns, Λ, b0, bs, hS, hmem, hlow, hbs => by
      exact absurd hbs (by simp only [stmtsBodyZ, reduceCtorEq, not_false_eq_true])
  | n + 1, k + 1, [], Γ, fn, fT, ns, Λ, b0, bs, hS, hmem, hlow, hbs => by
      simp only [lowBodyF] at hlow
      exact lowEnd_ohne hlow
  | n + 1, k + 1, s0 :: ss, Γ, fn, fT, ns, Λ, b0, bs, hS, hmem, hlow, hbs => by
      have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
        fun st hm => hmem st (List.mem_cons_of_mem _ hm)
      have hhead : s0 ∈ (fnAt u c).body := hmem s0 (List.mem_cons_self ..)
      cases s0
      case bind x d v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind hstep0
        obtain ⟨ls, rest, hls, hrest, rfl⟩ := lowBodyF_bind_ok c hlow
        simp only [Endblock.ohneLocks]
        exact lauf_ohne S c hc r n k ss (fn.mitBindung x ls.range)
          (fT.mitBindung x (0, 0)) (ns.push x) rest bs' (hS.bind x (0, 0) ls.range) hmemss hrest hbs'
      case bindW x d v =>
        obtain ⟨id, fields, eT, bs', htT, heT, hbs', rfl⟩ := stmtsBodyZ_bindRecord_some hbs
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindRecord_ok c ((recordBinderType_sicht hS d v).symm.trans htT) hlow
        simp only [Endblock.ohneLocks]
        exact lauf_ohne S c hc r n k ss (fn.mitWert x (.prod id fields))
          (fT.mitWert x (.prod id fields)) (ns.push x) rest bs' (hS.bindRecord x id fields) hmemss hrest hbs'
      case bindMut x lo hi v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut hstep0
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindMut_ok c hlow
        simp only [Endblock.ohneLocks]
        exact lauf_ohne S c hc r n k ss (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) (ns.push x) rest bs' (hS.bind x (lo, hi) (lo, hi)) hmemss hrest hbs'
      case bindB x v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB hstep0
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindB_ok c hlow
        simp only [Endblock.ohneLocks]
        exact lauf_ohne S c hc r n k ss (fn.mitBindungB x)
          (fT.mitBindungB x) (ns.push x) rest bs' (hS.bindB x) hmemss hrest hbs'
      case bindOpt x num v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨hn, eT, heT, rfl, rfl, rfl⟩ := schrittB_bindOpt hstep0
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindOpt_ok c (hn := hn) hlow
        simp only [Endblock.ohneLocks]
        exact lauf_ohne S c hc r n k ss (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩))
          (fT.mitOpt x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) rest bs'
          (hS.bindOpt x num ((declOf u).count ⟨num, hn⟩)) hmemss hrest hbs'
      case loopBeg x tab inv =>
        obtain ⟨rfl, tZ, bodyB, tailZ, allocated, ys, htZ, hBodyZ, hTailZ, rfl⟩ := stmtsBodyZ_loop_some hbs
        obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowBodyF_loop_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hStruct
        obtain ⟨t, bodyG, ht, hBodyG, hΛ, hst⟩ := lowStruct_loop_ok hStruct
        subst Λ₁
        cases hst
        have htEq : tZ = t := by
          rw [ht] at htZ
          exact (Except.ok.inj htZ).symm
        subst tZ
        obtain ⟨hrBody, hsufBody, hBody⟩ := seq_ohne S c hc m k ss
          (fn.mitIndex x t.val ((declOf u).count t)) (fT.mitIndex x t.val ((declOf u).count t))
          (ns.push x) ⟨Λ, bodyG⟩ (.blkEnd :: tail) bodyB (.blkEnd :: tailZ) allocated
          (hS.index x t.val ((declOf u).count t)) hmemss hBodyG hBodyZ
        have htail : tailZ = tail := (List.cons.inj hrBody).2
        subst tailZ
        have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans hsufBody
        simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
        exact ⟨hBody, lauf_ohne S c hc r n k tail fn fT (ns.resume allocated) q ys hS
          (fun st hm => hmemss st (mem_of_suffix hsuf hm)) hQ hTailZ⟩
      case matchTagBeg sidx x binders =>
        obtain ⟨cs, e, arms, tailZ, allocated, ys, hn, he, hAZ, hYZ, rfl⟩ := stmtsBodyZ_tag_some hbs
        obtain ⟨id, ht, hBare, hid, rfl⟩ := tagSubject_some he
        have ht' : valueParamTy fn x = some (.sum cs) := (hS.2.2.2.2 x).symm.trans ht
        obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowBodyF_tag_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hStruct
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
        simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
        exact ⟨hBareRel.ohne hArms, lauf_ohne S c hc r n k tail fn fT (ns.resume allocated) q ys hS
          (fun st hm => hmemss st (mem_of_suffix hsuf' hm)) hQ hYZ⟩
      case matchWhyBeg x =>
        obtain ⟨count, e, arms, tailZ, allocated, ys, he, hAZ, hYZ, rfl⟩ := stmtsBodyZ_reason_some hbs
        obtain ⟨id, ht, hid, rfl⟩ := reasonSubject_some he
        have ht' : valueParamTy fn x = some (.why count) := (hS.2.2.2.2 x).symm.trans ht
        obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowBodyF_reason_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hStruct
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
        simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
        exact ⟨hArms, lauf_ohne S c hc r n k tail fn fT (ns.resume allocated) q ys hS
          (fun st hm => hmemss st (mem_of_suffix hsuf' hm)) hQ hYZ⟩
      case matchBeg num v x =>
        obtain ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, he, hPZ, hAZ, hYZ, rfl⟩ := stmtsBodyZ_option_some hbs
        obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowBodyF_option_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hStruct
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
        simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
        exact ⟨⟨hP, hA⟩, lauf_ohne S c hc r n k tail fn fT (ns.resume used2) q ys hS
          (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hQ hYZ⟩
      case narrowBeg x lo hi =>
        obtain ⟨e, errorBody, tailZ, ys, hname, hEZ, hYZ, rfl⟩ := stmtsBodyZ_narrow_some hbs
        obtain ⟨hn, id, hid, rfl⟩ := narrowName_some hname
        have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
        obtain ⟨j, a, b, v, err, tail, q, hj, hv, hEG, hQG, rfl⟩ := lowBodyF_narrow_ok hn' hlow
        have heq : tail = tailZ := (List.cons.inj (endBodyZ_rest blockFuel k ss fn fT ns err
          (.blkEnd :: tail) (.blkEnd :: tailZ) errorBody hEG hEZ)).2
        subst tailZ
        have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans (endBodyZ_suffix k fT ns ss errorBody _ hEZ)
        have hErr := endBodyZ_ohne S.tab c blockFuel k ss fn fT ns err (.blkEnd :: tail) errorBody hS hEG hEZ
        simp only [Endblock.ohneLocks, Bool.and_eq_true]
        exact ⟨hErr, lauf_ohne S c hc r n k tail (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) (ns.push x) q ys (hS.bind x (lo, hi) (lo, hi))
          (fun st hm => hmemss st (mem_of_suffix hsuf hm)) hQG hYZ⟩
      case bindCall x g args =>
        obtain ⟨bB, fT', ns', ys, hstep, hys, rfl⟩ := stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨bt, hbT, rfl, rfl⟩ := schrittB_bindCall hstep
        obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowBodyF_bindCall_ok hlow
        obtain ⟨ht, sh, hsh⟩ := resultCall_type hk he hbT
        subst bt
        obtain ⟨hidx, _, _⟩ := lowRufKopf_ok hk
        have hcallee : fnSuch u g = some (fnAt u head.callee) := fnIdx_find _ _ _ hidx
        have hd := callee_getragen_calls S hc (CallsIn.bind hhead) hcallee
        have hType := (S.boolErg head.callee hd).1
        simp only [Endblock.ohneLocks]
        exact lauf_ohne S c hc r n k ss (mitRuf u fn x head.callee ty)
          (fT.mitTy x ty) (ns.push x) q ys (hS.bindRuf x head.callee hsh hType he) hmemss hq hys
      case setVar | setVarB | setVarOpt | assign | assignTab | assignOpt | assignTabOpt | assignGlob | assignGlobB | call =>
        obtain ⟨bT, fT', ns', bs', hstepT, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨hstepN, rfl, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r _ ss (by exact True.intro) hlow
        simp only [Endblock.ohneLocks, Bool.and_eq_true]
        exact ⟨lowStmtL_einzeln_ohne S.tab (by exact True.intro) hgst,
          lauf_ohne S c hc r n k ss fn _ _ rest bs' hS hmemss hrest hbs'⟩
      case ifEnde cnd =>
        obtain ⟨ce, tt, te, r1, used1, used2, rfl, hce, hTZ, hEZ, rfl⟩ := stmtsBodyZ_ifEnde_some hbs
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowBodyF_ifEnde_ok hlow
        obtain ⟨hr1, hsuf1, hBt⟩ := ende_ohne S c hc blockFuel k ss fn fT ns tb
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hS hmemss True.intro hT hTZ
        have h1 := (List.cons.inj hr1).2
        subst r1
        have hsuf1' := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨_, _, hBe⟩ := ende_ohne S c hc blockFuel k rest1 fn fT
          (ns.resume used1) eb [.blkEnd] te [.blkEnd] used2 hS
          (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) True.intro hE hEZ
        simp only [Endblock.ohneLocks, Bool.and_eq_true]
        exact ⟨hBt, hBe⟩
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', used1, used2, hce, hTZ, hEZ, hbs', rfl⟩ := stmtsBodyZ_ifBeg_some hbs
        obtain ⟨Λ₁, st, rest', e, hst, hrest, rfl⟩ := lowBodyF_ifBeg_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hBt⟩ := seq_ohne S c hc m k ss fn fT ns ⟨Λ₁, tb⟩
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hS hmemss hT hTZ
        have h1 : r1 = rest1 := (List.cons.inj hr1).2
        rw [h1] at hEZ
        have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hBe⟩ := seq_ohne S c hc m k rest1 fn fT (ns.resume used1) ⟨Λ₁, eb⟩
          (.blkEnd :: rest') te (.blkEnd :: r2) used2 hS
          (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) hE hEZ
        have h2 : r2 = rest' := (List.cons.inj hr2).2
        rw [h2] at hbs'
        have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        simp only [Endblock.ohneLocks, Stmt.ohneLocks, Bool.and_eq_true]
        exact ⟨⟨hBt, hBe⟩, lauf_ohne S c hc r n k rest' fn fT (ns.resume used2) e bs' hS
          (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hrest hbs'⟩
      all_goals exact absurd hbs (by simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

/-- An ending block keeps `ohneLocks` across a transport of its context and resources. -/
theorem Endblock.ohneLocks_heq {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx}
    {Λ Λ' : List (Res D)} (hΓ : Γ = Γ') (hΛ : Λ = Λ') (b : Endblock D V l Γ Λ)
    (b' : Endblock D V l Γ' Λ') (h : HEq b b') : b.ohneLocks = b'.ohneLocks := by
  subst hΓ hΛ
  cases h
  rfl

/-- **The lowered body of a carried function contains no `locks` block** (and no scoped return):
    the premise of `koerperGutS_ohne`, so its lock-invariant duty is its plain duty. -/
theorem rumpf_ohne {P : Programm (declOf u)} {fs : List (declOf u).Fn} (S : Getragen u C)
    (hlow : lowerAllg u = .ok (P, fs)) (c : Fin u.fns.length) (hc : C c) {body : List Gabbro.Body.Stmt}
    (hbody : zuBodyZ u (fnAt u c) = some body) : (P.rumpf c).ohneLocks = true := by
  have G := gesenkt_of_teil S hlow
  obtain ⟨b0, hb0, hPb⟩ := G.rumpf c hc
  have h := lauf_ohne S c hc (fnAt u c).ret ((fnAt u c).body.length + 1)
    ((fnAt u c).body.length + 1) (fnAt u c).body (fnAt u c) (fnAt u c) (BodyNames.start (fnAt u c)) b0 body
    (Sicht.refl _) (fun _ hm => hm) hb0 hbody
  rw [Endblock.ohneLocks_heq (ctxParams_eq u c).symm (anfangRes_eq u c).symm (P.rumpf c) b0 hPb]
  exact h

end Gabbro.Bruecke
