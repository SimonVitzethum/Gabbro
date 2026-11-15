module
public import Bruecke.Kette.Block
public import Bruecke.Anweisung.Zweig.EndForm
public import Bruecke.Anweisung.Zweig.EndBereich
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Explicit ending arms reuse the nested reader and its generic block simulations.
    A closing marker is required: statements after the ending are never silently consumed. -/
theorem laufEndSeq_G {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C)
    (c : Fin u.fns.length) (hc : C c) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) :
    ∀ n k ss {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (b : Endblock (declOf u) (verOf u c) false Γ Λ) rest bs restZ used,
      UmfangB Γ fn ns → Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      BindFrischL (protectedNames fn.params fn.kinds) ss → EndMarker rest →
      lowEndL (l := false) u c Γ fn n Λ [] ss = .ok (b, rest) →
      seqZ u k fT ns ss = some (bs, restZ, used) →
      restZ = rest ∧ rest <:+ ss ∧
      ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
        EndZiel_G u C c O passes R fn ns.active b σ ρ s bs := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k ss Γ fn fT ns Λ b rest bs restZ used hU hS hmem hF hm hlow hbs
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
        refine ⟨rfl, List.suffix_cons _ _, fun σ ρ s hW hL => ?_⟩
        have hr' := (retZ_sicht hS ns r).symm.trans hr
        by_cases hn : ∃ i, r = .why i
        · obtain ⟨i, rfl⟩ := hn
          obtain ⟨hlt, hp, rfl⟩ := lowRetWhyEnd_ok hg
          simp only [retZ, Option.some.injEq] at hr'
          subst bst
          exact ausgangZiel_why ⟨i, hlt⟩ hW
        have hn' : ∀ i, r ≠ .why i := fun i he => hn ⟨i, he⟩
        obtain ⟨σ', v, he, hw, hs⟩ := lowRetEnd_sim c hg hr' hn' hU S.tab O passes R σ ρ s hW hL

        rw [endZiel_false_iff]
        refine ⟨fun err hh => (by rw [he] at hh; cases hh), fun σ'' v' hh => ?_,
          fun σ' r' hh => (by rw [he] at hh; cases hh)⟩
        rw [he] at hh
        cases hh
        exact ⟨[], (by simp), (by simp [Oben]), List.Pairwise.nil,
          fun ρB _ _ => ⟨s, by simp only [Gabbro.Body.exec, hs ρB], hw⟩⟩
    case bind x d v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind ht
      obtain ⟨hx, hF'⟩ := bindFrischL_bind hF
      obtain ⟨ls, q, hls, hq, rfl⟩ := lowEndL_bind_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x ls.range)
        (fT.mitBindung x (0, 0)) (ns.push x) q rest ys restZ used (hU.bind hx ls.range)
        (hS.bind x (0, 0) ls.range) hmemss hF' hm hq hy
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hs, hw, hl⟩ := lowBind_named_sim (x := x) hls
        ((namedSide_sicht hS ns v).symm.trans heT) hU S.tab hU.valid σ ρ s hW hL
      exact endZiel_bind_G hs (fun w => Int.le_refl _) (IH.2.2 _ _ _ hw hl)
    case bindW x d v =>
      obtain ⟨id, fields, eT, ys, htT, heT, hy, rfl⟩ := seqZ_bindRecord_some hbs
      have hx : NameFrisch (protectedNames fn.params fn.kinds) x := hF.1
      have hF' : BindFrischL (protectedNames fn.params fn.kinds) ss := hF.2
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEnd_bindRecord_ok ((recordBinderType_sicht hS d v).symm.trans htT) hlow
      have heB : namedSide u fn ns v = some eT := (namedSide_sicht hS ns v).symm.trans heT
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitWert x (.prod id fields))
        (fT.mitWert x (.prod id fields)) (ns.push x) q rest ys restZ used
        (hU.bindRecord hx id fields) (hS.bindRecord x id fields) hmemss
        (by simpa only [UFn.mitWert, uArtVon, protectedNames] using hF') hm hq hy
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindRecord_named_sim (x := x) hev heB hU S.tab σ ρ s hW hL
      exact endZiel_bind_G hstep (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL')
    case bindMut x lo hi v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut ht
      obtain ⟨hx, hF'⟩ := bindFrischL_bindMut hF
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEndL_bindMut_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used (hU.bind hx (lo, hi))
        (hS.bind x (lo, hi) (lo, hi)) hmemss hF' hm hq hy
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hs, hw, hl⟩ := lowBindMut_named_sim (x := x) hev
        ((namedSide_sicht hS ns v).symm.trans heT) hU S.tab hU.valid σ ρ s hW hL
      exact endZiel_bind_G hs (fun w => Int.le_refl _) (IH.2.2 _ _ _ hw hl)
    case bindB x v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB ht
      obtain ⟨hx, hF'⟩ := bindFrischL_bindB hF
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEndL_bindB_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindungB x)
        (fT.mitBindungB x) (ns.push x) q rest ys restZ used (hU.bindB hx)
        (hS.bindB x) hmemss hF' hm hq hy
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hs, hw, hl⟩ := lowBindB_named_sim (x := x) hev
        ((condZ_sicht hS ns v).symm.trans heT) hU S.tab σ ρ s hW hL
      exact endZiel_bind_G hs (fun w => Int.le_refl _) (IH.2.2 _ _ _ hw hl)
    case setVar | setVarB | setVarOpt | assign | assignTab | assignOpt | assignTabOpt | assignGlob | assignGlobB | call =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨htN, rfl, rfl⟩ := schrittB_einzeln_sicht hS ht (by trivial)
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowEndL_leaf_ok (by trivial) hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hU hS hmemss
        (bindFrischL_sonst (by rfl) hF) hm hq hy
      exact ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        endZiel_cons_G (stmtZiel_einzeln_G G S c hc O passes R hRR hhead (by trivial)
          hst htN hU σ ρ s hW hL) IH.2.2⟩
    case bindOpt x num v =>
      obtain ⟨bT, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hn, eT, heT, rfl, rfl, rfl⟩ := schrittB_bindOpt ht
      obtain ⟨hx, hF'⟩ := bindFrischL_bindOpt hF
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowEndL_bindOpt_ok (hn := hn) hlow
      have heB : namedOption u fn ns v = some eT := (namedOption_sicht hS ns v).symm.trans heT
      have hU' : UmfangB (.opt ((declOf u).count ⟨num, hn⟩) :: Γ) (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) := hU.bindOpt num ((declOf u).count ⟨num, hn⟩) hx
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩))
        (fT.mitOpt x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) q rest ys restZ used hU' (hS.bindOpt x num ((declOf u).count ⟨num, hn⟩))
        hmemss hF' hm hq hy
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindOpt_named_sim (x := x) hev heB hU S.tab σ ρ s hW hL
      exact endZiel_bind_G hstep (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL')
    case matchWhyBeg x =>
      obtain ⟨count, e, arms, tailZ, allocated, ys, he, hAZ, hYZ, rfl⟩ := seqZ_reason_some hbs
      obtain ⟨id, ht, hid, rfl⟩ := reasonSubject_some he
      have ht' : valueParamTy fn x = some (.why count) := (hS.2.2.2.2 x).symm.trans ht
      have hid' := (BodyNames.lookup_sicht hS ns x).symm.trans hid
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowEndL_struct_ok (.inr (.inr (.inr (.inr ⟨x, rfl⟩)))) hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨j, v, ga, hj, hv, hAG, hΛ, hst⟩ := lowStruct_reason_ok ht' hStruct
      subst Λ₁
      cases hst
      have hF0 := bindFrischL_sonst (by rfl) hF
      obtain ⟨hr, hsuf, hArms⟩ := reasonArms_G_with m (by
          intro fuel hlt k ss _ fn ft ns _ p tail bs tailZ used hU hV hm hF hG hB
          exact laufSeq_G G S c hc O passes R hRR fuel k ss fn ft ns p tail bs tailZ used hU hV hm hF hG hB)
        m (Nat.le_refl m) count k 0 ss fn fT ns Λ ga
        (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hU hS hmemss hF0 hAG hAZ
      have ht : tailZ = tail := (List.cons.inj hr).2
      subst tailZ
      have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
      have hU' := hU.resume (reasonArmsZ_used k fT count 0 ns ss arms (.blkEnd :: tail) allocated hAZ)
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used
        hU' hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm))
        (bindFrischL_suffix hF0 hsuf') hm hQ hYZ
      exact ⟨IH.1, (IH.2.1.trans hsuf').trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        endZiel_cons_G (stmtZiel_reason_G hj hv hid' hArms σ ρ s hW hL) IH.2.2⟩
    case matchTagBeg sidx x binders =>
      obtain ⟨cs, e, arms, tailZ, allocated, ys, hn, he, hAZ, hYZ, rfl⟩ := seqZ_tag_some hbs
      obtain ⟨id, ht, hBare, hid, rfl⟩ := tagSubject_some he
      have ht' : valueParamTy fn x = some (.sum cs) := (hS.2.2.2.2 x).symm.trans ht
      have hid' := (BodyNames.lookup_sicht hS ns x).symm.trans hid
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowEndL_struct_ok (.inr (.inr (.inr (.inl ⟨sidx, x, binders, rfl⟩)))) hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨j, v, tagG, hj, hv, hTagG, hΛ, hst⟩ := lowStruct_tag_ok hn ht' hStruct
      subst Λ₁
      cases hst
      obtain ⟨ga, hAG, hBareRel⟩ := lowArms_bare m fn Λ cs binders ss tagG (.blkEnd :: tail) hBare hTagG
      have hF0 := bindFrischL_sonst (by rfl) hF
      obtain ⟨hr, hsuf, hArms⟩ := reasonArms_G_with m (by
          intro fuel hlt k ss _ fn ft ns _ p tail bs tailZ used hU hV hm hF hG hB
          exact laufSeq_G G S c hc O passes R hRR fuel k ss fn ft ns p tail bs tailZ used hU hV hm hF hG hB)
        m (Nat.le_refl m) cs.length k 0 ss fn fT ns Λ ga
        (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hU hS hmemss hF0 hAG hAZ
      have ht : tailZ = tail := (List.cons.inj hr).2
      subst tailZ
      have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
      have hU' := hU.resume (reasonArmsZ_used k fT cs.length 0 ns ss arms (.blkEnd :: tail) allocated hAZ)
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used
        hU' hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm))
        (bindFrischL_suffix hF0 hsuf') hm hQ hYZ
      exact ⟨IH.1, (IH.2.1.trans hsuf').trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        endZiel_cons_G (stmtZiel_tag_G hj hv hid' hBareRel hArms σ ρ s hW hL) IH.2.2⟩
    case matchBeg num v x =>
      obtain ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, he, hPZ, hAZ, hYZ, rfl⟩ := seqZ_option_some hbs
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowEndL_struct_ok (.inr (.inr (.inl ⟨num, v, x, rfl⟩))) hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨ev, pG, aG, rest1, hv, hPG, hAG, rfl⟩ := lowStruct_option_ok hn hStruct
      have hF0 : BindFrischL (protectedNames fn.params fn.kinds) ss := hF.2
      obtain ⟨hr1, hsuf1, hP⟩ := laufSeq_G G S c hc O passes R hRR m k ss
        (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩))
        (fT.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x)
        ⟨Λ₁, pG⟩ (.ifElse :: rest1) pb (.ifElse :: r1) used1
        (hU.index hF.1 num ((declOf u).count ⟨num, hn⟩))
        (hS.index x num ((declOf u).count ⟨num, hn⟩)) hmemss
        (by simpa only [UFn.mitIndex, protectedNames] using hF0) hPG hPZ
      have h1 : r1 = rest1 := (List.cons.inj hr1).2
      subst r1
      have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
      have hUsed := seqZ_used k _ (ns.push x) ss pb (.ifElse :: rest1) used1 hPZ
      have hU1 := hU.resume (fun z hz => hUsed z (BodyNames.used_push ns x z hz))
      obtain ⟨hr2, hsuf2, hA⟩ := laufSeq_G G S c hc O passes R hRR m k rest1 fn fT
        (ns.resume used1) ⟨Λ₁, aG⟩ (.blkEnd :: tail) ab (.blkEnd :: r2) used2 hU1 hS
        (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) (bindFrischL_suffix hF0 hsuf1') hAG hAZ
      have h2 : r2 = tail := (List.cons.inj hr2).2
      subst r2
      have hsuf2' : tail <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hRest⟩ := ih (m + 1) (by omega) k tail fn fT
        (ns.resume used2) q rest ys restZ used (hU1.afterSeq hAZ) hS
        (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) (bindFrischL_suffix hF0 hsuf2') hm hQ hYZ
      exact ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        endZiel_cons_G (stmtZiel_option_G hU hS hv he hP hA σ ρ s hW hL) hRest⟩
    case bindCall x g args =>
      obtain ⟨bB, fT', ns', ys, ht, hy, rfl⟩ := seqZ_schritt_some hbs (by trivial)
      obtain ⟨bt, hbT, rfl, rfl⟩ := schrittB_bindCall ht
      obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowEndL_bindCall_ok hlow
      obtain ⟨hty, sh, hsh⟩ := resultCall_type hk he hbT
      subst bt
      have hb := (namedResult_sicht hS ns x g args).symm.trans hbT
      obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
      have hf := fnIdx_find _ _ _ hi
      have hd := callee_getragen_calls S hc (CallsIn.bind hhead) hf
      have hType := (S.boolErg head.callee hd).1
      have hF' : BindFrischL (protectedNames (mitRuf u fn x head.callee ty).params
          (mitRuf u fn x head.callee ty).kinds) ss := by
        rw [protectedNames_mitRuf fn x head.callee hsh]; exact hF.2
      have IH := ih n (Nat.lt_succ_self n) k ss (mitRuf u fn x head.callee ty) (fT.mitTy x ty)
        (ns.push x) q rest ys restZ used (hU.bindRuf hF.1 head.callee hsh hType he)
        (hS.bindRuf x head.callee hsh hType he) hmemss hF' hm hq hy
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      cases hR : R head.callee (σ.lese Λ head.args.orte)
          (evalArgs (σ.lese Λ head.args.orte) head.args (σ.lese Λ head.args.orte) ρ) with
      | ok σ₁ v =>
        obtain ⟨A, s₁, hs, hw, hl⟩ := resultCall_strecke G S hc R hRR hk he hb hhead hU σ σ₁ ρ s hW hL v hR
        have hrun : (∀ err, execEnd O passes R (.bindCall head.callee head.args he head.hp hr q) σ ρ = .logik err →
            execEnd O passes R q σ₁ (Env.cons (ergWert he v) ρ) = .logik err) ∧
            (∀ σ' v', execEnd O passes R (.bindCall head.callee head.args he head.hp hr q) σ ρ = .zurueck σ' v' →
              execEnd O passes R q σ₁ (Env.cons (ergWert he v) ρ) = .zurueck σ' v') ∧
            (∀ σ' r', execEnd O passes R (.bindCall head.callee head.args he head.hp hr q) σ ρ = .why σ' r' →
              execEnd O passes R q σ₁ (Env.cons (ergWert he v) ρ) = .why σ' r') := by
          refine ⟨?_, ?_, ?_⟩
          · intro err hh; simp only [execEnd, hR] at hh; exact EndAusgang.schrumpf_logik hh
          · intro σ' v' hh; simp only [execEnd, hR] at hh; exact endSchrumpf_zurueck hh
          · intro σ' r' hh; simp only [execEnd, hR] at hh; exact endSchrumpf_why hh
        simpa only [List.singleton_append] using endZiel_strecke_G hrun hs (IH.2.2 _ _ _ hw hl)
      | why σ₁ why => exact (Nat.not_lt_zero why.val (Nat.lt_of_lt_of_eq why.isLt hr)).elim
      | logik err =>
        obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
        have hf := fnIdx_find _ _ _ hi
        have hd := callee_getragen_calls S hc (CallsIn.bind hhead) hf
        rw [endZiel_false_iff]
        refine ⟨fun err' hh => ?_, fun σ' v' hh => ?_,
          fun σ' r' hh => (by simp only [execEnd, hR] at hh; cases hh)⟩
        · simp only [execEnd, hR] at hh; cases hh
          exact ⟨head.callee, _, _, hd, hR⟩
        · simp only [execEnd, hR] at hh; cases hh
      | hardware err =>
        rw [endZiel_false_iff]
        exact ⟨fun _ hh => (by simp only [execEnd, hR] at hh; cases hh),
          fun _ _ hh => (by simp only [execEnd, hR] at hh; cases hh),
          fun _ _ hh => (by simp only [execEnd, hR] at hh; cases hh)⟩
    case narrowBeg x lo hi =>
      obtain ⟨e, errorBody, tailZ, ys, hname, hEZ, hYZ, rfl⟩ := seqZ_narrow_some hbs
      obtain ⟨hn, id, hid, rfl⟩ := narrowName_some hname
      have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
      have hid' := (BodyNames.lookup_sicht hS ns x).symm.trans hid
      obtain ⟨j, a, b, v, err, tail, q, hj, hv, hEG, hQG, rfl⟩ := lowEndL_narrow_ok hn' hlow
      have heq : tail = tailZ := (List.cons.inj (endBodyZ_rest n k ss fn fT ns err
        (.blkEnd :: tail) (.blkEnd :: tailZ) errorBody hEG hEZ)).2
      subst tailZ
      have hsuf := (List.suffix_cons _ _).trans (endBodyZ_suffix k fT ns ss errorBody _ hEZ)
      have hmemTail : ∀ st ∈ tail, st ∈ (fnAt u c).body := fun st h => hmemss st (mem_of_suffix hsuf h)
      have hErr := endBodyZ_sim G S c hc O passes R hRR n k ss fn fT ns err
        (.blkEnd :: tail) errorBody hU hS hmemss (bindFrischL_suffix hF (List.suffix_cons _ _)) hEG hEZ
      have IH := ih n (Nat.lt_succ_self n) k tail (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used (hU.bind hF.1 (lo, hi))
        (hS.bind x (lo, hi) (lo, hi)) hmemTail (bindFrischL_suffix hF.2 hsuf) hm hQG hYZ
      exact ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        endZiel_narrow_G hj hv hid' hU hErr IH.2.2 σ ρ s hW hL⟩
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
      obtain ⟨hrBody, hsufBody, hBody⟩ := laufSeq_G G S c hc O passes R hRR m k ss
        (fn.mitIndex x tZ.val ((declOf u).count tZ)) (fT.mitIndex x tZ.val ((declOf u).count tZ))
        (ns.push x) ⟨Λ, bodyG⟩ (.blkEnd :: tail) bodyB (.blkEnd :: tailZ) allocated
        (hU.index hF.1 tZ.val ((declOf u).count tZ)) (hS.index x tZ.val ((declOf u).count tZ))
        hmemss hF.2 hBodyG hBodyZ
      have htail : tailZ = tail := (List.cons.inj hrBody).2
      subst tailZ
      have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans hsufBody
      have hUsed := seqZ_used k (fT.mitIndex x tZ.val ((declOf u).count tZ))
        (ns.push x) ss bodyB (.blkEnd :: tail) allocated hBodyZ
      have hUrest := hU.resume (fun z hz => hUsed z (BodyNames.used_push ns x z hz))
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used hUrest hS
        (fun st h => hmemss st (mem_of_suffix hsuf h)) (bindFrischL_suffix hF.2 hsuf) hm hQ hTailZ
      exact ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        endZiel_cons_G (stmtZiel_loop_G hU hBody σ ρ s hW hL) IH.2.2⟩
    case ifBeg cnd | ifEnde cnd =>
      obtain ⟨ce, tt, te, r1, r2, ys, used1, used2, hce, hTZ, hEZ, hYZ, rfl⟩ :=
        seqZ_wenn_some (cnd := cnd) hbs (by first | exact .inl rfl | exact .inr rfl)
      have hF0 := bindFrischL_sonst (by rfl) hF
      have hcases : EndIfCases u c Γ fn n Λ cnd ss b rest := by
        first
        | exact lowEndL_ifEnde_cases hm hlow
        | exact Or.inr (lowEndL_struct_ok (.inl ⟨cnd, rfl⟩) hlow)
      rcases hcases with ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ |
        ⟨Λ₁, st, tail, q, hst, hq, rfl⟩
      · obtain ⟨hr1, hsuf1, hBt⟩ := ih n (Nat.lt_succ_self n) k ss fn fT ns tb
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hU hS hmemss hF0 True.intro hT hTZ
        have h1 := (List.cons.inj hr1).2
        subst r1
        have hsuf1' := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hBe⟩ := ih n (Nat.lt_succ_self n) k rest1 fn fT (ns.resume used1) eb
          (.blkEnd :: rest) te (.blkEnd :: r2) used2 (hU.afterSeq hTZ) hS
          (fun st h => hmemss st (mem_of_suffix hsuf1' h)) (bindFrischL_suffix hF0 hsuf1') True.intro hE hEZ
        have h2 := (List.cons.inj hr2).2
        subst r2
        obtain ⟨rfl, rfl, _⟩ := seqZ_marker_some hm hYZ
        exact ⟨rfl, ((List.suffix_cons _ _).trans hsuf2).trans
          (hsuf1'.trans (List.suffix_cons _ _)), fun σ ρ s hW hL =>
            endZiel_ite_G S.tab hU hS hcv hce hBt hBe σ ρ s hW hL⟩
      · obtain _ | m := n
        · rw [lowStructL_zero] at hst; cases hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hBt⟩ := laufSeq_G G S c hc O passes R hRR m k ss fn fT ns ⟨Λ₁, tb⟩
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hU hS hmemss hF0 hT hTZ
        have h1 := (List.cons.inj hr1).2
        subst r1
        have hsuf1' := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hBe⟩ := laufSeq_G G S c hc O passes R hRR m k rest1 fn fT (ns.resume used1)
          ⟨Λ₁, eb⟩ (.blkEnd :: tail) te (.blkEnd :: r2) used2 (hU.afterSeq hTZ) hS
          (fun st h => hmemss st (mem_of_suffix hsuf1' h)) (bindFrischL_suffix hF0 hsuf1') hE hEZ
        have h2 := (List.cons.inj hr2).2
        subst r2
        have hsuf2' := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume used2) q rest ys restZ used
          ((hU.afterSeq hTZ).afterSeq hEZ) hS (fun st h => hmemss st (mem_of_suffix hsuf2' h))
          (bindFrischL_suffix hF0 hsuf2') hm hq hYZ
        exact ⟨IH.1, (IH.2.1.trans hsuf2').trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
          endZiel_cons_G (stmtZiel_ite_G S.tab hU hS hcv hce hBt hBe σ ρ s hW hL) IH.2.2⟩
    all_goals exact absurd hbs (by simp only [seqZ, schrittB, namedStmt, stmtBody,
      Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

end Gabbro.Bruecke
