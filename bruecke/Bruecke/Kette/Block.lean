module
public import Bruecke.Anweisung.Option.Kopf
public import Bruecke.Anweisung.Option.Werte
public import Bruecke.Kette.Schritt
public import Bruecke.Anweisung.Zweig.Schritt
public import Bruecke.Anweisung.Zweig.Vorrat
public import Bruecke.Kette.Formen.Ruf
public import Bruecke.Kette.Formen.Bereich
public import Bruecke.Anweisung.Schleife.Simulation
public import Bruecke.Anweisung.Match.NestedKopf
public import Bruecke.Anweisung.Match.Simulation
public import Bruecke.Kette.Formen.Dispatch
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Each arm stops at the same marker and keeps membership in its carried caller's flat body. -/
theorem laufSeq_G {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C) (c : Fin u.fns.length) (hc : C c)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) :
    ∀ (n : Nat) {loopMode : Bool} (k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) loopMode Γ Λ Λ')
      (rest : List UStmt) (t : List Gabbro.Body.Stmt) (restZ : List UStmt) (used : List String),
      UmfangB Γ fn ns → Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) → BindFrischL (protectedNames fn.params fn.kinds) ss →
      lowSeqL (l := loopMode) u c Γ fn n Λ [] ss = .ok (p, rest) →
      seqZ u k fT ns ss = some (t, restZ, used) →
      restZ = rest ∧ rest <:+ ss ∧
      ∀ (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State),
        WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' → BlockZiel_G u C c O passes R fn ns.active p.2 σ ρ s t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro loopMode k ss Γ fn fT ns Λ p rest t restZ used hU hS hmem hF hlow hbs
    obtain _ | n := n
    · rw [lowSeqL_zero] at hlow; cases hlow
    obtain _ | k := k
    · exact absurd hbs (by simp only [seqZ, reduceCtorEq, not_false_eq_true])
    obtain _ | ⟨s0, ss⟩ := ss
    · rw [lowSeq_nil] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl, _⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, fun σ ρ s hW hL => blockZiel_nil_G fn ns.active σ ρ s hW hL⟩
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
      exact ⟨rfl, List.suffix_refl _, fun σ ρ s hW hL => blockZiel_nil_G fn ns.active σ ρ s hW hL⟩
    case bind x d v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind hstepT
      obtain ⟨hx, hF'⟩ := bindFrischL_bind hF
      obtain ⟨ls, q, hls, hq, rfl⟩ := lowSeq_bind_ok hlow
      have heB : namedSide u fn ns v = some eT := (namedSide_sicht hS ns v).symm.trans heT
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x ls.range)
        (fT.mitBindung x (0, 0)) (ns.push x) q rest ys restZ used (hU.bind hx ls.range)
        (hS.bind x (0, 0) ls.range) hmemss hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBind_named_sim (x := x) hls heB hU S.tab hU.valid σ ρ s hW hL
      exact blockZiel_bind_G (fun ρB _ => hstep ρB) (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL')
    case bindW x d v =>
      obtain ⟨id, fields, eT, ys, htT, heT, hys, rfl⟩ := seqZ_bindRecord_some hbs
      have hx : NameFrisch (protectedNames fn.params fn.kinds) x := hF.1
      have hF' : BindFrischL (protectedNames fn.params fn.kinds) ss := hF.2
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindRecord_ok ((recordBinderType_sicht hS d v).symm.trans htT) hlow
      have heB : namedSide u fn ns v = some eT := (namedSide_sicht hS ns v).symm.trans heT
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitWert x (.prod id fields))
        (fT.mitWert x (.prod id fields)) (ns.push x) q rest ys restZ used
        (hU.bindRecord hx id fields) (hS.bindRecord x id fields) hmemss
        (by simpa only [UFn.mitWert, uArtVon, protectedNames] using hF') hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindRecord_named_sim (x := x) hev heB hU S.tab σ ρ s hW hL
      exact blockZiel_bindRecord_G (fun ρB _ => hstep ρB) (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL')
    case bindMut x lo hi v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut hstepT
      obtain ⟨hx, hF'⟩ := bindFrischL_bindMut hF
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindMut_ok hlow
      have heB : namedSide u fn ns v = some eT := (namedSide_sicht hS ns v).symm.trans heT
      have hU' : UmfangB (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) (ns.push x) := hU.bind hx (lo, hi)
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used hU' (hS.bind x (lo, hi) (lo, hi))
        hmemss hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindMut_named_sim (x := x) hev heB hU S.tab hU.valid σ ρ s hW hL
      exact blockZiel_bind_G (fun ρB _ => hstep ρB) (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL')
    case bindB x v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB hstepT
      obtain ⟨hx, hF'⟩ := bindFrischL_bindB hF
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindB_ok hlow
      have heB : condZ u fn ns v = some eT := (condZ_sicht hS ns v).symm.trans heT
      have hU' : UmfangB (.bool :: Γ) (fn.mitBindungB x) (ns.push x) := hU.bindB hx
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindungB x)
        (fT.mitBindungB x) (ns.push x) q rest ys restZ used hU' (hS.bindB x)
        hmemss hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindB_named_sim (x := x) hev heB hU S.tab σ ρ s hW hL
      exact blockZiel_bindB_G (fun ρB _ => hstep ρB) (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL')
    case bindOpt x num v =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hn, eT, heT, rfl, rfl, rfl⟩ := schrittB_bindOpt hstepT
      obtain ⟨hx, hF'⟩ := bindFrischL_bindOpt hF
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindOpt_ok (hn := hn) hlow
      have heB : namedOption u fn ns v = some eT := (namedOption_sicht hS ns v).symm.trans heT
      have hU' : UmfangB (.opt ((declOf u).count ⟨num, hn⟩) :: Γ) (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) := hU.bindOpt num ((declOf u).count ⟨num, hn⟩) hx
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩))
        (fT.mitOpt x num ((declOf u).count ⟨num, hn⟩)) (ns.push x) q rest ys restZ used hU' (hS.bindOpt x num ((declOf u).count ⟨num, hn⟩))
        hmemss hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindOpt_named_sim (x := x) hev heB hU S.tab σ ρ s hW hL
      exact blockZiel_bindOpt_G (fun ρB _ => hstep ρB) (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL')
    case matchWhyBeg x =>
      obtain ⟨count, e, arms, tailZ, allocated, ys, he, hAZ, hYZ, rfl⟩ := seqZ_reason_some hbs
      obtain ⟨id, ht, hid, rfl⟩ := reasonSubject_some he
      have ht' : valueParamTy fn x = some (.why count) := (hS.2.2.2.2 x).symm.trans ht
      have hid' := (BodyNames.lookup_sicht hS ns x).symm.trans hid
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowSeq_reason_ok hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨j, v, ga, hj, hv, hAG, hΛ, hst⟩ := lowStruct_reason_ok ht' hStruct
      subst Λ₁
      cases hst
      have hF0 := bindFrischL_sonst (by rfl) hF
      obtain ⟨hr, hsuf, hArms⟩ := reasonArms_G_with m (by
          intro fuel hlt k ss _ fn ft ns _ p tail bs tailZ used hU hV hm hF hG hB
          exact ih fuel (by omega) k ss fn ft ns p tail bs tailZ used hU hV hm hF hG hB)
        m (Nat.le_refl m) count k 0 ss fn fT ns Λ ga
        (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hU hS hmemss hF0 hAG hAZ
      have ht : tailZ = tail := (List.cons.inj hr).2
      subst tailZ
      have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
      have hU' := hU.resume (reasonArmsZ_used k fT count 0 ns ss arms (.blkEnd :: tail) allocated hAZ)
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used
        hU' hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm))
        (bindFrischL_suffix hF0 hsuf') hQ hYZ
      exact ⟨IH.1, (IH.2.1.trans hsuf').trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        blockZiel_cons_G (stmtZiel_reason_G hj hv hid' hArms σ ρ s hW hL) IH.2.2⟩
    case matchTagBeg sidx x binders =>
      obtain ⟨cs, e, arms, tailZ, allocated, ys, hn, he, hAZ, hYZ, rfl⟩ := seqZ_tag_some hbs
      obtain ⟨id, ht, hBare, hid, rfl⟩ := tagSubject_some he
      have ht' : valueParamTy fn x = some (.sum cs) := (hS.2.2.2.2 x).symm.trans ht
      have hid' := (BodyNames.lookup_sicht hS ns x).symm.trans hid
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowSeq_tag_ok hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨j, v, tagG, hj, hv, hTagG, hΛ, hst⟩ := lowStruct_tag_ok hn ht' hStruct
      subst Λ₁
      cases hst
      obtain ⟨ga, hAG, hBareRel⟩ := lowArms_bare m fn Λ cs binders ss tagG (.blkEnd :: tail) hBare hTagG
      have hF0 := bindFrischL_sonst (by rfl) hF
      obtain ⟨hr, hsuf, hArms⟩ := reasonArms_G_with m (by
          intro fuel hlt k ss _ fn ft ns _ p tail bs tailZ used hU hV hm hF hG hB
          exact ih fuel (by omega) k ss fn ft ns p tail bs tailZ used hU hV hm hF hG hB)
        m (Nat.le_refl m) cs.length k 0 ss fn fT ns Λ ga
        (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hU hS hmemss hF0 hAG hAZ
      have ht : tailZ = tail := (List.cons.inj hr).2
      subst tailZ
      have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
      have hU' := hU.resume (reasonArmsZ_used k fT cs.length 0 ns ss arms (.blkEnd :: tail) allocated hAZ)
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used
        hU' hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm))
        (bindFrischL_suffix hF0 hsuf') hQ hYZ
      exact ⟨IH.1, (IH.2.1.trans hsuf').trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        blockZiel_cons_G (stmtZiel_tag_G hj hv hid' hBareRel hArms σ ρ s hW hL) IH.2.2⟩
    case matchBeg num v x =>
      obtain ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, he, hPZ, hAZ, hYZ, rfl⟩ := seqZ_option_some hbs
      obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowSeq_option_ok hlow
      obtain _ | m := n
      · rw [lowStructL_zero] at hStruct; cases hStruct
      obtain ⟨ev, pG, aG, rest1, hv, hPG, hAG, rfl⟩ := lowStruct_option_ok hn hStruct
      have hF0 : BindFrischL (protectedNames fn.params fn.kinds) ss := hF.2
      obtain ⟨hr1, hsuf1, hP⟩ := ih m (by omega) k ss
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
      obtain ⟨hr2, hsuf2, hA⟩ := ih m (by omega) k rest1 fn fT
        (ns.resume used1) ⟨Λ₁, aG⟩ (.blkEnd :: tail) ab (.blkEnd :: r2) used2 hU1 hS
        (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) (bindFrischL_suffix hF0 hsuf1') hAG hAZ
      have h2 : r2 = tail := (List.cons.inj hr2).2
      subst r2
      have hsuf2' : tail <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hRest⟩ := ih (m + 1) (by omega) k tail fn fT
        (ns.resume used2) q rest ys restZ used (hU1.afterSeq hAZ) hS
        (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) (bindFrischL_suffix hF0 hsuf2') hQ hYZ
      exact ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        blockZiel_cons_G (stmtZiel_option_G hU hS hv he hP hA σ ρ s hW hL) hRest⟩
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
        (hU.index hF.1 t.val ((declOf u).count t)) (hS.index x t.val ((declOf u).count t))
        hmemss hF.2 hBodyG hBodyZ
      have htail : tailZ = tail := (List.cons.inj hrBody).2
      subst tailZ
      have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans hsufBody
      have hmemTail : ∀ st ∈ tail, st ∈ (fnAt u c).body := fun st hm => hmemss st (mem_of_suffix hsuf hm)
      have hUsed := seqZ_used k (fT.mitIndex x t.val ((declOf u).count t))
        (ns.push x) ss bodyB (.blkEnd :: tail) allocated hBodyZ
      have hUrest := hU.resume (fun z hz => hUsed z (BodyNames.used_push ns x z hz))
      have IH := ih (m + 1) (by omega) k tail fn fT (ns.resume allocated) q rest ys restZ used hUrest hS hmemTail
        (bindFrischL_suffix hF.2 hsuf) hQ hTailZ
      exact ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        blockZiel_cons_G (stmtZiel_loop_G hU hBody σ ρ s hW hL) (fun σ₁ ρ₁ s₁ hW₁ hL₁ => IH.2.2 σ₁ ρ₁ s₁ hW₁ hL₁)⟩
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
      have hErr := endBodyZ_sim G S c hc O passes R hRR n k ss fn fT ns err
        (.blkEnd :: tail) errorBody hU hS hmemss hF.2 hEG hEZ
      have IH := ih n (Nat.lt_succ_self n) k tail (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) (ns.push x) q rest ys restZ used (hU.bind hF.1 (lo, hi))
        (hS.bind x (lo, hi) (lo, hi)) hmemTail (bindFrischL_suffix hF.2 hsuf) hQG hYZ
      exact ⟨IH.1, (IH.2.1.trans hsuf).trans (List.suffix_cons _ _), fun σ ρ s hW hL =>
        blockZiel_narrow_G hj hv hid' hU hErr (fun σ ρ s hW hL => IH.2.2 σ ρ s hW hL) σ ρ s hW hL⟩
    case bindCall x g args =>
      obtain ⟨bB, fT', ns', ys, hstep, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨bt, hbT, rfl, rfl⟩ := schrittB_bindCall hstep
      obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowSeq_bindCall_ok hlow
      obtain ⟨ht, sh, hsh⟩ := resultCall_type hk he hbT
      subst bt
      have hb : namedResult u fn ns x g args = some (bB, ty) :=
        (namedResult_sicht hS ns x g args).symm.trans hbT
      obtain ⟨hidx, _, _⟩ := lowRufKopf_ok hk
      have hcallee : fnSuch u g = some (fnAt u head.callee) := fnIdx_find _ _ _ hidx
      have hd := callee_getragen_calls S hc (CallsIn.bind hhead) hcallee
      have hType := (S.boolErg head.callee hd).1
      have hU' := hU.bindRuf hF.1 head.callee hsh hType he
      have hF' : BindFrischL (protectedNames (mitRuf u fn x head.callee ty).params (mitRuf u fn x head.callee ty).kinds) ss := by
        rw [protectedNames_mitRuf fn x head.callee hsh]
        exact hF.2
      have IH := ih n (Nat.lt_succ_self n) k ss (mitRuf u fn x head.callee ty)
        (fT.mitTy x ty) (ns.push x) q rest ys restZ used hU' (hS.bindRuf x head.callee hsh hType he) hmemss hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      cases hR : R head.callee (σ.lese Λ head.args.orte)
          (evalArgs (σ.lese Λ head.args.orte) head.args (σ.lese Λ head.args.orte) ρ) with
      | ok σ₁ v =>
        obtain ⟨A, s₁, hStretch, hW₁, hL₁⟩ :=
          resultCall_strecke G S hc R hRR hk he hb hhead hU σ σ₁ ρ s hW hL v hR
        exact blockZiel_bindCall_ok_G hsh head he hr q.2 hR hStretch (IH.2.2 σ₁ _ s₁ hW₁ hL₁)
      | why σ₁ why =>
        exact (Nat.not_lt_zero why.val (Nat.lt_of_lt_of_eq why.isLt hr)).elim
      | logik err =>
        obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
        have hf : fnSuch u g = some (fnAt u head.callee) := fnIdx_find _ _ _ hi
        have hd := callee_getragen_calls S hc (CallsIn.bind hhead) hf
        refine ⟨fun err' hh => ?_, fun σ' v' hh => ?_ , fun σ' ρ' hh => ?_, fun leave hl σ' ρ' hh => (by
          cases leave <;> simp only [execBlock, hR, controlG, Bool.false_eq_true, ↓reduceIte] at hh <;> cases hh),
          fun σ' r hh => (by simp only [execBlock, hR] at hh; cases hh)⟩
        · simp only [execBlock, hR] at hh
          cases hh
          exact ⟨head.callee, _, _, hd, hR⟩
        · simp only [execBlock, hR] at hh
          cases hh
        · simp only [execBlock, hR] at hh
          cases hh
      | hardware err =>
        refine ⟨fun err' hh => ?_, fun σ' v' hh => ?_ , fun σ' ρ' hh => ?_, fun leave hl σ' ρ' hh => (by
          cases leave <;> simp only [execBlock, hR, controlG, Bool.false_eq_true, ↓reduceIte] at hh <;> cases hh),
          fun σ' r hh => (by simp only [execBlock, hR] at hh; cases hh)⟩
        all_goals simp only [execBlock, hR] at hh; cases hh
    case setVar | setVarB | setVarOpt | assign | assignTab | assignOpt | assignTabOpt | assignGlob | assignGlobB | call =>
      obtain ⟨bT, fT', ns', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hstepN, rfl, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
      have hF' := bindFrischL_sonst (by rfl) hF
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hU hS hmemss hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      exact blockZiel_cons_G
        (stmtZiel_einzeln_G G S c hc O passes R hRR hhead (by exact True.intro) hst hstepN hU σ ρ s hW hL)
        (fun σ₁ ρ₁ s₁ hW₁ hL₁ => IH.2.2 σ₁ ρ₁ s₁ hW₁ hL₁)
    case leave x | next x =>
      obtain ⟨ys, hys, rfl⟩ := (by first
        | exact seqZ_control_some (leave := true) hbs
        | exact seqZ_control_some (leave := false) hbs)
      obtain ⟨hl, q, hq, rfl⟩ := (by first
        | exact lowSeq_control_ok (leave := true) hlow
        | exact lowSeq_control_ok (leave := false) hlow)
      have IH := ih n (Nat.lt_succ_self n) k ss fn fT ns q rest ys restZ used
        hU hS hmemss (bindFrischL_sonst (by rfl) hF) hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      first
        | exact blockZiel_cons_G (stmtZiel_control_G true hl σ ρ s hW hL)
            (fun σ₁ ρ₁ s₁ hW₁ hL₁ => IH.2.2 σ₁ ρ₁ s₁ hW₁ hL₁)
        | exact blockZiel_cons_G (stmtZiel_control_G false hl σ ρ s hW hL)
            (fun σ₁ ρ₁ s₁ hW₁ hL₁ => IH.2.2 σ₁ ρ₁ s₁ hW₁ hL₁)
    case ret r0 =>
      obtain ⟨bst, ys, hbT, hys, rfl⟩ := seqZ_ret_some hbs
      have hbN : retZ u fn ns r0 = some bst := (retZ_sicht hS ns r0).symm.trans hbT
      have hF' := bindFrischL_sonst (by rfl) hF
      obtain ⟨st, q, hst, hq, rfl⟩ := lowSeq_ret_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ _ q rest ys restZ used hU hS hmemss hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      exact blockZiel_cons_G (stmtZiel_ret_G c hst hbN hU S.tab O passes R σ ρ s hW hL)
        (fun σ₁ ρ₁ s₁ hW₁ hL₁ => IH.2.2 σ₁ ρ₁ s₁ hW₁ hL₁)
    case ifBeg cnd | ifEnde cnd =>
      obtain ⟨Λ₁, st, rest', q, hst, hq, rfl⟩ :=
        lowSeq_wenn_ok (cnd := cnd) hlow (by first | exact .inl rfl | exact .inr rfl)
      obtain ⟨ce, tt, te, r1, r2, ys, used1, used2, hce, hTZ, hEZ, hYZ, rfl⟩ :=
        seqZ_wenn_some (cnd := cnd) hbs (by first | exact .inl rfl | exact .inr rfl)
      have hF0 : BindFrischL (protectedNames fn.params fn.kinds) ss := bindFrischL_sonst (by rfl) hF
      obtain _ | m := n
      · rw [lowStructL_zero] at hst; cases hst
      obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
      obtain ⟨hr1, hsuf1, hBt⟩ := ih m (by omega) k ss fn _ ns ⟨Λ₁, tb⟩ (.ifElse :: rest1) tt
        (.ifElse :: r1) used1 hU hS hmemss hF0 hT hTZ
      have h1 : r1 = rest1 := (List.cons.inj hr1).2
      rw [h1] at hEZ
      have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
      obtain ⟨hr2, hsuf2, hBe⟩ := ih m (by omega) k rest1 fn _ (ns.resume used1) ⟨Λ₁, eb⟩ (.blkEnd :: rest') te
        (.blkEnd :: r2) used2 (hU.afterSeq hTZ) hS
          (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) (bindFrischL_suffix hF0 hsuf1') hE hEZ
      have h2 : r2 = rest' := (List.cons.inj hr2).2
      rw [h2] at hYZ
      have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hBc⟩ := ih (m + 1) (by omega) k rest' fn _ (ns.resume used2) q rest ys restZ used ((hU.afterSeq hTZ).afterSeq hEZ) hS
        (fun st hm => hmemss st (mem_of_suffix hsuf2' hm))
        (bindFrischL_suffix hF0 hsuf2') hq hYZ
      refine ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      exact blockZiel_cons_G
        (stmtZiel_ite_G S.tab hU hS hcv hce (fun σ ρ s hW hL => hBt σ ρ s hW hL)
          (fun σ ρ s hW hL => hBe σ ρ s hW hL) σ ρ s hW hL)
        (fun σ₁ ρ₁ s₁ hW₁ hL₁ => hBc σ₁ ρ₁ s₁ hW₁ hL₁)
    all_goals exact absurd hbs (by simp only [seqZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

end Gabbro.Bruecke
