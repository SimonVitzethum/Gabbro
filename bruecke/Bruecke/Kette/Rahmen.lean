module
public import Bruecke.Kette.RahmenBlock
public import Bruecke.Anweisung.Match.Kopf
public import Bruecke.Anweisung.Match.Rahmen
public import Bruecke.Kette.Formen.ReasonStatisch
public import Bruecke.Anweisung.Match.TagKopf
public import Bruecke.Anweisung.Match.TagRahmen
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem statisch_G (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env) (r : URet) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt),
      Γ = fn.params.map (·.2) → Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowBodyF u c Γ fn n Λ ss r = .ok b0 → stmtsBodyZ u k fT ns ss r = some bs →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, CallsIn ss cname args) →
        Gabbro.Body.Frame ρB cname (writesU gf)) →
      Statisch ρB (writesU (fnAt u c)) bs
  | 0, k, ss, Γ, fn, fT, ns, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      simp only [lowBodyF] at hlow <;> cases hlow
  | n + 1, 0, ss, Γ, fn, fT, ns, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      exact absurd hbs (by simp only [stmtsBodyZ, reduceCtorEq, not_false_eq_true])
  | n + 1, k + 1, [], Γ, fn, fT, ns, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      simp only [stmtsBodyZ] at hbs
      exact statisch_rets bs (namedEnd_rets (fn := fT) (r := r) hbs)
  | n + 1, k + 1, s0 :: ss, Γ, fn, fT, ns, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
        fun st hm => hmem st (List.mem_cons_of_mem _ hm)
      have hhead : s0 ∈ (fnAt u c).body := hmem s0 (List.mem_cons_self ..)
      have hFss : ∀ cname gf, fnSuch u cname = some gf → (∃ args, CallsIn ss cname args) →
          Gabbro.Body.Frame ρB cname (writesU gf) :=
        fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, hm.cons _⟩
      cases s0
      case bind x d v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind hstep0
        obtain ⟨ls, rest, hls, hrest, rfl⟩ := lowBodyF_bind_ok c hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss (fn.mitBindung x ls.range)
          (fT.mitBindung x (0, 0)) (ns.push x) rest bs'
          (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bind x (0, 0) ls.range) hmemss hrest hbs' hFss)
      case bindW x d v =>
        obtain ⟨id, fields, eT, bs', rfl, heT, hbs', rfl⟩ := stmtsBodyZ_bindRecord_some hbs
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindRecord_ok c hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss (fn.mitWert x (.prod id fields))
          (fT.mitWert x (.prod id fields)) (ns.push x) rest bs'
          (congrArg (List.cons _) hΓ) (hS.bindRecord x id fields) hmemss hrest hbs' hFss)
      case bindMut x lo hi v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut hstep0
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindMut_ok c hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) (ns.push x) rest bs'
          (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bind x (lo, hi) (lo, hi)) hmemss hrest hbs' hFss)
      case bindB x v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB hstep0
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindB_ok c hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss (fn.mitBindungB x)
          (fT.mitBindungB x) (ns.push x) rest bs'
          (by rw [mitBindungB_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bindB x) hmemss hrest hbs' hFss)
      case loopBeg x tab inv =>
        obtain ⟨rfl, hg, tZ, bodyB, tailZ, allocated, ys, htZ, hBodyZ, hTailZ, rfl⟩ := stmtsBodyZ_loop_some hbs
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
        obtain ⟨htail, hsuf⟩ := loopWrites_rest m k ss
          (fn.mitIndex x t.val ((declOf u).count t)) (fT.mitIndex x t.val ((declOf u).count t))
          (ns.push x) bodyG tail tailZ bodyB allocated hg hBodyG hBodyZ
        subst tailZ
        have hmemTail : ∀ st ∈ tail, st ∈ (fnAt u c).body := fun st hm => hmemss st (mem_of_suffix hsuf hm)
        have hUsed := seqZ_used k (fT.mitIndex x t.val ((declOf u).count t))
          (ns.push x) ss bodyB (.blkEnd :: tail) allocated hBodyZ
        have hΓi : .index ((declOf u).count t) :: Γ =
            (fn.mitIndex x t.val ((declOf u).count t)).params.map (·.2) := congrArg (List.cons _) hΓ
        obtain ⟨_, _, hFrameBody⟩ := statischSeq_G S c hc ρB m k ss
          (fn.mitIndex x t.val ((declOf u).count t)) (fT.mitIndex x t.val ((declOf u).count t))
          (ns.push x) ⟨Λ, bodyG⟩ (.blkEnd :: tail) bodyB (.blkEnd :: tail) allocated
          hΓi (hS.index x t.val ((declOf u).count t)) hmemss hBodyG hBodyZ hFss
        have IH := statisch_G S c hc ρB r n k tail fn fT (ns.resume allocated) q ys hΓ hS hmemTail hQ hTailZ
          (fun g gf hgf ⟨args, hc⟩ => hFss g gf hgf ⟨args, hc.mono (fun _ hm => mem_of_suffix hsuf hm)⟩)
        exact .forEach _ _ _ _ hFrameBody IH
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
        obtain ⟨hr, hsuf, hArms⟩ := reasonArms_statisch S hc ρB m cs.length k 0 ss fn fT ns Λ ga
          (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hΓ hS hmemss hAG hAZ hFss
        have ht : tailZ = tail := (List.cons.inj hr).2
        subst tailZ
        have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
        exact .selected _ _ (tag_frame hArms)
          (statisch_G S c hc ρB r n k tail fn fT (ns.resume allocated) q ys hΓ hS
            (fun st hm => hmemss st (mem_of_suffix hsuf' hm)) hQ hYZ
            (fun cn gf hgf ⟨args, hc⟩ => hFss cn gf hgf ⟨args, hc.mono (fun _ h => mem_of_suffix hsuf' h)⟩))
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
        obtain ⟨hr, hsuf, hArms⟩ := reasonArms_statisch S hc ρB m count k 0 ss fn fT ns Λ ga
          (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hΓ hS hmemss hAG hAZ hFss
        have ht : tailZ = tail := (List.cons.inj hr).2
        subst tailZ
        have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
        exact .selected _ _ (reason_frame hArms)
          (statisch_G S c hc ρB r n k tail fn fT (ns.resume allocated) q ys hΓ hS
            (fun st hm => hmemss st (mem_of_suffix hsuf' hm)) hQ hYZ
            (fun cn gf hgf ⟨args, hc⟩ => hFss cn gf hgf ⟨args, hc.mono (fun _ h => mem_of_suffix hsuf' h)⟩))
      case matchBeg num v x =>
        obtain ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, he, hPZ, hAZ, hYZ, rfl⟩ := stmtsBodyZ_option_some hbs
        obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowBodyF_option_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hStruct
        obtain ⟨ev, pG, aG, rest1, hv, hPG, hAG, rfl⟩ := lowStruct_option_ok hn hStruct
        obtain ⟨hr1, hsuf1, hP⟩ := statischSeq_G S c hc ρB m k ss
          (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩))
          (fT.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x)
          ⟨Λ₁, pG⟩ (.ifElse :: rest1) pb (.ifElse :: r1) used1
          (congrArg (List.cons _) hΓ) (hS.index x num ((declOf u).count ⟨num, hn⟩))
          hmemss hPG hPZ hFss
        have h1 : r1 = rest1 := (List.cons.inj hr1).2
        subst r1
        have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hA⟩ := statischSeq_G S c hc ρB m k rest1 fn fT
          (ns.resume used1) ⟨Λ₁, aG⟩ (.blkEnd :: tail) ab (.blkEnd :: r2) used2 hΓ hS
          (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) hAG hAZ
          (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, hm.mono (fun _ h => mem_of_suffix hsuf1' h)⟩)
        have h2 : r2 = tail := (List.cons.inj hr2).2
        subst r2
        have hsuf2' : tail <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        exact .selected _ _ (option_frame hP hA)
          (statisch_G S c hc ρB r n k tail fn fT (ns.resume used2) q ys hΓ hS
            (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hQ hYZ
            (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, hm.mono (fun _ h => mem_of_suffix hsuf2' h)⟩))
      case narrowBeg x lo hi =>
        obtain ⟨e, errorBody, tailZ, ys, hname, hEZ, hYZ, rfl⟩ := stmtsBodyZ_narrow_some hbs
        obtain ⟨hn, id, hid, rfl⟩ := narrowName_some hname
        have hn' : numericParam fn x = true := (hS.1 x).symm.trans hn
        have hid' : ns.lookup fn x = some id := (BodyNames.lookup_sicht hS ns x).symm.trans hid
        obtain ⟨j, a, b, v, err, tail, q, hj, hv, hEG, hQG, rfl⟩ := lowBodyF_narrow_ok hn' hlow
        have heq : tail = tailZ := (List.cons.inj (endBodyZ_rest blockFuel k ss fn fT ns err
          (.blkEnd :: tail) (.blkEnd :: tailZ) errorBody hEG hEZ)).2
        subst tailZ
        have hsuf : tail <:+ ss := (List.suffix_cons _ _).trans (endBodyZ_suffix k fT ns ss errorBody _ hEZ)
        have hmemTail : ∀ st ∈ tail, st ∈ (fnAt u c).body := fun st hm => hmemss st (mem_of_suffix hsuf hm)
        have hErr := endBodyZ_statisch S hc ρB blockFuel k ss fn fT ns err (.blkEnd :: tail)
          errorBody hΓ hS hmemss hEG hEZ hFss
        have hΓ' : .int lo hi :: Γ = (fn.mitBindung x (lo, hi)).params.map (·.2) :=
          congrArg (List.cons _) hΓ
        have IH := statisch_G S c hc ρB r n k tail (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) (ns.push x) q ys hΓ' (hS.bind x (lo, hi) (lo, hi))
          hmemTail hQG hYZ (fun g gf hgf ⟨args, hc⟩ => hFss g gf hgf ⟨args, hc.mono (fun _ hm => mem_of_suffix hsuf hm)⟩)
        exact .ite _ _ _ _ (.bindName _ _ _ .nil) hErr IH
      case bindCall x g args =>
        obtain ⟨bB, fT', ns', ys, hstep, hys, rfl⟩ := stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨bt, hb, rfl, rfl⟩ := schrittB_bindCall hstep
        obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowBodyF_bindCall_ok hlow
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
        have IH := statisch_G S c hc ρB r n k ss (fn.mitTy x ty)
          (fT.mitTy x ty) (ns.push x) q ys hctx (hS.bindTy x hsh) hmemss hq hys hFss
        exact .bindCall _ _ _ _ _ _ (fun t p hp => hframe t p (fun hm => hp (hsub _ hm))) IH
      case setVar x v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨-, id, eT, -, -, rfl, rfl, rfl⟩ := schrittB_setVar hstep0
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.setVar x v) ss trivial hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss fn _ _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      case setVarB x v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨id, eT, -, -, rfl, rfl, rfl⟩ := schrittB_setVarB hstep0
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.setVarB x v) ss trivial hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss fn _ _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      case assign | assignTab | assignGlob | call =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨hstepN, rfl, rfl⟩ := schrittB_einzeln_sicht hS hstep0 (by exact True.intro)
        obtain ⟨hx, -, -⟩ := schrittB_stmt hstepN (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r _ ss (by exact True.intro) hlow
        exact statisch_schritt_G S c hc ρB hΓ _ ss hhead hgst hx hF
          (statisch_G S c hc ρB r n k ss fn _ _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', used1, used2, hce, hTZ, hEZ, hbs', rfl⟩ := stmtsBodyZ_ifBeg_some hbs
        obtain ⟨Λ₁, st, rest', e, hst, hrest, rfl⟩ := lowBodyF_ifBeg_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hSt⟩ := statischSeq_G S c hc ρB m k ss fn _ ns ⟨Λ₁, tb⟩ (.ifElse :: rest1)
          tt (.ifElse :: r1) used1 hΓ hS hmemss hT hTZ hFss
        have h1 : r1 = rest1 := (List.cons.inj hr1).2
        rw [h1] at hEZ
        have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hSe⟩ := statischSeq_G S c hc ρB m k rest1 fn _ (ns.resume used1) ⟨Λ₁, eb⟩
          (.blkEnd :: rest') te (.blkEnd :: r2) used2 hΓ hS (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) hE hEZ
          (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, hm.mono (fun _ h => mem_of_suffix hsuf1' h)⟩)
        have h2 : r2 = rest' := (List.cons.inj hr2).2
        rw [h2] at hbs'
        have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        exact .ite _ _ _ _ hSt hSe (statisch_G S c hc ρB r n k rest' fn _ (ns.resume used2) e bs' hΓ hS (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hrest hbs'
          (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, hm.mono (fun _ h => mem_of_suffix hsuf2' h)⟩))
      all_goals exact absurd hbs (by simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

theorem exec_rahmen_G (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env) (r : URet)
    (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
    (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt)
    (hΓ : Γ = fn.params.map (·.2)) (hS : Sicht u fT fn)
    (hmem : ∀ st ∈ ss, st ∈ (fnAt u c).body)
    (hlow : lowBodyF u c Γ fn n Λ ss r = .ok b0) (hbs : stmtsBodyZ u k fT ns ss r = some bs)
    (hF : ∀ cname gf, fnSuch u cname = some gf → (∃ args, CallsIn ss cname args) →
      Gabbro.Body.Frame ρB cname (writesU gf)) :
    ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB bs t) = some s' →
      ∀ p, p.carrier ∉ (writesU (fnAt u c)) → s'.world p = t.world p :=
  exec_statisch (statisch_G S c hc ρB r n k ss fn _ ns b0 bs hΓ hS hmem hlow hbs hF)

end Gabbro.Bruecke
