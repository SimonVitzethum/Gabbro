module
public import Bruecke.Kette.Block
public import Bruecke.Anweisung.Match.Kopf
public import Bruecke.Anweisung.Match.Simulation
public import Bruecke.Kette.Formen.ReasonSchritt
public import Bruecke.Kette.Formen.Tag
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Body simulation with bindings and branches, using frames and logical outcomes only of C. -/
theorem lauf_G {P : Programm (declOf u)} (G : GesenktC u C P) (S : Getragen u C) (c : Fin u.fns.length) (hc : C c)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (r : URet) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt),
      UmfangB Γ fn ns → Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) → BindFrischL (protectedNames fn.params fn.kinds) ss →
      lowBodyF u c Γ fn n Λ ss r = .ok b0 → stmtsBodyZ u k fT ns ss r = some bs →
      ∀ (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State),
        WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
        LaufZielTeilB u C c O passes R b0 σ ρ s bs
  | 0, k, ss, Γ, fn, fT, ns, Λ, b0, bs, hU, hS, hmem, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [lowBodyF] at hlow <;> cases hlow
  | n + 1, 0, ss, Γ, fn, fT, ns, Λ, b0, bs, hU, hS, hmem, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      exact absurd hbs (by simp only [stmtsBodyZ, reduceCtorEq, not_false_eq_true])
  | n + 1, k + 1, [], Γ, fn, fT, ns, Λ, b0, bs, hU, hS, hmem, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [lowBodyF] at hlow
      simp only [stmtsBodyZ] at hbs
      have heB : namedEnd u fn ns r = some bs := by
        rw [← namedEnd_sicht hS ns r]
        exact hbs
      obtain ⟨σ', v, hex, hsl, hB⟩ := lowEnd_simB c hlow heB hU S.tab O passes R σ ρ s hW hL
      refine ⟨fun e h => (by rw [hex] at h; cases h), fun σ'' v' h => ?_⟩
      rw [hex] at h
      cases h
      exact ⟨[], by simp, by simp [Oben], List.Pairwise.nil, fun ρB _ _ =>
        ⟨s, (hB ρB).1, (hB ρB).2, hsl⟩⟩
  | n + 1, k + 1, s0 :: ss, Γ, fn, fT, ns, Λ, b0, bs, hU, hS, hmem, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
        fun st hm => hmem st (List.mem_cons_of_mem _ hm)
      have hhead : s0 ∈ (fnAt u c).body := hmem s0 (List.mem_cons_self ..)
      cases s0
      case bind x d v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind hstep0
        obtain ⟨hx, hF'⟩ := bindFrischL_bind hF
        obtain ⟨ls, rest, hls, hrest, rfl⟩ := lowBodyF_bind_ok c hlow
        have heB : namedSide u fn ns v = some eT := (namedSide_sicht hS ns v).symm.trans heT
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBind_named_sim (x := x) hls heB hU S.tab hU.valid σ ρ s hW hL
        have IH := lauf_G G S c hc O passes R hRR r n k ss (fn.mitBindung x ls.range)
          (fT.mitBindung x (0, 0)) (ns.push x) rest bs' (hU.bind hx ls.range) (hS.bind x (0, 0) ls.range)
          hmemss hF' hrest hbs' _ _
          ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL'
        exact laufZiel_schritt_teilB (bind_lauf O passes R ls.term rest σ ρ) (fun ρB _ => hstep ρB)
          (fun w => Int.le_refl _) IH
      case bindW x d v =>
        obtain ⟨id, fields, eT, bs', rfl, heT, hbs', rfl⟩ := stmtsBodyZ_bindRecord_some hbs
        have hx : NameFrisch (protectedNames fn.params fn.kinds) x := hF.1
        have hF' : BindFrischL (protectedNames fn.params fn.kinds) ss := hF.2
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindRecord_ok c hlow
        have heB : namedSide u fn ns v = some eT := (namedSide_sicht hS ns v).symm.trans heT
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindRecord_named_sim (x := x) hev heB hU S.tab σ ρ s hW hL
        have IH := lauf_G G S c hc O passes R hRR r n k ss (fn.mitWert x (.prod id fields))
          (fT.mitWert x (.prod id fields)) (ns.push x) rest bs'
          (hU.bindRecord hx id fields) (hS.bindRecord x id fields) hmemss
          (by simpa only [UFn.mitWert, uArtVon, protectedNames] using hF') hrest hbs' _ _
          ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL'
        exact laufZiel_schritt_teilB (bind_lauf O passes R ev rest σ ρ) (fun ρB _ => hstep ρB)
          (fun w => Int.le_refl _) IH
      case bindMut x lo hi v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut hstep0
        obtain ⟨hx, hF'⟩ := bindFrischL_bindMut hF
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindMut_ok c hlow
        have heB : namedSide u fn ns v = some eT := (namedSide_sicht hS ns v).symm.trans heT
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindMut_named_sim (x := x) hev heB hU S.tab hU.valid σ ρ s hW hL
        have hU' : UmfangB (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) (ns.push x) := hU.bind hx (lo, hi)
        have IH := lauf_G G S c hc O passes R hRR r n k ss (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) (ns.push x) rest bs' hU' (hS.bind x (lo, hi) (lo, hi))
          hmemss hF' hrest hbs' _ _
          ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL'
        exact laufZiel_schritt_teilB (bind_lauf O passes R ev rest σ ρ) (fun ρB _ => hstep ρB)
          (fun w => Int.le_refl _) IH
      case bindB x v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindB hstep0
        obtain ⟨hx, hF'⟩ := bindFrischL_bindB hF
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindB_ok c hlow
        have heB : condZ u fn ns v = some eT := (condZ_sicht hS ns v).symm.trans heT
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindB_named_sim (x := x) hev heB hU S.tab σ ρ s hW hL
        have hU' : UmfangB (.bool :: Γ) (fn.mitBindungB x) (ns.push x) := hU.bindB hx
        have IH := lauf_G G S c hc O passes R hRR r n k ss (fn.mitBindungB x)
          (fT.mitBindungB x) (ns.push x) rest bs' hU' (hS.bindB x)
          hmemss hF' hrest hbs' _ _
          ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) bv⟩ hWl hL'
        exact laufZiel_schritt_teilB (bind_lauf O passes R ev rest σ ρ) (fun ρB _ => hstep ρB)
          (fun w => Int.le_refl _) IH
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
        have hUrest := hU.resume (fun z hz => hUsed z (BodyNames.used_push ns x z hz))
        have IH := lauf_G G S c hc O passes R hRR r n k tail fn fT (ns.resume allocated) q ys hUrest hS hmemTail
          (bindFrischL_suffix hF.2 hsuf) hQ hTailZ
        exact laufZiel_cons_G (stmtZiel_loop_G G S c hc O passes R hRR hU hS hF.1 hmemss hg hBodyG hBodyZ σ ρ s hW hL)
          (fun σ₁ ρ₁ s₁ hW₁ hL₁ => IH σ₁ ρ₁ s₁ hW₁ hL₁)
      case matchTagBeg sidx x binders =>
        obtain ⟨cs, e, arms, tailZ, allocated, ys, hn, he, hAZ, hYZ, rfl⟩ := stmtsBodyZ_tag_some hbs
        obtain ⟨id, ht, hBare, hid, rfl⟩ := tagSubject_some he
        have ht' : valueParamTy fn x = some (.sum cs) := (hS.2.2.2.2 x).symm.trans ht
        have hid' := (BodyNames.lookup_sicht hS ns x).symm.trans hid
        obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowBodyF_tag_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hStruct
        obtain ⟨j, v, tagG, hj, hv, hTagG, hΛ, hst⟩ := lowStruct_tag_ok hn ht' hStruct
        subst Λ₁
        cases hst
        obtain ⟨ga, hAG, hBareRel⟩ := lowArms_bare m fn Λ cs binders ss tagG (.blkEnd :: tail) hBare hTagG
        have hF0 := bindFrischL_sonst (by rfl) hF
        obtain ⟨hr, hsuf, hArms⟩ := reasonArms_G G S hc hRR m cs.length k 0 ss fn fT ns Λ ga
          (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hU hS hmemss hF0 hAG hAZ
        have ht : tailZ = tail := (List.cons.inj hr).2
        subst tailZ
        have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
        have hU' := hU.resume (reasonArmsZ_used k fT cs.length 0 ns ss arms (.blkEnd :: tail) allocated hAZ)
        exact laufZiel_cons_G (stmtZiel_tag_G hj hv hid' hBareRel hArms σ ρ s hW hL)
          (fun σ₁ ρ₁ s₁ hW₁ hL₁ => lauf_G G S c hc O passes R hRR r n k tail fn fT
            (ns.resume allocated) q ys hU' hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm))
            (bindFrischL_suffix hF0 hsuf') hQ hYZ σ₁ ρ₁ s₁ hW₁ hL₁)
      case matchWhyBeg x =>
        obtain ⟨count, e, arms, tailZ, allocated, ys, he, hAZ, hYZ, rfl⟩ := stmtsBodyZ_reason_some hbs
        obtain ⟨id, ht, hid, rfl⟩ := reasonSubject_some he
        have ht' : valueParamTy fn x = some (.why count) := (hS.2.2.2.2 x).symm.trans ht
        have hid' := (BodyNames.lookup_sicht hS ns x).symm.trans hid
        obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowBodyF_reason_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hStruct
        obtain ⟨j, v, ga, hj, hv, hAG, hΛ, hst⟩ := lowStruct_reason_ok ht' hStruct
        subst Λ₁
        cases hst
        have hF0 := bindFrischL_sonst (by rfl) hF
        obtain ⟨hr, hsuf, hArms⟩ := reasonArms_G G S hc hRR m count k 0 ss fn fT ns Λ ga
          (.blkEnd :: tail) arms (.blkEnd :: tailZ) allocated hU hS hmemss hF0 hAG hAZ
        have ht : tailZ = tail := (List.cons.inj hr).2
        subst tailZ
        have hsuf' : tail <:+ ss := (List.suffix_cons _ _).trans hsuf
        have hU' := hU.resume (reasonArmsZ_used k fT count 0 ns ss arms (.blkEnd :: tail) allocated hAZ)
        exact laufZiel_cons_G (stmtZiel_reason_G hj hv hid' hArms σ ρ s hW hL)
          (fun σ₁ ρ₁ s₁ hW₁ hL₁ => lauf_G G S c hc O passes R hRR r n k tail fn fT
            (ns.resume allocated) q ys hU' hS (fun st hm => hmemss st (mem_of_suffix hsuf' hm))
            (bindFrischL_suffix hF0 hsuf') hQ hYZ σ₁ ρ₁ s₁ hW₁ hL₁)
      case matchBeg num v x =>
        obtain ⟨hn, e, pb, ab, r1, r2, ys, used1, used2, he, hPZ, hAZ, hYZ, rfl⟩ := stmtsBodyZ_option_some hbs
        obtain ⟨Λ₁, st, tail, q, hStruct, hQ, rfl⟩ := lowBodyF_option_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hStruct
        obtain ⟨ev, pG, aG, rest1, hv, hPG, hAG, rfl⟩ := lowStruct_option_ok hn hStruct
        have hUindex := hU.index hF.1 num ((declOf u).count ⟨num, hn⟩)
        have hF0 : BindFrischL (protectedNames fn.params fn.kinds) ss := hF.2
        obtain ⟨hr1, hsuf1, hP⟩ := laufSeq_G G S c hc O passes R hRR m k ss
          (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩))
          (fT.mitIndex x num ((declOf u).count ⟨num, hn⟩)) (ns.push x)
          ⟨Λ₁, pG⟩ (.ifElse :: rest1) pb (.ifElse :: r1) used1 hUindex
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
        exact laufZiel_cons_G
          (stmtZiel_option_G hU hS hv he hP hA σ ρ s hW hL)
          (fun σ₁ ρ₁ s₁ hW₁ hL₁ => lauf_G G S c hc O passes R hRR r n k tail fn fT
            (ns.resume used2) q ys (hU1.afterSeq hAZ) hS
            (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) (bindFrischL_suffix hF0 hsuf2')
            hQ hYZ σ₁ ρ₁ s₁ hW₁ hL₁)
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
        have hErr := endBodyZ_sim G S c hc O passes R hRR blockFuel k ss fn fT ns err
          (.blkEnd :: tail) errorBody hU hS hmemss hEG hEZ
        have IH := lauf_G G S c hc O passes R hRR r n k tail (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) (ns.push x) q ys (hU.bind hF.1 (lo, hi))
          (hS.bind x (lo, hi) (lo, hi)) hmemTail (bindFrischL_suffix hF.2 hsuf) hQG hYZ
        exact laufZiel_narrow_G hj hv hid' hU hErr IH σ ρ s hW hL
      case bindCall x g args =>
        obtain ⟨bB, fT', ns', ys, hstep, hys, rfl⟩ := stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨bt, hbT, rfl, rfl⟩ := schrittB_bindCall hstep
        obtain ⟨head, ty, he, hr, q, hk, hq, rfl⟩ := lowBodyF_bindCall_ok hlow
        obtain ⟨ht, sh, hsh⟩ := resultCall_type hk he hbT
        subst bt
        have hb : namedResult u fn ns x g args = some (bB, ty) :=
          (namedResult_sicht hS ns x g args).symm.trans hbT
        rw [mitRuf_scalar fn x head.callee hsh] at hq
        have hU' := hU.bindTy hF.1 hsh
        have hF' : BindFrischL (protectedNames (fn.mitTy x ty).params (fn.mitTy x ty).kinds) ss := by
          rw [protectedNames_mitTy fn x hsh]
          exact hF.2
        have IH := lauf_G G S c hc O passes R hRR r n k ss (fn.mitTy x ty)
          (fT.mitTy x ty) (ns.push x) q ys hU' (hS.bindTy x hsh) hmemss hF' hq hys
        cases hR : R head.callee (σ.lese Λ head.args.orte)
            (evalArgs (σ.lese Λ head.args.orte) head.args (σ.lese Λ head.args.orte) ρ) with
        | ok σ₁ v =>
          obtain ⟨A, s₁, hStretch, hW₁, hL₁⟩ :=
            resultCall_strecke G S hc R hRR hk he hb hhead hU σ σ₁ ρ s hW hL v hR
          have hrun : (∀ err, execEnd O passes R (.bindCall head.callee head.args he head.hp hr q) σ ρ = .logik err →
              execEnd O passes R q σ₁ (Env.cons (ergWert he v) ρ) = .logik err) ∧
              (∀ σ' v', execEnd O passes R (.bindCall head.callee head.args he head.hp hr q) σ ρ = .zurueck σ' v' →
                execEnd O passes R q σ₁ (Env.cons (ergWert he v) ρ) = .zurueck σ' v') := by
            constructor
            · intro err hh
              simp only [execEnd, hR] at hh
              exact EndAusgang.schrumpf_logik hh
            · intro σ' v' hh
              simp only [execEnd, hR] at hh
              exact endSchrumpf_zurueck hh
          have hh := laufZiel_strecke_G hrun hStretch (IH σ₁ _ s₁ hW₁ hL₁)
          rw [List.singleton_append] at hh
          exact hh
        | why σ₁ why =>
          exact (Nat.not_lt_zero why.val (Nat.lt_of_lt_of_eq why.isLt hr)).elim
        | logik err =>
          obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
          have hf : fnSuch u g = some (fnAt u head.callee) := fnIdx_find _ _ _ hi
          have hd := callee_getragen_calls S hc (CallsIn.bind hhead) hf
          refine ⟨fun err' hh => ?_, fun σ' v' hh => ?_ ⟩
          · simp only [execEnd, hR] at hh
            cases hh
            exact ⟨head.callee, _, _, hd, hR⟩
          · simp only [execEnd, hR] at hh
            cases hh

        | hardware err =>
          refine ⟨fun err' hh => ?_, fun σ' v' hh => ?_ ⟩
          all_goals simp only [execEnd, hR] at hh; cases hh
      case setVar | setVarB | assign | assignTab | assignGlob | call =>
        obtain ⟨bT, fT', ns', bs', hstepT, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨hstepN, rfl, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
        have hF' := bindFrischL_sonst (by rfl) hF
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r _ ss (by exact True.intro) hlow
        exact laufZiel_cons_G
          (stmtZiel_einzeln_G G S c hc O passes R hRR hhead (by exact True.intro) hgst hstepN hU σ ρ s hW hL)
          (fun σ₁ ρ₁ s₁ hW₁ hL₁ =>
            lauf_G G S c hc O passes R hRR r n k ss fn _ _ rest bs' hU hS hmemss hF' hrest hbs' σ₁ ρ₁ s₁ hW₁
              hL₁)
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', used1, used2, hce, hTZ, hEZ, hbs', rfl⟩ := stmtsBodyZ_ifBeg_some hbs
        have hF0 : BindFrischL (protectedNames fn.params fn.kinds) ss := bindFrischL_sonst (by rfl) hF
        obtain ⟨Λ₁, st, rest', e, hst, hrest, rfl⟩ := lowBodyF_ifBeg_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hBt⟩ := laufSeq_G G S c hc O passes R hRR m k ss fn _ ns ⟨Λ₁, tb⟩
          (.ifElse :: rest1) tt (.ifElse :: r1) used1 hU hS hmemss hF0 hT hTZ
        have h1 : r1 = rest1 := (List.cons.inj hr1).2
        rw [h1] at hEZ
        have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hBe⟩ := laufSeq_G G S c hc O passes R hRR m k rest1 fn _ (ns.resume used1) ⟨Λ₁, eb⟩
          (.blkEnd :: rest') te (.blkEnd :: r2) used2 (hU.afterSeq hTZ) hS
          (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) (bindFrischL_suffix hF0 hsuf1') hE hEZ
        have h2 : r2 = rest' := (List.cons.inj hr2).2
        rw [h2] at hbs'
        have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        have hF2 := bindFrischL_suffix hF0 hsuf2'
        exact laufZiel_cons_G
          (stmtZiel_ite_G S.tab hU hS hcv hce (fun σ ρ s hW hL => hBt σ ρ s hW hL)
            (fun σ ρ s hW hL => hBe σ ρ s hW hL) σ ρ s hW hL)
          (fun σ₁ ρ₁ s₁ hW₁ hL₁ =>
            lauf_G G S c hc O passes R hRR r n k rest' fn _ (ns.resume used2) e bs' ((hU.afterSeq hTZ).afterSeq hEZ) hS (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hF2 hrest hbs' σ₁ ρ₁ s₁ hW₁
              hL₁)
      all_goals exact absurd hbs (by simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

end Gabbro.Bruecke
