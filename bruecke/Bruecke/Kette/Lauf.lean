module
public import Bruecke.Kette.Block
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
      case setVar | assign | assignTab | assignGlob | call =>
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
