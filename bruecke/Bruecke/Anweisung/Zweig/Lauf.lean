module
public import Bruecke.Anweisung.Zweig.Block
@[expose] public section

/-!
# C6, part 6: the run of a body with conditionals

`laufZ` follows the body reader `lowBodyF` like `laufB`, with one more case: a conditional
(`ifBeg`) is the structured statement `Stmt.ite` at `blockFuel`, its arms run by `laufSeq`, the
rest of the body in the scope at the `if`. A `let` and a `let mut` are `laufB`'s cases; the
statements `lowStmtL` reads go through `stmtZiel_einzeln`. The conclusion is `lauf`'s
(`LaufZiel`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- **The run of a lowered body with local bindings and conditionals.** From related states in a
    scope the body reader reached, with fresh binders: the G run never blames a caller's
    `requires`, and where it returns there is an answer table under which the Body run of
    `stmtsBodyZ` ends in a related state with the same answer. -/
theorem laufZ {P : Programm (declOf u)} (G : Gesenkt u P) (S : Stimmig u) (c : Fin u.fns.length)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) (r : URet) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt),
      UmfangB Γ fn → Sicht u fT fn → BindFrischL (fn.params.map (·.1)) ss →
      lowBodyF u c Γ fn n Λ ss r = .ok b0 → stmtsBodyZ u k fT ss r = some bs →
      ∀ (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State),
        WRel u σ s.world → LRel fn 0 ρ s.local' →
        LaufZiel u c O passes R b0 σ ρ s bs
  | 0, k, ss, Γ, fn, fT, Λ, b0, bs, hU, hS, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [lowBodyF] at hlow <;> cases hlow
  | n + 1, 0, ss, Γ, fn, fT, Λ, b0, bs, hU, hS, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      exact absurd hbs (by simp [stmtsBodyZ])
  | n + 1, k + 1, [], Γ, fn, fT, Λ, b0, bs, hU, hS, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      simp only [lowBodyF] at hlow
      simp only [stmtsBodyZ] at hbs
      have heB : endBody u fn r = some bs := by
        rw [← endBody_sicht hS r]
        exact hbs
      obtain ⟨σ', v, hex, hsl, hB⟩ := lowEnd_simB c hlow heB hU S.tab O passes R σ ρ s hW hL
      refine ⟨fun e h => (by rw [hex] at h; cases h), fun σ'' v' h => ?_⟩
      rw [hex] at h
      cases h
      exact ⟨[], by simp, by simp [Oben], List.Pairwise.nil, fun ρB _ _ =>
        ⟨s, (hB ρB).1, (hB ρB).2, wrel_slots u hsl hW⟩⟩
  | n + 1, k + 1, s0 :: ss, Γ, fn, fT, Λ, b0, bs, hU, hS, hF, hlow, hbs, σ, ρ, s, hW, hL => by
      cases s0
      case bind x d v =>
        obtain ⟨bB, fT', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bind hstep0
        obtain ⟨hx, hF'⟩ := bindFrischL_bind hF
        obtain ⟨ls, rest, hls, hrest, rfl⟩ := lowBodyF_bind_ok c hlow
        have heB : sideExpr u fn v = some eT := (sideExpr_sicht hS v).symm.trans heT
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBind_sim (x := x) hls heB hU S.tab σ ρ s hW hL
        have IH := laufZ G S c O passes R hRR r n k ss (fn.mitBindung x ls.range)
          (fT.mitBindung x (0, 0)) rest bs' (hU.bind hx ls.range) (hS.bind x (0, 0) ls.range)
          (by rw [mitBindung_namen]; exact hF') hrest hbs' _ _
          ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩ hWl hL'
        exact laufZiel_schritt (bind_lauf O passes R ls.term rest σ ρ) (fun ρB _ => hstep ρB)
          (fun w => Int.le_refl _) IH
      case bindMut x lo hi v =>
        obtain ⟨bB, fT', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bindMut hstep0
        obtain ⟨hx, hF'⟩ := bindFrischL_bindMut hF
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindMut_ok c hlow
        have heB : sideExpr u fn v = some eT := (sideExpr_sicht hS v).symm.trans heT
        obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindMut_sim (x := x) hev heB hU S.tab σ ρ s hW hL
        have hU' : UmfangB (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) := hU.bind hx (lo, hi)
        have IH := laufZ G S c O passes R hRR r n k ss (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) rest bs' hU' (hS.bind x (lo, hi) (lo, hi))
          (by rw [mitBindung_namen]; exact hF') hrest hbs' _ _
          ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩ hWl hL'
        exact laufZiel_schritt (bind_lauf O passes R ev rest σ ρ) (fun ρB _ => hstep ρB)
          (fun w => Int.le_refl _) IH
      case setVar | assign | assignTab | call =>
        obtain ⟨bT, fT', bs', hstepT, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨hstepN, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
        have hF' := bindFrischL_sonst (by rfl) hF
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r _ ss (by exact True.intro) hlow
        exact laufZiel_cons
          (stmtZiel_einzeln G S c O passes R hRR (by exact True.intro) hgst hstepN hU σ ρ s hW hL)
          (fun σ₁ ρ₁ s₁ hW₁ hL₁ =>
            laufZ G S c O passes R hRR r n k ss fn _ rest bs' hU hS hF' hrest hbs' σ₁ ρ₁ s₁ hW₁
              hL₁)
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', hce, hTZ, hEZ, hbs', rfl⟩ := stmtsBodyZ_ifBeg_some hbs
        have hF0 : BindFrischL (fn.params.map (·.1)) ss := bindFrischL_sonst (by rfl) hF
        obtain ⟨Λ₁, st, rest', e, hst, hrest, rfl⟩ := lowBodyF_ifBeg_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hBt⟩ := laufSeq G S c O passes R hRR m k ss fn _ ⟨Λ₁, tb⟩
          (.ifElse :: rest1) tt (.ifElse :: r1) hU hS hF0 hT hTZ
        have h1 : r1 = rest1 := (List.cons.inj hr1).2
        rw [h1] at hEZ
        have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hBe⟩ := laufSeq G S c O passes R hRR m k rest1 fn _ ⟨Λ₁, eb⟩
          (.blkEnd :: rest') te (.blkEnd :: r2) hU hS (bindFrischL_suffix hF0 hsuf1') hE hEZ
        have h2 : r2 = rest' := (List.cons.inj hr2).2
        rw [h2] at hbs'
        have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        have hF2 := bindFrischL_suffix hF0 hsuf2'
        exact laufZiel_cons
          (stmtZiel_ite S hU hS hcv hce (fun σ ρ s hW hL => hBt σ ρ s hW hL)
            (fun σ ρ s hW hL => hBe σ ρ s hW hL) σ ρ s hW hL)
          (fun σ₁ ρ₁ s₁ hW₁ hL₁ =>
            laufZ G S c O passes R hRR r n k rest' fn _ e bs' hU hS hF2 hrest hbs' σ₁ ρ₁ s₁ hW₁
              hL₁)
      all_goals exact absurd hbs (by simp [stmtsBodyZ, schrittB, stmtBody])

end Gabbro.Bruecke
