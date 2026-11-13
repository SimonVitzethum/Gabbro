module
public import Bruecke.Anweisung.Zweig.Schritt
@[expose] public section

/-!
# C6, part 5: the run of a block

`laufSeq` follows the block reader `lowSeqL`, by strong induction on its fuel: the block and its
translation stop at the same marker (`restZ = rest`), what is left is a suffix of what was read,
and from related states the run of the block against its translation is a `BlockZiel` -- a
`logik` outcome is a callee's, a return a `RueckZ`, a fall-through a stretch to related states in
the scope at the block's start (a binder of the block leaves the scope, `blockZiel_bind`). A
conditional inside a block reads its two arms one fuel level below, the rest at the same level.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- **The run of a lowered block against its Body translation.** -/
theorem laufSeq {P : Programm (declOf u)} (G : Gesenkt u P) (S : Stimmig u) (c : Fin u.fns.length)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) {Λ : List (Res (declOf u))}
      (p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) false Γ Λ Λ')
      (rest : List UStmt) (t : List Gabbro.Body.Stmt) (restZ : List UStmt),
      UmfangB Γ fn → Sicht u fT fn → BindFrischL (fn.params.map (·.1)) ss →
      lowSeqL (l := false) u c Γ fn n Λ [] ss = .ok (p, rest) →
      seqZ u k fT ss = some (t, restZ) →
      restZ = rest ∧ rest <:+ ss ∧
      ∀ (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State),
        WRel u σ s.world → LRel fn 0 ρ s.local' → BlockZiel u c O passes R fn p.2 σ ρ s t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k ss Γ fn fT Λ p rest t restZ hU hS hF hlow hbs
    obtain _ | n := n
    · rw [lowSeqL_zero] at hlow; cases hlow
    obtain _ | k := k
    · exact absurd hbs (by simp [seqZ])
    obtain _ | ⟨s0, ss⟩ := ss
    · rw [lowSeq_nil] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, fun σ ρ s hW hL => blockZiel_nil fn σ ρ s hW hL⟩
    cases s0
    case blkEnd | ifElse =>
      first
        | rw [lowSeq_blkEnd] at hlow
        | rw [lowSeq_ifElse] at hlow
      cases hlow
      simp only [seqZ, Option.some.injEq, Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      exact ⟨rfl, List.suffix_refl _, fun σ ρ s hW hL => blockZiel_nil fn σ ρ s hW hL⟩
    case bind x d v =>
      obtain ⟨bT, fT', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bind hstepT
      obtain ⟨hx, hF'⟩ := bindFrischL_bind hF
      obtain ⟨ls, q, hls, hq, rfl⟩ := lowSeq_bind_ok hlow
      have heB : sideExpr u fn v = some eT := (sideExpr_sicht hS v).symm.trans heT
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x ls.range)
        (fT.mitBindung x (0, 0)) q rest ys restZ (hU.bind hx ls.range)
        (hS.bind x (0, 0) ls.range) (by rw [mitBindung_namen]; exact hF') hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBind_sim (x := x) hls heB hU S.tab σ ρ s hW hL
      exact blockZiel_bind hx.1 (fun ρB _ => hstep ρB) (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩ hWl hL')
    case bindMut x lo hi v =>
      obtain ⟨bT, fT', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨eT, heT, rfl, rfl⟩ := schrittB_bindMut hstepT
      obtain ⟨hx, hF'⟩ := bindFrischL_bindMut hF
      obtain ⟨ev, q, hev, hq, rfl⟩ := lowSeq_bindMut_ok hlow
      have heB : sideExpr u fn v = some eT := (sideExpr_sicht hS v).symm.trans heT
      have hU' : UmfangB (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) := hU.bind hx (lo, hi)
      have IH := ih n (Nat.lt_succ_self n) k ss (fn.mitBindung x (lo, hi))
        (fT.mitBindung x (lo, hi)) q rest ys restZ hU' (hS.bind x (lo, hi) (lo, hi))
        (by rw [mitBindung_namen]; exact hF') hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      obtain ⟨bv, hstep, hWl, hL'⟩ := lowBindMut_sim (x := x) hev heB hU S.tab σ ρ s hW hL
      exact blockZiel_bind hx.1 (fun ρB _ => hstep ρB) (fun w => Int.le_refl _)
        (IH.2.2 _ _ ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩ hWl hL')
    case setVar | assign | assignTab | call =>
      obtain ⟨bT, fT', ys, hstepT, hys, rfl⟩ := seqZ_schritt_some hbs (by exact True.intro)
      obtain ⟨hstepN, rfl⟩ := schrittB_einzeln_sicht hS hstepT (by exact True.intro)
      have hF' := bindFrischL_sonst (by rfl) hF
      obtain ⟨Λ₁, st, q, hst, hq, rfl⟩ := lowSeq_einzeln_ok hlow (by exact True.intro)
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ q rest ys restZ hU hS hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      exact blockZiel_cons
        (stmtZiel_einzeln G S c O passes R hRR (by exact True.intro) hst hstepN hU σ ρ s hW hL)
        (fun σ₁ ρ₁ s₁ hW₁ hL₁ => IH.2.2 σ₁ ρ₁ s₁ hW₁ hL₁)
    case ret r0 =>
      obtain ⟨bst, ys, hbT, hys, rfl⟩ := seqZ_ret_some hbs
      have hbN : retZ u fn r0 = some bst := (retZ_sicht hS r0).symm.trans hbT
      have hF' := bindFrischL_sonst (by rfl) hF
      obtain ⟨st, q, hst, hq, rfl⟩ := lowSeq_ret_ok hlow
      have IH := ih n (Nat.lt_succ_self n) k ss fn _ q rest ys restZ hU hS hF' hq hys
      refine ⟨IH.1, IH.2.1.trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      exact blockZiel_cons (stmtZiel_ret c hst hbN hU S.tab O passes R σ ρ s hW hL)
        (fun σ₁ ρ₁ s₁ hW₁ hL₁ => IH.2.2 σ₁ ρ₁ s₁ hW₁ hL₁)
    case ifBeg cnd | ifEnde cnd =>
      obtain ⟨Λ₁, st, rest', q, hst, hq, rfl⟩ :=
        lowSeq_wenn_ok (cnd := cnd) hlow (by first | exact .inl rfl | exact .inr rfl)
      obtain ⟨ce, tt, te, r1, r2, ys, hce, hTZ, hEZ, hYZ, rfl⟩ :=
        seqZ_wenn_some (cnd := cnd) hbs (by first | exact .inl rfl | exact .inr rfl)
      have hF0 : BindFrischL (fn.params.map (·.1)) ss := bindFrischL_sonst (by rfl) hF
      obtain _ | m := n
      · rw [lowStructL_zero] at hst; cases hst
      obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
      obtain ⟨hr1, hsuf1, hBt⟩ := ih m (by omega) k ss fn _ ⟨Λ₁, tb⟩ (.ifElse :: rest1) tt
        (.ifElse :: r1) hU hS hF0 hT hTZ
      have h1 : r1 = rest1 := (List.cons.inj hr1).2
      rw [h1] at hEZ
      have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
      obtain ⟨hr2, hsuf2, hBe⟩ := ih m (by omega) k rest1 fn _ ⟨Λ₁, eb⟩ (.blkEnd :: rest') te
        (.blkEnd :: r2) hU hS (bindFrischL_suffix hF0 hsuf1') hE hEZ
      have h2 : r2 = rest' := (List.cons.inj hr2).2
      rw [h2] at hYZ
      have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
      obtain ⟨hr3, hsuf3, hBc⟩ := ih (m + 1) (by omega) k rest' fn _ q rest ys restZ hU hS
        (bindFrischL_suffix hF0 hsuf2') hq hYZ
      refine ⟨hr3, (hsuf3.trans hsuf2').trans (List.suffix_cons _ _), fun σ ρ s hW hL => ?_⟩
      exact blockZiel_cons
        (stmtZiel_ite S hU hS hcv hce (fun σ ρ s hW hL => hBt σ ρ s hW hL)
          (fun σ ρ s hW hL => hBe σ ρ s hW hL) σ ρ s hW hL)
        (fun σ₁ ρ₁ s₁ hW₁ hL₁ => hBc σ₁ ρ₁ s₁ hW₁ hL₁)
    all_goals exact absurd hbs (by simp [seqZ, schrittB, stmtBody])

end Gabbro.Bruecke
