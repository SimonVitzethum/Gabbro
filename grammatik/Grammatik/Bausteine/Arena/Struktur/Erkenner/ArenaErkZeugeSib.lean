/-
  File:      Grammatik/ArenaErkZeugeSib.lean
  Subject:   WITNESSES AND PLANTED DEFECTS FOR THE PARENT STORE AND `revoke` ON EXECUTED BLOCKS (PLAN-DYNAMIC.md section
             8a.1, third pass), on the five-field arena of `ArenaErkZeugeKombi.lean` (field `2`, the list link there, serves
             as the PARENT field `par`; field `3` is the first child, field `4` the next sibling, word `4` the root).

  Two worlds: `wk2` (the tree `0 (right 3)`, the live slot `2` in no structure, free list `[1]`) and `wk3` (the tree
  `0 (left 3 (left 2))`, parents `3 -> 0`, `2 -> 3`, free list `[1]`). Both are sibling-consistent.
    * `erst_zeuge`     -- `sib_haengenErst_zug` run: slot `2` becomes the FIRST child of the root `0`, its parent is `0`;
    * `bruder_zeuge`   -- `sib_haengenBruder_zug` run: slot `2` becomes the NEXT SIBLING of `3`, its parent is the parent
                          of `3` (the nil marker: `3` is a child of the root only through the right link);
    * `revoke_zeuge`   -- `baum_unterbaum_aus_links_zug` run: the subtree `3 (left 2)` is cut off the root `0`; the tree is
                          `0`, and the slots `3` and `2` are live orphans (releasable);
    * `bruderOhneVater_defekt` -- planted defect: the new sibling gets the parent `p` instead of `p`'s parent; the model
                          rejects the world (`sib_ohne_vater_bricht`);
    * `freiOhneSchnitt_defekt` -- planted defect: the child of the root is released while it is still linked in the tree.
-/
import Grammatik.Bausteine.Arena.Struktur.Erkenner.ArenaErkZeugeKombi
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaSibZug

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace ErkKombi

def parN : Int → Int := fun _ => 4

/-- The tree `0 (right 3)`, the list is empty, slot `2` is live and in no structure. -/
def wk2 : World FD2 := wd2 4 1 4 0 nilF parN nilF rf0

theorem stand_wk2 : FA2.stand wk2 = 4 := rfl
theorem wz_wk2 : Wz2.st wk2 = 0 := rfl
theorem par_wk2 (j : Int) : LL2.wert wk2 j = 4 := by show max 0 (min 4 (parN j)) = 4; unfold parN; decide
theorem lf_wk2 (j : Int) : Lf2.wert wk2 j = 4 := by show max 0 (min 4 (nilF j)) = 4; unfold nilF; decide
theorem rf_wk2 (j : Int) : Rf2.wert wk2 j = rf0 j := by
  show max 0 (min 4 (rf0 j)) = rf0 j
  unfold rf0; split <;> omega

theorem freiOk_wk2 : FA2.FreiOk wk2 :=
  FreiForm.freiOk_gleich FA2 (σ := wk) (σ' := wk2) rfl (fun _ => rfl) rfl freiOk_wk

theorem lebt_wk2 (i : Int) : FA2.Lebt wk2 i ↔ (0 ≤ i ∧ i < 4 ∧ i ≠ 1) := by
  rw [FreiForm.lebt_gleich FA2 (σ := wk) (σ' := wk2) rfl (fun _ => rfl) rfl i]
  exact lebt_wk i

theorem baumF_wk2 : BaumF 4 (Lf2.wert wk2) (Rf2.wert wk2) 0 [0, 3] := by
  have h3 : BaumF 4 (Lf2.wert wk2) (Rf2.wert wk2) 3 [3] := by
    have := BaumF.node (c := 4) (l := Lf2.wert wk2) (r := Rf2.wert wk2) 3 (by decide) (by decide) [] []
      (by rw [lf_wk2]; exact BaumF.nil) (by rw [rf_wk2]; exact BaumF.nil)
    simpa using this
  have := BaumF.node (c := 4) (l := Lf2.wert wk2) (r := Rf2.wert wk2) 0 (by decide) (by decide) [] [3]
    (by rw [lf_wk2]; exact BaumF.nil) (by rw [rf_wk2]; exact h3)
  simpa using this

theorem baumOk_wk2 : BaumOk FA2 Lf2 Rf2 Wz2 wk2 := by
  unfold BaumOk
  rw [wz_wk2]
  refine ⟨[0, 3], baumF_wk2, by decide, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact (lebt_wk2 _).mpr (by decide)
  · exact (lebt_wk2 _).mpr (by decide)

/-- Every member of the tree `0 (right 3)` is `0` or `3`. -/
theorem inBaum_wk2 (j : Int) (h : InBaum 4 (Lf2.wert wk2) (Rf2.wert wk2) (Wz2.st wk2) j) : j = 0 ∨ j = 3 := by
  obtain ⟨S, hS, hm⟩ := h
  rw [wz_wk2] at hS
  have := BaumF.eindeutig hS baumF_wk2
  subst this
  simpa using hm

/-- **The sibling demand holds on `wk2`:** the next sibling `3` of the root `0` has the parent of `0` (all parents are the nil
    marker). -/
theorem sibOk_wk2 : SibOk Lf2 Rf2 LL2 Wz2 wk2 := by
  intro j hj
  rcases inBaum_wk2 j hj with rfl | rfl
  · refine ⟨fun h => absurd h (by rw [lf_wk2]; decide), fun _ => ?_⟩
    rw [rf_wk2, par_wk2, par_wk2]
  · refine ⟨fun h => absurd h (by rw [lf_wk2]; decide), fun h => absurd h (by rw [rf_wk2]; decide)⟩

/-! ### A concrete context -/

def rho02 : Env FD2 G2k :=
  .cons (⟨0, by decide, by decide⟩ : Wert FD2 (Ty.index (FD2.count FA2.tab)))
    (.cons (⟨2, by decide, by decide⟩ : Wert FD2 (Ty.index (FD2.count FA2.tab))) .nil)

theorem rho02_p : (rho02.get (.here : Var G2k _)).n = 0 := rfl
theorem rho02_i : (rho02.get (.there .here : Var G2k _)).n = 2 := rfl

theorem nicht_in_2 : ¬ InBaum 4 (Lf2.wert wk2) (Rf2.wert wk2) (Wz2.st wk2) 2 := fun h => by
  rcases inBaum_wk2 2 h with e | e <;> cases e

/-- **`sib_haengenErst_zug` on a real world, run:** slot `2` becomes the first child of the root `0`, its parent is `0`; the
    tree and the sibling demand hold afterwards. -/
theorem erst_zeuge :
    ∃ σ' : World FD2, execBlock (V := FV2) (l := false) oF2 0 rF2
        (Block.blattEinErst (V := FV2) (l := false) Lf2 Rf2 LL2 (.here : Var G2k _) (.there .here : Var G2k _) rfl
          fdarf2 (Block.nil (Γ := G2k) (Λ := []))) wk2 rho02 = .ok σ' rho02 ∧
      BaumOk FA2 Lf2 Rf2 Wz2 σ' ∧ SibOk Lf2 Rf2 LL2 Wz2 σ' ∧
      InBaum 4 (Lf2.wert σ') (Rf2.wert σ') (Wz2.st σ') 2 ∧ LL2.wert σ' 2 = 0 := by
  obtain ⟨σ', he, hb, hs, -, -, hin, hpp⟩ := sib_haengenErst_zug oF2 0 rF2 Wz2 Lf2 Rf2 LL2 (V := FV2) (l := false)
    (Γ := G2k) (Λ := []) (Λ' := []) (by decide) (by decide)
    (by decide) (.here : Var G2k _) (.there .here : Var G2k _) rfl fdarf2 (Block.nil (Γ := G2k) (Λ := [])) wk2 rho02
    freiOk_wk2 baumOk_wk2 sibOk_wk2
    (by rw [rho02_p]; exact ⟨[0, 3], by rw [wz_wk2]; exact baumF_wk2, by simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self, or_false]⟩)
    (by rw [rho02_p, lf_wk2])
    (by rw [rho02_i]; exact (lebt_wk2 2).mpr (by decide))
    (by rw [rho02_i]; exact nicht_in_2)
  rw [rho02_i] at hin
  rw [rho02_i, rho02_p] at hpp
  exact ⟨σ', he, hb, hs, hin, hpp⟩

/-! ### The next sibling -/

def rho32 : Env FD2 G2k :=
  .cons (⟨3, by decide, by decide⟩ : Wert FD2 (Ty.index (FD2.count FA2.tab)))
    (.cons (⟨2, by decide, by decide⟩ : Wert FD2 (Ty.index (FD2.count FA2.tab))) .nil)

theorem rho32_p : (rho32.get (.here : Var G2k _)).n = 3 := rfl
theorem rho32_i : (rho32.get (.there .here : Var G2k _)).n = 2 := rfl

/-- **`sib_haengenBruder_zug` on a real world, run:** slot `2` becomes the next sibling of `3`, with the parent of `3` (the nil
    marker); the tree and the sibling demand hold afterwards. -/
theorem bruder_zeuge :
    ∃ σ' : World FD2, execBlock (V := FV2) (l := false) oF2 0 rF2
        (Block.blattEinBruder (V := FV2) (l := false) Lf2 Rf2 LL2 (.here : Var G2k _) (.there .here : Var G2k _) rfl
          fdarf2 (Block.nil (Γ := G2k) (Λ := []))) wk2 rho32 = .ok σ' rho32 ∧
      BaumOk FA2 Lf2 Rf2 Wz2 σ' ∧ SibOk Lf2 Rf2 LL2 Wz2 σ' ∧
      InBaum 4 (Lf2.wert σ') (Rf2.wert σ') (Wz2.st σ') 2 ∧ LL2.wert σ' 2 = 4 := by
  obtain ⟨σ', he, hb, hs, -, -, hin, hpp⟩ := sib_haengenBruder_zug oF2 0 rF2 Wz2 Lf2 Rf2 LL2 (V := FV2) (l := false)
    (Γ := G2k) (Λ := []) (Λ' := []) (by decide) (by decide)
    (by decide) (.here : Var G2k _) (.there .here : Var G2k _) rfl fdarf2 (Block.nil (Γ := G2k) (Λ := [])) wk2 rho32
    freiOk_wk2 baumOk_wk2 sibOk_wk2
    (by rw [rho32_p]; exact ⟨[0, 3], by rw [wz_wk2]; exact baumF_wk2, by simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_false, or_true]⟩)
    (by rw [rho32_p, rf_wk2]; unfold rf0; decide)
    (by rw [rho32_i]; exact (lebt_wk2 2).mpr (by decide))
    (by rw [rho32_i]; exact nicht_in_2)
  rw [rho32_i] at hin
  rw [rho32_i, rho32_p, par_wk2] at hpp
  exact ⟨σ', he, hb, hs, hin, hpp⟩

/-! ### `revoke`: the world with a subtree -/

def lf3 : Int → Int := fun k => if k = 0 then 3 else if k = 3 then 2 else 4
def parW : Int → Int := fun k => if k = 3 then 0 else if k = 2 then 3 else 4

/-- The tree `0 (left 3 (left 2))` with the parents `3 -> 0`, `2 -> 3`; slot `1` on the free list. -/
def wk3 : World FD2 := wd2 4 1 4 0 nilF parW lf3 nilF

theorem wz_wk3 : Wz2.st wk3 = 0 := rfl
theorem lf_wk3 (j : Int) : Lf2.wert wk3 j = lf3 j := by
  show max 0 (min 4 (lf3 j)) = lf3 j
  unfold lf3; split <;> (try split) <;> omega
theorem rf_wk3 (j : Int) : Rf2.wert wk3 j = 4 := by show max 0 (min 4 (nilF j)) = 4; unfold nilF; decide
theorem par_wk3 (j : Int) : LL2.wert wk3 j = parW j := by
  show max 0 (min 4 (parW j)) = parW j
  unfold parW; split <;> (try split) <;> omega

theorem freiOk_wk3 : FA2.FreiOk wk3 :=
  FreiForm.freiOk_gleich FA2 (σ := wk) (σ' := wk3) rfl (fun _ => rfl) rfl freiOk_wk

theorem lebt_wk3 (i : Int) : FA2.Lebt wk3 i ↔ (0 ≤ i ∧ i < 4 ∧ i ≠ 1) := by
  rw [FreiForm.lebt_gleich FA2 (σ := wk) (σ' := wk3) rfl (fun _ => rfl) rfl i]
  exact lebt_wk i

theorem baumF2_wk3 : BaumF 4 (Lf2.wert wk3) (Rf2.wert wk3) 2 [2] := by
  have := BaumF.node (c := 4) (l := Lf2.wert wk3) (r := Rf2.wert wk3) 2 (by decide) (by decide) [] []
    (by rw [lf_wk3, show lf3 2 = 4 by unfold lf3; decide]; exact BaumF.nil) (by rw [rf_wk3]; exact BaumF.nil)
  simpa using this

theorem baumF3_wk3 : BaumF 4 (Lf2.wert wk3) (Rf2.wert wk3) 3 [3, 2] := by
  have := BaumF.node (c := 4) (l := Lf2.wert wk3) (r := Rf2.wert wk3) 3 (by decide) (by decide) [2] []
    (by rw [lf_wk3]; unfold lf3; simpa using baumF2_wk3) (by rw [rf_wk3]; exact BaumF.nil)
  simpa using this

theorem baumF_wk3 : BaumF 4 (Lf2.wert wk3) (Rf2.wert wk3) 0 [0, 3, 2] := by
  have := BaumF.node (c := 4) (l := Lf2.wert wk3) (r := Rf2.wert wk3) 0 (by decide) (by decide) [3, 2] []
    (by rw [lf_wk3]; unfold lf3; simpa using baumF3_wk3) (by rw [rf_wk3]; exact BaumF.nil)
  simpa using this

theorem baumOk_wk3 : BaumOk FA2 Lf2 Rf2 Wz2 wk3 := by
  unfold BaumOk
  rw [wz_wk3]
  refine ⟨[0, 3, 2], baumF_wk3, by decide, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> exact (lebt_wk3 _).mpr (by decide)

theorem inBaum_wk3 (j : Int) (h : InBaum 4 (Lf2.wert wk3) (Rf2.wert wk3) (Wz2.st wk3) j) : j = 0 ∨ j = 3 ∨ j = 2 := by
  obtain ⟨S, hS, hm⟩ := h
  rw [wz_wk3] at hS
  have := BaumF.eindeutig hS baumF_wk3
  subst this
  simpa using hm

/-- **The sibling demand holds on `wk3`:** the first child of `0` is `3` with parent `0`, the first child of `3` is `2` with
    parent `3`, there are no siblings. -/
theorem sibOk_wk3 : SibOk Lf2 Rf2 LL2 Wz2 wk3 := by
  intro j hj
  rcases inBaum_wk3 j hj with rfl | rfl | rfl
  · refine ⟨fun _ => ?_, fun h => absurd h (by rw [rf_wk3]; decide)⟩
    rw [lf_wk3, par_wk3]; unfold lf3 parW; decide
  · refine ⟨fun _ => ?_, fun h => absurd h (by rw [rf_wk3]; decide)⟩
    rw [lf_wk3, par_wk3]; unfold lf3 parW; decide
  · refine ⟨fun h => absurd h (by rw [lf_wk3]; unfold lf3; decide), fun h => absurd h (by rw [rf_wk3]; decide)⟩

def rhoR0 : Env FD2 G1k := .cons (⟨0, by decide, by decide⟩ : Wert FD2 (Ty.index (FD2.count FA2.tab))) .nil

theorem rhoR0_p : (rhoR0.get (.here : Var G1k _)).n = 0 := rfl

/-- **`baum_unterbaum_aus_links_zug` on a real world, run (`revoke`):** the subtree `3 (left 2)` is cut off the root `0`. The tree
    that remains is the root, sibling-consistent; slots `3` and `2` are live orphans and in the tree no more. -/
theorem revoke_zeuge :
    ∃ (σ' : World FD2) (k : Wert FD2 (Ty.index (FD2.count FA2.tab))),
      execBlock (V := FV2) (l := false) oF2 0 rF2
        (Block.blattAus (V := FV2) (l := false) Lf2 (.here : Var G1k _) rfl fdarf2 vollK1
          (Block.nil (Γ := Ty.index (FD2.count FA2.tab) :: G1k) (Λ := []))) wk3 rhoR0 = .ok σ' rhoR0 ∧
      k.n = 3 ∧ BaumOk FA2 Lf2 Rf2 Wz2 σ' ∧ SibOk Lf2 Rf2 LL2 Wz2 σ' ∧
      ¬ InBaum 4 (Lf2.wert σ') (Rf2.wert σ') (Wz2.st σ') 2 ∧ FA2.Lebt σ' 2 ∧
      ¬ InBaum 4 (Lf2.wert σ') (Rf2.wert σ') (Wz2.st σ') 3 ∧ FA2.Lebt σ' 3 := by
  obtain ⟨σ', k, he, hkn, hb, hs, -, -, -, hout⟩ := baum_unterbaum_aus_links_zug oF2 0 rF2 Wz2 Lf2 Rf2 LL2
    (V := FV2) (l := false) (Γ := G1k) (Λ := []) (Λ' := []) (by decide) (by decide) (.here : Var G1k _) rfl fdarf2
    vollK1 (Block.nil (Γ := Ty.index (FD2.count FA2.tab) :: G1k) (Λ := [])) wk3 rhoR0 freiOk_wk3 baumOk_wk3 sibOk_wk3
    (by rw [rhoR0_p]; exact ⟨[0, 3, 2], by rw [wz_wk3]; exact baumF_wk3, by simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self, or_false]⟩)
    (by rw [rhoR0_p, lf_wk3]; unfold lf3; decide)
  have hk3 : k.n = 3 := by rw [hkn, rhoR0_p, lf_wk3]; rfl
  have hsub : ∀ j, j = 3 ∨ j = 2 → InBaum 4 (Lf2.wert wk3) (Rf2.wert wk3) k.n j := by
    intro j hj
    rw [hk3]
    refine ⟨[3, 2], baumF3_wk3, ?_⟩
    rcases hj with rfl | rfl <;> simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self, or_false, or_true]
  obtain ⟨h2, l2⟩ := hout 2 (hsub 2 (Or.inr rfl))
  obtain ⟨h3, l3⟩ := hout 3 (hsub 3 (Or.inl rfl))
  exact ⟨σ', k, he, hk3, hb, hs, h2, l2, h3, l3⟩

/-! ### Planted defect: a new sibling with the wrong parent -/

/-- Hang `i` at the right place of `p`, but store the parent `p` (the parent of a FIRST CHILD) instead of the parent of `p`. -/
def bruderOhneVater : Block FD2 FV2 false G2k [] [] :=
  Block.blattEin Rf2 Lf2 (.here : Var G2k _) (.there .here : Var G2k _) rfl fdarf2
    (Block.cons (Stmt.assignSlot FA2.tab LL2.f (Expr.var (.there .here : Var G2k _))
      (Block.linkIdxAlsFeld LL2 (.here : Var G2k _)) rfl fdarf2) Block.nil)

def bruderFalschOk : Bool :=
  match execBlock (V := FV2) oF2 0 rF2 bruderOhneVater wk2 rho32 with
  | .ok σ' _ =>
    decide (Rf2.wert σ' 3 = 2 ∧ LL2.wert σ' 2 = 3 ∧ LL2.wert σ' 3 = 4 ∧ Wz2.st σ' = 0 ∧ Rf2.wert σ' 0 = 3 ∧
      Lf2.wert σ' 0 = 4 ∧ Lf2.wert σ' 3 = 4 ∧ Lf2.wert σ' 2 = 4 ∧ Rf2.wert σ' 2 = 4)
  | _ => false

theorem bruderFalschOk_wahr : bruderFalschOk = true := by decide +kernel

/-- **Without the parent of `p` the sibling demand breaks:** the new sibling `2` of `3` has the parent `3` instead of the
    parent of `3`. The tree itself is fine; the model rejects the world (`sib_ohne_vater_bricht`). -/
theorem bruderOhneVater_defekt :
    ∃ (σ' : World FD2) (ρ' : Env FD2 G2k),
      execBlock (V := FV2) oF2 0 rF2 bruderOhneVater wk2 rho32 = .ok σ' ρ' ∧ ¬ SibOk Lf2 Rf2 LL2 Wz2 σ' := by
  have hd := bruderFalschOk_wahr
  unfold bruderFalschOk at hd
  revert hd
  generalize hx : execBlock (V := FV2) oF2 0 rF2 bruderOhneVater wk2 rho32 = o
  cases o with
  | ok σ' ρ =>
    intro hd
    simp only [decide_eq_true_eq] at hd
    obtain ⟨hr3, hp2, hp3, hw, hr0, hl0, hl3, hl2, hr2⟩ := hd
    refine ⟨σ', ρ, rfl, fun hs => ?_⟩
    have h2 : BaumF 4 (Lf2.wert σ') (Rf2.wert σ') 2 [2] := by
      have := BaumF.node (c := 4) (l := Lf2.wert σ') (r := Rf2.wert σ') 2 (by decide) (by decide) [] []
        (by rw [hl2]; exact BaumF.nil) (by rw [hr2]; exact BaumF.nil)
      simpa using this
    have h3 : BaumF 4 (Lf2.wert σ') (Rf2.wert σ') 3 [3, 2] := by
      have := BaumF.node (c := 4) (l := Lf2.wert σ') (r := Rf2.wert σ') 3 (by decide) (by decide) [] [2]
        (by rw [hl3]; exact BaumF.nil) (by rw [hr3]; exact h2)
      simpa using this
    have h0 : BaumF 4 (Lf2.wert σ') (Rf2.wert σ') 0 [0, 3, 2] := by
      have := BaumF.node (c := 4) (l := Lf2.wert σ') (r := Rf2.wert σ') 0 (by decide) (by decide) [] [3, 2]
        (by rw [hl0]; exact BaumF.nil) (by rw [hr0]; exact h3)
      simpa using this
    have hin : InBaum 4 (Lf2.wert σ') (Rf2.wert σ') (Wz2.st σ') 3 := by
      rw [hw]; exact ⟨[0, 3, 2], h0, by simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self, or_false, or_true]⟩
    exact sib_ohne_vater_bricht hin hr3 (by decide) (by rw [hp2, hp3]; decide) hs
  | zurueck _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | why _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | leave _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | next _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | logik _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | hardware _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])

/-! ### Planted defect: a child released while it is still linked -/

def rhoR3 : Env FD2 G1k := .cons (⟨3, by decide, by decide⟩ : Wert FD2 (Ty.index (FD2.count FA2.tab))) .nil

/-- Release slot `3` WITHOUT cutting it off the tree first. -/
def freiOhneSchnitt : Block FD2 FV2 false G1k [] [] :=
  Block.freiVar FA2 (.here : Var G1k _) rfl fdarf2 rfl (fgdarf2 _) .nil

def freiOhneSchnittOk : Bool :=
  match execBlock (V := FV2) oF2 0 rF2 freiOhneSchnitt wk3 rhoR3 with
  | .ok σ' _ =>
    decide (FA2.kopfSt σ' = 3 ∧ FA2.naechst σ' 3 = 1 ∧ FA2.naechst σ' 1 = 4 ∧ Wz2.st σ' = 0 ∧ Lf2.wert σ' 0 = 3)
  | _ => false

theorem freiOhneSchnittOk_wahr : freiOhneSchnittOk = true := by decide +kernel

/-- **Releasing a slot that is still in the tree breaks the tree:** slot `3` is the left child of the root and now the head of
    the free list, and a member of the tree must be live. (The checker's `N586` refuses the release of a slot that is not
    owned; the cut of `revoke` is what makes it owned.) -/
theorem freiOhneSchnitt_defekt :
    ∃ (σ' : World FD2) (ρ' : Env FD2 G1k),
      execBlock (V := FV2) oF2 0 rF2 freiOhneSchnitt wk3 rhoR3 = .ok σ' ρ' ∧ ¬ BaumOk FA2 Lf2 Rf2 Wz2 σ' := by
  have hd := freiOhneSchnittOk_wahr
  unfold freiOhneSchnittOk at hd
  revert hd
  generalize hx : execBlock (V := FV2) oF2 0 rF2 freiOhneSchnitt wk3 rhoR3 = o
  cases o with
  | ok σ' ρ =>
    intro hd
    simp only [decide_eq_true_eq] at hd
    obtain ⟨hk, hn3, hn1, hw, hl0⟩ := hd
    refine ⟨σ', ρ, rfl, fun hb => ?_⟩
    have hb' : BaumOkF 4 (Lf2.wert σ') (Rf2.wert σ') 0 (FA2.Lebt σ') := by
      have := hb; unfold BaumOk at this; rwa [hw] at this
    have hroot : InBaum 4 (Lf2.wert σ') (Rf2.wert σ') 0 0 := ArenaKette.InBaum.wurzel hb' (by decide)
    have hin : InBaum 4 (Lf2.wert σ') (Rf2.wert σ') 0 3 := by
      have := hroot.links (by rw [hl0]; decide)
      rwa [hl0] at this
    have hlebt := BaumOkF.lebt_in hb' hin
    have hauf : FA2.AufListe σ' 3 :=
      ⟨[3, 1], by
        rw [hk]
        exact FreiForm.Kette.cons 3 (by decide) (by decide) [1] (by
          rw [hn3]
          exact FreiForm.Kette.cons 1 (by decide) (by decide) [] (by rw [hn1]; exact FreiForm.Kette.nil)), by simp only [List.mem_cons, Int.reduceEq, List.not_mem_nil, or_self, or_false]⟩
    exact hlebt.2.2 hauf
  | zurueck _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | why _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | leave _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | next _ _ _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | logik _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])
  | hardware _ => intro hd; exact absurd hd (by simp only [Bool.false_eq_true, not_false_eq_true])

end ErkKombi

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.ErkKombi.sibOk_wk2
#print axioms Gabbro.Grammatik.ErkKombi.erst_zeuge
#print axioms Gabbro.Grammatik.ErkKombi.bruder_zeuge
#print axioms Gabbro.Grammatik.ErkKombi.sibOk_wk3
#print axioms Gabbro.Grammatik.ErkKombi.revoke_zeuge
#print axioms Gabbro.Grammatik.ErkKombi.bruderOhneVater_defekt
#print axioms Gabbro.Grammatik.ErkKombi.freiOhneSchnitt_defekt
