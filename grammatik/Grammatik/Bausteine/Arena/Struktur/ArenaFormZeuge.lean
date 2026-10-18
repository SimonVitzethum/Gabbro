/-
  File:      Grammatik/ArenaFormZeuge.lean
  Subject:   WITNESSES for the EXECUTED link forms and `grow` (PLAN-DYNAMISCH.md section 8a.1, steps 1-2), on the
             concrete arena of `ArenaDynZeuge.lean` (four slots, slot `1` on the free list, list `2 -> 0`, tree
             `2 (left 0)`): the hypotheses of every `*_zug` theorem hold on a real world, the forms are RUN, and the
             conclusion speaks about a non-empty structure.

    * `push_zeuge`    -- the live, unlinked slot `3` is linked in at the head: head `3`, link `3 -> 2`.
    * `pop_zeuge'`    -- the head `2` is unlinked and the binder holds it: head `0`.
    * `blattEin_zeuge`, `blattAus_zeuge` -- the tree: slot `3` hung at the right of the root `2`; the leaf `0` cut off
      at the left of `2`.
    * `grow_zeuge`    -- a commit by `1` on a world whose committed word is below the ceiling keeps list and free list.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaDynZeuge
import Grammatik.Bausteine.Arena.Struktur.ArenaBaumForm
import Grammatik.Bausteine.Arena.Struktur.ArenaWachs

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

namespace InvDynZeuge

/-- An index value of the four-slot table. -/
def idx (n : Int) (h0 : 0 ≤ n) (h1 : n ≤ 3) : Wert FD (Ty.index (FD.count FA.tab)) := ⟨n, h0, h1⟩

/-- The environment that binds the index `3`. -/
def rho3 : Env FD [Ty.index (FD.count FA.tab)] := .cons (idx 3 (by decide) (by decide)) .nil

theorem rho3_n : (rho3.get .here).n = 3 := rfl

/-- Slot `3` is live and not on the list `2 -> 0`. -/
theorem nicht_auf_3 : ¬ Auf 4 (LL.wert w0) (LG.st w0) 3 := by
  rintro ⟨L, hL, hm⟩
  rw [lg_w0] at hL
  have := KetteF.eindeutig hL listeKette_w0
  subst this; simp at hm

theorem lebt_3 : FA.Lebt w0 3 := (lebt_w0 3).mpr (by decide)

/-! ### `push` -/

theorem push_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ σ' : World FD,
      execBlock (V := FV) O passes R
          (Block.linkPush (l := false) (Γ := [Ty.index (FD.count FA.tab)]) (Λ' := []) LL LG .here rfl fdarf rfl
            (fgdarf _) .nil) w0 rho3
        = .ok σ' rho3 ∧
      ListOk FA LL LG σ' ∧ LG.st σ' = 3 ∧ LL.wert σ' 3 = 2 := by
  obtain ⟨σ1, he1, hl1, -, -, hg, hli, -, -⟩ := liste_push_zug O passes R LL LG (V := FV) (l := false)
    (Γ := [Ty.index (FD.count FA.tab)]) (Λ := []) (Λ' := []) .here rfl fdarf rfl (fgdarf _) .nil w0
    rho3 listOk_w0 freiOk_w0 (by rw [rho3_n]; exact lebt_3)
    (by rw [lg_w0, rho3_n]; exact nicht_auf_3)
  exact ⟨σ1, he1, hl1, by rw [rho3_n] at hg; exact hg, by rw [lg_w0, rho3_n] at hli; exact hli⟩

/-! ### `pop` -/

theorem pop_zeuge' (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) (voll : Endblock FD FV false [] []) :
    ∃ σ' : World FD,
      execBlock (V := FV) O passes R
          (Block.linkPop (l := false) (Γ := []) (Λ' := []) LL LG rfl (fgdarf _) fdarf voll .nil) w0 .nil = .ok σ' .nil ∧
      ListOk FA LL LG σ' ∧ LG.st σ' = 0 ∧ FA.Lebt σ' 2 := by
  obtain ⟨σ1, k, he1, hkn, hl1, -, -, hnot, hlebt, hg, -⟩ := liste_pop_zug O passes R LL LG (V := FV) (l := false) (Γ := [])
    (Λ := []) (Λ' := []) rfl (fgdarf _) fdarf voll .nil w0 .nil listOk_w0 freiOk_w0 (by rw [lg_w0]; decide)
  refine ⟨σ1, he1, hl1, ?_, ?_⟩
  · rw [hg, lg_w0, ll_w0]; rfl
  · have : k.n = 2 := by rw [hkn, lg_w0]
    rw [this] at hlebt; exact hlebt

/-! ### The tree: leaf in at the right, leaf out at the left -/

theorem hp_2 : InBaum 4 (LL.wert w0) (RR.wert w0) (LG.st w0) 2 := by
  rw [lg_w0]; exact ⟨[2, 0], baumB_w0, by simp⟩

theorem nicht_in_3 : ¬ InBaum 4 (LL.wert w0) (RR.wert w0) (LG.st w0) 3 := by
  rintro ⟨S, hS, hm⟩
  rw [lg_w0] at hS
  have := BaumF.eindeutig hS baumB_w0
  subst this; simp at hm

/-- Two index variables: the root `2` (newest) and the slot `3`. -/
def rho23 : Env FD [Ty.index (FD.count FA.tab), Ty.index (FD.count FA.tab)] :=
  .cons (idx 2 (by decide) (by decide)) (.cons (idx 3 (by decide) (by decide)) .nil)

/-- **Leaf in, executed:** the live slot `3` is hung at the empty right place of the root `2`; the result is a tree of
    two slots and `3` is in it. -/
theorem blattEin_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ σ' : World FD,
      execBlock (V := FV) O passes R
          (Block.blattEin (l := false) (Λ' := []) RR LL .here (.there .here) rfl fdarf .nil) w0 rho23 = .ok σ' rho23 ∧
      BaumOk FA LL RR LG σ' ∧ InBaum 4 (LL.wert σ') (RR.wert σ') (LG.st σ') 3 := by
  obtain ⟨σ1, he1, h1, h2, -, -⟩ := baum_einfuegen_rechts_zug O passes R LG LL RR (V := FV) (l := false)
    (Λ := []) (Λ' := []) (by decide) .here (.there .here) rfl fdarf .nil w0 rho23 freiOk_w0 baumOk_w0
    hp_2 (by rw [rr_w0]) (lebt_3) nicht_in_3
  exact ⟨σ1, he1, h1, h2⟩

/-- The environment that binds the root `2`. -/
def rho2 : Env FD [Ty.index (FD.count FA.tab)] := .cons (idx 2 (by decide) (by decide)) .nil

/-- **Leaf out, executed:** the leaf `0` at the left of the root `2` is cut off; the binder holds it, it is live and no
    longer in the tree. -/
theorem blattAus_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) (voll : Endblock FD FV false [Ty.index (FD.count FA.tab)] []) :
    ∃ σ' : World FD,
      execBlock (V := FV) O passes R
          (Block.blattAus (l := false) (Γ := [Ty.index (FD.count FA.tab)]) (Λ' := []) LL .here rfl fdarf
            (voll) .nil) w0 rho2 = .ok σ' rho2 ∧
      BaumOk FA LL RR LG σ' ∧ ¬ InBaum 4 (LL.wert σ') (RR.wert σ') (LG.st σ') 0 ∧ FA.Lebt σ' 0 := by
  obtain ⟨σ1, k, he1, hkn, h1, -, -, h2, h3⟩ := baum_blatt_aus_links_zug O passes R LG LL RR (V := FV) (l := false)
    (Λ := []) (Λ' := []) (by decide) .here rfl fdarf voll .nil w0 rho2 freiOk_w0 baumOk_w0
    hp_2 (by show LL.wert w0 2 < 4; rw [ll_w0]; decide)
    (by show LL.wert w0 (LL.wert w0 2) = 4; rw [ll_w0, ll_w0]; decide)
    (by show RR.wert w0 (LL.wert w0 2) = 4; rw [rr_w0])
  have hk0 : k.n = 0 := by rw [hkn]; show LL.wert w0 2 = 0; rw [ll_w0]; rfl
  rw [hk0] at h2 h3
  exact ⟨σ1, he1, h1, h2, h3⟩

/-! ### `unlink` -/

/-- **`unlink` after the predecessor `2`, executed:** the list `2 -> 0` becomes `2`, the binder holds `0`, which is
    live and no longer linked, so it may be released. -/
theorem unlink_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f)
    (voll : Endblock FD FV false [Ty.index (FD.count FA.tab)] []) :
    ∃ σ' : World FD,
      execBlock (V := FV) O passes R
          (Block.linkUnlink (l := false) (Γ := [Ty.index (FD.count FA.tab)]) (Λ' := []) LL .here rfl fdarf
            voll .nil) w0 rho2 = .ok σ' rho2 ∧
      ListOk FA LL LG σ' ∧ ¬ Auf 4 (LL.wert σ') (LG.st σ') 0 ∧ FA.Lebt σ' 0 ∧ LL.wert σ' 2 = 4 := by
  obtain ⟨σ1, k, he1, hkn, h1, -, -, h2, h3, hnp, -⟩ := liste_unlink_zug O passes R LL LG (V := FV) (l := false)
    (Λ := []) (Λ' := []) .here rfl fdarf voll .nil w0 rho2 listOk_w0 freiOk_w0
    (by show Auf 4 (LL.wert w0) (LG.st w0) 2; rw [lg_w0]; exact ⟨[2, 0], listeKette_w0, by simp⟩)
    (by show LL.wert w0 2 < 4; rw [ll_w0]; decide)
  have hk0 : k.n = 0 := by rw [hkn]; show LL.wert w0 2 = 0; rw [ll_w0]; rfl
  rw [hk0] at h2 h3
  refine ⟨σ1, he1, h1, h2, h3, ?_⟩
  have : LL.wert σ1 2 = LL.wert w0 (LL.wert w0 2) := hnp
  rw [this, ll_w0, ll_w0]; decide

/-! ### `grow` -/

/-- `w0` with the committed word at `2` (below the ceiling `4`). -/
def w0k : World FD := { w0 with globs := fun g => if g = 1 then zc 2 else w0.globs g }

theorem komSt_w0k : FA.komSt w0k = 2 := by decide

theorem freiOk_w0k : FA.FreiOk w0k := by
  obtain ⟨L, hk, hnd, hlt⟩ := freiOk_w0
  exact FA.freiOk_gleich (σ := w0) (σ' := w0k) rfl (fun _ => rfl) rfl ⟨L, hk, hnd, hlt⟩

theorem listOk_w0k : ListOk FA LL LG w0k := by
  have hl : LL.wert w0k = LL.wert w0 := rfl
  have hg : LG.st w0k = LG.st w0 := rfl
  have hlebt : ∀ j, FA.Lebt w0k j ↔ FA.Lebt w0 j := FA.lebt_gleich (σ := w0) (σ' := w0k) rfl (fun _ => rfl) rfl
  unfold ListOk
  rw [hl, hg]
  exact listOk_w0.rahmen (fun j hj => (hlebt j).mpr (listOk_w0.lebt_auf hj)) (fun _ _ => rfl)

/-- **`grow` by `1`, executed, on a world whose committed word is `2`:** the commit succeeds (`2 + 1 ≤ 4`), the committed
    word becomes `3`, and the free list, every liveness and the list `2 -> 0` are untouched. -/
theorem grow_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) (voll : Endblock FD FV false [] []) :
    ∃ σ' : World FD,
      execBlock (V := FV) O passes R
          (Block.dynGrowB (l := false) (Γ := []) (Λ' := []) FA.toDynForm 1 rfl (fgdarf _) voll .nil) w0k .nil = .ok σ' .nil ∧
      FA.FreiOk σ' ∧ ListOk FA LL LG σ' ∧ FA.komSt σ' = 3 := by
  obtain ⟨σ1, he1, hok, -, hl, hkomm⟩ := grow_liste O passes R FA LL LG (V := FV) (l := false) (Γ := [])
    (Λ := []) (Λ' := []) 1 rfl (fgdarf _) voll .nil w0k .nil
    (by rw [komSt_w0k]; decide) (by rw [komSt_w0k]; decide) freiOk_w0k listOk_w0k
  exact ⟨σ1, he1, hok, hl, by rw [hkomm, komSt_w0k]; rfl⟩

end InvDynZeuge

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.InvDynZeuge.push_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.pop_zeuge'
#print axioms Gabbro.Grammatik.InvDynZeuge.blattEin_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.blattAus_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.unlink_zeuge
#print axioms Gabbro.Grammatik.InvDynZeuge.grow_zeuge
