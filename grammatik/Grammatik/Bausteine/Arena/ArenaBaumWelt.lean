/-
  File:      Grammatik/ArenaBaumWelt.lean
  Subject:   `InvDyn` FOR A BINARY TREE OVER LIVE ARENA SLOTS (the shape of the capability derivation tree, O4-O6),
             preserved by `alloc` (both branches) and `free` (PLAN-DYNAMISCH.md section 8a, phase 2).

  The tree lives in two link fields `lft`, `rgt` of the arena's table (type `int 0 count`, `count` = no child) and a
  root global. `BaumOk` is `ArenaBaum.BaumOkF` over the world's links with `Lebt` as the live predicate:

    * every link is in range,
    * tree shape: the slots of the tree are pairwise distinct (subtrees disjoint, no slot its own ancestor) and the
      tree is finite (the inductive `BaumF` exists),
    * every slot of the tree is LIVE (below the used counter, not on the free list).

  The allocator moves keep it and hand out an unlinked live slot (`baum_frisch`, `baum_nimm`); `free` of a live slot
  that is no longer in the tree keeps it and kills the slot (`baum_frei`). The link stores are statements about the
  worlds they leave: `baum_einfuegen_links/rechts` (a live unlinked slot becomes the child of a member whose child
  place is empty), `baum_blatt_aus_links/rechts` (a leaf is cut off a member) and `baum_frei_nach_blatt` (the leaf is
  then released). The `sibling-consistency demand` of O6 is a further predicate over the same functions; it is the
  next piece (PLAN-DYNAMISCH 8a).
-/
import Grammatik.Bausteine.Arena.ArenaListe
import Grammatik.Bausteine.Arena.ArenaBaum

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-- **`InvDyn` for a binary tree:** shape, range, finiteness and liveness of every slot. -/
def BaumOk (A : FreiForm D) (Lf Rf : LinkFeld A) (G : LinkKopf A) (σ : World D) : Prop :=
  BaumOkF (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (A.Lebt σ)

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (A : FreiForm D) (Lf Rf : LinkFeld A) (G : LinkKopf A)

/-- The tree survives a run that only touched the allocator's places, as long as its own slots stay live. -/
theorem BaumOk.fremd {σ σ' : World D} (h : BaumOk A Lf Rf G σ) (hf : A.Fremd σ σ')
    (hl : ∀ j, InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j → A.Lebt σ' j) :
    BaumOk A Lf Rf G σ' := by
  unfold BaumOk at *
  rw [Lf.wert_fremd' hf, Rf.wert_fremd' hf, G.st_fremd hf]
  exact h.rahmen' hl (fun _ _ => ⟨rfl, rfl⟩)

/-- **`alloc` from the used counter keeps the tree and hands out an unlinked live slot.** -/
theorem baum_frisch (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ)
    (hkn : k.n = A.stand σ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.arenaRumpf (l := l) (Λ' := Λ) A.toArenaForm v hwT hLT hwG hLG .nil) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧
      A.FreiOk σ' ∧ BaumOk A Lf Rf G σ' ∧ A.Lebt σ' k.n ∧
      ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') k.n := by
  obtain ⟨σ', he, hf, hok', hmono, hnew⟩ := frisch_lebt O passes R (l := l) A v hwT hLT hwG hLG σ k ρ hkn hok
  refine ⟨σ', he, hok', hb.fremd A Lf Rf G hf (fun j hj => hmono j (hb.lebt_in hj)), hnew, ?_⟩
  rw [Lf.wert_fremd' hf, Rf.wert_fremd' hf, G.st_fremd hf]
  exact hb.nicht_in (fun j => A.stand σ ≤ j) (fun j hj => by have := hj.2.1; omega) (by omega)

/-- **`alloc` from the free list keeps the tree and hands out an unlinked live slot.** -/
theorem baum_nimm (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiNimm (Λ' := Λ) A v hwT hLT hwK hLK voll .nil) σ ρ = .ok σ' ρ ∧
      A.FreiOk σ' ∧ BaumOk A Lf Rf G σ' ∧ A.Lebt σ' (A.kopfSt σ) ∧
      ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') (A.kopfSt σ) := by
  obtain ⟨σ', he, hf, hok', hmono, hnew, hauf⟩ := nimm_lebt O passes R (l := l) A v hwT hLT hwK hLK voll σ ρ hne hok
  refine ⟨σ', he, hok', hb.fremd A Lf Rf G hf (fun j hj => hmono j (hb.lebt_in hj)), hnew, ?_⟩
  rw [Lf.wert_fremd' hf, Rf.wert_fremd' hf, G.st_fremd hf]
  exact hb.nicht_in (fun j => A.AufListe σ j) (fun j hj => hj.2.2) hauf

/-- **`free` of a live slot that is no longer in the tree keeps the tree and the free list, and kills the slot.** -/
theorem baum_frei
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ)
    (hlebt : A.Lebt σ k.n) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hnot : ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) k.n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiRumpf (l := l) (Λ' := Λ) A hwT hLT hwK hLK (.nil)) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧
      A.FreiOk σ' ∧ BaumOk A Lf Rf G σ' ∧ ¬ A.Lebt σ' k.n := by
  obtain ⟨σ', he, hf, hok', hmono, hdead⟩ := frei_lebt O passes R (l := l) A hwT hLT hwK hLK σ k ρ hlebt hok
  exact ⟨σ', he, hok', hb.fremd A Lf Rf G hf (fun j hj => hmono j (hb.lebt_in hj) (fun e => hnot (e ▸ hj))), hdead⟩

/-! ## The link stores (statements about the worlds they leave) -/

/-- **Leaf in at the left:** a live slot `i` that is not in the tree becomes the left child of a member `p` that has none.
    The free list and the counter are as before (the stores are not the allocator's). -/
theorem baum_einfuegen_links {σ σ' : World D} (hb : BaumOk A Lf Rf G σ) (p i : Int)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) p) (hpl : Lf.wert σ p = D.count A.tab)
    (hi : A.Lebt σ i) (hnot : ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) i)
    (hk : A.kopfSt σ' = A.kopfSt σ) (hn : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ)
    (hg : G.st σ' = G.st σ) (hlp : Lf.wert σ' p = i) (hli : Lf.wert σ' i = D.count A.tab)
    (hri : Rf.wert σ' i = D.count A.tab)
    (hol : ∀ j, j ≠ p → j ≠ i → Lf.wert σ' j = Lf.wert σ j) (hor : ∀ j, j ≠ i → Rf.wert σ' j = Rf.wert σ j) :
    BaumOk A Lf Rf G σ' ∧ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') i := by
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  unfold BaumOk at *
  rw [hg]
  exact einfuegen_ok hb hp hpl hi.1 (by have := hi.2.1; have := A.stand_le σ; omega) (hmono i hi) hmono hnot
    hlp hli hri hol hor

/-- **Leaf in at the right.** -/
theorem baum_einfuegen_rechts {σ σ' : World D} (hb : BaumOk A Lf Rf G σ) (p i : Int)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) p) (hpr : Rf.wert σ p = D.count A.tab)
    (hi : A.Lebt σ i) (hnot : ¬ InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) i)
    (hk : A.kopfSt σ' = A.kopfSt σ) (hn : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ)
    (hg : G.st σ' = G.st σ) (hrp : Rf.wert σ' p = i) (hri : Rf.wert σ' i = D.count A.tab)
    (hli : Lf.wert σ' i = D.count A.tab)
    (hor : ∀ j, j ≠ p → j ≠ i → Rf.wert σ' j = Rf.wert σ j) (hol : ∀ j, j ≠ i → Lf.wert σ' j = Lf.wert σ j) :
    BaumOk A Lf Rf G σ' ∧ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') i := by
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  unfold BaumOk at *
  rw [hg]
  exact einfuegen_rechts_ok hb hp hpr hi.1 (by have := hi.2.1; have := A.stand_le σ; omega) (hmono i hi) hmono
    hnot hrp hri hli hor hol

/-- **Leaf out at the left:** the leaf `i` that hangs at the left place of a member `p` is cut off. It is live, no longer
    in the tree, and may now be released. -/
theorem baum_blatt_aus_links {σ σ' : World D} (hb : BaumOk A Lf Rf G σ) (p i : Int)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) p) (hpi : Lf.wert σ p = i)
    (hi : i < D.count A.tab) (h0 : 0 ≤ i) (hll : Lf.wert σ i = D.count A.tab) (hrl : Rf.wert σ i = D.count A.tab)
    (hk : A.kopfSt σ' = A.kopfSt σ) (hn : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ)
    (hg : G.st σ' = G.st σ) (hlp : Lf.wert σ' p = D.count A.tab)
    (hol : ∀ j, j ≠ p → Lf.wert σ' j = Lf.wert σ j) (hor : ∀ j, Rf.wert σ' j = Rf.wert σ j) :
    BaumOk A Lf Rf G σ' ∧ ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') i ∧ A.Lebt σ' i := by
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  have hr : Rf.wert σ' = Rf.wert σ := funext hor
  have hlive : A.Lebt σ i := by
    have hin : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) i := by
      have := hp.links (by rw [hpi]; exact hi); rwa [hpi] at this
    exact hb.lebt_in hin
  unfold BaumOk at *
  rw [hg, hr]
  obtain ⟨h1, h2⟩ := blatt_aus_ok (l' := Lf.wert σ') hb hp hpi h0 hi hll hrl hmono hlp hol
  exact ⟨h1, h2, hmono i hlive⟩

/-- **Leaf out at the right.** -/
theorem baum_blatt_aus_rechts {σ σ' : World D} (hb : BaumOk A Lf Rf G σ) (p i : Int)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) p) (hpi : Rf.wert σ p = i)
    (hi : i < D.count A.tab) (h0 : 0 ≤ i) (hll : Lf.wert σ i = D.count A.tab) (hrl : Rf.wert σ i = D.count A.tab)
    (hk : A.kopfSt σ' = A.kopfSt σ) (hn : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ)
    (hg : G.st σ' = G.st σ) (hrp : Rf.wert σ' p = D.count A.tab)
    (hor : ∀ j, j ≠ p → Rf.wert σ' j = Rf.wert σ j) (hol : ∀ j, Lf.wert σ' j = Lf.wert σ j) :
    BaumOk A Lf Rf G σ' ∧ ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') i ∧ A.Lebt σ' i := by
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  have hl : Lf.wert σ' = Lf.wert σ := funext hol
  have hlive : A.Lebt σ i := by
    have hin : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) i := by have := hp.rechts (by rw [hpi]; exact hi); rwa [hpi] at this
    exact hb.lebt_in hin
  unfold BaumOk at *
  rw [hg, hl]
  obtain ⟨h1, h2⟩ := blatt_aus_rechts_ok (r' := Rf.wert σ') hb hp hpi h0 hi hll hrl hmono hrp hor
  exact ⟨h1, h2, hmono i hlive⟩

/-- **The leaf discipline:** after a leaf was cut off (left or right, `hcut`), release exactly that slot. The free list,
    the tree and the death of the slot all hold afterwards. -/
theorem baum_frei_nach_blatt
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (σ σ₁ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) (hok : A.FreiOk σ)
    (hk : A.kopfSt σ₁ = A.kopfSt σ) (hn : ∀ j, A.naechst σ₁ j = A.naechst σ j) (hs : A.stand σ₁ = A.stand σ)
    (hcut : BaumOk A Lf Rf G σ₁ ∧
      ¬ InBaum (D.count A.tab) (Lf.wert σ₁) (Rf.wert σ₁) (G.st σ₁) k.n ∧ A.Lebt σ₁ k.n) :
    ∃ σ₂ : World D,
      execBlock (V := V) O passes R
          (Block.freiRumpf (l := l) (Λ' := Λ) A hwT hLT hwK hLK (.nil)) σ₁ (.cons k ρ)
        = .ok σ₂ (.cons k ρ) ∧
      A.FreiOk σ₂ ∧ BaumOk A Lf Rf G σ₂ ∧ ¬ A.Lebt σ₂ k.n :=
  baum_frei O passes R A Lf Rf G hwT hLT hwK hLK σ₁ k ρ hcut.2.2 (A.freiOk_gleich hk hn hs hok) hcut.1 hcut.2.1

end Bedeutung

end Gabbro.Grammatik
