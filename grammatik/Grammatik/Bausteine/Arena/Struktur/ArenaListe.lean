/-
  File:      Grammatik/ArenaListe.lean
  Subject:   `InvDyn` FOR A SINGLY LINKED LIST OVER LIVE ARENA SLOTS, preserved by `alloc` (both branches) and
             `free` (PLAN-DYNAMISCH.md section 8a, phase 2).

  The list lives in a link field `lnk` of the arena's table (a field of type `int 0 count`; `count` is the nil
  marker) and a head global (same type). Both are separate from everything the allocator owns, so the allocator
  never moves a link (`ArenaFremd.lean`). The invariant `ListOk` is `ArenaKette.ListOkF` over the world's links
  with `Lebt` as the live predicate:

    * every link is in range (`KetteF` visits only slots below `count`),
    * the chain is FINITE and has no cycle (`KetteF` exists, its slots are pairwise distinct),
    * every slot on it is LIVE: below the used counter and NOT on the free list.

  What is proved, on the executed forms of `ArenaFrei.lean` where those exist:
    * `liste_frisch`  -- `alloc` from the counter: free list and list stay well formed; the new slot is live and not
      yet linked.
    * `liste_nimm`    -- `alloc` from the free list: likewise for the slot taken off the list.
    * `liste_frei`    -- `free` of a live slot that is no longer linked (the checker's `N586` plus the unlink the
      program performed): free list and list stay well formed and the slot is dead.
  and, as statements about what the link stores leave (the link stores are plain `assignSlot`/`assignGlob`):
    * `liste_push`, `liste_pop`, `liste_unlink` -- link in at the head, unlink the head, unlink after a predecessor;
    * `liste_pop_frei` -- the stack discipline: pop the head, then release exactly that slot.
  The counter-theorem for a double link is `ArenaKette.push_doppelt_bricht`.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaFremd
import Grammatik.Bausteine.Arena.Struktur.ArenaKette

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-! ## 1. Link fields and link heads that the allocator does not own -/

/-- A link field of the arena's table: an index field, not the payload and not the free-list link. -/
structure LinkFeld (A : FreiForm D) where
  f : D.Feld A.tab
  hf : D.typ A.tab f = Ty.int 0 (D.count A.tab)
  h1 : f ≠ A.feld
  h2 : f ≠ A.nxt

/-- A link head: an index global, not the counter, not the head of the free list and not the committed word
    (`grow` writes `komm`, so a head that is `komm` would be moved by a commit). -/
structure LinkKopf (A : FreiForm D) where
  g : D.Glob
  hg : D.gtyp g = Ty.int 0 (D.count A.tab)
  h1 : g ≠ A.zaehl
  h2 : g ≠ A.kopf
  h3 : g ≠ A.komm

namespace LinkFeld
variable {A : FreiForm D}

/-- The link of slot `k`, read out of a world. -/
def wert (L : LinkFeld A) (σ : World D) (k : Int) : Int := (Wert.umTyp L.hf (σ.slots A.tab k L.f)).n

theorem wert_fremd (L : LinkFeld A) {σ σ' : World D} (h : A.Fremd σ σ') (k : Int) :
    L.wert σ' k = L.wert σ k := by
  simp only [wert, h.2 k L.f L.h1 L.h2]

theorem wert_fremd' (L : LinkFeld A) {σ σ' : World D} (h : A.Fremd σ σ') : L.wert σ' = L.wert σ :=
  funext (L.wert_fremd h)

end LinkFeld

namespace LinkKopf
variable {A : FreiForm D}

/-- The head, read out of a world. -/
def st (G : LinkKopf A) (σ : World D) : Int := (Wert.umTyp G.hg (σ.globs G.g)).n

theorem st_fremd (G : LinkKopf A) {σ σ' : World D} (h : A.Fremd σ σ') : G.st σ' = G.st σ := by
  simp only [st, h.1 G.g G.h1 G.h2 G.h3]

end LinkKopf

/-- **`InvDyn` for a list:** the chain from the head is finite, acyclic, in range, and consists of live slots. -/
def ListOk (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A) (σ : World D) : Prop :=
  ListOkF (D.count A.tab) (L.wert σ) (G.st σ) (A.Lebt σ)

/-! ## 2. The allocator moves keep the list -/

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (A : FreiForm D) (L : LinkFeld A) (G : LinkKopf A)

/-- **`alloc` from the used counter keeps the list and hands out an unlinked live slot.** `hkn`: the slot bound is
    the counter's value (what `arenaAlloc`'s guard binds). -/
theorem liste_frisch (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ)
    (hkn : k.n = A.stand σ) (hok : A.FreiOk σ) (hl : ListOk A L G σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.arenaRumpf (l := l) (Λ' := Λ) A.toArenaForm v hwT hLT hwG hLG .nil) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧
      A.FreiOk σ' ∧ ListOk A L G σ' ∧ A.Lebt σ' k.n ∧ ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') k.n := by
  obtain ⟨σ', he, h1, h2, h3⟩ := frischRumpf_fakten O passes R (l := l) A v hwT hLT hwG hLG σ k ρ
  obtain ⟨σ'', he2, hf⟩ := frischRumpf_fremd O passes R (l := l) A v hwT hLT hwG hLG σ k ρ
  rw [he] at he2; cases he2
  have hs : A.stand σ' = A.stand σ + 1 := by rw [h3, hkn]
  obtain ⟨hok', hmono, hnew⟩ := A.lebt_bump hok h1 h2 hs
  have hLf := L.wert_fremd' hf
  have hGf := G.st_fremd hf
  have hl' : ListOk A L G σ' := by
    unfold ListOk at *
    rw [hLf, hGf]
    exact hl.rahmen (fun j hj => hmono j (hl.lebt_auf hj)) (fun _ _ => rfl)
  refine ⟨σ', he, hok', hl', by rw [hkn]; exact hnew, ?_⟩
  rw [hLf, hGf]
  refine hl.nicht_auf (fun j => A.stand σ ≤ j) (fun j hj => by have := hj.2.1; omega) (by omega)

/-- **`alloc` from the free list keeps the list and hands out an unlinked live slot.** -/
theorem liste_nimm (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ) (hl : ListOk A L G σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiNimm (Λ' := Λ) A v hwT hLT hwK hLK voll .nil) σ ρ = .ok σ' ρ ∧
      A.FreiOk σ' ∧ ListOk A L G σ' ∧ A.Lebt σ' (A.kopfSt σ) ∧
      ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') (A.kopfSt σ) := by
  obtain ⟨σ', he, h1, h2, h3⟩ := freiNimm_fakten O passes R (l := l) A v hwT hLT hwK hLK voll σ ρ hne
  obtain ⟨σ'', he2, hf⟩ := freiNimm_fremd O passes R (l := l) A v hwT hLT hwK hLK voll σ ρ hne
  rw [he] at he2; cases he2
  obtain ⟨hok', hmono, hnew⟩ := A.lebt_abheb hne hok h1 h2 h3
  have hLf := L.wert_fremd' hf
  have hGf := G.st_fremd hf
  have hl' : ListOk A L G σ' := by
    unfold ListOk at *
    rw [hLf, hGf]
    exact hl.rahmen (fun j hj => hmono j (hl.lebt_auf hj)) (fun _ _ => rfl)
  refine ⟨σ', he, hok', hl', hnew, ?_⟩
  rw [hLf, hGf]
  have hkk : A.AufListe σ (A.kopfSt σ) := by
    obtain ⟨L0, hk0, _, _⟩ := hok
    generalize hg : A.kopfSt σ = kk at hk0 hne ⊢
    cases hk0 with
    | nil => exact absurd hne (Int.lt_irrefl _)
    | cons k h0 hk1 L1 h1 => refine ⟨kk :: L1, ?_, List.mem_cons_self⟩; rw [hg]; exact FreiForm.Kette.cons kk h0 hk1 L1 h1
  exact hl.nicht_auf (fun j => A.AufListe σ j) (fun j hj => hj.2.2) hkk

/-- **`free` of a live slot that is no longer linked keeps the list and the free list, and kills the slot.** -/
theorem liste_frei
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ)
    (hlebt : A.Lebt σ k.n) (hok : A.FreiOk σ) (hl : ListOk A L G σ)
    (hnot : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) k.n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R
          (Block.freiRumpf (l := l) (Λ' := Λ) A hwT hLT hwK hLK (.nil)) σ (.cons k ρ)
        = .ok σ' (.cons k ρ) ∧
      A.FreiOk σ' ∧ ListOk A L G σ' ∧ ¬ A.Lebt σ' k.n := by
  obtain ⟨σ', he, h1, h2, h3, h4⟩ := freiRumpf_fakten O passes R (l := l) A hwT hLT hwK hLK σ k ρ
  obtain ⟨σ'', he2, hf⟩ := freiRumpf_fremd O passes R (l := l) A hwT hLT hwK hLK σ k ρ
  rw [he] at he2; cases he2
  obtain ⟨hok', hmono, hdead⟩ := A.lebt_frei k.n hlebt hok h1 h2 h3 h4
  have hLf := L.wert_fremd' hf
  have hGf := G.st_fremd hf
  refine ⟨σ', he, hok', ?_, hdead⟩
  unfold ListOk at *
  rw [hLf, hGf]
  refine hl.rahmen (fun j hj => hmono j ?_ ?_) (fun _ _ => rfl)
  · exact hl.lebt_auf hj
  · rintro rfl; exact hnot hj

/-! ## 3. The link stores keep the list (statements about the worlds the stores leave) -/

/-- **Link in** (`lnk[i] = head; head = i`) at the front of the list: `i` live and not yet linked. The free-list state
    and the counter are as before (the stores are not the allocator's). -/
theorem liste_push {σ σ' : World D} (hl : ListOk A L G σ) (i : Int) (hi : A.Lebt σ i)
    (hnot : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) i)
    (hk : A.kopfSt σ' = A.kopfSt σ) (hn : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ)
    (hg : G.st σ' = i) (hli : L.wert σ' i = G.st σ) (ho : ∀ j, j ≠ i → L.wert σ' j = L.wert σ j) :
    ListOk A L G σ' := by
  unfold ListOk at *
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  exact push_ok hl hi.1 (by have := hi.2.1; have := A.stand_le σ; omega) (hmono i hi) hmono hnot hg hli ho

/-- **Unlink the head** (`head = lnk[head]`): the list stays well formed; the slot taken off is live, no longer linked,
    and may now be released. -/
theorem liste_pop {σ σ' : World D} (hl : ListOk A L G σ) (hne : G.st σ < D.count A.tab)
    (hk : A.kopfSt σ' = A.kopfSt σ) (hn : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ)
    (hg : G.st σ' = L.wert σ (G.st σ)) (ho : ∀ j, L.wert σ' j = L.wert σ j) :
    ListOk A L G σ' ∧ ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') (G.st σ) ∧ A.Lebt σ' (G.st σ) := by
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  have hfun : L.wert σ' = L.wert σ := funext ho
  unfold ListOk at *
  obtain ⟨h1, h2⟩ := pop_ok (nx' := L.wert σ') hl hne hmono hg ho
  refine ⟨h1, h2, hmono _ (hl.lebt_auf (auf_kopf hne (by obtain ⟨L0, hk0, _⟩ := hl; exact ⟨L0, hk0⟩)))⟩

/-- **Unlink after a predecessor** (`lnk[p] = lnk[i]`, `i = lnk[p]`): the list stays well formed; `i` is live, no longer
    linked, and may now be released. -/
theorem liste_unlink {σ σ' : World D} (hl : ListOk A L G σ) (p : Int)
    (hp : Auf (D.count A.tab) (L.wert σ) (G.st σ) p) (hi : L.wert σ p < D.count A.tab)
    (hk : A.kopfSt σ' = A.kopfSt σ) (hn : ∀ j, A.naechst σ' j = A.naechst σ j) (hs : A.stand σ' = A.stand σ)
    (hg : G.st σ' = G.st σ) (hnp : L.wert σ' p = L.wert σ (L.wert σ p))
    (ho : ∀ j, j ≠ p → L.wert σ' j = L.wert σ j) :
    ListOk A L G σ' ∧ ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') (L.wert σ p) ∧ A.Lebt σ' (L.wert σ p) := by
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  unfold ListOk at *
  obtain ⟨h1, h2⟩ := unlink_ok (nx' := L.wert σ') hl hp rfl hi hmono hnp ho
  rw [hg]
  exact ⟨h1, h2, hmono _ (hl.lebt_auf (auf_nach hp hi))⟩

/-- **The stack discipline:** pop the head, then release exactly the slot that came off. The free list, the list
    and the death of the slot all hold afterwards. -/
theorem liste_pop_frei
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (σ σ₁ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ)
    (hl : ListOk A L G σ) (hok : A.FreiOk σ) (hne : G.st σ < D.count A.tab) (hkn : k.n = G.st σ)
    (hk : A.kopfSt σ₁ = A.kopfSt σ) (hn : ∀ j, A.naechst σ₁ j = A.naechst σ j) (hs : A.stand σ₁ = A.stand σ)
    (hg : G.st σ₁ = L.wert σ (G.st σ)) (ho : ∀ j, L.wert σ₁ j = L.wert σ j) :
    ∃ σ₂ : World D,
      execBlock (V := V) O passes R
          (Block.freiRumpf (l := l) (Λ' := Λ) A hwT hLT hwK hLK (.nil)) σ₁ (.cons k ρ)
        = .ok σ₂ (.cons k ρ) ∧
      A.FreiOk σ₂ ∧ ListOk A L G σ₂ ∧ ¬ A.Lebt σ₂ k.n := by
  obtain ⟨hl1, hnot, hlebt⟩ := liste_pop A L G hl hne hk hn hs hg ho
  rw [← hkn] at hnot hlebt
  exact liste_frei O passes R A L G hwT hLT hwK hLK σ₁ k ρ hlebt (A.freiOk_gleich hk hn hs hok) hl1 hnot

end Bedeutung

end Gabbro.Grammatik
