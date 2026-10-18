/-
  File:      Grammatik/ArenaLinkForm.lean
  Subject:   THE EXECUTED FORMS OF THE LIST LINK STORES (PLAN-DYNAMISCH.md section 8a.1, step (1)): `push`, `pop`
             and `unlink` as `Block`s over the existing statements `assignSlot`/`assignGlob`/`narrow` (no new
             constructor), with the proof that each executed form leaves exactly the store facts that
             `liste_push`, `liste_pop` and `liste_unlink` (`ArenaListe.lean`) take as hypotheses -- so those
             theorems now hold on executed Blocks, for ANY continuation `rest`.

  The forms (the index `x` is any bound index variable of the context, not only the newest one):

    `Block.linkPush L G x rest`    =  `lnk[x] = head;  head = x;  rest`
    `Block.linkPop  L G voll rest` =  `let i = head (narrow, else voll);  head = lnk[i];  rest`   (`i` is the new binder)
    `Block.linkUnlink L G p voll rest` = `let i = lnk[p] (narrow, else voll);  lnk[p] = lnk[i];  rest`

  Each `*_ausfuehren` theorem is a statement about the world the stores leave, valid under every `rest`:
  `execBlock (form … rest) σ ρ = execBlock rest σ' ρ'` (`schrumpf` drops the binder of a `narrow`), together with the
  frame facts (link field, head, and the allocator's three views: head of the free list, free links, counter).
-/
import Grammatik.Bausteine.Arena.ArenaListe

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-! ## 1. Raw frames of the two stores, read through the link views -/

theorem World.slots_schreibSlot_selbst (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) : (σ.schreibSlot t Λ k f v).slots t k f = v := by
  simp only [World.schreibSlot, World.merke, World.storeSlot, dif_pos, if_pos]

theorem World.slots_schreibSlot_anderer (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) (k' : Int) (f' : D.Feld t) (h : k' ≠ k) :
    (σ.schreibSlot t Λ k f v).slots t k' f' = σ.slots t k' f' := by
  simp only [World.schreibSlot, World.merke, World.storeSlot, dif_pos, if_neg h]

theorem World.globs_schreibGlob_selbst (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g)) :
    (σ.schreibGlob g Λ v).globs g = v := by
  simp only [World.schreibGlob, World.merke, World.storeGlob, dif_pos]

namespace LinkFeld
variable {A : FreiForm D}

@[simp] theorem wert_lese (L : LinkFeld A) (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) (k : Int) :
    L.wert (σ.lese Λ o) k = L.wert σ k := rfl

@[simp] theorem wert_schreibGlob (L : LinkFeld A) (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) (k : Int) : L.wert (σ.schreibGlob g Λ v) k = L.wert σ k := rfl

/-- A store into the link field at slot `i` puts exactly the written value there ... -/
theorem wert_schreibSlot_selbst (L : LinkFeld A) (σ : World D) (Λ : List (Res D)) (i : Int)
    (v : Wert D (D.typ A.tab L.f)) :
    L.wert (σ.schreibSlot A.tab Λ i L.f v) i = (Wert.umTyp L.hf v).n := by
  simp only [wert, World.slots_schreibSlot_selbst]

/-- ... and leaves the link of every other slot. -/
theorem wert_schreibSlot_anderer (L : LinkFeld A) (σ : World D) (Λ : List (Res D)) (i : Int)
    (v : Wert D (D.typ A.tab L.f)) (j : Int) (h : j ≠ i) :
    L.wert (σ.schreibSlot A.tab Λ i L.f v) j = L.wert σ j := by
  simp only [wert, World.slots_schreibSlot_anderer _ _ _ _ _ _ _ _ h]

/-- A store into another field leaves this link field where it was. -/
theorem wert_schreibSlot_feld (L L' : LinkFeld A) (h : L'.f ≠ L.f) (σ : World D) (Λ : List (Res D)) (i : Int)
    (v : Wert D (D.typ A.tab L.f)) (j : Int) :
    L'.wert (σ.schreibSlot A.tab Λ i L.f v) j = L'.wert σ j := by
  simp only [wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ h]

end LinkFeld

namespace LinkKopf
variable {A : FreiForm D}

@[simp] theorem st_lese (G : LinkKopf A) (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) :
    G.st (σ.lese Λ o) = G.st σ := rfl

@[simp] theorem st_schreibSlot (G : LinkKopf A) (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) : G.st (σ.schreibSlot t Λ k f v) = G.st σ := rfl

theorem st_schreibGlob_selbst (G : LinkKopf A) (σ : World D) (Λ : List (Res D)) (v : Wert D (D.gtyp G.g)) :
    G.st (σ.schreibGlob G.g Λ v) = (Wert.umTyp G.hg v).n := by
  simp only [st, World.schreibGlob, World.merke, World.storeGlob, dif_pos]

end LinkKopf

namespace FreiForm
variable (A : FreiForm D)

/-- A store into a global that is neither the head of the free list nor ... leaves the head of the free list. -/
theorem kopfSt_schreibGlob_ne (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g))
    (h : A.kopf ≠ g) : A.kopfSt (σ.schreibGlob g Λ v) = A.kopfSt σ := by
  simp only [kopfSt, World.schreibGlob, World.merke, World.storeGlob, dif_neg h]

theorem stand_schreibGlob_ne (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g))
    (h : A.zaehl ≠ g) : A.stand (σ.schreibGlob g Λ v) = A.stand σ := by
  simp only [ArenaForm.stand, World.schreibGlob, World.merke, World.storeGlob, dif_neg h]

theorem komSt_schreibGlob_ne (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g))
    (h : A.komm ≠ g) : A.komSt (σ.schreibGlob g Λ v) = A.komSt σ := by
  simp only [DynForm.komSt, World.schreibGlob, World.merke, World.storeGlob, dif_neg h]

/-- A store into a field other than the free-list link leaves every free-list link. -/
theorem naechst_schreibSlot_ne (σ : World D) (Λ : List (Res D)) (i : Int) (f : D.Feld A.tab)
    (v : Wert D (D.typ A.tab f)) (h : f ≠ A.nxt) (j : Int) :
    A.naechst (σ.schreibSlot A.tab Λ i f v) j = A.naechst σ j := by
  simp only [naechst, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ (Ne.symm h)]

end FreiForm

@[simp] theorem Env.get_cons_there {τ σ : Ty} {Γ : Ctx} (k : Wert D σ) (ρ : Env D Γ) (p : Var Γ τ) :
    (Env.cons k ρ).get (Var.there p) = ρ.get p := rfl

@[simp] theorem Env.get_cons_here {τ : Ty} {Γ : Ctx} (k : Wert D τ) (ρ : Env D Γ) :
    (Env.cons k ρ).get Var.here = k := rfl

/-! ## 2. The three forms -/

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {A : FreiForm D}

/-- The head word, at the link field's declared type. -/
def linkKopfAlsFeld (L : LinkFeld A) (G : LinkKopf A) (hLG : gdarf D G.g Λ) :
    Expr D Γ Λ (D.typ A.tab L.f) :=
  Expr.umTyp (G.hg.trans L.hf.symm) (Expr.glob G.g hLG)

/-- The index variable `x`, at the head word's declared type. -/
def linkIdxAlsKopf (G : LinkKopf A) (x : Var Γ (Ty.index (D.count A.tab))) : Expr D Γ Λ (D.gtyp G.g) :=
  Expr.umTyp G.hg.symm
    (Expr.widen (lo := 0) (hi := D.count A.tab - 1) (lo' := 0) (hi' := D.count A.tab)
      (by omega) (by omega) (Expr.var x))

/-- **`lnk[x] = head;  head = x;  rest`** -- link the slot `x` in at the front of the list. -/
def linkPush (L : LinkFeld A) (G : LinkKopf A) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ)
    (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  .cons (.assignSlot A.tab L.f (Expr.var x) (linkKopfAlsFeld L G hLG) hwT hLT)
    (.cons (.assignGlob G.g (linkIdxAlsKopf G x) hwG hLG) rest)

/-- The link of the new binder (the old head), at the head word's declared type: `head = lnk[i]`. -/
def linkWeiter (L : LinkFeld A) (G : LinkKopf A) (hLT : darf D A.tab Λ) :
    Expr D (Ty.index (D.count A.tab) :: Γ) Λ (D.gtyp G.g) :=
  Expr.umTyp (L.hf.trans G.hg.symm) (Expr.slot A.tab L.f (Expr.var .here) hLT)

/-- **`let i = head else voll;  head = lnk[i];  rest`** -- take the head off. `narrow` of the head into the index
    range: it fits when the list is non-empty; `voll` is the empty-list branch. -/
def linkPop (L : LinkFeld A) (G : LinkKopf A)
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp G.hg (Expr.glob G.g hLG)) 0 (D.count A.tab - 1) voll
    (.cons (.assignGlob G.g (linkWeiter L G hLT) hwG hLG) rest)

/-- **`let i = lnk[p] else voll;  lnk[p] = lnk[i];  rest`** -- unlink the slot after the predecessor `p`. -/
def linkUnlink (L : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp L.hf (Expr.slot A.tab L.f (Expr.var p) hLT)) 0 (D.count A.tab - 1) voll
    (.cons (.assignSlot A.tab L.f (Expr.var (.there p)) (Expr.slot A.tab L.f (Expr.var .here) hLT) hwT hLT) rest)

end Block

/-! ## 3. What the executed forms leave -/

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (L : LinkFeld A) (G : LinkKopf A)

/-- **`push` leaves:** the head is `x`, the link of `x` is the old head, every other link stays, and the allocator's
    head, free links and counter stay. Valid for every continuation `rest`. -/
theorem linkPush_ausfuehren
    (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.linkPush L G x hwT hLT hwG hLG rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      G.st σ' = (ρ.get x).n ∧ L.wert σ' (ρ.get x).n = G.st σ ∧
      (∀ j, j ≠ (ρ.get x).n → L.wert σ' j = L.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  refine ⟨_, rfl, ?_⟩
  simp only [eval, Block.linkKopfAlsFeld, Block.linkIdxAlsKopf, eval_umTyp, Expr.orte, orte_umTyp,
    List.nil_append, LinkKopf.st_schreibGlob_selbst, LinkKopf.st_schreibSlot, LinkKopf.st_lese,
    LinkFeld.wert_schreibGlob, LinkFeld.wert_lese,
    A.kopfSt_schreibGlob_ne _ _ _ _ (Ne.symm G.h2), A.stand_schreibGlob_ne _ _ _ _ (Ne.symm G.h1),
    FreiForm.naechst_schreibGlob, A.naechst_schreibSlot_ne _ _ _ _ _ L.h2, FreiForm.naechst_lese,
    FreiForm.kopfSt_schreibSlot, FreiForm.kopfSt_lese, ArenaForm.stand_lese, ArenaForm.stand_schreibSlot]
  refine ⟨umTyp_rund_n G.hg _, ?_, ?_, trivial, fun _ => trivial, trivial⟩
  · rw [L.wert_schreibSlot_selbst]
    exact umTyp_trans_n _ _ _
  · intro j hj
    rw [L.wert_schreibSlot_anderer _ _ _ _ _ hj]
    rfl

/-- **`pop` leaves:** the binder holds the old head `i`, the head is the link of `i`, no link moves, and the allocator's
    views stay. The list must be non-empty. Valid for every continuation `rest`. -/
theorem linkPop_ausfuehren
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hne : G.st σ < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.linkPop L G hwG hLG hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = G.st σ ∧ G.st σ' = L.wert σ (G.st σ) ∧ (∀ j, L.wert σ' j = L.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ G.st σ ∧ G.st σ ≤ D.count A.tab - 1 := ⟨(Wert.umTyp G.hg (σ.globs G.g)).lo_le, by omega⟩
  simp only [Block.linkPop, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_pos (by exact hk)]
  refine ⟨?s, ?k, ?e, ?n, ?r⟩
  case e => rfl
  case n => rfl
  case r =>
    simp only [eval, Block.linkWeiter, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append, List.cons_append,
      List.append_nil, LinkKopf.st_schreibGlob_selbst, LinkKopf.st_lese, LinkFeld.wert_schreibGlob,
      LinkFeld.wert_lese, A.kopfSt_schreibGlob_ne _ _ _ _ (Ne.symm G.h2), A.stand_schreibGlob_ne _ _ _ _ (Ne.symm G.h1),
      FreiForm.naechst_schreibGlob, FreiForm.naechst_lese, FreiForm.kopfSt_lese, ArenaForm.stand_lese, Env.get]
    refine ⟨?_, fun _ => trivial, trivial, fun _ => trivial, trivial⟩
    exact umTyp_trans_n _ _ _

/-- **`unlink` leaves:** the binder holds `i = lnk[p]`, the link of `p` is now the link of `i`, no other link and not the
    head moves, and the allocator's views stay. `i` must be a slot (`hi`). Valid for every continuation `rest`. -/
theorem linkUnlink_ausfuehren
    (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hi : L.wert σ (ρ.get p).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.linkUnlink L p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = L.wert σ (ρ.get p).n ∧ G.st σ' = G.st σ ∧
      L.wert σ' (ρ.get p).n = L.wert σ (L.wert σ (ρ.get p).n) ∧
      (∀ j, j ≠ (ρ.get p).n → L.wert σ' j = L.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ L.wert σ (ρ.get p).n ∧ L.wert σ (ρ.get p).n ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp L.hf (σ.slots A.tab (ρ.get p).n L.f)).lo_le, by omega⟩
  simp only [Block.linkUnlink, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_pos (by exact hk)]
  refine ⟨?s, ?k, ?e, ?n, ?r⟩
  case e => rfl
  case n => rfl
  case r =>
    simp only [eval, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append, List.cons_append,
      List.append_nil, LinkKopf.st_schreibSlot, LinkKopf.st_lese, LinkFeld.wert_lese,
      A.kopfSt_schreibSlot, FreiForm.naechst_lese, FreiForm.kopfSt_lese, ArenaForm.stand_lese,
      ArenaForm.stand_schreibSlot, A.naechst_schreibSlot_ne _ _ _ _ _ L.h2, Env.get_cons_there, Env.get_cons_here]
    refine ⟨trivial, ?_, fun j hj => ?_, trivial, fun _ => trivial, trivial⟩
    · exact L.wert_schreibSlot_selbst _ _ _ _
    · exact L.wert_schreibSlot_anderer _ _ _ _ _ hj

/-! ## 4. The list invariant on the executed forms -/

/-- **Executed `push` keeps the list.** `x` names a live slot that is not linked (the checker's `N586` and the
    discipline of a freshly allocated or popped slot); afterwards the head is `x`. Valid for every continuation. -/
theorem liste_push_zug
    (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hl : ListOk A L G σ) (hok : A.FreiOk σ)
    (hi : A.Lebt σ (ρ.get x).n) (hnot : ¬ Auf (D.count A.tab) (L.wert σ) (G.st σ) (ρ.get x).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.linkPush L G x hwT hLT hwG hLG rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      ListOk A L G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧ G.st σ' = (ρ.get x).n ∧
      L.wert σ' (ρ.get x).n = G.st σ := by
  obtain ⟨σ', he, hg, hli, ho, hk, hn, hs⟩ :=
    linkPush_ausfuehren O passes R L G x hwT hLT hwG hLG rest σ ρ
  exact ⟨σ', he, liste_push A L G hl _ hi hnot hk hn hs hg hli ho, A.freiOk_gleich hk hn hs hok,
    A.lebt_gleich hk hn hs, hg, hli⟩

/-- **Executed `pop` keeps the list.** The binder holds the old head, which is live and no longer linked, so it may be
    released (`liste_pop_frei`). Valid for every continuation. -/
theorem liste_pop_zug
    (hwG : V.gschreibt G.g = true) (hLG : gdarf D G.g Λ) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hl : ListOk A L G σ) (hok : A.FreiOk σ) (hne : G.st σ < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.linkPop L G hwG hLG hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = G.st σ ∧ ListOk A L G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') k.n ∧ A.Lebt σ' k.n ∧ G.st σ' = L.wert σ (G.st σ) := by
  obtain ⟨σ', k, he, hkn, hg, ho, hk, hn, hs⟩ :=
    linkPop_ausfuehren O passes R L G hwG hLG hLT voll rest σ ρ hne
  obtain ⟨h1, h2, h3⟩ := liste_pop A L G hl hne hk hn hs hg ho
  exact ⟨σ', k, he, hkn, h1, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, hkn ▸ h2, hkn ▸ h3, hg⟩

/-- **Executed `unlink` keeps the list.** `p` is on the list and has a successor `i`; the binder holds `i`, which is
    live and no longer linked, so it may be released. Valid for every continuation. -/
theorem liste_unlink_zug
    (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hl : ListOk A L G σ) (hok : A.FreiOk σ)
    (hp : Auf (D.count A.tab) (L.wert σ) (G.st σ) (ρ.get p).n) (hi : L.wert σ (ρ.get p).n < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.linkUnlink L p hwT hLT voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = L.wert σ (ρ.get p).n ∧ ListOk A L G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      ¬ Auf (D.count A.tab) (L.wert σ') (G.st σ') k.n ∧ A.Lebt σ' k.n ∧
      L.wert σ' (ρ.get p).n = L.wert σ (L.wert σ (ρ.get p).n) := by
  obtain ⟨σ', k, he, hkn, hg, hnp, ho, hk, hn, hs⟩ :=
    linkUnlink_ausfuehren O passes R L G p hwT hLT voll rest σ ρ hi
  obtain ⟨h1, h2, h3⟩ := liste_unlink A L G hl _ hp hi hk hn hs hg hnp ho
  exact ⟨σ', k, he, hkn, h1, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, hkn ▸ h2, hkn ▸ h3, hnp⟩

end Bedeutung

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.linkPush_ausfuehren
#print axioms Gabbro.Grammatik.linkPop_ausfuehren
#print axioms Gabbro.Grammatik.linkUnlink_ausfuehren
#print axioms Gabbro.Grammatik.liste_push_zug
#print axioms Gabbro.Grammatik.liste_pop_zug
#print axioms Gabbro.Grammatik.liste_unlink_zug
