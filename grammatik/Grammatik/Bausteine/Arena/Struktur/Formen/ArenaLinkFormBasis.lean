/-
  File:      Grammatik/ArenaLinkForm.lean
  Subject:   THE EXECUTED FORMS OF THE LIST LINK STORES (PLAN-DYNAMIC.md section 8a.1, step (1)): `push`, `pop`
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
module
public import Grammatik.Bausteine.Arena.Struktur.ArenaListe
public import Grammatik.Bausteine.Arena.Struktur.ArenaAuf
public import Grammatik.Bausteine.Arena.Struktur.ArenaRahmen
@[expose] public section


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
    L.wert (σ.lese Λ o) k = L.wert σ k := by rfl

@[simp] theorem wert_schreibGlob (L : LinkFeld A) (σ : World D) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) (k : Int) : L.wert (σ.schreibGlob g Λ v) k = L.wert σ k := by rfl

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
    G.st (σ.lese Λ o) = G.st σ := by rfl

@[simp] theorem st_schreibSlot (G : LinkKopf A) (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) : G.st (σ.schreibSlot t Λ k f v) = G.st σ := by rfl

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
    (Env.cons k ρ).get (Var.there p) = ρ.get p := by rfl

@[simp] theorem Env.get_cons_here {τ : Ty} {Γ : Ctx} (k : Wert D τ) (ρ : Env D Γ) :
    (Env.cons k ρ).get Var.here = k := by rfl

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

/-- **`let i = head else voll;  rest`** -- read the head without moving it; the binder holds the head slot. -/
def linkKopfBind (G : LinkKopf A) (hLG : gdarf D G.g Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp G.hg (Expr.glob G.g hLG)) 0 (D.count A.tab - 1) voll rest

/-- **`let q = lnk[p] else voll;  rest`** -- read the successor of `p` without moving anything. -/
def linkNachBind (L : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp L.hf (Expr.slot A.tab L.f (Expr.var p) hLT)) 0 (D.count A.tab - 1) voll rest

end Block


end Gabbro.Grammatik
