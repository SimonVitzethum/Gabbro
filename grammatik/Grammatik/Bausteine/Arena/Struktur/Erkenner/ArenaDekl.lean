/-
  File:      Grammatik/ArenaDekl.lean
  Subject:   WHAT THE RECOGNIZER GUARDS (PLAN-DYNAMISCH.md section 8a.1, third pass): the structures one arena carries and
             the invariant of all of them together.

  An arena may carry ONE singly linked list (`ListDekl`: a link field and a head global), ONE binary tree (`BaumDekl`:
  two child fields and a root global), both, or neither. `Dekl` names which, and says that the list's words and the
  tree's words are different words (`getrennt`): a store to the one never moves the other.

  The invariant of the whole arena (`Dekl.Ok`) is the free list's (`FreiOk`), the list's (`ListOk`), the tree's
  (`BaumOk`) and the DISJOINTNESS of the two (no slot is a member of both: a slot that leaves the list is then not in
  the tree, so it may be released). A structure that the declaration does not name has no members and no obligation.

  `GlL K σ σ'` / `GlB K σ σ'` say: every word the list / the tree reads is the same in `σ'` as in `σ`. Whatever a move
  does not touch is `Gl`: an allocator run (`A.Fremd`), a payload store, a recorded read, and -- through the frame of an
  executed form (`LinkRahmen`) and `getrennt` -- every move of the OTHER structure.
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaBaumFormZug
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaAllocForm
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaWachs

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

/-- The list of an arena: its link field and its head. -/
structure ListDekl (A : FreiForm D) where
  L : LinkFeld A
  G : LinkKopf A

/-- The tree of an arena: its two child fields (left = first child, right = next sibling) and its root. -/
structure BaumDekl (A : FreiForm D) where
  Lf : LinkFeld A
  Rf : LinkFeld A
  Wz : LinkKopf A
  hd : Lf.f ≠ Rf.f

/-- **The structures of one arena:** at most one list and at most one tree, on different words. -/
structure Dekl (A : FreiForm D) where
  liste : Option (ListDekl A)
  baum : Option (BaumDekl A)
  getrennt : ∀ l b, liste = some l → baum = some b →
    l.L.f ≠ b.Lf.f ∧ l.L.f ≠ b.Rf.f ∧ l.G.g ≠ b.Wz.g

namespace Dekl
variable {A : FreiForm D} (K : Dekl A)

/-- `j` is a member of the list. -/
def InL (σ : World D) (j : Int) : Prop :=
  match K.liste with
  | none => False
  | some d => Auf (D.count A.tab) (d.L.wert σ) (d.G.st σ) j

/-- `j` is a member of the tree. -/
def InB (σ : World D) (j : Int) : Prop :=
  match K.baum with
  | none => False
  | some b => InBaum (D.count A.tab) (b.Lf.wert σ) (b.Rf.wert σ) (b.Wz.st σ) j

/-- The list is well formed (trivially, when the arena has none). -/
def LOk (σ : World D) : Prop :=
  match K.liste with
  | none => True
  | some d => ListOk A d.L d.G σ

/-- The tree is well formed (trivially, when the arena has none). -/
def BOk (σ : World D) : Prop :=
  match K.baum with
  | none => True
  | some b => BaumOk A b.Lf b.Rf b.Wz σ

/-- **The invariant of the arena:** the free list, the list and the tree are well formed, and no slot is in both
    structures. -/
def Ok (σ : World D) : Prop :=
  A.FreiOk σ ∧ K.LOk σ ∧ K.BOk σ ∧ ∀ j, ¬ (K.InL σ j ∧ K.InB σ j)

variable {K}

theorem InL_some {d : ListDekl A} (h : K.liste = some d) (σ : World D) (j : Int) :
    K.InL σ j ↔ Auf (D.count A.tab) (d.L.wert σ) (d.G.st σ) j := by
  simp only [InL, h]

theorem InL_none (h : K.liste = none) (σ : World D) (j : Int) : ¬ K.InL σ j := by
  simp only [InL, h, not_false_eq_true]

theorem LOk_some {d : ListDekl A} (h : K.liste = some d) (σ : World D) : K.LOk σ ↔ ListOk A d.L d.G σ := by
  simp only [LOk, h]

theorem LOk_none (h : K.liste = none) (σ : World D) : K.LOk σ := by
  simp only [LOk, h]

theorem InB_some {b : BaumDekl A} (h : K.baum = some b) (σ : World D) (j : Int) :
    K.InB σ j ↔ InBaum (D.count A.tab) (b.Lf.wert σ) (b.Rf.wert σ) (b.Wz.st σ) j := by
  simp only [InB, h]

theorem InB_none (h : K.baum = none) (σ : World D) (j : Int) : ¬ K.InB σ j := by
  simp only [InB, h, not_false_eq_true]

theorem BOk_some {b : BaumDekl A} (h : K.baum = some b) (σ : World D) : K.BOk σ ↔ BaumOk A b.Lf b.Rf b.Wz σ := by
  simp only [BOk, h]

theorem BOk_none (h : K.baum = none) (σ : World D) : K.BOk σ := by
  simp only [BOk, h]

/-- A member of the list is live. -/
theorem InL.lebt {σ : World D} (h : K.LOk σ) {j : Int} (hj : K.InL σ j) : A.Lebt σ j := by
  cases hK : K.liste with
  | none => exact absurd hj (InL_none hK σ j)
  | some d => exact ListOkF.lebt_auf ((LOk_some hK σ).mp h) ((InL_some hK σ j).mp hj)

/-- A member of the tree is live. -/
theorem InB.lebt {σ : World D} (h : K.BOk σ) {j : Int} (hj : K.InB σ j) : A.Lebt σ j := by
  cases hK : K.baum with
  | none => exact absurd hj (InB_none hK σ j)
  | some b => exact BaumOkF.lebt_in ((BOk_some hK σ).mp h) ((InB_some hK σ j).mp hj)

/-! ## The frames -/

/-- Every word the list reads is the same in `σ'` as in `σ`. -/
structure GlL (K : Dekl A) (σ σ' : World D) : Prop where
  l : ∀ d, K.liste = some d → (∀ j, d.L.wert σ' j = d.L.wert σ j) ∧ d.G.st σ' = d.G.st σ

/-- Every word the tree reads is the same in `σ'` as in `σ`. -/
structure GlB (K : Dekl A) (σ σ' : World D) : Prop where
  b : ∀ b, K.baum = some b →
    (∀ j, b.Lf.wert σ' j = b.Lf.wert σ j) ∧ (∀ j, b.Rf.wert σ' j = b.Rf.wert σ j) ∧ b.Wz.st σ' = b.Wz.st σ

theorem GlL.refl (σ : World D) : GlL K σ σ := ⟨fun _ _ => ⟨fun _ => rfl, rfl⟩⟩

theorem GlB.refl (σ : World D) : GlB K σ σ := ⟨fun _ _ => ⟨fun _ => rfl, fun _ => rfl, rfl⟩⟩

theorem GlL.lese (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) : GlL K σ (σ.lese Λ o) :=
  ⟨fun _ _ => ⟨fun _ => rfl, rfl⟩⟩

theorem GlB.lese (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) : GlB K σ (σ.lese Λ o) :=
  ⟨fun _ _ => ⟨fun _ => rfl, fun _ => rfl, rfl⟩⟩

theorem GlL.trans {σ σ' σ'' : World D} (h : GlL K σ σ') (h' : GlL K σ' σ'') : GlL K σ σ'' :=
  ⟨fun d hd => ⟨fun j => ((h'.l d hd).1 j).trans ((h.l d hd).1 j), ((h'.l d hd).2).trans ((h.l d hd).2)⟩⟩

theorem GlB.trans {σ σ' σ'' : World D} (h : GlB K σ σ') (h' : GlB K σ' σ'') : GlB K σ σ'' :=
  ⟨fun b hb => ⟨fun j => ((h'.b b hb).1 j).trans ((h.b b hb).1 j),
    fun j => ((h'.b b hb).2.1 j).trans ((h.b b hb).2.1 j), ((h'.b b hb).2.2).trans ((h.b b hb).2.2)⟩⟩

/-- An allocator run moves no link and no head. -/
theorem GlL.fremd {σ σ' : World D} (hf : A.Fremd σ σ') : GlL K σ σ' :=
  ⟨fun d _ => ⟨fun j => congrFun (d.L.wert_fremd' hf) j, d.G.st_fremd hf⟩⟩

theorem GlB.fremd {σ σ' : World D} (hf : A.Fremd σ σ') : GlB K σ σ' :=
  ⟨fun b _ => ⟨fun j => congrFun (b.Lf.wert_fremd' hf) j, fun j => congrFun (b.Rf.wert_fremd' hf) j,
    b.Wz.st_fremd hf⟩⟩

/-- A store into the PAYLOAD field moves no link and no head. -/
theorem GlL.nutzlast (σ : World D) (Λ : List (Res D)) (i : Int) (v : Wert D (D.typ A.tab A.feld)) :
    GlL K σ (σ.schreibSlot A.tab Λ i A.feld v) :=
  ⟨fun d _ => ⟨fun j => by simp only [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ d.L.h1], rfl⟩⟩

theorem GlB.nutzlast (σ : World D) (Λ : List (Res D)) (i : Int) (v : Wert D (D.typ A.tab A.feld)) :
    GlB K σ (σ.schreibSlot A.tab Λ i A.feld v) :=
  ⟨fun b _ => ⟨fun j => by simp only [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ b.Lf.h1],
    fun j => by simp only [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ b.Rf.h1], rfl⟩⟩

/-- A run whose frame names none of the list's words leaves the list alone. -/
theorem GlL.rahmen {fs : List (D.Feld A.tab)} {gs : List D.Glob} {σ σ' : World D} (hr : LinkRahmen A fs gs σ σ')
    (h : ∀ d, K.liste = some d → d.L.f ∉ fs ∧ d.G.g ∉ gs) : GlL K σ σ' :=
  ⟨fun d hd => ⟨fun j => congrFun (hr.feld d.L (h d hd).1) j, hr.kopf d.G (h d hd).2⟩⟩

theorem GlB.rahmen {fs : List (D.Feld A.tab)} {gs : List D.Glob} {σ σ' : World D} (hr : LinkRahmen A fs gs σ σ')
    (h : ∀ b, K.baum = some b → b.Lf.f ∉ fs ∧ b.Rf.f ∉ fs ∧ b.Wz.g ∉ gs) : GlB K σ σ' :=
  ⟨fun b hb => ⟨fun j => congrFun (hr.feld b.Lf (h b hb).1) j, fun j => congrFun (hr.feld b.Rf (h b hb).2.1) j,
    hr.kopf b.Wz (h b hb).2.2⟩⟩

theorem GlL.inL {σ σ' : World D} (h : GlL K σ σ') (j : Int) : K.InL σ' j ↔ K.InL σ j := by
  cases hK : K.liste with
  | none => exact ⟨fun x => absurd x (InL_none hK _ _), fun x => absurd x (InL_none hK _ _)⟩
  | some d =>
    rw [InL_some hK, InL_some hK, funext (h.l d hK).1, (h.l d hK).2]

theorem GlB.inB {σ σ' : World D} (h : GlB K σ σ') (j : Int) : K.InB σ' j ↔ K.InB σ j := by
  cases hK : K.baum with
  | none => exact ⟨fun x => absurd x (InB_none hK _ _), fun x => absurd x (InB_none hK _ _)⟩
  | some b =>
    obtain ⟨h1, h2, h3⟩ := h.b b hK
    rw [InB_some hK, InB_some hK, funext h1, funext h2, h3]

/-- The list stays well formed when its words are as before and its members stay live. -/
theorem GlL.lok {σ σ' : World D} (h : GlL K σ σ') (hlive : ∀ j, K.InL σ j → A.Lebt σ' j) (hok : K.LOk σ) :
    K.LOk σ' := by
  cases hK : K.liste with
  | none => exact LOk_none hK _
  | some d =>
    obtain ⟨h1, h2⟩ := h.l d hK
    rw [LOk_some hK] at hok ⊢
    unfold ListOk at hok ⊢
    rw [funext h1, h2]
    exact hok.rahmen (fun j hj => hlive j ((InL_some hK σ j).mpr hj)) (fun _ _ => rfl)

/-- The tree stays well formed when its words are as before and its members stay live. -/
theorem GlB.bok {σ σ' : World D} (h : GlB K σ σ') (hlive : ∀ j, K.InB σ j → A.Lebt σ' j) (hok : K.BOk σ) :
    K.BOk σ' := by
  cases hK : K.baum with
  | none => exact BOk_none hK _
  | some b =>
    obtain ⟨h1, h2, h3⟩ := h.b b hK
    rw [BOk_some hK] at hok ⊢
    unfold BaumOk at hok ⊢
    rw [funext h1, funext h2, h3]
    exact hok.rahmen' (fun j hj => hlive j ((InB_some hK σ j).mpr hj))
      (fun _ _ => ⟨rfl, rfl⟩)

/-- **The arena invariant survives a run that moves no word of either structure** (and keeps the free list and every
    member live). -/
theorem Ok.gleich {σ σ' : World D} (hL : GlL K σ σ') (hB : GlB K σ σ') (hf : A.FreiOk σ')
    (hlive : ∀ j, (K.InL σ j ∨ K.InB σ j) → A.Lebt σ' j) (h : K.Ok σ) : K.Ok σ' :=
  ⟨hf, hL.lok (fun j hj => hlive j (Or.inl hj)) h.2.1, hB.bok (fun j hj => hlive j (Or.inr hj)) h.2.2.1,
    fun j hj => h.2.2.2 j ⟨(hL.inL j).mp hj.1, (hB.inB j).mp hj.2⟩⟩

end Dekl

end Gabbro.Grammatik
