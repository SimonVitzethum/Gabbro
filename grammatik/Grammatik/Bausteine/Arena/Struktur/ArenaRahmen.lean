/-
  File:      Grammatik/ArenaRahmen.lean
  Subject:   THE FRAME OF A LINK STORE (PLAN-DYNAMISCH.md section 8a.1, third pass): which link fields and which link
             heads a run can have moved. A body that holds a list AND a tree on one arena needs, for every move of the
             one, the fact that the other did not see it. `LinkRahmen A fs gs σ σ'` says: every link field that is not
             in `fs` reads the same in `σ'` as in `σ`, and every link head that is not in `gs` reads the same.

  The executed forms (`ArenaLinkForm.lean`, `ArenaBaumForm.lean`, `ArenaBaumFormG.lean`) each carry the frame of the stores
  they make as one more conjunct (`push`: field `lnk`, head; `leaf in`: the two child fields; ...).
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaLebt
import Grammatik.Bausteine.Arena.Struktur.ArenaListe

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A store into one table leaves every slot of every other table. -/
theorem World.slots_schreibSlot_andere_tabelle (σ : World D) (t t' : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) (k' : Int) (f' : D.Feld t') (h : t' ≠ t) :
    (σ.schreibSlot t Λ k f v).slots t' k' f' = σ.slots t' k' f' := by
  simp only [World.schreibSlot, World.merke, World.storeSlot, dif_neg h]

/-- **The frame of a run:** link fields outside `fs` and link heads outside `gs` read as before. -/
structure LinkRahmen (A : FreiForm D) (fs : List (D.Feld A.tab)) (gs : List D.Glob) (σ σ' : World D) : Prop where
  feld : ∀ C : LinkFeld A, C.f ∉ fs → C.wert σ' = C.wert σ
  kopf : ∀ G : LinkKopf A, G.g ∉ gs → G.st σ' = G.st σ

namespace LinkRahmen
variable {A : FreiForm D}

/-- Nothing moved. -/
theorem refl (σ : World D) : LinkRahmen A [] [] σ σ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- A recorded read moves no link. -/
theorem lese (σ : World D) (Λ : List (Res D)) (o : List (D.Tab ⊕ D.Glob)) : LinkRahmen A [] [] σ (σ.lese Λ o) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- A store into one field of the arena's table. -/
theorem schreibSlot (σ : World D) (Λ : List (Res D)) (i : Int) (f : D.Feld A.tab) (v : Wert D (D.typ A.tab f)) :
    LinkRahmen A [f] [] σ (σ.schreibSlot A.tab Λ i f v) := by
  refine ⟨fun C hC => funext fun j => ?_, fun _ _ => rfl⟩
  have hne : C.f ≠ f := fun e => hC (by simp [e])
  simp only [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ hne]

/-- A store into one global. -/
theorem schreibGlob (σ : World D) (Λ : List (Res D)) (g : D.Glob) (v : Wert D (D.gtyp g)) :
    LinkRahmen A [] [g] σ (σ.schreibGlob g Λ v) := by
  refine ⟨fun _ _ => rfl, fun G hG => ?_⟩
  have hne : G.g ≠ g := fun e => hG (by simp [e])
  simp only [LinkKopf.st, World.globs_schreibGlob_ne _ _ _ _ _ hne]

/-- Two runs one after the other. -/
theorem trans {fs fs' : List (D.Feld A.tab)} {gs gs' : List D.Glob} {σ σ' σ'' : World D}
    (h : LinkRahmen A fs gs σ σ') (h' : LinkRahmen A fs' gs' σ' σ'') :
    LinkRahmen A (fs ++ fs') (gs ++ gs') σ σ'' :=
  ⟨fun C hC => (h'.feld C (fun e => hC (List.mem_append.mpr (Or.inr e)))).trans
      (h.feld C (fun e => hC (List.mem_append.mpr (Or.inl e)))),
   fun G hG => (h'.kopf G (fun e => hG (List.mem_append.mpr (Or.inr e)))).trans
      (h.kopf G (fun e => hG (List.mem_append.mpr (Or.inl e))))⟩

/-- A frame that names more fields and heads is weaker. -/
theorem mono {fs fs2 : List (D.Feld A.tab)} {gs gs2 : List D.Glob} {σ σ' : World D}
    (h : LinkRahmen A fs gs σ σ') (hf : ∀ f ∈ fs, f ∈ fs2) (hg : ∀ g ∈ gs, g ∈ gs2) :
    LinkRahmen A fs2 gs2 σ σ' :=
  ⟨fun C hC => h.feld C (fun e => hC (hf _ e)), fun G hG => h.kopf G (fun e => hG (hg _ e))⟩

end LinkRahmen

end Gabbro.Grammatik
