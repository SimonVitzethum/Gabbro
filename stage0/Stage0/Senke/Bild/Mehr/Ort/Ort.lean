/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Ort/Ort.lean
  Subject:   Worlds that agree on a set of carriers (multi-thread image theorem, package MT2: the G side of the
             commit). At a segment end, machine G's thread takes the steps the single-thread chain computed from the
             world of ITS boundary; meanwhile other threads have committed writes to carriers this thread does not
             access. `OrtGleich C σ σ'`: the two worlds have the same trace and agree on every carrier in `C` (the
             carriers the segment accesses). This file gives its algebra: a read keeps it (`lese`), an expression
             whose places lie in `C` has the same value in both (`wert`, from `eval_liest_nur_orte`), and a write
             of the same value -- to ANY carrier -- keeps it (`schreibSlot`, `schreibGlob`, `schreibBytes`). The
             statements that run on it are in `Mehr/Ort/Blatt.lean`.
-/
module
public import Grammatik.Kern.Syntax.Extensions.Extraktion.T3.Teil2
public import Grammatik.Kern.Syntax.Satz.T1Frame
public import Grammatik.Kern.Semantik.Maschine.T2
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **Two worlds that agree on the carriers `C`**, with the same trace. -/
structure OrtGleich (C : D.Tab ⊕ D.Glob → Prop) (σ σ' : World D) : Prop where
  spur : σ.spur = σ'.spur
  slots : ∀ t, C (.inl t) → σ.slots t = σ'.slots t
  globs : ∀ g, C (.inr g) → σ.globs g = σ'.globs g

/-! ## Stores -/

/-- A store into a table leaves the other fields of the same row and the other rows. -/
theorem storeSlot_daneben (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) (k' : Int)
    (f' : D.Feld t) (h : k' ≠ k ∨ f' ≠ f) : (σ.storeSlot t k f v).slots t k' f' = σ.slots t k' f' := by
  by_cases hkk : k' = k
  · have hff : f' ≠ f := by
      cases h with
      | inl hkk' => exact absurd hkk hkk'
      | inr hff => exact hff
    simp only [World.storeSlot, hkk, ↓reduceDIte, ↓reduceIte, hff]
  · simp only [World.storeSlot, ↓reduceDIte, hkk, ↓reduceIte]

/-- **A store keeps the agreement of a table**: two worlds that agree on the table `t'` agree on it after the same
    store, wherever it goes. -/
theorem storeSlot_gleich {σ σ' : World D} {t' : D.Tab} (h : σ.slots t' = σ'.slots t') (t : D.Tab) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) : (σ.storeSlot t k f v).slots t' = (σ'.storeSlot t k f v).slots t' := by
  funext k' f'
  by_cases ht : t' = t
  · subst ht
    by_cases hkf : k' = k ∧ f' = f
    · obtain ⟨rfl, rfl⟩ := hkf
      rw [storeSlot_hit, storeSlot_hit]
    · have h' : k' ≠ k ∨ f' ≠ f := by
        by_cases hk : k' = k
        · exact Or.inr fun hf => hkf ⟨hk, hf⟩
        · exact Or.inl hk
      rw [storeSlot_daneben _ _ _ _ _ _ _ h', storeSlot_daneben _ _ _ _ _ _ _ h', h]
  · rw [storeSlot_andere _ _ _ _ _ _ ht, storeSlot_andere _ _ _ _ _ _ ht, h]

/-- A store keeps the agreement of a global. -/
theorem storeGlob_gleich {σ σ' : World D} {g' : D.Glob} (h : σ.globs g' = σ'.globs g') (g : D.Glob)
    (v : Wert D (D.gtyp g)) : (σ.storeGlob g v).globs g' = (σ'.storeGlob g v).globs g' := by
  by_cases hg : g' = g
  · subst hg
    rw [storeGlob_hit, storeGlob_hit]
  · rw [storeGlob_andere _ _ _ _ hg, storeGlob_andere _ _ _ _ hg, h]

namespace OrtGleich

variable {C : D.Tab ⊕ D.Glob → Prop}

theorem refl (σ : World D) : OrtGleich C σ σ := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem symm {σ σ' : World D} (h : OrtGleich C σ σ') : OrtGleich C σ' σ :=
  ⟨h.spur.symm, fun t ht => (h.slots t ht).symm, fun g hg => (h.globs g hg).symm⟩

theorem trans {σ1 σ2 σ3 : World D} (h1 : OrtGleich C σ1 σ2) (h2 : OrtGleich C σ2 σ3) : OrtGleich C σ1 σ3 :=
  ⟨h1.spur.trans h2.spur, fun t ht => (h1.slots t ht).trans (h2.slots t ht),
    fun g hg => (h1.globs g hg).trans (h2.globs g hg)⟩

/-- The same locks are held. -/
theorem haelt {σ σ' : World D} (h : OrtGleich C σ σ') : σ.haelt = σ'.haelt := by
  unfold World.haelt
  rw [h.spur]

/-- **A read keeps the agreement** (it records the same events, with the same held locks). -/
theorem lese {σ σ' : World D} (h : OrtGleich C σ σ') (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    OrtGleich C (σ.lese Λ os) (σ'.lese Λ os) where
  spur := by
    simp only [World.lese, World.merke, World.haelt, h.spur]
  slots := h.slots
  globs := h.globs

/-- Recording the same events keeps the agreement. -/
theorem merke {σ σ' : World D} (h : OrtGleich C σ σ') (es : List (Ereignis D)) :
    OrtGleich C (σ.merke es) (σ'.merke es) where
  spur := by
    simp only [World.merke, h.spur]
  slots := h.slots
  globs := h.globs

/-- **An expression whose places lie in `C` has the same value** in both worlds. -/
theorem wert {σ σ' : World D} (h : OrtGleich C σ σ') {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (he : ∀ o ∈ e.orte, C o) (ρ : Env D Γ) : eval σ e σ ρ = eval σ' e σ' ρ :=
  Extraktion.eval_liest_nur_orte e e.orte (fun _ ho => ho) σ σ' σ σ' ρ
    (fun t ht k f => by rw [h.slots t (he _ ht)]) (fun g hg => h.globs g (he _ hg))
    (fun t ht k f => by rw [h.slots t (he _ ht)]) (fun g hg => h.globs g (he _ hg))

/-- **The same write keeps the agreement**, to any table. -/
theorem schreibSlot {σ σ' : World D} (h : OrtGleich C σ σ') (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) : OrtGleich C (σ.schreibSlot t Λ k f v) (σ'.schreibSlot t Λ k f v) where
  spur := by
    simp only [World.schreibSlot, World.merke, World.storeSlot, World.haelt, h.spur]
  slots := fun t' ht' => storeSlot_gleich (h.slots t' ht') t k f v
  globs := h.globs

/-- The same write keeps the agreement, to any global. -/
theorem schreibGlob {σ σ' : World D} (h : OrtGleich C σ σ') (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) : OrtGleich C (σ.schreibGlob g Λ v) (σ'.schreibGlob g Λ v) where
  spur := by
    simp only [World.schreibGlob, World.merke, World.storeGlob, World.haelt, h.spur]
  slots := h.slots
  globs := fun g' hg' => storeGlob_gleich (h.globs g' hg') g v

/-- The same bytes written keep the agreement. -/
theorem schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) :
    ∀ (bs : List Byte) (k : Int) {σ σ' : World D}, OrtGleich C σ σ' →
      OrtGleich C (σ.schreibBytes t f hf Λ k bs) (σ'.schreibBytes t f hf Λ k bs)
  | [], _, _, _, h => h
  | _ :: bs, k, _, _, h => by
    simp only [World.schreibBytes]
    exact schreibBytes t f hf Λ bs (k + 1) (h.schreibSlot t Λ k f _)

end OrtGleich

end Gabbro.Stage0.Senke.BildMehr
