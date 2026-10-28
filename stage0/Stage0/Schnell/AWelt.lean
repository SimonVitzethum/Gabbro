/-
  File:      stage0/Stage0/Schnell/AWelt.lean
  Subject:   **The array memory of the fast machine.** Each field of each table is an array of its values, each static
             one entry, both tagged with their type; a cell the arrays do not hold (a field not prepared, an index
             outside, a type that does not fit) is read from a memory `basis`. `sicht`: the memory the arrays stand
             for. A write goes into its array in place (`Array.modify`), or into `basis` if no array holds the cell;
             `sicht_schreib`: the memory after the writes is the memory with the writes (`schreibAuf`). `bereite`
             fills a field's array from the current memory and leaves it unchanged (`sicht_bereite`).
-/
import Stage0.Schritt.Schreib
import Mathlib.Data.Nat.Pairing

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **Numbers for tables, fields and statics**, one-to-one; and which fields and statics to prepare. -/
structure Kodierung (D : Deklaration) where
  tn : D.Tab → Nat
  tn_inj : ∀ t t', tn t = tn t' → t = t'
  fn : (t : D.Tab) → D.Feld t → Nat
  fn_inj : ∀ t f f', fn t f = fn t f' → f = f'
  gn : D.Glob → Nat
  gn_inj : ∀ g g', gn g = gn g' → g = g'
  felder : List (Σ t : D.Tab, D.Feld t)
  globs : List D.Glob

/-- The array of a table's field. -/
def Kodierung.idx (K : Kodierung D) (t : D.Tab) (f : D.Feld t) : Nat := Nat.pair (K.tn t) (K.fn t f)

theorem Kodierung.idx_inj (K : Kodierung D) {t t' : D.Tab} {f : D.Feld t} {f' : D.Feld t'}
    (h : K.idx t f = K.idx t' f') : ∃ ht : t = t', ht ▸ f = f' := by
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
  obtain rfl := K.tn_inj _ _ h1
  exact ⟨rfl, K.fn_inj _ _ _ h2⟩

/-- **The array memory.** -/
structure AWelt (D : Deklaration) where
  basis : Speicher D
  felder : Array (Σ τ : Ty, Array (Wert D τ))
  gl : Array (Option (Σ τ : Ty, Wert D τ))

variable (K : Kodierung D)

/-- A cell of a typed array, if the array holds it. -/
def zelleAus {τ σ : Ty} (h : τ = σ) (a : Array (Wert D τ)) (k : Int) : Option (Wert D σ) :=
  if hk : 0 ≤ k ∧ k.toNat < a.size then some (h ▸ a[k.toNat]) else none

/-- The value of a cell. -/
def AWelt.slot (A : AWelt D) (t : D.Tab) (k : Int) (f : D.Feld t) : Wert D (D.typ t f) :=
  match A.felder[K.idx t f]? with
  | some ⟨τ, a⟩ =>
    if h : τ = D.typ t f then (zelleAus h a k).getD (A.basis.slots t k f) else A.basis.slots t k f
  | none => A.basis.slots t k f

/-- The value of a static. -/
def AWelt.glob (A : AWelt D) (g : D.Glob) : Wert D (D.gtyp g) :=
  match A.gl[K.gn g]? with
  | some (some ⟨τ, v⟩) => if h : τ = D.gtyp g then h ▸ v else A.basis.globs g
  | _ => A.basis.globs g

/-- **The memory the arrays stand for.** -/
def AWelt.sicht (A : AWelt D) : Speicher D := ⟨fun t k f => A.slot K t k f, fun g => A.glob K g⟩

/-- An array holds the cell. -/
def AWelt.haelt (A : AWelt D) (t : D.Tab) (k : Int) (f : D.Feld t) : Bool :=
  match A.felder[K.idx t f]? with
  | some ⟨τ, a⟩ => decide (τ = D.typ t f) && decide (0 ≤ k) && decide (k.toNat < a.size)
  | none => false

/-- An entry holds the static. -/
def AWelt.haeltG (A : AWelt D) (g : D.Glob) : Bool :=
  match A.gl[K.gn g]? with
  | some (some ⟨τ, _⟩) => decide (τ = D.gtyp g)
  | _ => false

/-- Write a cell into a typed array. -/
def setzeZelle {σ : Ty} (k : Int) (v : Wert D σ) (e : Σ τ : Ty, Array (Wert D τ)) : Σ τ : Ty, Array (Wert D τ) :=
  if h : σ = e.1 then ⟨e.1, e.2.setIfInBounds k.toNat (h ▸ v)⟩ else e

/-- **One write.** -/
def AWelt.schreib1 (A : AWelt D) : Schreib D → AWelt D
  | .slot t k f v =>
    if A.haelt K t k f then { A with felder := A.felder.modify (K.idx t f) (setzeZelle k v) }
    else { A with basis := (Schreib.slot t k f v).auf A.basis }
  | .glob g v =>
    if A.haeltG K g then { A with gl := A.gl.modify (K.gn g) (fun _ => some ⟨D.gtyp g, v⟩) }
    else { A with basis := (Schreib.glob g v).auf A.basis }

/-- Writes in order. -/
def AWelt.schreibe (A : AWelt D) (w : List (Schreib D)) : AWelt D := w.foldl (fun A s => A.schreib1 K s) A

/-- The cell a write does not hit keeps its value. -/
theorem storeSlot_sonst (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (t' : D.Tab) (k' : Int) (f' : D.Feld t') (h : ¬ (∃ ht : t' = t, k' = k ∧ ht ▸ f' = f)) :
    (σ.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f' := by
  by_cases ht : t' = t
  · subst ht
    by_cases hk : k' = k
    · subst hk
      have hf : f' ≠ f := fun hf => h ⟨rfl, rfl, hf⟩
      simp only [World.storeSlot, ↓reduceDIte, ↓reduceIte, hf]
    · simp only [World.storeSlot, ↓reduceDIte, hk, ↓reduceIte]
  · simp only [World.storeSlot, ht, ↓reduceDIte]

theorem zelleAus_setze {τ : Ty} (a : Array (Wert D τ)) (k k' : Int) (v : Wert D τ) (hk0 : 0 ≤ k)
    (hka : k.toNat < a.size) :
    zelleAus rfl (a.setIfInBounds k.toNat v) k' = if k' = k then some v else zelleAus rfl a k' := by
  unfold zelleAus
  by_cases hkk : k' = k
  · subst hkk
    simp only [hk0, Array.size_setIfInBounds, hka, and_self, ↓reduceDIte, Array.getElem_setIfInBounds_self, ↓reduceIte]
  · rw [if_neg hkk]
    by_cases h' : 0 ≤ k' ∧ k'.toNat < a.size
    · have hne : k.toNat ≠ k'.toNat := by omega
      simp only [h', Array.size_setIfInBounds, and_self, ↓reduceDIte, Array.getElem_setIfInBounds_ne _ hne]
    · simp only [Array.size_setIfInBounds]
      simp only [h', ↓reduceDIte]

theorem sicht_schreib1 (A : AWelt D) (s : Schreib D) : (A.schreib1 K s).sicht K = s.auf (A.sicht K) := by
  cases s with
  | slot t k f v =>
    simp only [AWelt.schreib1]
    split
    · rename_i hh
      obtain ⟨τ, a, he, hτ, hk0, hka⟩ : ∃ τ a, A.felder[K.idx t f]? = some ⟨τ, a⟩ ∧ τ = D.typ t f ∧ 0 ≤ k ∧
          k.toNat < a.size := by
        unfold AWelt.haelt at hh
        split at hh
        · rename_i τ a he
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
          exact ⟨τ, a, he, hh.1.1, hh.1.2, hh.2⟩
        · cases hh
      subst hτ
      simp only [AWelt.sicht, Schreib.auf, World.speicher, Speicher.mk.injEq]
      refine ⟨?_, rfl⟩
      funext t' k' f'
      by_cases hi : K.idx t f = K.idx t' f'
      · obtain ⟨rfl, rfl⟩ := K.idx_inj hi
        simp only [AWelt.slot, Array.getElem?_modify, he, Option.map_some, setzeZelle, ite_true, dite_true,
          ↓reduceIte, ↓reduceDIte, zelleAus_setze a k k' v hk0 hka]
        by_cases hkk : k' = k
        · subst hkk
          simp only [if_pos rfl, Option.getD_some]
          exact (storeSlot_hit _ _ _ _ _).symm
        · simp only [hkk, if_false]
          simp only [World.storeSlot, Speicher.welt, ↓reduceDIte, hkk, ↓reduceIte, he]
      · rw [storeSlot_sonst _ _ _ _ _ _ _ _ (fun ⟨ht, _, hf⟩ => by subst ht; subst hf; exact hi rfl)]
        simp only [AWelt.slot, Array.getElem?_modify, if_neg hi, Speicher.welt]
    · rename_i hh
      simp only [AWelt.sicht, Schreib.auf, World.speicher, Speicher.mk.injEq]
      refine ⟨?_, rfl⟩
      funext t' k' f'
      by_cases hc : ∃ ht : t' = t, k' = k ∧ ht ▸ f' = f
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        have e := storeSlot_hit (A.basis.welt []) t' k' f' v
        rw [storeSlot_hit]
        simp only [AWelt.slot, e]
        unfold AWelt.haelt at hh
        split
        · rename_i τ a he
          rw [he] at hh
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hh
          split
          · rename_i hτ
            subst hτ
            unfold zelleAus
            split
            · rename_i hk
              exact absurd hk.2 (hh ⟨rfl, hk.1⟩)
            · rfl
          · rfl
        · rfl
      · have e := storeSlot_sonst (A.basis.welt []) t k f v t' k' f' hc
        simp only [Speicher.welt] at e
        rw [storeSlot_sonst _ _ _ _ _ _ _ _ hc]
        simp only [AWelt.slot, e, Speicher.welt]
  | glob g v =>
    simp only [AWelt.schreib1]
    split
    · rename_i hh
      simp only [AWelt.sicht, Schreib.auf, World.speicher, Speicher.mk.injEq]
      refine ⟨rfl, ?_⟩
      funext g'
      by_cases hg : g' = g
      · subst hg
        rw [storeGlob_hit]
        simp only [AWelt.glob, Array.getElem?_modify, ↓reduceIte]
        unfold AWelt.haeltG at hh
        split at hh
        · rename_i τ x he
          simp only [he, Option.map_some, ↓reduceDIte]
        · cases hh
      · have hne : K.gn g ≠ K.gn g' := fun h => hg (K.gn_inj _ _ h).symm
        rw [storeGlob_andere _ _ _ _ hg]
        simp only [AWelt.glob, Array.getElem?_modify, hne, ite_false, Speicher.welt]
    · rename_i hh
      simp only [AWelt.sicht, Schreib.auf, World.speicher, Speicher.mk.injEq]
      refine ⟨rfl, ?_⟩
      funext g'
      by_cases hg : g' = g
      · subst hg
        rw [storeGlob_hit]
        have e := storeGlob_hit (A.basis.welt []) g' v
        simp only [AWelt.glob]
        unfold AWelt.haeltG at hh
        split
        · rename_i τ x he
          rw [he] at hh
          simp only [decide_eq_true_eq] at hh
          simp only [hh, dite_false]
          exact e
        · exact e
      · have e := storeGlob_andere (A.basis.welt []) g v g' hg
        simp only [Speicher.welt] at e
        rw [storeGlob_andere _ _ _ _ hg]
        simp only [AWelt.glob, e, Speicher.welt]

/-- **The arrays after the writes stand for the memory with the writes.** -/
theorem sicht_schreibe (A : AWelt D) (w : List (Schreib D)) :
    (A.schreibe K w).sicht K = schreibAuf w (A.sicht K) := by
  induction w generalizing A with
  | nil => rfl
  | cons s w ih =>
    simp only [AWelt.schreibe, List.foldl_cons, schreibAuf] at ih ⊢
    rw [ih, sicht_schreib1]

/-- **Prepare a field**: its array of `n` cells (or more, if it held more), filled from the current memory. -/
def AWelt.bereite (A : AWelt D) (t : D.Tab) (f : D.Feld t) (n : Nat) : AWelt D :=
  let alt := match A.felder[K.idx t f]? with
    | some ⟨_, a⟩ => a.size
    | none => 0
  let e : Σ τ : Ty, Array (Wert D τ) := ⟨D.typ t f, Array.ofFn (n := max n alt) fun k => A.slot K t (k.val : Int) f⟩
  { A with felder := A.felder.setIfInBounds (K.idx t f) e }

/-- **Prepare a static**: its entry, from the current memory. -/
def AWelt.bereiteG (A : AWelt D) (g : D.Glob) : AWelt D :=
  { A with gl := A.gl.setIfInBounds (K.gn g) (some ⟨D.gtyp g, A.glob K g⟩) }

theorem sicht_bereite (A : AWelt D) (t : D.Tab) (f : D.Feld t) (n : Nat) :
    (A.bereite K t f n).sicht K = A.sicht K := by
  simp only [AWelt.sicht, Speicher.mk.injEq]
  refine ⟨?_, rfl⟩
  funext t' k' f'
  by_cases hi : K.idx t f = K.idx t' f'
  · obtain ⟨rfl, rfl⟩ := K.idx_inj hi
    by_cases hs : K.idx t f < A.felder.size
    · conv_lhs => unfold AWelt.slot
      simp only [AWelt.bereite, Array.getElem?_setIfInBounds_self_of_lt hs, dite_true]
      unfold zelleAus
      split
      · rename_i hk
        simp only [Option.getD_some, Array.getElem_ofFn]
        congr 1
        omega
      · rename_i hk
        simp only [Option.getD_none]
        unfold AWelt.slot
        split
        · rename_i τ a he
          split
          · rename_i hτ
            subst hτ
            unfold zelleAus
            split
            · rename_i hk'
              exfalso
              apply hk
              refine ⟨hk'.1, ?_⟩
              simp only [Array.size_ofFn, he]
              omega
            · rfl
          · rfl
        · rfl
    · simp only [AWelt.bereite, Array.setIfInBounds_eq_of_size_le (Nat.not_lt.mp hs)]
  · simp only [AWelt.slot, AWelt.bereite, Array.getElem?_setIfInBounds_ne hi]

theorem sicht_bereiteG (A : AWelt D) (g : D.Glob) : (A.bereiteG K g).sicht K = A.sicht K := by
  simp only [AWelt.sicht, Speicher.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext g'
  by_cases hg : K.gn g = K.gn g'
  · obtain rfl := K.gn_inj _ _ hg
    by_cases hs : K.gn g < A.gl.size
    · conv_lhs => unfold AWelt.glob
      simp only [AWelt.bereiteG, Array.getElem?_setIfInBounds_self_of_lt hs, dite_true]
    · simp only [AWelt.bereiteG, Array.setIfInBounds_eq_of_size_le (Nat.not_lt.mp hs)]
  · simp only [AWelt.glob, AWelt.bereiteG, Array.getElem?_setIfInBounds_ne hg]

/-- **The array memory of a memory**: every field and static the encoding names, prepared. -/
def AWelt.von (S : Speicher D) : AWelt D :=
  let nF := (K.felder.map fun e => K.idx e.1 e.2).foldl max 0 + 1
  let nG := (K.globs.map K.gn).foldl max 0 + 1
  let A0 : AWelt D := ⟨S, Array.replicate nF ⟨.bool, #[]⟩, Array.replicate nG none⟩
  let A1 := K.felder.foldl (fun A e => A.bereite K e.1 e.2 (D.count e.1).toNat) A0
  K.globs.foldl (fun A g => A.bereiteG K g) A1

theorem sicht_leer (S : Speicher D) (nF nG : Nat) :
    (⟨S, Array.replicate nF ⟨.bool, #[]⟩, Array.replicate nG none⟩ : AWelt D).sicht K = S := by
  simp only [AWelt.sicht]
  congr 1
  · funext t k f
    simp only [AWelt.slot]
    split
    · rename_i τ a he
      have hm := (Array.mem_replicate.mp (Array.mem_of_getElem? he)).2
      have hs : a.size = 0 := by
        have := congrArg (fun e : Σ τ : Ty, Array (Wert D τ) => e.2.size) hm
        simpa using this
      split
      · simp only [zelleAus, hs, Nat.not_lt_zero, and_false, ↓reduceDIte, Option.getD_none]
      · rfl
    · rfl
  · funext g
    simp only [AWelt.glob]
    split
    · rename_i τ v he
      have hm := (Array.mem_replicate.mp (Array.mem_of_getElem? he)).2
      cases hm
    · rfl

theorem sicht_von (S : Speicher D) : (AWelt.von K S).sicht K = S := by
  simp only [AWelt.von]
  generalize hA0 : (⟨S, _, _⟩ : AWelt D) = A0
  have h0 : A0.sicht K = S := by rw [← hA0]; exact sicht_leer K S _ _
  have h1 : ∀ (es : List (Σ t : D.Tab, D.Feld t)) (A : AWelt D),
      (es.foldl (fun A e => A.bereite K e.1 e.2 (D.count e.1).toNat) A).sicht K = A.sicht K := by
    intro es
    induction es with
    | nil => intro A; rfl
    | cons e es ih => intro A; simp only [List.foldl_cons]; rw [ih, sicht_bereite]
  have h2 : ∀ (gs : List D.Glob) (A : AWelt D),
      (gs.foldl (fun A g => A.bereiteG K g) A).sicht K = A.sicht K := by
    intro gs
    induction gs with
    | nil => intro A; rfl
    | cons g gs ih => intro A; simp only [List.foldl_cons]; rw [ih, sicht_bereiteG]
  rw [h2, h1, h0]

end Gabbro.Stage0
