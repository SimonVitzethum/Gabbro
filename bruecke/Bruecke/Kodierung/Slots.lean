module
public import Bruecke.Kodierung.Teil1
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- A successful field lookup retains its declared name. -/
theorem fieldIndex_name {u : UProg} {t : Fin u.tabs.length} {fld : String}
    {i : Fin (fieldCount u t)} (h : fieldIndex u t fld = some i) :
    ((tabAt u t).cols[i.val]?).map (·.1) = some fld := by
  unfold fieldIndex at h
  split at h
  · cases h
  · rename_i w hw
    cases h
    exact fieldAtPos_name _ _ _ hw

/-- A missing field name has no dependent field index. -/
theorem fieldIndex_none {u : UProg} {t : Fin u.tabs.length} {fld : String}
    (h : fieldAtPos (tabAt u t).cols fld = none) : fieldIndex u t fld = none := by
  unfold fieldIndex
  split
  · rfl
  · rename_i w hw
    rw [h] at hw
    cases hw

/-- A found field name has its declared position. -/
theorem fieldIndex_of {u : UProg} {t : Fin u.tabs.length} {fld : String} {w : Int × Int}
    (hw : fieldAtPos (tabAt u t).cols fld = some w) :
    fieldIndex u t fld = some ⟨fieldPos (tabAt u t).cols fld, fieldPos_lt _ _ _ hw⟩ := by
  unfold fieldIndex
  split
  · rename_i h
    rw [hw] at h
    cases h
  · rfl

/-- Integer field lookup and the general slot lookup select the same position. -/
theorem fieldIndex_int {u : UProg} {t : Fin u.tabs.length} {fld : String}
    {fh : FieldHit u t} (h : fieldHit u t fld = .ok fh) :
    fieldIndex u t fld = some fh.idx := by
  unfold fieldHit at h
  split at h
  · cases h
  · rename_i w hw
    dsimp only at h
    split at h
    · split at h
      · split at h
        · cases h
          exact fieldIndex_of hw
        · cases h
      · cases h
    · cases h

/-- Option field lookup uses that same position, without erasing its target table. -/
theorem fieldIndex_opt {u : UProg} {t : Fin u.tabs.length} {fld : String}
    {oh : OptHit u t} (h : fieldHitO u t fld = .ok oh) :
    fieldIndex u t fld = some oh.idx := by
  unfold fieldHitO at h
  split at h
  · cases h
  · rename_i w hw
    dsimp only at h
    repeat' split at h
    all_goals first | (cases h; exact fieldIndex_of hw) | (cases h; done) | cases h

/-! ## 4. Worlds, through the declaration's names -/

variable (u : UProg)

/-- The Body value a G world holds at the Body place `.slot c k fld`: the slot of the table the
    lowering finds by `c`, at the field it finds by `fld`. `none` = the name pair names nothing
    in the declaration. -/
def slotWert (σ : World (declOf u)) (c : String) (k : Int) (fld : String) :
    Option Gabbro.Body.Value :=
  match tabIdx u.tabs c with
  | .ok t =>
    (fieldIndex u t fld).map (fun f => valOf ((declOf u).typ t f) (σ.slots t k f))
  | .error _ => none

/-- **The world relation**: every place the declaration names holds the G value. -/
def WRel (σ : World (declOf u)) (w : Gabbro.Body.World) : Prop :=
  ∀ c k fld v, slotWert u σ c k fld = some v → w (.slot c k fld) = v

/-- The G world, written over a Body world: the declared places take the G values, every other
    place keeps what `base` holds. -/
def enc (σ : World (declOf u)) (base : Gabbro.Body.World) : Gabbro.Body.World := fun p =>
  match p with
  | .slot c k fld => (slotWert u σ c k fld).getD (base p)
  | p => base p

theorem wrel_enc (σ : World (declOf u)) (base : Gabbro.Body.World) : WRel u σ (enc u σ base) := by
  intro c k fld v h
  simp [enc, h]

/-- The world relation reads the SLOTS only: the lock trace is invisible to it. -/
theorem slotWert_congr {σ σ' : World (declOf u)} (h : σ'.slots = σ.slots) (c k fld) :
    slotWert u σ' c k fld = slotWert u σ c k fld := by
  unfold slotWert; rw [h]

theorem wrel_slots {σ σ' : World (declOf u)} {w : Gabbro.Body.World} (h : σ'.slots = σ.slots)
    (hw : WRel u σ w) : WRel u σ' w := by
  intro c k fld v hv
  rw [slotWert_congr u h] at hv
  exact hw c k fld v hv

@[simp] theorem lese_slots (σ : World (declOf u)) (Λ) (orte) : (σ.lese Λ orte).slots = σ.slots := rfl

/-- Where the world relation already holds, writing the G world over it changes nothing. -/
theorem enc_of_wrel {σ : World (declOf u)} {w : Gabbro.Body.World} (h : WRel u σ w) :
    enc u σ w = w := by
  funext p
  cases p with
  | slot c k fld =>
    simp only [enc]
    cases hv : slotWert u σ c k fld with
    | none => rfl
    | some v => exact (h c k fld v hv).symm
  | field c n => rfl
  | global n => rfl

/-- Read a declared slot at its resolved field position. -/
theorem wrel_lies_index {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w)
    (c : String) (t : Fin u.tabs.length) (ht : tabIdx u.tabs c = .ok t)
    (fld : String) (f : Fin (fieldCount u t)) (hf : fieldIndex u t fld = some f) (k : Int) :
    w (.slot c k fld) = valOf ((declOf u).typ t f) (σ.slots t k f) := by
  apply hW
  (simp only [slotWert, ht, hf]) <;> rfl

/-- A slot store preserves every other declared place, for every represented type. -/
theorem wrel_store_index {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w)
    (c : String) (t : Fin u.tabs.length) (ht : tabIdx u.tabs c = .ok t)
    (fld : String) (f : Fin (fieldCount u t)) (hf : fieldIndex u t fld = some f) (k : Int)
    (x : Wert (declOf u) ((declOf u).typ t f)) :
    WRel u (σ.storeSlot t k f x)
      (Gabbro.Body.store w (.slot c k fld) (valOf ((declOf u).typ t f) x)) := by
  intro c' k' fld' v hv
  unfold slotWert at hv
  split at hv
  · rename_i t' ht'
    cases hf' : fieldIndex u t' fld' with
    | none =>
      rw [hf'] at hv
      cases hv
    | some f' =>
      rw [hf'] at hv
      have hv' : valOf ((declOf u).typ t' f') ((σ.storeSlot t k f x).slots t' k' f') = v :=
        Option.some.inj hv
      subst v
      by_cases hp : (Gabbro.Body.Place.slot c' k' fld') = .slot c k fld
      · simp only [Gabbro.Body.Place.slot.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        rw [ht] at ht'
        cases ht'
        rw [hf] at hf'
        cases hf'
        rw [Gabbro.Body.store_here]
        exact congrArg (valOf _) (storeSlot_hit σ _ _ _ x).symm
      · rw [Gabbro.Body.store_elsewhere _ _ _ _ hp,
          wrel_lies_index u hW c' t' ht' fld' f' hf' k']
        congr 1
        by_cases htt : t' = t
        · subst t'
          by_cases hkk : k' = k
          · subst k'
            have hff : f' ≠ f := by
              intro e
              apply hp
              have nc := (tabIdx_name _ _ _ ht').symm.trans (tabIdx_name _ _ _ ht)
              have nf := fieldIndex_name hf'
              rw [e, fieldIndex_name hf] at nf
              have names := Option.some.inj nf
              simp only [nc, names]
            exact (storeSlot_fremd_feld σ t k f x k f' rfl hff).symm
          · simp [World.storeSlot, hkk]
        · exact (storeSlot_andere σ t k f x t' htt k' f').symm
  · cases hv

/-- Integer writes are instances of the general typed slot store. -/
theorem wrel_store {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w)
    (c : String) (t : Fin u.tabs.length) (ht : tabIdx u.tabs c = .ok t)
    (fld : String) (fh : FieldHit u t) (hf : fieldHit u t fld = .ok fh) (k : Int)
    (x : Wert (declOf u) ((declOf u).typ t fh.idx)) :
    WRel u (σ.storeSlot t k fh.idx x)
      (Gabbro.Body.store w (.slot c k fld) (valOf ((declOf u).typ t fh.idx) x)) :=
  wrel_store_index u hW c t ht fld fh.idx (fieldIndex_int hf) k x

theorem wrel_lies_k {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w)
    (c : String) (t : Fin u.tabs.length) (ht : tabIdx u.tabs c = .ok t)
    (fld : String) (fh : FieldHit u t) (hf : fieldHit u t fld = .ok fh) (k : Int) :
    w (.slot c k fld) = valOf ((declOf u).typ t fh.idx) (σ.slots t k fh.idx) :=
  wrel_lies_index u hW c t ht fld fh.idx (fieldIndex_int hf) k

/-- Every declared numeric field retains its checked range. -/
theorem valOf_feld (t : Fin u.tabs.length) (fh : FieldHit u t)
    (x : Wert (declOf u) ((declOf u).typ t fh.idx)) :
    ∃ n, valOf ((declOf u).typ t fh.idx) x = .int n ∧ fh.range.1 ≤ n ∧ n ≤ fh.range.2 := by
  have h : (declOf u).typ t fh.idx = .int fh.range.1 fh.range.2 := fh.hint
  revert x
  rw [h]
  intro x
  exact ⟨x.n, rfl, x.lo_le, x.le_hi⟩

end Gabbro.Bruecke
