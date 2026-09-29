import Grammatik.Parser.UebersetzeAllg2
import Grammatik.CSLInvarianteC
import Grammatik.Satz
import Gabbro.Body
import Bruecke.Pflichten

/-!
# S3, part 1: how a state of machine G reads as a state of `Gabbro.Body`

The simulation theorem (`Bruecke/Simulation.lean`) relates a run of the parser's lowered program
(machine G, `execEnd`) to a run of the body GabbroV proves things about (`Gabbro.Body.exec`).
This file fixes the READING of one state as the other:

* a G value reads as a Body value (`valOf`: a number is `.int n`, a truth value `.bool b`, and a
  pointer -- whose only content in G is the right to address its table -- is `.absent`);
* the G environment of a function reads positionally (`nthVal`), and a Body binding is related
  to it name by name through `paramPos`, the SAME lookup the lowering uses (`LRel`);
* a G world reads as a Body world through the declaration's names (`slotWert`, `WRel`): the Body
  place `.slot c k fld` is the G slot of the table `tabIdx c` and the field `fieldHit … fld` --
  again the lookups the lowering itself uses, so a duplicate name is read exactly as the
  lowering reads it (first occurrence);
* casts: the lowering transports terms along propositional type equations (`rw … ; exact`);
  every transport is handled through `HEq` once, here (`valOf_heq`, `eval_heq`, …).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-! ## 1. Values -/

/-- A G value as a Body value. Only numbers and truth values have a Body reading the bridge
    uses; every other type reads as `.absent` (a pointer's value is `()`). -/
def valOf {D : Deklaration} : (τ : Ty) → Wert D τ → Gabbro.Body.Value
  | .int _ _, z => .int (z : Zahl _ _).n
  | .bool, b => .bool (b : Bool)
  | _, _ => .absent

theorem valOf_heq {D : Deklaration} {τ₁ τ₂ : Ty} (h : τ₁ = τ₂) (x₁ : Wert D τ₁) (x₂ : Wert D τ₂)
    (hx : HEq x₁ x₂) : valOf τ₁ x₁ = valOf τ₂ x₂ := by
  subst h
  cases hx
  rfl

@[simp] theorem valOf_int {D : Deklaration} {lo hi : Int} (z : Wert D (.int lo hi)) :
    valOf (.int lo hi) z = .int (z : Zahl lo hi).n := rfl

@[simp] theorem valOf_bool {D : Deklaration} (b : Wert D .bool) :
    valOf .bool b = .bool (b : Bool) := rfl

/-! ## 2. Environments, positionally -/

/-- The `j`th entry of a G environment, read as a Body value (`.absent` past the end). -/
def nthVal {D : Deklaration} : {Γ : Ctx} → Env D Γ → Nat → Gabbro.Body.Value
  | _, .nil, _ => .absent
  | τ :: _, .cons v _, 0 => valOf τ v
  | _ :: _, .cons _ ρ, j + 1 => nthVal ρ j

@[simp] theorem nthVal_cons_zero {D : Deklaration} {τ : Ty} {Γ : Ctx} (v : Wert D τ) (ρ : Env D Γ) :
    nthVal (Env.cons v ρ) 0 = valOf τ v := rfl

@[simp] theorem nthVal_cons_succ {D : Deklaration} {τ : Ty} {Γ : Ctx} (v : Wert D τ) (ρ : Env D Γ)
    (j : Nat) : nthVal (Env.cons v ρ) (j + 1) = nthVal ρ j := rfl

/-- **The variable the lowering resolves at position `j` reads as the `j`th entry.** -/
theorem nthVal_lowVar {D : Deklaration} : ∀ (Γ : Ctx) (j : Nat) (τ : Ty) (x : Var Γ τ)
    (ρ : Env D Γ), lowVar Γ j τ = .ok x → nthVal ρ j = valOf τ (ρ.get x)
  | [], _, _, _, _, h => by simp [lowVar] at h
  | σ :: Γ, 0, τ, x, ρ, h => by
      unfold lowVar at h
      split at h
      · rename_i hστ
        subst hστ
        have h' : (Except.ok Var.hier : Except String (Var (σ :: Γ) σ)) = .ok x := h
        simp only [Except.ok.injEq] at h'
        subst h'
        cases ρ with
        | cons v ρ' => rfl
      · simp at h
  | σ :: Γ, j + 1, τ, x, ρ, h => by
      unfold lowVar at h
      split at h
      · simp at h
      · rename_i y hy
        simp only [Except.ok.injEq] at h
        subst h
        cases ρ with
        | cons v ρ' => exact nthVal_lowVar Γ j τ y ρ' hy

/-- The position a variable sits at: what `lowVar` answers there is the variable. -/
theorem lowVar_typ : ∀ (Γ : Ctx) (j : Nat) (τ : Ty) (x : Var Γ τ),
    lowVar Γ j τ = .ok x → Γ[j]? = some τ
  | [], _, _, _, h => by simp [lowVar] at h
  | σ :: Γ, 0, τ, x, h => by
      unfold lowVar at h
      split at h
      · rename_i hστ; subst hστ; rfl
      · simp at h
  | σ :: Γ, j + 1, τ, x, h => by
      unfold lowVar at h
      split at h
      · simp at h
      · rename_i y hy
        exact lowVar_typ Γ j τ y hy

/-! ## 3. Lookups by name -/

theorem paramPos_lt : ∀ (ps : List (String × Ty)) (p : String) (j : Nat),
    paramPos ps p = .ok j → j < ps.length
  | [], _, _, h => by simp [paramPos] at h
  | (q, _) :: rest, p, j, h => by
      unfold paramPos at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; simp
      · split at h
        · simp at h
        · rename_i k hk
          simp only [Except.ok.injEq] at h
          subst h
          have := paramPos_lt rest p k hk
          simp; omega

theorem paramPos_name : ∀ (ps : List (String × Ty)) (p : String) (j : Nat),
    paramPos ps p = .ok j → ∃ τ, ps[j]? = some (p, τ)
  | [], _, _, h => by simp [paramPos] at h
  | (q, τ) :: rest, p, j, h => by
      unfold paramPos at h
      split at h
      · rename_i hq
        simp only [Except.ok.injEq] at h; subst h
        refine ⟨τ, ?_⟩
        have : q = p := by simpa using hq
        subst this; rfl
      · split at h
        · simp at h
        · rename_i k hk
          simp only [Except.ok.injEq] at h
          subst h
          exact paramPos_name rest p k hk

/-- `paramPos` finds the first entry with the name -- the entry `List.find?` finds. -/
theorem paramPos_find : ∀ (ps : List (String × Ty)) (p : String) (j : Nat),
    paramPos ps p = .ok j → ps.find? (fun q => q.1 == p) = ps[j]?
  | [], _, _, h => by simp [paramPos] at h
  | (q, τ) :: rest, p, j, h => by
      unfold paramPos at h
      split at h
      · rename_i hq
        simp only [Except.ok.injEq] at h; subst h
        simp [List.find?, hq]
      · rename_i hq
        split at h
        · simp at h
        · rename_i k hk
          simp only [Except.ok.injEq] at h
          subst h
          have hq' : (q == p) = false := by simpa using hq
          simp only [List.find?, hq']
          exact paramPos_find rest p k hk

/-- Where `paramPos` finds nothing, `List.find?` finds nothing. -/
theorem paramPos_find_none : ∀ (ps : List (String × Ty)) (p : String) (e : String),
    paramPos ps p = .error e → ps.find? (fun q => q.1 == p) = none
  | [], _, _, _ => rfl
  | (q, τ) :: rest, p, e, h => by
      unfold paramPos at h
      split at h
      · cases h
      · rename_i hq
        split at h
        · rename_i e' he'
          have hq' : (q == p) = false := by simpa using hq
          simp only [List.find?, hq']
          exact paramPos_find_none rest p e' he'
        · cases h

/-- Where the name sits at a position and nowhere earlier, `paramPos` finds it there. -/
theorem paramPos_of_nodup : ∀ (ps : List (String × Ty)) (j : Nat) (p : String) (τ : Ty),
    (ps.map (·.1)).Nodup → ps[j]? = some (p, τ) → paramPos ps p = .ok j
  | [], _, _, _, _, h => by simp at h
  | (q, σ) :: rest, 0, p, τ, _, h => by
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp [paramPos]
  | (q, σ) :: rest, j + 1, p, τ, hn, h => by
      simp only [List.map_cons, List.nodup_cons] at hn
      have hj : rest[j]? = some (p, τ) := by simpa using h
      have hqp : (q == p) = false := by
        have hm : p ∈ rest.map (·.1) := by
          rw [List.mem_map]
          exact ⟨(p, τ), List.mem_of_getElem? hj, rfl⟩
        have : q ≠ p := fun e => hn.1 (e ▸ hm)
        simpa using this
      have ih := paramPos_of_nodup rest j p τ hn.2 hj
      simp [paramPos, hqp, ih]

/-- A found table carries the name it was found by. -/
theorem tabIdx_name : ∀ (ts : List UTab) (n : String) (t : Fin ts.length),
    tabIdx ts n = .ok t → (ts.get t).name = n
  | [], _, _, h => by simp [tabIdx] at h
  | x :: rest, n, t, h => by
      unfold tabIdx at h
      split at h
      · rename_i hx
        simp only [Except.ok.injEq] at h; subst h
        simpa using hx
      · split at h
        · simp at h
        · rename_i j hj
          simp only [Except.ok.injEq] at h
          subst h
          exact tabIdx_name rest n j hj

theorem fnIdx_name : ∀ (fs : List UFn) (n : String) (f : Fin fs.length),
    fnIdx fs n = .ok f → (fs.get f).name = n
  | [], _, _, h => by simp [fnIdx] at h
  | x :: rest, n, f, h => by
      unfold fnIdx at h
      split at h
      · rename_i hx
        simp only [Except.ok.injEq] at h; subst h
        simpa using hx
      · split at h
        · simp at h
        · rename_i j hj
          simp only [Except.ok.injEq] at h
          subst h
          exact fnIdx_name rest n j hj

/-- `fnIdx` finds what `List.find?` finds. -/
theorem fnIdx_find : ∀ (fs : List UFn) (n : String) (f : Fin fs.length),
    fnIdx fs n = .ok f → fs.find? (fun g => g.name == n) = some (fs.get f)
  | [], _, _, h => by simp [fnIdx] at h
  | x :: rest, n, f, h => by
      unfold fnIdx at h
      split at h
      · rename_i hx
        simp only [Except.ok.injEq] at h; subst h
        simp [List.find?, hx]
      · rename_i hx
        split at h
        · simp at h
        · rename_i j hj
          simp only [Except.ok.injEq] at h
          subst h
          have hx' : (x.name == n) = false := by simpa using hx
          simp only [List.find?, hx']
          exact fnIdx_find rest n j hj

/-- A found field carries the name it was found by, and the lowering's range. -/
theorem fieldAtPos_find : ∀ (fs : List (String × (Int × Int))) (n : String),
    fieldAtPos fs n = (fs.find? (fun q => q.1 == n)).map (·.2)
  | [], _ => rfl
  | (m, w) :: rest, n => by
      unfold fieldAtPos
      by_cases h : (m == n) = true
      · simp [List.find?, h]
      · have h' : (m == n) = false := by simpa using h
        simp only [List.find?, h']
        exact fieldAtPos_find rest n

/-- The field `fieldHit` finds carries the name it was found by. -/
theorem fieldAtPos_name : ∀ (fs : List (String × (Int × Int))) (n : String) (w : Int × Int),
    fieldAtPos fs n = some w → (fs[fieldPos fs n]?).map (·.1) = some n
  | [], _, _, h => by simp [fieldAtPos] at h
  | (m, v) :: rest, n, w, h => by
      unfold fieldAtPos at h
      unfold fieldPos
      by_cases hm : (m == n) = true
      · simp only [hm, ↓reduceIte]
        simpa using hm
      · have hm' : (m == n) = false := by simpa using hm
        simp only [hm'] at h ⊢
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact fieldAtPos_name rest n w h

theorem fieldHit_name (u : UProg) (t : Fin u.tabellen.length) (fld : String) (fh : FieldHit u t)
    (h : fieldHit u t fld = .ok fh) : ((tabAt u t).felder[fh.idx.val]?).map (·.1) = some fld := by
  unfold fieldHit at h
  split at h
  · cases h
  · rename_i w hw
    cases h
    exact fieldAtPos_name _ _ _ hw

/-! ## 4. Worlds, through the declaration's names -/

variable (u : UProg)

/-- The Body value a G world holds at the Body place `.slot c k fld`: the slot of the table the
    lowering finds by `c`, at the field it finds by `fld`. `none` = the name pair names nothing
    in the declaration. -/
def slotWert (σ : World (declOf u)) (c : String) (k : Int) (fld : String) :
    Option Gabbro.Body.Value :=
  match tabIdx u.tabellen c with
  | .ok t =>
    match fieldHit u t fld with
    | .ok fh => some (valOf ((declOf u).typ t fh.idx) (σ.slots t k fh.idx))
    | .error _ => none
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

/-- Every declared field holds a number in its recorded range. -/
theorem valOf_feld (t : Fin u.tabellen.length) (fh : FieldHit u t) (x : Wert (declOf u) ((declOf u).typ t fh.idx)) :
    ∃ n, valOf ((declOf u).typ t fh.idx) x = .int n ∧ fh.weit.1 ≤ n ∧ n ≤ fh.weit.2 := by
  have h : (declOf u).typ t fh.idx = .int fh.weit.1 fh.weit.2 := typAt_of u t fh.idx fh.weit fh.hit
  revert x
  rw [h]
  intro x
  exact ⟨(x : Zahl _ _).n, rfl, x.lo_le, x.le_hi⟩

/-- **A slot write keeps the world relation**: the G write at the found slot and the Body write
    at the named place. Two Body places that decode to one G slot are one place (the lookups
    find a table and a field by the name they carry). -/
theorem wrel_store {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w)
    (c : String) (t : Fin u.tabellen.length) (ht : tabIdx u.tabellen c = .ok t)
    (fld : String) (fh : FieldHit u t) (hf : fieldHit u t fld = .ok fh) (k : Int)
    (x : Wert (declOf u) ((declOf u).typ t fh.idx)) :
    WRel u (σ.storeSlot t k fh.idx x)
      (Gabbro.Body.store w (.slot c k fld) (valOf ((declOf u).typ t fh.idx) x)) := by
  intro c' k' fld' v hv
  unfold slotWert at hv
  split at hv
  · rename_i t' ht'
    split at hv
    · rename_i fh' hf'
      cases hv
      by_cases hp : (Gabbro.Body.Place.slot c' k' fld') = .slot c k fld
      · simp only [Gabbro.Body.Place.slot.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        rw [ht] at ht'
        cases ht'
        rw [hf] at hf'
        cases hf'
        rw [Gabbro.Body.store_here]
        congr 1
        exact (storeSlot_hit (D := declOf u) σ _ _ _ x).symm
      · rw [Gabbro.Body.store_elsewhere _ _ _ _ hp]
        have hold := hW c' k' fld' (valOf _ (σ.slots t' k' fh'.idx)) (by simp only [slotWert, ht', hf'])
        rw [hold]
        congr 1
        by_cases htt : t' = t
        · subst htt
          by_cases hkk : k' = k
          · subst hkk
            have hff : fh'.idx ≠ fh.idx := by
              intro e
              apply hp
              have n1 := tabIdx_name _ _ _ ht
              have n2 := tabIdx_name _ _ _ ht'
              have m1 := fieldHit_name u t' fld fh hf
              have m2 := fieldHit_name u t' fld' fh' hf'
              rw [e] at m2
              rw [m1] at m2
              simp only [Option.some.injEq] at m2
              rw [← n1, n2, m2]
            exact (storeSlot_fremd_feld (D := declOf u) σ t' k' fh.idx x k' fh'.idx rfl hff).symm
          · simp [World.storeSlot, hkk]
        · exact (storeSlot_andere (D := declOf u) σ t k fh.idx x t' htt k' fh'.idx).symm
    · cases hv
  · cases hv

theorem wrel_lies_k {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w)
    (c : String) (t : Fin u.tabellen.length) (ht : tabIdx u.tabellen c = .ok t)
    (fld : String) (fh : FieldHit u t) (hf : fieldHit u t fld = .ok fh) (k : Int) :
    w (.slot c k fld) = valOf ((declOf u).typ t fh.idx) (σ.slots t k fh.idx) := by
  apply hW
  simp only [slotWert, ht, hf]

/-- The typing `Pflichten.shapeOfU` reads is the lowering's: the first table by the name, the
    first field by the name. -/
theorem slotShape_tabIdx : ∀ (ts : List UTab) (c fld : String) (sh : Gabbro.Body.Shape),
    slotShape ts c fld = some sh → ∃ t : Fin ts.length, tabIdx ts c = .ok t ∧
      ((ts.get t).felder.find? (fun q => q.1 == fld)).map (fun q => Gabbro.Body.Shape.intIn q.2.1 q.2.2) = some sh
  | [], _, _, _, h => by simp [slotShape] at h
  | x :: rest, c, fld, sh, h => by
      unfold slotShape at h
      split at h
      · rename_i hc
        refine ⟨0, ?_, ?_⟩
        · simp [tabIdx, hc]
        · simpa using h
      · rename_i hc
        obtain ⟨t, ht, hf⟩ := slotShape_tabIdx rest c fld sh h
        refine ⟨t.succ, ?_, ?_⟩
        · have hc' : (x.name == c) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hc e.symm
          simp [tabIdx, hc', ht]
        · simpa using hf

theorem fieldHit_of (t : Fin u.tabellen.length) (fld : String) (w : Int × Int)
    (h : fieldAtPos (tabAt u t).felder fld = some w) : ∃ fh, fieldHit u t fld = .ok fh ∧ fh.weit = w := by
  unfold fieldHit
  split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i w' h'
    rw [h] at h'
    cases h'
    exact ⟨_, rfl, rfl⟩

/-- **A related world is well-typed** (the duty file's `wellFormed`, hypothesis `U2`). -/
theorem wf_of_wrel {σ : World (declOf u)} {w : Gabbro.Body.World} (hW : WRel u σ w) :
    Gabbro.Body.WF (shapeOfU u) w := by
  intro p sh hp
  cases p with
  | slot c k fld =>
    obtain ⟨t, ht, hf⟩ := slotShape_tabIdx u.tabellen c fld sh hp
    cases hq : (u.tabellen.get t).felder.find? (fun q => q.1 == fld) with
    | none => rw [hq] at hf; cases hf
    | some q =>
      rw [hq] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      subst hf
      have hfa : fieldAtPos (tabAt u t).felder fld = some q.2 := by
        rw [fieldAtPos_find]; simp only [tabAt]; rw [hq]; rfl
      obtain ⟨fh, hfh, hw⟩ := fieldHit_of u t fld q.2 hfa
      rw [wrel_lies_k u hW c t ht fld fh hfh k]
      obtain ⟨n, hn, hlo, hhi⟩ := valOf_feld u t fh (σ.slots t k fh.idx)
      rw [hn, ← hw]
      simp [hlo, hhi]
  | field c n => simp [shapeOfU] at hp
  | global n => simp [shapeOfU] at hp

/-! ## 5. Transport along type equations -/

/-- What `rw … ; exact b` builds is `b` up to `HEq`. -/
theorem mpr_heq {α β : Sort _} (h : α = β) (b : β) : HEq (Eq.mpr h b) b := by
  subst h; rfl

theorem mp_heq {α β : Sort _} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
  subst h; rfl

theorem mpr3id_heq {α β γ δ : Sort _} (h1 : α = β) (h2 : β = γ) (h3 : γ = δ) (x : δ) :
    HEq (Eq.mpr h1 (Eq.mpr h2 (Eq.mpr h3 (id x)))) x := by
  subst h1; subst h2; subst h3; rfl

theorem mpr2_heq {α β γ : Sort _} (h1 : α = β) (h2 : β = γ) (x : γ) :
    HEq (id (Eq.mpr h1 (Eq.mpr h2 x))) x := by
  subst h1; subst h2; rfl

theorem eval_heq {D : Deklaration} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} {τ₁ τ₂ : Ty}
    (hΛ : Λ₁ = Λ₂) (hτ : τ₁ = τ₂)
    (e₁ : Expr D Γ Λ₁ τ₁) (e₂ : Expr D Γ Λ₂ τ₂) (he : HEq e₁ e₂)
    (σ₀ σ : World D) (ρ : Env D Γ) : HEq (eval σ₀ e₁ σ ρ) (eval σ₀ e₂ σ ρ) := by
  subst hΛ; subst hτ; cases he; rfl

theorem orte_heq {D : Deklaration} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} {τ₁ τ₂ : Ty}
    (hΛ : Λ₁ = Λ₂) (hτ : τ₁ = τ₂)
    (e₁ : Expr D Γ Λ₁ τ₁) (e₂ : Expr D Γ Λ₂ τ₂) (he : HEq e₁ e₂) : e₁.orte = e₂.orte := by
  subst hΛ; subst hτ; cases he; rfl

/-- The value of a transported term, read as a Body value, is the value of the term. -/
theorem valOf_eval_heq {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ₁ τ₂ : Ty}
    (hτ : τ₁ = τ₂) (e₁ : Expr D Γ Λ τ₁) (e₂ : Expr D Γ Λ τ₂) (he : HEq e₁ e₂)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    valOf τ₁ (eval σ₀ e₁ σ ρ) = valOf τ₂ (eval σ₀ e₂ σ ρ) :=
  valOf_heq hτ _ _ (eval_heq rfl hτ e₁ e₂ he σ₀ σ ρ)

end Gabbro.Bruecke
