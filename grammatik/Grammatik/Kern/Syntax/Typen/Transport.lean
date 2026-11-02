module

public import Grammatik.Kern.Syntax.Typen.Teil1
public import Grammatik.Kern.Syntax.Typen.Fall
public import Grammatik.Kern.Syntax.Typen.Produkt

@[expose] public section

namespace Gabbro.Grammatik

mutual
/-- Rename signature and table identities recursively through every payload. -/
def Ty.mapNumbers (sn tn : Nat → Nat) : Ty → Ty
  | .int lo hi => .int lo hi
  | .bool => .bool
  | .opt n => .opt n
  | .sum cs => .sum (Ty.mapCases sn tn cs)
  | .why n => .why n
  | .never => .never
  | .fl lo hi => .fl lo hi
  | .fnptr n => .fnptr (sn n)
  | .ptr ⟨space, rights, .table n⟩ => .ptr ⟨space, rights, .table (tn n)⟩
  | .ref n => .ref (tn n)
  | .arr τ n => .arr (Ty.mapNumbers sn tn τ) n
  | .str n => .str n
  | .prod name fs => .prod name (Ty.mapFields sn tn fs)

/-- The same traversal on case lists; order and payload presence are preserved. -/
def Ty.mapCases (sn tn : Nat → Nat) : List (Option Ty) → List (Option Ty)
  | [] => []
  | none :: cs => none :: Ty.mapCases sn tn cs
  | some τ :: cs => some (Ty.mapNumbers sn tn τ) :: Ty.mapCases sn tn cs

/-- The same traversal on field lists; order is preserved. -/
def Ty.mapFields (sn tn : Nat → Nat) : List Ty → List Ty
  | [] => []
  | τ :: τs => Ty.mapNumbers sn tn τ :: Ty.mapFields sn tn τs
end

@[simp] theorem Ty.mapFields_length (sn tn : Nat → Nat) (fs : List Ty) :
    (Ty.mapFields sn tn fs).length = fs.length := by
  induction fs with
  | nil => rfl
  | cons τ τs ih => simp only [Ty.mapFields, List.length_cons, ih]

/-- A field position transported along the identity renaming of its list. -/
def FieldAt.mapNumbers (sn tn : Nat → Nat) : {fs : List Ty} → {σ : Ty} → FieldAt fs σ →
    FieldAt (Ty.mapFields sn tn fs) (Ty.mapNumbers sn tn σ)
  | _, _, .head => .head
  | _, _, .tail i => .tail (FieldAt.mapNumbers sn tn i)

@[simp] theorem Ty.mapCases_length (sn tn : Nat → Nat) (cs : List (Option Ty)) :
    (Ty.mapCases sn tn cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [Ty.mapCases, List.length_cons, ih]

mutual
@[simp] theorem Ty.mapNumbers_id : ∀ τ : Ty, Ty.mapNumbers id id τ = τ
  | .int _ _ | .bool | .opt _ | .why _ | .never | .fl _ _ | .fnptr _ | .ref _ | .str _ => rfl
  | .ptr ⟨space, rights, .table n⟩ => rfl
  | .sum cs => congrArg Ty.sum (Ty.mapCases_id cs)
  | .arr τ n => congrArg (fun t => Ty.arr t n) (Ty.mapNumbers_id τ)
  | .prod name fs => congrArg (Ty.prod name) (Ty.mapFields_id fs)

@[simp] theorem Ty.mapCases_id : ∀ cs : List (Option Ty), Ty.mapCases id id cs = cs
  | [] => rfl
  | none :: cs => congrArg (none :: ·) (Ty.mapCases_id cs)
  | some τ :: cs => by
    simp only [Ty.mapCases, Ty.mapNumbers_id τ, Ty.mapCases_id cs]

@[simp] theorem Ty.mapFields_id : ∀ fs : List Ty, Ty.mapFields id id fs = fs
  | [] => rfl
  | τ :: τs => by simp only [Ty.mapFields, Ty.mapNumbers_id τ, Ty.mapFields_id τs]
end

/-- Select the same complete payload after renaming declaration identities. -/
theorem Ty.mapCases_get (sn tn : Nat → Nat) (cs : List (Option Ty)) (i : Fin cs.length) :
    (Ty.mapCases sn tn cs).get ⟨i.val, by rw [Ty.mapCases_length]; exact i.isLt⟩ =
      (cs.get i).map (Ty.mapNumbers sn tn) := by
  induction cs with
  | nil => exact i.elim0
  | cons c cs ih =>
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero => cases c <;> rfl
    | succ i => cases c <;> exact ih ⟨i, Nat.lt_of_succ_lt_succ hi⟩

mutual
/-- Transport values with one signature-aware function-pointer map. Aggregate
    payloads share that map; references retain their cell and renamed region type. -/
def Val.relocate {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true}) :
    (τ : Ty) → Val F p τ → Val F' p' (Ty.mapNumbers sn tn τ)
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum cs, v => Val.relocateSum sn tn pointer cs v
  | .why _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr n, v => pointer n v
  | .ptr _, v => v
  | .ref _, v => v
  | .arr τ _, v => fun i => Val.relocate sn tn pointer τ (v i)
  | .str _, v => v
  | .prod _ fs, v => ProdVal.relocate sn tn pointer fs v

/-- Transport the selected case, retaining exactly its tag and full payload. -/
def Val.relocateSum {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true}) :
    (cs : List (Option Ty)) → Val F p (.sum cs) →
      Val F' p' (.sum (Ty.mapCases sn tn cs))
  | [], ⟨i, _⟩ => i.elim0
  | none :: _, ⟨⟨0, _⟩, v⟩ => ⟨⟨0, by simp only [Ty.mapCases, List.length_cons]; omega⟩, v⟩
  | some τ :: _, ⟨⟨0, _⟩, v⟩ =>
    ⟨⟨0, by simp only [Ty.mapCases, List.length_cons]; omega⟩, Val.relocate sn tn pointer τ v⟩
  | none :: cs, ⟨⟨i + 1, hi⟩, v⟩ =>
    let tail := Val.relocateSum sn tn pointer cs ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩
    ⟨tail.1.succ, tail.2⟩
  | some _ :: cs, ⟨⟨i + 1, hi⟩, v⟩ =>
    let tail := Val.relocateSum sn tn pointer cs ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩
    ⟨tail.1.succ, tail.2⟩

/-- Transport a whole product value field by field under the same map. -/
def ProdVal.relocate {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true}) :
    (fs : List Ty) → ProdVal F p fs → ProdVal F' p' (Ty.mapFields sn tn fs)
  | [], _ => ()
  | τ :: τs, v => (Val.relocate sn tn pointer τ v.1, ProdVal.relocate sn tn pointer τs v.2)
end

mutual
/-- Pull a value back along renamed types. The pointer callback may choose the
    representative for a signature, as the linking simulation already requires. -/
def Val.restrict {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F' // p' f (sn n) = true} → {f : F // p f n = true}) :
    (τ : Ty) → Val F' p' (Ty.mapNumbers sn tn τ) → Val F p τ
  | .int _ _, v => v
  | .bool, v => v
  | .opt _, v => v
  | .sum cs, v => Val.restrictSum sn tn pointer cs v
  | .why _, v => v
  | .never, v => v
  | .fl _ _, v => v
  | .fnptr n, v => pointer n v
  | .ptr _, v => v
  | .ref _, v => v
  | .arr τ _, v => fun i => Val.restrict sn tn pointer τ (v i)
  | .str _, v => v
  | .prod _ fs, v => ProdVal.restrict sn tn pointer fs v

/-- Pull back the full active payload without inspecting inactive cases. -/
def Val.restrictSum {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F' // p' f (sn n) = true} → {f : F // p f n = true}) :
    (cs : List (Option Ty)) → Val F' p' (.sum (Ty.mapCases sn tn cs)) → Val F p (.sum cs)
  | [], ⟨i, _⟩ => i.elim0
  | none :: _, ⟨⟨0, _⟩, v⟩ => ⟨⟨0, by simp only [List.length_cons]; omega⟩, v⟩
  | some τ :: _, ⟨⟨0, _⟩, v⟩ =>
    ⟨⟨0, by simp only [List.length_cons]; omega⟩, Val.restrict sn tn pointer τ v⟩
  | none :: cs, ⟨⟨i + 1, hi⟩, v⟩ =>
    let tail := Val.restrictSum sn tn pointer cs ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩
    ⟨tail.1.succ, tail.2⟩
  | some _ :: cs, ⟨⟨i + 1, hi⟩, v⟩ =>
    let tail := Val.restrictSum sn tn pointer cs ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩
    ⟨tail.1.succ, tail.2⟩

/-- Pull a whole product value back field by field. -/
def ProdVal.restrict {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F' // p' f (sn n) = true} → {f : F // p f n = true}) :
    (fs : List Ty) → ProdVal F' p' (Ty.mapFields sn tn fs) → ProdVal F p fs
  | [], _ => ()
  | τ :: τs, v => (Val.restrict sn tn pointer τ v.1, ProdVal.restrict sn tn pointer τs v.2)
end

/-- Transport commutes with field reads: reading after transport is transport after reading. -/
theorem ProdVal.relocate_get {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true}) :
    ∀ (fs : List Ty) {σ : Ty} (i : FieldAt fs σ) (v : ProdVal F p fs),
      prodGetW (FieldAt.mapNumbers sn tn i) (ProdVal.relocate sn tn pointer fs v) =
        Val.relocate sn tn pointer σ (prodGetW i v)
  | _, _, .head, _ => rfl
  | _, _, .tail i, v => ProdVal.relocate_get sn tn pointer _ i v.2

/-- Transport commutes with field replacement. -/
theorem ProdVal.relocate_set {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true}) :
    ∀ (fs : List Ty) {σ : Ty} (i : FieldAt fs σ) (v : ProdVal F p fs) (x : Val F p σ),
      ProdVal.relocate sn tn pointer fs (prodSetW i v x) =
        prodSetW (FieldAt.mapNumbers sn tn i)
          (ProdVal.relocate sn tn pointer fs v) (Val.relocate sn tn pointer σ x)
  | _, _, .head, _, _ => rfl
  | _, _, .tail i, v, x => ProdVal.pcons_congr rfl
      (ProdVal.relocate_set sn tn pointer _ i v.2 x)

/-- Transport a complete optional payload under the same pointer map as its sum. -/
def Nutzlast.relocate {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true}) :
    (c : Option Ty) → Nutzlast F p c → Nutzlast F' p' (c.map (Ty.mapNumbers sn tn))
  | none, v => v
  | some τ, v => Val.relocate sn tn pointer τ v

/-- Relocation selects the same tag and transports precisely its active payload. -/
theorem Val.relocateSum_mk {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true}) :
    ∀ (cs : List (Option Ty)) (i : Fin cs.length) (v : Nutzlast F p (cs.get i)),
      Val.relocateSum sn tn pointer cs ⟨i, Fall.ofNutzlast F p cs i v⟩ =
        ⟨⟨i.val, by rw [Ty.mapCases_length]; exact i.isLt⟩,
          Fall.ofNutzlast F' p' _ _
            ((Ty.mapCases_get sn tn cs i).symm ▸ Nutzlast.relocate sn tn pointer (cs.get i) v)⟩
  | [], i, _ => i.elim0
  | none :: _, ⟨0, _⟩, _ => rfl
  | some _ :: _, ⟨0, _⟩, _ => rfl
  | none :: cs, ⟨i + 1, hi⟩, v =>
    congrArg (fun z : Val F' p' (.sum (Ty.mapCases sn tn cs)) =>
      (⟨z.1.succ, z.2⟩ : Val F' p' (.sum (none :: Ty.mapCases sn tn cs))))
      (Val.relocateSum_mk sn tn pointer cs ⟨i, Nat.lt_of_succ_lt_succ hi⟩ v)
  | some τ :: cs, ⟨i + 1, hi⟩, v =>
    congrArg (fun z : Val F' p' (.sum (Ty.mapCases sn tn cs)) =>
      (⟨z.1.succ, z.2⟩ : Val F' p' (.sum (some (Ty.mapNumbers sn tn τ) :: Ty.mapCases sn tn cs))))
      (Val.relocateSum_mk sn tn pointer cs ⟨i, Nat.lt_of_succ_lt_succ hi⟩ v)

/-- Restrict an optional payload through the same signature representatives. -/
def Nutzlast.restrict {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F' // p' f (sn n) = true} → {f : F // p f n = true}) :
    (c : Option Ty) → Nutzlast F' p' (c.map (Ty.mapNumbers sn tn)) → Nutzlast F p c
  | none, v => v
  | some τ, v => Val.restrict sn tn pointer τ v

/-- Restriction retains the tag and consumes exactly its complete mapped payload. -/
theorem Val.restrictSum_mk {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
    (sn tn : Nat → Nat)
    (pointer : ∀ n, {f : F' // p' f (sn n) = true} → {f : F // p f n = true}) :
    ∀ (cs : List (Option Ty)) (i : Fin cs.length)
      (v : Nutzlast F' p' ((cs.get i).map (Ty.mapNumbers sn tn))),
      Val.restrictSum sn tn pointer cs
        ⟨⟨i.val, by rw [Ty.mapCases_length]; exact i.isLt⟩,
          Fall.ofNutzlast F' p' _ _ ((Ty.mapCases_get sn tn cs i).symm ▸ v)⟩ =
        ⟨i, Fall.ofNutzlast F p cs i (Nutzlast.restrict sn tn pointer (cs.get i) v)⟩
  | [], i, _ => i.elim0
  | none :: _, ⟨0, _⟩, _ => rfl
  | some _ :: _, ⟨0, _⟩, _ => rfl
  | c :: cs, ⟨i + 1, hi⟩, v => by
    let lift (z : Val F p (.sum cs)) : Val F p (.sum (c :: cs)) := ⟨z.1.succ, z.2⟩
    cases c <;> exact congrArg lift
      (Val.restrictSum_mk sn tn pointer cs ⟨i, Nat.lt_of_succ_lt_succ hi⟩ v)

section Inverse
variable {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
  (sn tn : Nat → Nat)
  (forward : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true})
  (backward : ∀ n, {f : F' // p' f (sn n) = true} → {f : F // p f n = true})
  (hleft : ∀ n v, backward n (forward n v) = v)

include hleft in
mutual
/-- A signature-wise left inverse remains a left inverse through typed payloads. -/
theorem Val.restrict_relocate : ∀ (τ : Ty) (v : Val F p τ),
    Val.restrict sn tn backward τ (Val.relocate sn tn forward τ v) = v
  | .int _ _, _ | .bool, _ | .opt _, _ | .why _, _ | .never, _ | .fl _ _, _
  | .ptr _, _ | .ref _, _ | .str _, _ => rfl
  | .fnptr n, v => hleft n v
  | .arr τ _, v => funext fun i => Val.restrict_relocate τ (v i)
  | .sum cs, v => Val.restrict_relocateSum cs v
  | .prod _ fs, v => ProdVal.restrict_relocate fs v

/-- The inverse also preserves the complete active tag/payload pair. -/
theorem Val.restrict_relocateSum : ∀ (cs : List (Option Ty)) (v : Val F p (.sum cs)),
    Val.restrictSum sn tn backward cs (Val.relocateSum sn tn forward cs v) = v
  | [], ⟨i, _⟩ => i.elim0
  | none :: _, ⟨⟨0, _⟩, _⟩ => rfl
  | some τ :: cs, ⟨⟨0, h⟩, v⟩ =>
    congrArg (fun w => (⟨⟨0, h⟩, w⟩ : Val F p (.sum (some τ :: cs)))) (Val.restrict_relocate τ v)
  | none :: cs, ⟨⟨i + 1, hi⟩, v⟩ =>
    congrArg (fun z : Val F p (.sum cs) => (⟨z.1.succ, z.2⟩ : Val F p (.sum (none :: cs))))
      (Val.restrict_relocateSum cs ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩)
  | some τ :: cs, ⟨⟨i + 1, hi⟩, v⟩ =>
    congrArg (fun z : Val F p (.sum cs) => (⟨z.1.succ, z.2⟩ : Val F p (.sum (some τ :: cs))))
      (Val.restrict_relocateSum cs ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩)

/-- The left inverse also preserves whole product values, field by field. -/
theorem ProdVal.restrict_relocate : ∀ (fs : List Ty) (v : ProdVal F p fs),
    ProdVal.restrict sn tn backward fs (ProdVal.relocate sn tn forward fs v) = v
  | [], _ => rfl
  | τ :: τs, v => ProdVal.pcons_congr (Val.restrict_relocate τ v.1) (ProdVal.restrict_relocate τs v.2)
end

end Inverse

section RightInverse
variable {F F' : Type} {p : F → Nat → Bool} {p' : F' → Nat → Bool}
  (sn tn : Nat → Nat)
  (forward : ∀ n, {f : F // p f n = true} → {f : F' // p' f (sn n) = true})
  (backward : ∀ n, {f : F' // p' f (sn n) = true} → {f : F // p f n = true})
  (hright : ∀ n v, forward n (backward n v) = v)

include hright in
mutual
/-- A signature-wise right inverse also preserves nested tagged values. -/
theorem Val.relocate_restrict : ∀ (τ : Ty) (v : Val F' p' (Ty.mapNumbers sn tn τ)),
    Val.relocate sn tn forward τ (Val.restrict sn tn backward τ v) = v
  | .int _ _, _ | .bool, _ | .opt _, _ | .why _, _ | .never, _ | .fl _ _, _
  | .ptr _, _ | .ref _, _ | .str _, _ => rfl
  | .fnptr n, v => hright n v
  | .arr τ _, v => funext fun i => Val.relocate_restrict τ (v i)
  | .sum cs, v => Val.relocate_restrictSum cs v
  | .prod _ fs, v => ProdVal.relocate_restrict fs v

theorem Val.relocate_restrictSum : ∀ (cs : List (Option Ty))
    (v : Val F' p' (.sum (Ty.mapCases sn tn cs))),
    Val.relocateSum sn tn forward cs (Val.restrictSum sn tn backward cs v) = v
  | [], ⟨i, _⟩ => i.elim0
  | none :: _, ⟨⟨0, _⟩, _⟩ => rfl
  | some τ :: cs, ⟨⟨0, h⟩, v⟩ =>
    congrArg (fun w => (⟨⟨0, h⟩, w⟩ : Val F' p' (.sum (Ty.mapCases sn tn (some τ :: cs)))))
      (Val.relocate_restrict τ v)
  | none :: cs, ⟨⟨i + 1, hi⟩, v⟩ =>
    congrArg (fun z : Val F' p' (.sum (Ty.mapCases sn tn cs)) =>
      (⟨z.1.succ, z.2⟩ : Val F' p' (.sum (none :: Ty.mapCases sn tn cs))))
      (Val.relocate_restrictSum cs ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩)
  | some τ :: cs, ⟨⟨i + 1, hi⟩, v⟩ =>
    congrArg (fun z : Val F' p' (.sum (Ty.mapCases sn tn cs)) =>
      (⟨z.1.succ, z.2⟩ : Val F' p' (.sum (some (Ty.mapNumbers sn tn τ) :: Ty.mapCases sn tn cs))))
      (Val.relocate_restrictSum cs ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩)

/-- The right inverse also preserves whole product values, field by field. -/
theorem ProdVal.relocate_restrict : ∀ (fs : List Ty) (v : ProdVal F' p' (Ty.mapFields sn tn fs)),
    ProdVal.relocate sn tn forward fs (ProdVal.restrict sn tn backward fs v) = v
  | [], _ => rfl
  | τ :: τs, v => ProdVal.pcons_congr (Val.relocate_restrict τ v.1) (ProdVal.relocate_restrict τs v.2)
end

end RightInverse

namespace TypedPayloadTransport

/-- Every function fits every pointer type. -/
def allP : Bool → Nat → Bool := fun _ _ => true

def schema : Ty := .sum [some (.arr (.sum [none, some (.fnptr 3)]) 1)]
def value : Val Bool allP schema :=
  ⟨⟨0, by decide⟩, fun _ => ⟨⟨1, by decide⟩, ⟨true, rfl⟩⟩⟩

def forward (n : Nat) (v : {f : Bool // allP f n = true}) :
    {f : Bool // allP f (n + 1) = true} := ⟨v.1, rfl⟩
def backward (n : Nat) (v : {f : Bool // allP f (n + 1) = true}) :
    {f : Bool // allP f n = true} := ⟨v.1, rfl⟩

theorem restrict_relocate_zeuge :
    Val.restrict (fun n => n + 1) id backward schema
      (Val.relocate (fun n => n + 1) id forward schema value) = value :=
  Val.restrict_relocate (p := allP) (p' := allP)
    (fun n => n + 1) id forward backward (fun _ _ => rfl) schema value

theorem relocate_restrict_zeuge :
    Val.relocate (fun n => n + 1) id forward schema
      (Val.restrict (fun n => n + 1) id backward schema
        (Val.relocate (fun n => n + 1) id forward schema value)) =
      Val.relocate (fun n => n + 1) id forward schema value :=
  Val.relocate_restrict (p := allP) (p' := allP)
    (fun n => n + 1) id forward backward (fun _ _ => rfl) schema _

end TypedPayloadTransport

end Gabbro.Grammatik
