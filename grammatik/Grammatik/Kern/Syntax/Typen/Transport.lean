module

public import Grammatik.Kern.Syntax.Typen.Teil1
      (Val.relocate_restrictSum sn tn forward backward hright cs
        ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, v⟩)
termination_by cs _ => sizeOf cs

/-- The right inverse also preserves whole product values, field by field. -/
theorem ProdVal.relocate_restrict : ∀ (fs : List Ty)
    (v : ProdVal F' p' (Ty.mapFields sn tn fs)),
    ProdVal.relocate sn tn forward fs (ProdVal.restrict sn tn backward fs v) = v
  | [], _ => rfl
  | τ :: τs, v => ProdVal.pcons_congr
      (Val.relocate_restrict sn tn forward backward hright τ v.1)
      (ProdVal.relocate_restrict τs v.2)
termination_by fs _ => sizeOf fs
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
