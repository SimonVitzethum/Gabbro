module

public import Init.Data.String.Basic
public import Init.Data.Array.Basic
public import Init.SizeOfLemmas

@[expose] public section
namespace Gabbro.Grammatik.Parser.Size

/-- A native realization of the existing kernel size, with its exact certificate. -/
abbrev Exact (α : Type) [SizeOf α] := (value : α) → { n : Nat // n = sizeOf value }

@[no_expose] def nat (value : Nat) : { n : Nat // n = sizeOf value } :=
  ⟨value, rfl⟩

@[no_expose] def bool (value : Bool) : { n : Nat // n = sizeOf value } :=
  ⟨1, by cases value <;> rfl⟩

/-- The three wrappers are UInt8, BitVec and Fin; the payload is the native byte. -/
@[no_expose] def byte (value : UInt8) : { n : Nat // n = sizeOf value } :=
  ⟨1 + (1 + (1 + value.toNat)), by
    cases value with
    | ofBitVec bits =>
      cases bits with
      | ofFin bits => cases bits; rfl⟩

@[no_expose] def bytes : Exact (List UInt8)
  | [] => ⟨1, rfl⟩
  | value :: rest =>
    let head := byte value
    let tail := bytes rest
    ⟨1 + head.val + tail.val, by
      simp only [List.cons.sizeOf_spec, head.property, tail.property]⟩

/-- Native byte/array conversions retain the complete UTF-8 representation. The
    three outer wrappers are String, ByteArray and Array, including empty data. -/
@[no_expose] def string (value : String) : { n : Nat // n = sizeOf value } :=
  let data := bytes value.toByteArray.data.toList
  ⟨1 + (1 + (1 + data.val)), by
    rw [data.property]
    cases value with
    | ofByteArray value valid =>
      cases value with
      | mk value => cases value; rfl⟩

end Gabbro.Grammatik.Parser.Size
