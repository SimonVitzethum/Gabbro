import Grammatik.Bausteine.Gleitkomma.Gleitkomma

/-
  File:      Grammatik/Code/Model/Types.lean
  Subject:   TRACK L -- `Code`: THE TARGET-INDEPENDENT LOW-LEVEL LANGUAGE, types and values.
             `Code` is the language machine G is lowered to before any CPU model enters
             (`dokumente/PLAN-TRANSLATION-VALIDATION.md` section 9a). It is NOT LLVM: no metadata, no
             attributes, no inline assembly. It keeps what every CPU has -- word-sized locals,
             byte memory, wraparound arithmetic at an explicit width, compare-and-branch,
             call/return, atomics with orderings -- and nothing the ISAs disagree on
             (`Conf`: word width and byte order are PARAMETERS). Names are short English words
             (at most five letters per word).

  WHAT IS HERE
    `Ty`      -- iN, float, double, ptr, arrays, structs, void. A struct is a CHAIN of field
                 types (`fld t rest`, ended by `unit`): one non-nested inductive, so decidable
                 equality needs no mutual recursion, and the layout is a plain left-to-right
                 walk. `{ i16, i32 }` is `fld (int 16) (fld (int 32) unit)`.
    layout    -- `Ty.align`, `Ty.size` (the ALLOC size), `Ty.store` (the bytes a load or store
                 touches), `Ty.fieldOff`, `Ty.gepOff`: natural alignment (an integer is aligned
                 to its size up to twice the word, a pointer to the word, `double` to 8).
    `Val`     -- an integer of width `w` is a `BitVec w`; floats are bit-exact values of the
                 kernel IEEE model (`Gleitkomma`, binary32 and binary64); a pointer is a
                 BLOCK and a byte offset (block-structured memory, `Memory.lean`), so two
                 distinct allocations never alias by construction.

  NAMED CUTS (also in `PLAN-TRANSLATION-VALIDATION.md` 9a)
    * no first-class aggregate values: aggregates live in memory and are reached by `gep`;
    * no integer to pointer conversion (device bases and region answers are L4);
    * every block is aligned to twice the word, so an alignment check is a check on the offset.
-/

namespace Gabbro.Code

open Gabbro.Grammatik.Gleitkomma

/-- **The target parameters.** Word width (32 or 64 bits) and byte order. Everything in `Code`
    that depends on them takes `[Conf]`; nothing is fixed to one ISA. -/
class Conf where
  wbits : Nat
  big : Bool
  wide : wbits = 32 ∨ wbits = 64

namespace Conf

/-- The word in bytes. -/
def wb [Conf] : Nat := wbits / 8

theorem wb_pos [c : Conf] : 0 < wb := by
  unfold wb; rcases c.wide with h | h <;> rw [h] <;> decide

end Conf

/-- The types of the subset. -/
inductive Ty where
  | int (w : Nat)
  | flt
  | dbl
  | ptr
  | void
  | arr (n : Nat) (t : Ty)
  /-- A struct as a chain of fields: `fld t rest` is a struct whose first field is `t` and
      whose remaining fields are the chain `rest`; `unit` is `{}`. -/
  | fld (t : Ty) (rest : Ty)
  | unit
  deriving DecidableEq, Repr

namespace Ty

variable [Conf]

/-- Natural alignment in bytes of an integer of width `w`: its size, up to twice the word. -/
def intAlign (w : Nat) : Nat :=
  let b := (w + 7) / 8
  min (if b ≤ 1 then 1 else if b ≤ 2 then 2 else if b ≤ 4 then 4 else if b ≤ 8 then 8 else 16)
    (2 * Conf.wb)

/-- ABI alignment. -/
def align : Ty → Nat
  | int w => intAlign w
  | flt => 4
  | dbl => 8
  | ptr => Conf.wb
  | void => 1
  | arr _ t => align t
  | fld t r => max (align t) (align r)
  | unit => 1

/-- Round `o` up to a multiple of `a` (`a > 0`). -/
def roundUp (o a : Nat) : Nat := (o + a - 1) / a * a

mutual
/-- The alloc size: what an array element or a struct field of this type occupies. -/
def size : Ty → Nat
  | int w => roundUp ((w + 7) / 8) (intAlign w)
  | flt => 4
  | dbl => 8
  | ptr => Conf.wb
  | void => 0
  | arr n t => n * size t
  | unit => 0
  | fld t r => roundUp (endOff r (size t)) (max (align t) (align r))
/-- The end offset of the chain `r` when its first field starts at offset `o`. -/
def endOff : Ty → Nat → Nat
  | fld t r, o => endOff r (roundUp o (align t) + size t)
  | _, o => o
end

/-- The bytes a `load` or `store` of this type touches (`iN` stores `ceil(N/8)` bytes). -/
def store : Ty → Nat
  | int w => (w + 7) / 8
  | flt => 4
  | dbl => 8
  | ptr => Conf.wb
  | t => size t

/-- Is it a scalar -- a type a `load` or a `store` carries. -/
def scalar : Ty → Bool
  | int _ | flt | dbl | ptr => true
  | _ => false

/-- The byte offset of field number `i` of the chain `t`, starting at offset `o`;
    `none` if the chain has no such field. -/
def fieldOff : Ty → Nat → Nat → Option (Nat × Ty)
  | fld t _, 0, o => some (roundUp o (align t), t)
  | fld t r, i + 1, o => fieldOff r i (roundUp o (align t) + size t)
  | _, _, _ => none

/-- The byte offset and the type reached by the indices of a `gep` AFTER the first one
    (the first one steps over whole `t`s and is applied by the caller). -/
def gepIn : Ty → List Int → Option (Int × Ty)
  | t, [] => some (0, t)
  | arr _ t, i :: is =>
      match gepIn t is with
      | some (o, u) => some (i * (size t : Int) + o, u)
      | none => none
  | fld t r, i :: is =>
      if 0 ≤ i then
        match fieldOff (fld t r) i.toNat 0 with
        | some (o, u) => (gepIn u is).map fun p => ((o : Int) + p.1, p.2)
        | none => none
      else none
  | _, _ :: _ => none

/-- The offset of `gep t, p, i0, i1, ...`: the first index scales by `size t`. -/
def gepOff (t : Ty) : List Int → Option (Int × Ty)
  | [] => none
  | i :: is => (gepIn t is).map fun p => (i * (size t : Int) + p.1, p.2)

end Ty

/-- The float formats `flt` and `dbl` are the kernel IEEE model's binary32 and binary64. -/
abbrev F32 := GBits f32
abbrev F64 := GBits f64

/-- The values of the subset. -/
inductive Val where
  | int (w : Nat) (v : BitVec w)
  | flt (g : F32)
  | dbl (g : F64)
  /-- A pointer: allocation block and byte offset in it. -/
  | ptr (b : Nat) (o : Int)
  deriving DecidableEq

namespace Val

/-- The type a value has. -/
def ty : Val → Ty
  | int w _ => .int w
  | flt _ => .flt
  | dbl _ => .dbl
  | ptr _ _ => .ptr

/-- `i1` true / false. -/
def bool (b : Bool) : Val := .int 1 (if b then 1 else 0)

/-- An `iW` constant from an integer (two's complement). -/
def ofInt (w : Nat) (n : Int) : Val := .int w (BitVec.ofInt w n)

end Val

end Gabbro.Code
