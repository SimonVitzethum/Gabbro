/-
  Checked stack frames and ABI memory obligations (lane 309).

  Frame extents, 16-byte call-boundary alignment, spill/callee-save/stack-arg
  layout and argument/result carriage over the canonical `Speicher` of
  `Grammatik.X86.Typen`/`Speicher`, using the shared `write64`/`read64`.
  No second register, instruction or memory model is created here; `schritt`
  semantics is never duplicated. Callee-save/entry contracts and external
  ABI byte correspondence stay OPEN (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- A checked stack frame: byte base plus depth, over canonical addresses. -/
structure Rahmen where
  basis : Nat
  tiefe : Nat
  deriving DecidableEq, Repr

/-- Top (post-frame) address as a natural number. -/
def Rahmen.spitzeNat (r : Rahmen) : Nat := r.basis + r.tiefe

/-- Word-slot count of a frame. -/
def Rahmen.schlitzZahl (r : Rahmen) : Nat := r.tiefe / 8

/-- Byte address of word slot `idx`, as a natural number. -/
def Rahmen.schlitzNat (r : Rahmen) (idx : Nat) : Nat := r.basis + idx * 8

/-- Byte address of word slot `idx` as a machine address. -/
def Rahmen.schlitzAddr (r : Rahmen) (idx : Nat) : Adresse :=
  BitVec.ofNat 64 (r.schlitzNat idx)

/-- Frame top as a machine word (the call-boundary stack pointer). -/
def Rahmen.spitzeWort (r : Rahmen) : Wort :=
  BitVec.ofNat 64 r.spitzeNat

/-- 16-byte call-boundary alignment of a machine address. -/
def ausgerichtet16 (a : Adresse) : Bool := decide (a.toNat % 16 = 0)

/- CUTS:
    - No instruction semantics, decoder, image mapping, TSO bridge, source
      correspondence, cost transfer or final-image acceptance is proved here.
    - Callee-save/entry contracts and external ABI byte correspondence are
      OPEN: this file states checked memory obligations only.
    - No Linux-specific mechanism: no stack sizes, guard pages, clone flags
      or syscall numbers appear here.
-/

end Gabbro.Grammatik.X86
