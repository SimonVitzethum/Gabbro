/-
  File:      Grammatik/X86/BitScan.lean
  Subject:   Zero-aware bit-scan helpers over the canonical fixed-width word.

  Lane 418 (continuous proof reserve): BSF/BSR-style least/greatest set-bit
  search over `trunc b w` (the canonical operand-size value from
  `Grammatik/X86/Wort.lean`), with NO fabricated result on zero input
  (`none`, plus an explicit ZF-style zero flag and an unconstrained
  destination). Reuses `Breite`/`Wort`/`Flags`-free `trunc` and `Speicher`
  (`write64`/`read64`) only; no new word/register/state types, no `Befehl`
  form, no `schritt` change. Consumer: the future performance profile's
  bit-test/loop lowering (one validated scan shape, never a silent `0`).

  No source correspondence, encoding, TSO bridge, cost transfer or native
  acceptance is claimed here; see CUTS at the end of this file.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- A set bit of the width-truncated operand: bit `i` of `trunc b w`. -/
def bitGesetzt (b : Breite) (w : Wort) (i : Nat) : Bool :=
  (trunc b w).toNat.testBit i

/-- Ascending fuel search for the least set bit at/above `s`. -/
def bsfVon : Nat → Nat → Nat → Option Nat
  | _, _, 0 => none
  | v, s, f + 1 => if v.testBit s then some s else bsfVon v (s + 1) f

/-- Least set-bit index of the truncated operand (`none` on zero input). -/
def bsfIdx (b : Breite) (w : Wort) : Option Nat :=
  bsfVon (trunc b w).toNat 0 b.bits

/-- Descending fuel search for the greatest set bit at/below `s`. -/
def bsrVon : Nat → Nat → Nat → Option Nat
  | _, _, 0 => none
  | v, s, f + 1 => if v.testBit s then some s else bsrVon v (s - 1) f

/-- Greatest set-bit index of the truncated operand (`none` on zero). -/
def bsrIdx (b : Breite) (w : Wort) : Option Nat :=
  match b with
  | .b8 => bsrVon (trunc b w).toNat 7 8
  | .b16 => bsrVon (trunc b w).toNat 15 16
  | .b32 => bsrVon (trunc b w).toNat 31 32
  | .b64 => bsrVon (trunc b w).toNat 63 64

/- CUTS (skeleton):
   Range/bit/minimality/zero-flag/destination lemmas, boundary probes and
   the memory witness are open. No encoding/source/TSO/cost/native claim.
-/
