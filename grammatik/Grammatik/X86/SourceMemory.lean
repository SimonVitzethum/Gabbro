/-
  File:      Grammatik/X86/SourceMemory.lean
  Subject:   Source world/table values to target byte representation (lane 570).

  The ONE small generic representation interface between real source
  `Deklaration`/`World` table carriers and accepted `TableLayout`/`Speicher`
  bytes, for the bounded integer fragment (one `.int lo hi` slot stored as
  one little-endian 8-byte word). Source writes reuse the actual
  `execStmt` table-write operation (`World.schreibSlot`, unfolded by
  `execStmt_assignSlot`); target writes reuse `write64`/`read64`; checked
  premises reuse `repOk` (range/width/region) and `layoutOk`/`regionDisjunkt`.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Parser.Uebersetze
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze

/-- A source integer value as a target word: the (nonnegative) number as
    64 bits. Faithful exactly when `0 <= v.n` and `v.n < 2 ^ 64`
    (`zahlWort_wortZahl`); outside that the mapping is lossy by
    construction (`Int.toNat` clips negatives, `BitVec.ofNat` wraps). -/
def zahlWort {lo hi : Int} (v : Zahl lo hi) : Wort :=
  BitVec.ofNat 64 v.n.toNat

/-- A target word back as a source integer: `some` exactly when the
    unsigned value lies in `lo .. hi`. The `none` case is the checked
    out-of-range refusal of the interface. -/
def wortZahl (lo hi : Int) (w : Wort) : Option (Zahl lo hi) :=
  if h : lo ≤ Int.ofNat w.toNat ∧ Int.ofNat w.toNat ≤ hi then
    some ⟨Int.ofNat w.toNat, h.1, h.2⟩
  else none

/-- ROUNDTRIP: a source value in a nonnegative range below `2 ^ 64`
    survives the word mapping. Uses both bounds: `hLo` for the `toNat`
    inversion, `hHi` for the `ofNat` modulo identity. -/
theorem zahlWort_wortZahl {lo hi : Int} (v : Zahl lo hi)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64) :
    wortZahl lo hi (zahlWort v) = some v := by
  obtain ⟨n, hlo, hhi⟩ := v
  have hnn : 0 ≤ n := by omega
  have hnn2 : 0 ≤ hi := by omega
  have hcast : ((2 ^ 64 : Nat) : Int) = (2 ^ 64 : Int) := by decide
  have hlt : hi.toNat < 2 ^ 64 := by
    have h2 : hi < ((2 ^ 64 : Nat) : Int) := by
      rw [hcast]; exact hHi
    exact (Int.toNat_lt hnn2).mpr h2
  have hmod : n.toNat % 2 ^ 64 = n.toNat :=
    Nat.mod_eq_of_lt (by
      have hle : n.toNat ≤ hi.toNat := Int.toNat_le_toNat hhi
      omega)
  simp only [wortZahl, zahlWort, BitVec.toNat_ofNat, hmod]
  have hnn' : Int.ofNat n.toNat = n := Int.toNat_of_nonneg hnn
  simp only [hnn']
  rw [dif_pos ⟨hlo, hhi⟩]

/-- The ONE checked admission Bool of the interface: range (`0 <= lo`,
    `hi < 2 ^ 64`), width (an `.int` field, never `bool`/sums/FP/pointers)
    and region (the 8-byte slot fits the layout entry extent with no
    64-bit wrap). A Rust layout hint is re-decided against this, never a
    premise. -/
def repOk (ty : Ty) (base len off : Nat) : Bool :=
  match ty with
  | .int lo hi =>
    decide (0 ≤ lo ∧ hi < 2 ^ 64 ∧ off + 8 ≤ len ∧ base + off + 8 ≤ 2 ^ 64)
  | _ => false

/-- An accepted check yields exactly the range/width/region facts the
    preservation theorems consume. -/
theorem repOk_klingt {lo hi : Int} {base len off : Nat}
    (h : repOk (.int lo hi) base len off = true) :
    0 ≤ lo ∧ hi < 2 ^ 64 ∧ off + 8 ≤ len ∧ base + off + 8 ≤ 2 ^ 64 := by
  unfold repOk at h
  simp only [decide_eq_true_eq] at h
  exact h

/- CUTS:
    - Representation predicate, preservation theorems, refusals and the
      joint witness are still to come.
-/

#print axioms zahlWort

end Gabbro.Grammatik.X86
