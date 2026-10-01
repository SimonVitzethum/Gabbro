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
  bsrVon (trunc b w).toNat (b.bits - 1) b.bits

/-! ## 1. Forward search: range, set bit, minimality, zero behaviour. -/

/-- Forward search is correct: a hit lies in the searched interval, names
    a set bit and is minimal. One induction proves the conjunction; the
    three facts below are projections, so consumers pay no second induction. -/
theorem bsfVon_korrekt (v s f i : Nat) (h : bsfVon v s f = some i) :
    s ≤ i ∧ i < s + f ∧ v.testBit i = true ∧
      (∀ j, s ≤ j → j < i → v.testBit j = false) := by
  induction f generalizing s with
  | zero => simp [bsfVon] at h
  | succ f ih =>
    simp only [bsfVon] at h
    split at h
    · next hb =>
      injection h with hsub
      subst hsub
      refine ⟨Nat.le_refl _, by omega, by simpa using hb, ?_⟩
      intro j hlo hlt
      exact False.elim (by omega : False)
    · next hb =>
      obtain ⟨h1, h2, h3, h4⟩ := ih (s + 1) h
      have hbf : v.testBit s = false := by simpa using hb
      refine ⟨by omega, by omega, h3, ?_⟩
      intro j hlo hlt
      have hle : s + 1 ≤ j ∨ j = s := by omega
      cases hle with
      | inl hlo2 => exact h4 j hlo2 hlt
      | inr hjs => subst hjs; exact hbf

/-- A forward hit lies in the searched interval. -/
theorem bsfVon_schranke (v s f i : Nat) (h : bsfVon v s f = some i) :
    s ≤ i ∧ i < s + f :=
  ⟨(bsfVon_korrekt v s f i h).1, (bsfVon_korrekt v s f i h).2.1⟩

/-- A forward hit names a set bit. -/
theorem bsfVon_bit (v s f i : Nat) (h : bsfVon v s f = some i) :
    v.testBit i = true :=
  (bsfVon_korrekt v s f i h).2.2.1

/-- A forward hit is minimal: every bit between the start and the hit is clear. -/
theorem bsfVon_min (v s f i j : Nat) (h : bsfVon v s f = some i)
    (hlo : s ≤ j) (hlt : j < i) : v.testBit j = false :=
  (bsfVon_korrekt v s f i h).2.2.2 j hlo hlt

/-- No set bit in the interval means no hit. -/
theorem bsfVon_alle_null (v s f : Nat)
    (h : ∀ j, s ≤ j → j < s + f → v.testBit j = false) :
    bsfVon v s f = none := by
  induction f generalizing s with
  | zero => rfl
  | succ f ih =>
    simp only [bsfVon]
    split
    · next hb =>
      have h0 : v.testBit s = false := h s (Nat.le_refl s) (by omega)
      simp_all
    · next _ =>
      exact ih (s + 1) (fun j hlo hlt => h j (by omega) (by omega))

/-- A returned forward index lies inside the operand width. -/
theorem bsfIdx_schranke (b : Breite) (w : Wort) (i : Nat)
    (h : bsfIdx b w = some i) : i < b.bits := by
  have h2 := (bsfVon_schranke _ 0 _ i h).2
  omega

/-- A returned forward index names a set bit of the truncated operand. -/
theorem bsfIdx_bit (b : Breite) (w : Wort) (i : Nat)
    (h : bsfIdx b w = some i) : bitGesetzt b w i = true :=
  bsfVon_bit _ 0 _ i h

/-- A returned forward index is the least set bit: all lower bits are clear. -/
theorem bsfIdx_min (b : Breite) (w : Wort) (i j : Nat)
    (h : bsfIdx b w = some i) (hlt : j < i) :
    bitGesetzt b w j = false :=
  bsfVon_min _ 0 _ i j h (Nat.zero_le j) hlt

/-- A zero operand has no forward index (never a fabricated `some 0`).
    Per width by evaluation: the truncated word is `0`, so the fuel search
    over value `0` finds nothing at any width. -/
theorem bsfIdx_null_ist_none (b : Breite) (w : Wort)
    (h : trunc b w = 0) : bsfIdx b w = none := by
  have hnat : (trunc b w).toNat = 0 := by rw [h]; rfl
  unfold bsfIdx
  rw [hnat]
  cases b <;> decide

/-- A returned forward index proves the operand is nonzero. -/
theorem bsfIdx_some_nichtnull (b : Breite) (w : Wort) (i : Nat)
    (h : bsfIdx b w = some i) : trunc b w ≠ 0 := by
  intro hnull
  have hnone := bsfIdx_null_ist_none b w hnull
  rw [hnone] at h
  simp at h

/-! ## 2. Reverse search: range, set bit, maximality, zero behaviour. -/

/-- Reverse search is correct: a hit lies in the fuel-bounded interval,
    names a set bit and is maximal. One induction; the three facts below
    are projections. -/
theorem bsrVon_korrekt (v s f i : Nat) (h : bsrVon v s f = some i) :
    i ≤ s ∧ s ≤ i + f ∧ v.testBit i = true ∧
      (∀ j, i < j → j ≤ s → v.testBit j = false) := by
  induction f generalizing s with
  | zero => simp [bsrVon] at h
  | succ f ih =>
    simp only [bsrVon] at h
    split at h
    · next hb =>
      injection h with hsub
      subst hsub
      refine ⟨Nat.le_refl _, by omega, by simpa using hb, ?_⟩
      intro j hhi hlo
      exact False.elim (by omega : False)
    · next hb =>
      obtain ⟨h1, h2, h3, h4⟩ := ih (s - 1) h
      have hbf : v.testBit s = false := by simpa using hb
      refine ⟨by omega, by omega, h3, ?_⟩
      intro j hhi hlo
      have hle : j ≤ s - 1 ∨ j = s := by omega
      cases hle with
      | inl hlo2 => exact h4 j hhi hlo2
      | inr hjs => subst hjs; exact hbf

/-- A reverse hit lies in the searched interval (fuel-bounded below). -/
theorem bsrVon_schranke (v s f i : Nat) (h : bsrVon v s f = some i) :
    i ≤ s ∧ s ≤ i + f :=
  ⟨(bsrVon_korrekt v s f i h).1, (bsrVon_korrekt v s f i h).2.1⟩

/-- A reverse hit names a set bit. -/
theorem bsrVon_bit (v s f i : Nat) (h : bsrVon v s f = some i) :
    v.testBit i = true :=
  (bsrVon_korrekt v s f i h).2.2.1

/-- A reverse hit is maximal: every bit between the hit and the start is clear. -/
theorem bsrVon_max (v s f i j : Nat) (h : bsrVon v s f = some i)
    (hhi : i < j) (hlo : j ≤ s) : v.testBit j = false :=
  (bsrVon_korrekt v s f i h).2.2.2 j hhi hlo

/-- Every operand width is positive (four architectural widths). -/
theorem breite_bits_pos (b : Breite) : 0 < b.bits := by
  cases b <;> decide

/-- A returned reverse index lies inside the operand width. -/
theorem bsrIdx_schranke (b : Breite) (w : Wort) (i : Nat)
    (h : bsrIdx b w = some i) : i < b.bits := by
  obtain ⟨h1, _⟩ := bsrVon_schranke _ _ _ i h
  have hpos := breite_bits_pos b
  omega

/-- A returned reverse index names a set bit of the truncated operand. -/
theorem bsrIdx_bit (b : Breite) (w : Wort) (i : Nat)
    (h : bsrIdx b w = some i) : bitGesetzt b w i = true :=
  bsrVon_bit _ _ _ i h

/-- A returned reverse index is the greatest set bit: all higher in-width
    bits are clear. -/
theorem bsrIdx_max (b : Breite) (w : Wort) (i j : Nat)
    (h : bsrIdx b w = some i) (hhi : i < j) (hlt : j < b.bits) :
    bitGesetzt b w j = false := by
  have hle : j ≤ b.bits - 1 := by
    have hpos := breite_bits_pos b
    omega
  exact bsrVon_max _ _ _ i j h hhi hle

/-- No set bit in the downward interval means no reverse hit. -/
theorem bsrVon_alle_null (v s f : Nat)
    (h : ∀ j, s - f ≤ j → j ≤ s → v.testBit j = false) :
    bsrVon v s f = none := by
  induction f generalizing s with
  | zero => rfl
  | succ f ih =>
    simp only [bsrVon]
    split
    · next hb =>
      have h0 : v.testBit s = false := h s (by omega) (Nat.le_refl s)
      simp_all
    · next _ =>
      exact ih (s - 1) (fun j hlo hhi => h j (by omega) (by omega))

/-- A zero operand has no reverse index either (same per-width evaluation). -/
theorem bsrIdx_null_ist_none (b : Breite) (w : Wort)
    (h : trunc b w = 0) : bsrIdx b w = none := by
  have hnat : (trunc b w).toNat = 0 := by rw [h]; rfl
  unfold bsrIdx
  rw [hnat]
  cases b <;> decide

/-- A returned reverse index proves the operand is nonzero. -/
theorem bsrIdx_some_nichtnull (b : Breite) (w : Wort) (i : Nat)
    (h : bsrIdx b w = some i) : trunc b w ≠ 0 := by
  intro hnull
  have hnone := bsrIdx_null_ist_none b w hnull
  rw [hnone] at h
  simp at h

/-! ## 3. Zero flag and the scan validity shape.

    The zero flag is set exactly on a zero truncated operand. The validity
    relation pins what a future native form must present: a zero operand
    yields no index (the destination stays unconstrained, never a
    fabricated `some 0`), a returned index proves a nonzero operand with
    its range, set bit and extremality, and the flag always agrees. -/

/-- ZF-style zero flag: set exactly when the truncated operand is zero. -/
def scanZF (b : Breite) (w : Wort) : Bool := decide (trunc b w = 0)

/-- The flag reads the zero operand. -/
theorem scanZF_heisst (b : Breite) (w : Wort) :
    scanZF b w = true ↔ trunc b w = 0 := by
  simp [scanZF]

/-- Validity for a forward-scan snapshot: zero yields no index, an index
    proves nonzero with range, set bit and minimality, the flag agrees. -/
def BsfGueltig (b : Breite) (w : Wort) (o : Option Nat) (zf : Bool) : Prop :=
  (trunc b w = 0 → o = none) ∧
  (∀ i, o = some i → trunc b w ≠ 0 ∧ i < b.bits ∧
    bitGesetzt b w i = true ∧ ∀ j, j < i → bitGesetzt b w j = false) ∧
  (zf = decide (trunc b w = 0))

/-- Validity for a reverse-scan snapshot: the same shape with maximality. -/
def BsrGueltig (b : Breite) (w : Wort) (o : Option Nat) (zf : Bool) : Prop :=
  (trunc b w = 0 → o = none) ∧
  (∀ i, o = some i → trunc b w ≠ 0 ∧ i < b.bits ∧
    bitGesetzt b w i = true ∧
    ∀ j, i < j → j < b.bits → bitGesetzt b w j = false) ∧
  (zf = decide (trunc b w = 0))

/-- The forward helper with its flag satisfies forward validity. -/
theorem bsfIdx_gueltig (b : Breite) (w : Wort) :
    BsfGueltig b w (bsfIdx b w) (scanZF b w) := by
  refine ⟨bsfIdx_null_ist_none b w, ?_, rfl⟩
  intro i h
  exact ⟨bsfIdx_some_nichtnull b w i h, bsfIdx_schranke b w i h,
    bsfIdx_bit b w i h, fun j hj => bsfIdx_min b w i j h hj⟩

/-- The reverse helper with its flag satisfies reverse validity. -/
theorem bsrIdx_gueltig (b : Breite) (w : Wort) :
    BsrGueltig b w (bsrIdx b w) (scanZF b w) := by
  refine ⟨bsrIdx_null_ist_none b w, ?_, rfl⟩
  intro i h
  exact ⟨bsrIdx_some_nichtnull b w i h, bsrIdx_schranke b w i h,
    bsrIdx_bit b w i h,
    fun j h1 h2 => bsrIdx_max b w i j h h1 h2⟩

/-- A set flag means no index in either direction (no fabricated result). -/
theorem scanZF_null_kein_index (b : Breite) (w : Wort)
    (h : scanZF b w = true) :
    bsfIdx b w = none ∧ bsrIdx b w = none := by
  have hnull : trunc b w = 0 := (scanZF_heisst b w).mp h
  exact ⟨bsfIdx_null_ist_none b w hnull, bsrIdx_null_ist_none b w hnull⟩

/-- A returned index in either direction clears the flag. -/
theorem scanZF_index_nichtnull (b : Breite) (w : Wort) (i : Nat)
    (h : bsfIdx b w = some i ∨ bsrIdx b w = some i) :
    scanZF b w = false := by
  have hne : trunc b w ≠ 0 := by
    cases h with
    | inl hf => exact bsfIdx_some_nichtnull b w i hf
    | inr hr => exact bsrIdx_some_nichtnull b w i hr
  cases hsc : scanZF b w with
  | true =>
    have hnull := (scanZF_heisst b w).mp hsc
    exact absurd hnull hne
  | false => rfl

/-! ## 4. Boundary probes (finite concrete checks via `decide`). -/

/-- `1` scans to `0` in both directions. -/
theorem probe_bsf_eins : bsfIdx .b64 1 = some 0 ∧ bsrIdx .b64 1 = some 0 := by
  decide

/-- The top bit scans to `63` in both directions. -/
theorem probe_bsf_hoch :
    bsfIdx .b64 0x8000000000000000 = some 63 ∧
    bsrIdx .b64 0x8000000000000000 = some 63 := by
  decide

/-- Zero scans to nothing and sets the flag (never `some 0`). -/
theorem probe_bsf_null :
    bsfIdx .b64 0 = none ∧ bsrIdx .b64 0 = none ∧
    scanZF .b64 0 = true := by
  decide

/-- Fixed-width evidence: bit 8 lies outside an 8-bit operand, so the
    truncated value is zero and the scan refuses. -/
theorem probe_bsf_schmal_ignoriert_hoch :
    bsfIdx .b8 0x100 = none ∧ bsrIdx .b8 0x100 = none ∧
    scanZF .b8 0x100 = true := by
  decide

/-- Narrow scan: `0x81` spans the full 8-bit width. -/
theorem probe_bsr_schmal :
    bsfIdx .b8 0x81 = some 0 ∧ bsrIdx .b8 0x81 = some 7 ∧
    scanZF .b8 0x81 = false := by
  decide

/-- `0x10` scans to `4`: the value stored through memory in §5. -/
theorem probe_bsf_mitte :
    bsfIdx .b64 0x10 = some 4 ∧ bsrIdx .b64 0x10 = some 4 ∧
    scanZF .b64 0x10 = false := by
  decide

/-! ## 5. Joint witness: a scanned index through real memory.

    The least set bit `4` of `0x10` is stored through the canonical
    permission-checked `write64` and read back through `read64`; the store
    observably changes memory. Value, flag and memory change are pinned
    jointly on a nonzero word. -/

/-- The witness memory after storing the scanned index `4`. -/
def scanSondenSpeicherNach : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 4 }

/-- Scanned index plus flag read changing memory. -/
theorem bitscan_speicher_zeuge :
    bsfIdx .b64 0x10 = some 4 ∧ scanZF .b64 0x10 = false ∧
    ∃ m' : Speicher,
      write64 zeugenSpeicher 0 4 = some m' ∧
      read64 m' 0 = some 4 ∧
      zeugenSpeicher.bytes 0 ≠ m'.bytes 0 := by
  refine ⟨by decide, by decide, ?_⟩
  refine ⟨scanSondenSpeicherNach, ?_, ?_, ?_⟩
  · have hwr : write64 zeugenSpeicher 0 4 = some scanSondenSpeicherNach := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    exact hwr
  · have hwr : write64 zeugenSpeicher 0 4 = some scanSondenSpeicherNach := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd := read64_nach_write64 zeugenSpeicher _ 0 4 hwr rfl
    exact hrd
  · have hhit := writeBytesN_hit zeugenSpeicher 0 4
      8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 4 0
    unfold writeBytes
    rw [hhit]
    decide

/- CUTS:
   - No `Befehl` extension and no `schritt` change: the 14 pilot forms are
     untouched. How a future BSF/BSR/TZCNT/LZCNT native form presents its
     evidence is `BsfGueltig`/`BsrGueltig`; wiring, decoder bytes, image
     bytes and final acceptance stay OPEN with the Typen owner.
   - No totality on nonzero operands: `trunc ≠ 0 → ∃ i, scan = some i` is
     NOT proved (only zero → none and some → nonzero). A consumer that
     needs the defined-when direction must prove it or keep the refusal.
   - No flag snapshot beyond ZF: CF/OF/SF/PF/AF treatment of any future
     native form is not modelled here (all other flags unconstrained).
   - No source correspondence, no TSO/concurrency bridge (sequential facts
     over one word or one `Speicher`; per-access granularity and tearing
     stay with the bridge lane), no cost transfer, no hardware verification:
     the width truncation, the fuel-search semantics and the ZF reading are
     STATED executable helpers, not verified against silicon.
   - This file adds no new source-language construct or checker rule: no
     diagnostic, poison-probe, example or CLI numbers are taken.
-/

#print axioms bitGesetzt
#print axioms bsfIdx
#print axioms bsrIdx
#print axioms bsfVon_korrekt
#print axioms bsrVon_korrekt
#print axioms bsfVon_schranke
#print axioms bsfVon_bit
#print axioms bsfVon_min
#print axioms bsfVon_alle_null
#print axioms bsfIdx_schranke
#print axioms bsfIdx_bit
#print axioms bsfIdx_min
#print axioms bsfIdx_null_ist_none
#print axioms bsfIdx_some_nichtnull
#print axioms bsrVon_schranke
#print axioms bsrVon_bit
#print axioms bsrVon_max
#print axioms breite_bits_pos
#print axioms bsrIdx_schranke
#print axioms bsrIdx_bit
#print axioms bsrIdx_max
#print axioms bsrVon_alle_null
#print axioms bsrIdx_null_ist_none
#print axioms bsrIdx_some_nichtnull
#print axioms scanZF_heisst
#print axioms bsfIdx_gueltig
#print axioms bsrIdx_gueltig
#print axioms scanZF_null_kein_index
#print axioms scanZF_index_nichtnull
#print axioms probe_bsf_eins
#print axioms probe_bsf_hoch
#print axioms probe_bsf_null
#print axioms probe_bsf_schmal_ignoriert_hoch
#print axioms probe_bsr_schmal
#print axioms probe_bsf_mitte
#print axioms bitscan_speicher_zeuge

end Gabbro.Grammatik.X86
