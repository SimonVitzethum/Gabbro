/-
  File:      Grammatik/X86/MemoryTypeHardwareExecution.lean
  Subject:   UC MMIO architectural access and ordering over the canonical
             byte/register/memory state.

  Lane 694 (hardware completion): normal WB RAM follows TSO; selected UC
  device addresses follow exact documented architecture constraints with
  one generic named hardware device-response interface. OS/page-table/
  memory-type configuration is software user logic establishing explicit
  profile facts, never a trusted Bool.

  Provenance (official Intel SDM 325462-093US, September 2026, local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  - Vol.1 Section 20.5 (memory-mapped I/O ordering): UC region reads and
    writes appear in order on the pins; MTRRs make the MMIO space UC;
    chipsets may post UC writes (CPU-retired is not device-completed).
  - Vol.3A Section 14.3 Table 14-2 (Strong Uncacheable UC): reads/writes
    appear on the bus in program order without reordering, no speculative
    access; x87/SIMD UC re-access NOTE (only GP-register forms admitted).
  - Vol.3A Section 14.3.3 (UC code fetch limits; code stays WB here).
  - Vol.3A Sections 11.1.2/11.2.5 (UC lock serialization, I/O and locked
    instruction drain of buffered writes; no universal fence claimed).
  AMD retrieval failed; no AMD provenance or silicon proof is claimed.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.Codec
import Grammatik.X86.TSO
import Grammatik.X86.FeatureProfile
import Grammatik.X86.NarrowOps
import Grammatik.X86.NarrowCodec
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- UC MMIO window profile: the explicit list of UC regions established by
    software (MTRR/PAT/page tables are user logic). An address is UC only
    by membership here; WB is the default elsewhere. -/
abbrev UcProfil := List Region

/-! ## 1. UC profile: explicit software-established membership. -/

/-- One UC region covers `[start, start+len)`: inside with no 64-bit wrap. -/
def decktUc (r : Region) (start len : Nat) : Bool :=
  decide (r.basis ≤ start ∧ start + len ≤ r.basis + r.len ∧
    start + len ≤ 2 ^ 64)

/-- An `n`-byte access at `a` is UC exactly by membership in one listed
    region. WB is whatever no listed region covers. -/
def istUc : UcProfil → Adresse → Nat → Bool
  | [], _, _ => false
  | r :: rest, a, n => decktUc r a.toNat n || istUc rest a n

/-- The empty profile admits no UC access: WB is the default everywhere. -/
theorem istUc_leer (a : Adresse) (n : Nat) : istUc [] a n = false := rfl

/-- A covering head region makes the access UC. -/
theorem istUc_kopf (r : Region) (rest : UcProfil) (a : Adresse) (n : Nat)
    (hd : decktUc r a.toNat n = true) :
    istUc (r :: rest) a n = true := by
  unfold istUc
  rw [hd, Bool.true_or]

/-- Membership of a covering region anywhere in the list makes it UC. -/
theorem istUc_mem (profil : UcProfil) (r : Region) (a : Adresse) (n : Nat)
    (hr : r ∈ profil) (hd : decktUc r a.toNat n = true) :
    istUc profil a n = true := by
  induction profil with
  | nil => simp at hr
  | cons q rest ih =>
    simp only [istUc]
    simp at hr
    rcases hr with rfl | hr
    · rw [hd, Bool.true_or]
    · rw [Bool.or_eq_true]
      exact Or.inr (ih hr)

/-- Width to admitted performance feature: 64-bit needs scalar-64 silicon,
    narrower widths ride the scalar-32 tier. -/
def breiteMerkmal : Breite → PerfMerkmal
  | .b64 => .skalar64
  | _ => .skalar32

/-- Width admission is silicon plus readiness, never bare existence. -/
def breiteZugelassen (hw : HwProfil) (b : BereitProfil)
    (w : Breite) : Bool :=
  merkmalZugelassen hw b (breiteMerkmal w)

/-- Width admission carries silicon support. -/
theorem breiteZugelassen_hat (hw : HwProfil) (b : BereitProfil)
    (w : Breite) (h : breiteZugelassen hw b w = true) :
    hat hw (breiteMerkmal w) = true :=
  (merkmalZugelassen_heisst_beide hw b _ h).1

/-- Width admission carries control-state readiness. -/
theorem breiteZugelassen_bereit (hw : HwProfil) (b : BereitProfil)
    (w : Breite) (h : breiteZugelassen hw b w = true) :
    bereit b (breiteMerkmal w) = true :=
  (merkmalZugelassen_heisst_beide hw b _ h).2

/-! ## 2. Generic named device: window, response, side effects.

  The selected MMIO window is 8 bytes at `geraetBasis`. The device is
  the ONE generic named hardware interface of this file: deterministic
  little-endian width-indexed reads/writes with an access counter, so a
  read observably has side effects (status-clear shapes refine this via
  the counter, never silently). x87/SIMD forms are never admitted here
  (SDM Table 14-2 NOTE: UC re-access is implementation dependent; only
  general-purpose-register loads/stores touch UC). -/

/-- Device window base: the single selected 8-byte MMIO window. -/
def geraetBasis : Nat := 65536

/-- Generic named hardware device: 8 data bytes plus an access counter.
    Every successful read or write increments the counter. -/
structure Geraet where
  daten : Fin 8 → Byte
  zugriffe : Nat

/-- The reset device: zeroed bytes, no access yet. -/
def geraetAnfang : Geraet := ⟨fun _ => BitVec.ofNat 8 0, 0⟩

/-- Offset of an address inside the device window. -/
def geraetOff (a : Adresse) : Nat := a.toNat - geraetBasis

/-- Window check: the `n`-byte access at `a` lies inside the 8-byte
    window with no 64-bit wrap. -/
def imFenster (a : Adresse) (n : Nat) : Bool :=
  decide (geraetBasis ≤ a.toNat ∧ a.toNat + n ≤ geraetBasis + 8 ∧
    a.toNat + n ≤ 2 ^ 64)

/-- The window check carries the offset bound the device needs. -/
theorem imFenster_off (a : Adresse) (n : Nat)
    (h : imFenster a n = true) : geraetOff a + n ≤ 8 := by
  have hdec : geraetBasis ≤ a.toNat ∧ a.toNat + n ≤ geraetBasis + 8 ∧
      a.toNat + n ≤ 2 ^ 64 := of_decide_eq_true h
  show a.toNat - geraetBasis + n ≤ 8
  omega

/-- The window check carries no-wrap. -/
theorem imFenster_ohneUmbruch (a : Adresse) (n : Nat)
    (h : imFenster a n = true) : a.toNat + n ≤ 2 ^ 64 := by
  have hdec : geraetBasis ≤ a.toNat ∧ a.toNat + n ≤ geraetBasis + 8 ∧
      a.toNat + n ≤ 2 ^ 64 := of_decide_eq_true h
  exact hdec.2.2

/-- Bounded window index: `none` outside the 8 bytes. -/
def fin8 (n : Nat) : Option (Fin 8) :=
  if h : n < 8 then some ⟨n, h⟩ else none

/-- A valid index resolves. -/
theorem fin8_gleich (n : Nat) (h : n < 8) : fin8 n = some ⟨n, h⟩ := by
  unfold fin8
  rw [dif_pos h]

/-- An out-of-window index refuses. -/
theorem fin8_nichts (n : Nat) (h : ¬ n < 8) : fin8 n = none := by
  unfold fin8
  rw [dif_neg h]

/-- Window byte update. -/
def datenSetze (d : Fin 8 → Byte) (i : Fin 8) (v : Byte) :
    Fin 8 → Byte :=
  fun j => if j = i then v else d j

/-- The updated index answers the new byte. -/
theorem datenSetze_gleich (d : Fin 8 → Byte) (i : Fin 8) (v : Byte) :
    datenSetze d i v i = v := by
  simp [datenSetze]

/-- Any other index keeps its byte. -/
theorem datenSetze_anders (d : Fin 8 → Byte) (i j : Fin 8) (v : Byte)
    (h : j ≠ i) : datenSetze d i v j = d j := by
  simp [datenSetze, h]

/-- Width-indexed device read: the window bytes little-endian, the
    counter incremented (read side effect). `none` is an explicit
    refusal outside the window. -/
def geraetLiest (g : Geraet) (b : Breite) (off : Nat) :
    Option (Geraet × Wort) :=
  match b with
  | .b8 =>
    match fin8 off with
    | some i =>
      some (⟨g.daten, g.zugriffe + 1⟩, BitVec.ofNat 64 (g.daten i).toNat)
    | none => none
  | .b16 =>
    match fin8 off, fin8 (off + 1) with
    | some i0, some i1 =>
      some (⟨g.daten, g.zugriffe + 1⟩,
        BitVec.ofNat 64 ((g.daten i0).toNat + (g.daten i1).toNat * 256))
    | _, _ => none
  | .b32 =>
    match fin8 off, fin8 (off + 1), fin8 (off + 2), fin8 (off + 3) with
    | some i0, some i1, some i2, some i3 =>
      some (⟨g.daten, g.zugriffe + 1⟩,
        BitVec.ofNat 64 ((g.daten i0).toNat + (g.daten i1).toNat * 256 +
          (g.daten i2).toNat * 65536 + (g.daten i3).toNat * 16777216))
    | _, _, _, _ => none
  | .b64 =>
    match fin8 off, fin8 (off + 1), fin8 (off + 2), fin8 (off + 3),
        fin8 (off + 4), fin8 (off + 5), fin8 (off + 6),
        fin8 (off + 7) with
    | some i0, some i1, some i2, some i3,
      some i4, some i5, some i6, some i7 =>
      some (⟨g.daten, g.zugriffe + 1⟩,
        BitVec.ofNat 64 ((g.daten i0).toNat + (g.daten i1).toNat * 256 +
          (g.daten i2).toNat * 65536 + (g.daten i3).toNat * 16777216 +
          (g.daten i4).toNat * 4294967296 +
          (g.daten i5).toNat * 1099511627776 +
          (g.daten i6).toNat * 281474976710656 +
          (g.daten i7).toNat * 72057594037927936))
    | _, _, _, _, _, _, _, _ => none

/-- Width-indexed device write: the word's low bytes into the window,
    the counter incremented. `none` is an explicit refusal. -/
def geraetSchreibt (g : Geraet) (b : Breite) (off : Nat)
    (v : Wort) : Option Geraet :=
  match b with
  | .b8 =>
    match fin8 off with
    | some i =>
      some ⟨datenSetze g.daten i (wortByte v 0), g.zugriffe + 1⟩
    | none => none
  | .b16 =>
    match fin8 off, fin8 (off + 1) with
    | some i0, some i1 =>
      some ⟨datenSetze (datenSetze g.daten i0 (wortByte v 0))
        i1 (wortByte v 1), g.zugriffe + 1⟩
    | _, _ => none
  | .b32 =>
    match fin8 off, fin8 (off + 1), fin8 (off + 2), fin8 (off + 3) with
    | some i0, some i1, some i2, some i3 =>
      some ⟨datenSetze (datenSetze (datenSetze
        (datenSetze g.daten i0 (wortByte v 0)) i1 (wortByte v 1))
        i2 (wortByte v 2)) i3 (wortByte v 3), g.zugriffe + 1⟩
    | _, _, _, _ => none
  | .b64 =>
    match fin8 off, fin8 (off + 1), fin8 (off + 2), fin8 (off + 3),
        fin8 (off + 4), fin8 (off + 5), fin8 (off + 6),
        fin8 (off + 7) with
    | some i0, some i1, some i2, some i3,
      some i4, some i5, some i6, some i7 =>
      some ⟨datenSetze (datenSetze (datenSetze
        (datenSetze (datenSetze (datenSetze
        (datenSetze (datenSetze g.daten i0 (wortByte v 0))
        i1 (wortByte v 1)) i2 (wortByte v 2)) i3 (wortByte v 3))
        i4 (wortByte v 4)) i5 (wortByte v 5)) i6 (wortByte v 6))
        i7 (wortByte v 7), g.zugriffe + 1⟩
    | _, _, _, _, _, _, _, _ => none

/-- A successful device read increments exactly the counter: data bytes
    are preserved, so the side effect is exactly the count. -/
theorem geraetLiest_zaehlt (g : Geraet) (b : Breite) (off : Nat)
    (g' : Geraet) (v : Wort) (h : geraetLiest g b off = some (g', v)) :
    g'.zugriffe = g.zugriffe + 1 ∧ g'.daten = g.daten := by
  cases b with
  | b8 =>
    simp only [geraetLiest] at h
    cases hfin : fin8 off with
    | none => simp [hfin] at h
    | some i => simp [hfin] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | b16 =>
    simp only [geraetLiest] at h
    cases h0 : fin8 off with
    | none => simp [h0] at h
    | some i0 =>
      cases h1 : fin8 (off + 1) with
      | none => simp [h0, h1] at h
      | some i1 =>
        simp [h0, h1] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | b32 =>
    simp only [geraetLiest] at h
    cases h0 : fin8 off with
    | none => simp [h0] at h
    | some i0 =>
      cases h1 : fin8 (off + 1) with
      | none => simp [h0, h1] at h
      | some i1 =>
        cases h2 : fin8 (off + 2) with
        | none => simp [h0, h1, h2] at h
        | some i2 =>
          cases h3 : fin8 (off + 3) with
          | none => simp [h0, h1, h2, h3] at h
          | some i3 =>
            simp [h0, h1, h2, h3] at h
            obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | b64 =>
    simp only [geraetLiest] at h
    cases h0 : fin8 off with
    | none => simp [h0] at h
    | some i0 =>
      cases h1 : fin8 (off + 1) with
      | none => simp [h0, h1] at h
      | some i1 =>
        cases h2 : fin8 (off + 2) with
        | none => simp [h0, h1, h2] at h
        | some i2 =>
          cases h3 : fin8 (off + 3) with
          | none => simp [h0, h1, h2, h3] at h
          | some i3 =>
            cases h4 : fin8 (off + 4) with
            | none => simp [h0, h1, h2, h3, h4] at h
            | some i4 =>
              cases h5 : fin8 (off + 5) with
              | none => simp [h0, h1, h2, h3, h4, h5] at h
              | some i5 =>
                cases h6 : fin8 (off + 6) with
                | none => simp [h0, h1, h2, h3, h4, h5, h6] at h
                | some i6 =>
                  cases h7 : fin8 (off + 7) with
                  | none => simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
                  | some i7 =>
                    simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
                    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-- A successful device write increments exactly the counter. -/
theorem geraetSchreibt_zaehlt (g : Geraet) (b : Breite) (off : Nat)
    (v : Wort) (g' : Geraet) (h : geraetSchreibt g b off v = some g') :
    g'.zugriffe = g.zugriffe + 1 := by
  cases b with
  | b8 =>
    simp only [geraetSchreibt] at h
    cases hfin : fin8 off with
    | none => simp [hfin] at h
    | some i => simp [hfin] at h; cases h; rfl
  | b16 =>
    simp only [geraetSchreibt] at h
    cases h0 : fin8 off with
    | none => simp [h0] at h
    | some i0 =>
      cases h1 : fin8 (off + 1) with
      | none => simp [h0, h1] at h
      | some i1 => simp [h0, h1] at h; cases h; rfl
  | b32 =>
    simp only [geraetSchreibt] at h
    cases h0 : fin8 off with
    | none => simp [h0] at h
    | some i0 =>
      cases h1 : fin8 (off + 1) with
      | none => simp [h0, h1] at h
      | some i1 =>
        cases h2 : fin8 (off + 2) with
        | none => simp [h0, h1, h2] at h
        | some i2 =>
          cases h3 : fin8 (off + 3) with
          | none => simp [h0, h1, h2, h3] at h
          | some i3 => simp [h0, h1, h2, h3] at h; cases h; rfl
  | b64 =>
    simp only [geraetSchreibt] at h
    cases h0 : fin8 off with
    | none => simp [h0] at h
    | some i0 =>
      cases h1 : fin8 (off + 1) with
      | none => simp [h0, h1] at h
      | some i1 =>
        cases h2 : fin8 (off + 2) with
        | none => simp [h0, h1, h2] at h
        | some i2 =>
          cases h3 : fin8 (off + 3) with
          | none => simp [h0, h1, h2, h3] at h
          | some i3 =>
            cases h4 : fin8 (off + 4) with
            | none => simp [h0, h1, h2, h3, h4] at h
            | some i4 =>
              cases h5 : fin8 (off + 5) with
              | none => simp [h0, h1, h2, h3, h4, h5] at h
              | some i5 =>
                cases h6 : fin8 (off + 6) with
                | none => simp [h0, h1, h2, h3, h4, h5, h6] at h
                | some i6 =>
                  cases h7 : fin8 (off + 7) with
                  | none => simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
                  | some i7 =>
                    simp [h0, h1, h2, h3, h4, h5, h6, h7] at h
                    cases h; rfl

/-- A one-byte device read outside the window refuses. -/
theorem geraetLiest_b8_verweigert (g : Geraet) (off : Nat)
    (h : fin8 off = none) : geraetLiest g .b8 off = none := by
  simp [geraetLiest, h]

/-- A one-byte device write outside the window refuses. -/
theorem geraetSchreibt_b8_verweigert (g : Geraet) (off : Nat) (v : Wort)
    (h : fin8 off = none) : geraetSchreibt g .b8 off v = none := by
  simp [geraetSchreibt, h]

end Gabbro.Grammatik.X86
