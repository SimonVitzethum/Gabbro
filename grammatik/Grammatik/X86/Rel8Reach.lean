/-
  File:      Grammatik/X86/Rel8Reach.lean
  Subject:   Short-branch reachability with decoded-start check and wide fallback.

  Lane 772 (hardware completion): the selection layer over the accepted
  short forms (`EB cb`, `70+cc cb` from lane 680) and the accepted wide
  certificate (`zweigOk` from lane 423). A short branch reaches exactly
  the targets within -128..+127 of its virtual next-RIP; an admitted
  short target is a decoded instruction start or a listed entry (the
  reused `indirektZielOk` check); anything else falls back to the wide
  rel32 form, which provably reaches the same target. All execution
  runs through the reused `schritt`/`jmpKurzSchritt` steps; no `Befehl`
  constructor, decoder row or interpreter is added here.

  Manual provenance (clone-local, no network): Intel SDM combined
  volumes 1-4, edition 325462-093US (September 2026),
  `.tmp/HARDWARE-REFERENCES/` (`REFERENCES.json`, verified 2026-10-02,
  sha256 `a4a62e6a…f9168ee`; AMD retrieval failed, no AMD claim).
  Headings read: Vol.2A Ch.3 `JMP-Jump` (`EB cb JMP rel8`, "Jump short,
  RIP = RIP + 8-bit displacement sign extended to 64-bits", p.3-504),
  `Jcc-Jump if Condition Is Met` (`7x cb` rel8 table, "Jump short if …",
  p.3-499), and the relative-offset rule ("encoded as a signed 8-, 16-,
  or 32-bit immediate value … added to … the address of the instruction
  following the JMP instruction", pp.3-504-3-505).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.ControlFlow
import Grammatik.X86.BranchLayout
import Grammatik.X86.Relokation
import Grammatik.X86.RelocatedExecution
import Grammatik.X86.IndirectControlHardwareForms
import Grammatik.X86.Vektor

namespace Gabbro.Grammatik.X86

/-- Signed-8 fit: the displacement fits a rel8 field, i.e. the target
    lies within -128..+127 of the virtual next-RIP. -/
def rel8Passt (d : Int) : Bool :=
  decide (-128 ≤ d ∧ d < 128)

/-- Fit characterization: the check holds exactly on the signed-8
    range. Every premise is used. -/
theorem rel8Passt_grenzen (d : Int) (h : rel8Passt d = true) :
    -128 ≤ d ∧ d < 128 := by
  unfold rel8Passt at h
  exact of_decide_eq_true h

/-- Two's-complement reading of the rel8 byte: the signed value the
    manual's "signed 8-bit immediate" names. -/
def disp8Signed (b : Byte) : Int :=
  if b.toNat < 128 then (b.toNat : Int) else (b.toNat : Int) - 256

/-- Every rel8 byte value lies in signed-8 range. -/
theorem disp8Signed_schranke (b : Byte) :
    -128 ≤ disp8Signed b ∧ disp8Signed b < 128 := by
  have hb := b.isLt
  by_cases hc : b.toNat < 128
  · simp only [disp8Signed, if_pos hc]
    omega
  · simp only [disp8Signed, if_neg hc]
    omega

/-- Every rel8 byte value passes the reachability check: width-level
    refusal never fires for a decoded rel8 field; the check bites only
    at layout level (target minus next-RIP). -/
theorem disp8Signed_passt (b : Byte) :
    rel8Passt (disp8Signed b) = true := by
  have h := disp8Signed_schranke b
  simp only [rel8Passt, decide_eq_true_eq]
  exact h

/-- BYTE PIN: `0x10` reads as +16 (the taken short witness below). -/
theorem pin_disp8_vor : disp8Signed (natByte 16) = 16 := by
  decide

/-- BYTE PIN: `0xFB` reads as -5 (one short step back). -/
theorem pin_disp8_zurueck : disp8Signed (natByte 251) = -5 := by
  decide

/-- BYTE PIN: `0x7F` is the farthest forward reach (+127). -/
theorem pin_disp8_max : disp8Signed (natByte 127) = 127 := by
  decide

/-- BYTE PIN: `0x80` is the farthest backward reach (-128). -/
theorem pin_disp8_min : disp8Signed (natByte 128) = -128 := by
  decide

/-- RANGE EDGE: +127 is reachable, +128 is not. -/
theorem pin_reichweite_oben :
    rel8Passt 127 = true ∧ rel8Passt 128 = false := by
  decide

/-- RANGE EDGE: -128 is reachable, -129 is not. -/
theorem pin_reichweite_unten :
    rel8Passt (-128) = true ∧ rel8Passt (-129) = false := by
  decide

/-! ## Sign-extension bridge: `dispWort8` meets `rel32Enc64`.

    Execution adds `dispWort8 b` (sign extension through `sext`) while
    relocation computes `rel32Enc64 (disp8Signed b)` (two's-complement
    representative). Both branch on the same bit: bit 7 of the byte
    value. The proof mirrors the accepted `dispWort_bridge` (lane 291)
    with the bit-7 boundary; `testBit_div_pow` is reused. -/

/-- Bit 7 of a byte value is the signed-8 boundary. -/
theorem bit7_equiv (n : Nat) (h : n < 256) :
    n.testBit 7 = decide (128 ≤ n) := by
  have h7 : n.testBit 7 = (n / 2 ^ 7).testBit 0 :=
    testBit_div_pow n 7
  rw [h7, Nat.testBit_zero]
  have hdiv : n / 2 ^ 7 < 2 := by
    have h0 : (0 : Nat) < 2 ^ 7 := by decide
    rw [Nat.div_lt_iff_lt_mul h0]
    omega
  have hmod : (n / 2 ^ 7) % 2 = n / 2 ^ 7 :=
    Nat.mod_eq_of_lt hdiv
  rw [hmod]
  have hiff : (n / 2 ^ 7 = 1) ↔ (128 ≤ n) := by
    omega
  simp only [hiff]

/-- BRIDGE: the short-branch sign extension of a rel8 byte is the
    relocation 64-bit representative of its signed value. This is the
    one fact that lets a relocation address equation speak about the
    reused short `kurzZiel` step. -/
theorem dispWort8_bridge (b : Byte) :
    dispWort8 b = BitVec.ofNat 64 (rel32Enc64 (disp8Signed b)) := by
  have hb := b.isLt
  have hlo : (trunc .b8 (BitVec.ofNat 64 b.toNat)).toNat = b.toNat := by
    have hw : (BitVec.ofNat 64 b.toNat).toNat = b.toNat := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [trunc_nat, hw]
    have hbits : Breite.bits .b8 = 8 := rfl
    rw [hbits]
    exact Nat.mod_eq_of_lt hb
  have hbit' : b.toNat.testBit (signBit .b8) =
      decide (128 ≤ b.toNat) := by
    rw [show signBit .b8 = 7 from rfl]
    exact bit7_equiv b.toNat hb
  unfold dispWort8
  simp only [sext, hlo, hbit']
  by_cases hge : 128 ≤ b.toNat
  · rw [if_pos (decide_eq_true hge)]
    have hbits : Breite.bits .b8 = 8 := rfl
    rw [hbits]
    have hds : disp8Signed b = (b.toNat : Int) - 256 := by
      unfold disp8Signed
      rw [if_neg (by omega)]
    rw [hds]
    have hneg : ¬ (0 : Int) ≤ (b.toNat : Int) - 256 := by
      omega
    unfold rel32Enc64 tcNat
    rw [if_neg hneg]
    have e : (((b.toNat : Int) - 256 +
        ((18446744073709551616 : Nat) : Int))).toNat =
        b.toNat + (2 ^ 64 - 2 ^ 8) := by
      have e2 : (b.toNat : Int) - 256 +
          ((18446744073709551616 : Nat) : Int) =
          ((b.toNat + (18446744073709551616 - 256) : Nat) : Int) := by
        omega
      rw [e2, Int.toNat_natCast]
    rw [e]
  · rw [if_neg (by rw [decide_eq_false hge]; decide)]
    have hds : disp8Signed b = (b.toNat : Int) := by
      unfold disp8Signed
      rw [if_pos (by omega)]
    rw [hds]
    have hpos : (0 : Int) ≤ (b.toNat : Int) := by omega
    unfold rel32Enc64 tcNat
    rw [if_pos hpos, Int.toNat_natCast]

/-! ## Short-branch selection with the wide-form fallback.

    The validator admits `.kurz` exactly for rel8-reachable targets
    that are decoded instruction starts or listed entries (the reused
    `indirektZielOk` check); every other site keeps the wide rel32
    form. Lengths are carried data (2 short, 5/6 wide). -/

/-- Short-branch selection: `.kurz` iff the displacement fits rel8,
    the next-RIP equation holds at the short length, and the short
    target is admitted; otherwise the wide form. -/
def rel8Wahl (starts eintraege : List Adresse)
    (start : Nat) (d : Int) (ziel : Nat) : ZweigForm :=
  if rel8Passt d then
    if decide ((ziel : Int) = (start : Int) + 2 + d) then
      if indirektZielOk starts eintraege (BitVec.ofNat 64 ziel) then .kurz
      else .weit
    else .weit
  else .weit

/-- ACCEPTANCE: a reachable admitted target selects the short form.
    Every premise is used. -/
theorem rel8Wahl_kurz (starts eintraege : List Adresse)
    (start : Nat) (d : Int) (ziel : Nat)
    (hfit : rel8Passt d = true)
    (hgleich : (ziel : Int) = (start : Int) + 2 + d)
    (hstart : indirektZielOk starts eintraege (BitVec.ofNat 64 ziel) = true) :
    rel8Wahl starts eintraege start d ziel = .kurz := by
  unfold rel8Wahl
  simp only [hfit, decide_eq_true hgleich, hstart, if_true]

/-- REFUSAL (out of range): an unreachable target keeps the wide form. -/
theorem rel8Wahl_weit_aussen (starts eintraege : List Adresse)
    (start : Nat) (d : Int) (ziel : Nat)
    (h : rel8Passt d = false) :
    rel8Wahl starts eintraege start d ziel = .weit := by
  unfold rel8Wahl
  simp [h]

/-- REFUSAL (no decoded start): an unadmitted target keeps the wide
    form, even when reachable. Every premise is used. -/
theorem rel8Wahl_weit_ohne_start (starts eintraege : List Adresse)
    (start : Nat) (d : Int) (ziel : Nat)
    (hfit : rel8Passt d = true)
    (hgleich : (ziel : Int) = (start : Int) + 2 + d)
    (hstart : indirektZielOk starts eintraege (BitVec.ofNat 64 ziel) = false) :
    rel8Wahl starts eintraege start d ziel = .weit := by
  unfold rel8Wahl
  simp [hfit, decide_eq_true hgleich, hstart]

/-- ADMISSION GUARANTEE: an admitted short target is a decoded
    instruction start or a listed entry. Every premise is used. -/
theorem rel8Wahl_garantiert (starts eintraege : List Adresse)
    (start : Nat) (d : Int) (ziel : Nat)
    (h : rel8Wahl starts eintraege start d ziel = .kurz) :
    (BitVec.ofNat 64 ziel) ∈ starts ∨
      (BitVec.ofNat 64 ziel) ∈ eintraege := by
  unfold rel8Wahl at h
  by_cases hf : rel8Passt d = true
  · rw [if_pos hf] at h
    by_cases hg : (ziel : Int) = (start : Int) + 2 + d
    · rw [if_pos (decide_eq_true hg)] at h
      by_cases hs : indirektZielOk starts eintraege
        (BitVec.ofNat 64 ziel) = true
      · rw [if_pos hs] at h
        exact indirektZielOk_garantiert _ _ _ hs
      · rw [if_neg hs] at h
        exact absurd h (by decide)
    · have hgn : decide ((ziel : Int) = (start : Int) + 2 + d) = false :=
        decide_eq_false hg
      rw [if_neg (by rw [hgn]; decide)] at h
      exact absurd h (by decide)
  · rw [if_neg hf] at h
    exact absurd h (by decide)

/-! ## Pinned short bytes on the reused encoders.

    The byte shapes come from the accepted lane-680 encoders (never
    re-encoded here); the pins fix the reachability extremes to their
    exact machine bytes. -/

/-- PINNED BYTES: short jump +16 is `EB 10`. -/
theorem pin_rel8jmp_vor :
    encodeJmpKurz (natByte 16) = [natByte 235, natByte 16] := by
  rfl

/-- PINNED BYTES: short `e -5` is `74 FB`. -/
theorem pin_rel8jcc_zurueck :
    encodeJccKurz .e (natByte 251) = [natByte 116, natByte 251] := by
  rfl

/-- PINNED BYTES: farthest forward short jump `EB 7F`. -/
theorem pin_rel8jmp_max :
    encodeJmpKurz (natByte 127) = [natByte 235, natByte 127] := by
  rfl

/-- PINNED BYTES: farthest backward short jump `EB 80`. -/
theorem pin_rel8jmp_min :
    encodeJmpKurz (natByte 128) = [natByte 235, natByte 128] := by
  rfl

/-- WIDE FALLBACK FITS: shifting a reachable displacement by the
    short/wide length difference (3 unconditional, 4 conditional) stays
    inside signed-32 range. Every premise is used. -/
theorem rel8_fallback_passt (d delta : Int) (h : rel8Passt d = true)
    (hdelta : delta = 3 ∨ delta = 4) :
    rel32Passt (d - delta) = true := by
  have hr := rel8Passt_grenzen d h
  simp only [rel32Passt, decide_eq_true_eq]
  rcases hdelta with rfl | rfl <;> omega

/-! ## Short-branch reachability connection.

    A reachable admitted short target is also wide-reachable at the
    same target: the wide displacement is the short one minus the
    short/wide length difference, the wide certificate is accepted,
    the wide target check admits it, and BOTH the reused short step
    and the reused wide step land on the target machine word. The
    short form therefore executes through the common architecture,
    and the wide form is a complete fallback. Every premise is used. -/

/-- CONNECTION (unconditional): a reachable admitted short jump has a
    wide fallback to the same target, and both reused steps land on
    the target word. -/
theorem Rel8Reach_verbindung (starts eintraege : List Adresse)
    (start ziel : Nat) (d : Int) (b : Byte)
    (s s' : Zustand)
    (hfit : rel8Passt d = true)
    (hgleich : (ziel : Int) = (start : Int) + 2 + d)
    (hd : disp8Signed b = d)
    (hstart : indirektZielOk starts eintraege (BitVec.ofNat 64 ziel) = true)
    (hrip : s.rip = BitVec.ofNat 64 start)
    (hkurz : jmpKurzSchritt 2 s b = some s')
    (hnext : start + 5 < 2 ^ 64) :
    ∃ d32 : BitVec 32,
      dispSigned d32 = d - 3 ∧
      zweigOk false ⟨start, 5, .weit, dispSigned d32, ziel⟩ = true ∧
      direktZielOk starts eintraege (BitVec.ofNat 64 start) 5 d32 = true ∧
      s'.rip = BitVec.ofNat 64 ziel ∧
      ∃ t'' : Zustand,
        schritt ⟨.jump32 d32, 5⟩ s = some t'' ∧
        t''.rip = BitVec.ofNat 64 ziel := by
  have hfitI := rel8Passt_grenzen d hfit
  obtain ⟨d32, hdisp⟩ := dispVonFit (d - 3) (by omega) (by omega)
  have hwide : (ziel : Int) = (start : Int) + 5 + (d - 3) := by omega
  have hfitw : rel32Passt (d - 3) = true :=
    rel8_fallback_passt d 3 hfit (Or.inl rfl)
  have hzweig : zweigOk false ⟨start, 5, .weit, dispSigned d32, ziel⟩ = true :=
    zweigOk_weit false ⟨start, 5, .weit, dispSigned d32, ziel⟩ rfl rfl
      (by rw [hdisp]; exact hwide) (by rw [hdisp]; exact hfitw)
  have hstart64 : start < 2 ^ 64 := by omega
  have hnext2 : start + 2 < 2 ^ 64 := by omega
  have hnach : BitVec.ofNat 64 start + BitVec.ofNat 64 5 =
      BitVec.ofNat 64 (start + 5) := by
    apply BitVec.eq_of_toNat_eq
    rw [rel32_next_rip _ _ hstart64 (by decide) hnext, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hnext]
  have hnach2 : BitVec.ofNat 64 start + BitVec.ofNat 64 2 =
      BitVec.ofNat 64 (start + 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [rel32_next_rip _ _ hstart64 (by decide) hnext2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hnext2]
  have hdef : (ziel : Int) = ((start + 2 : Nat) : Int) + d := by omega
  have hadr := rel32_adress_gleichung (start + 2) ziel d hdef
    (by omega) (by omega)
  have hkurz_rip := (jmpKurzSchritt_erfolg 2 s s' b (by decide) hkurz).1
  have hkurz_ziel : kurzZiel s.rip 2 b = BitVec.ofNat 64 ziel := by
    rw [hrip]
    unfold kurzZiel ripNach
    rw [hnach2, dispWort8_bridge, hd]
    exact hadr.symm
  have hdefw : (ziel : Int) = ((start + 5 : Nat) : Int) + (d - 3) := by omega
  have hadrw := rel32_adress_gleichung (start + 5) ziel (d - 3) hdefw
    (by omega) (by omega)
  have hdz : direktZiel (BitVec.ofNat 64 start) 5 d32 =
      BitVec.ofNat 64 ziel := by
    unfold direktZiel ripNach
    rw [hnach, dispWort_bridge, hdisp]
    exact hadrw.symm
  have hzok : direktZielOk starts eintraege (BitVec.ofNat 64 start) 5 d32 =
      true := by
    unfold direktZielOk
    rw [hdz]
    unfold indirektZielOk at hstart
    exact hstart
  have hwidestep : schritt ⟨.jump32 d32, 5⟩ s =
      some { s with rip := BitVec.ofNat 64 ziel } := by
    have hok5 : laengeOk 5 = true := by decide
    have hs := schritt_jump32 ⟨.jump32 d32, 5⟩ s d32 hok5 rfl
    have hripdz : ripNach s.rip 5 + dispWort d32 = BitVec.ofNat 64 ziel := by
      rw [hrip]
      unfold ripNach
      rw [hnach, dispWort_bridge, hdisp]
      exact hadrw.symm
    rw [hs, hripdz]
  exact ⟨d32, hdisp, hzweig, hzok, hkurz_rip.trans hkurz_ziel, _,
    hwidestep, rfl⟩

/-- CONNECTION (conditional taken): a reachable admitted taken short
    conditional jump has a wide fallback to the same target, and both
    reused steps land on the target word. Every premise is used. -/
theorem Rel8Reach_verbindung_bedingt (starts eintraege : List Adresse)
    (start ziel : Nat) (d : Int) (b : Byte) (c : Bedingung)
    (s s' : Zustand)
    (hfit : rel8Passt d = true)
    (hgleich : (ziel : Int) = (start : Int) + 2 + d)
    (hd : disp8Signed b = d)
    (hstart : indirektZielOk starts eintraege (BitVec.ofNat 64 ziel) = true)
    (hrip : s.rip = BitVec.ofNat 64 start)
    (hbed : bedingung c s.flags = true)
    (hjcc : jccKurzSchritt 2 s c b = some s')
    (hnext : start + 6 < 2 ^ 64) :
    ∃ d32 : BitVec 32,
      dispSigned d32 = d - 4 ∧
      zweigOk true ⟨start, 6, .weit, dispSigned d32, ziel⟩ = true ∧
      direktZielOk starts eintraege (BitVec.ofNat 64 start) 6 d32 = true ∧
      s'.rip = BitVec.ofNat 64 ziel ∧
      ∃ t'' : Zustand,
        schritt ⟨.jumpIf32 c d32, 6⟩ s = some t'' ∧
        t''.rip = BitVec.ofNat 64 ziel := by
  have hfitI := rel8Passt_grenzen d hfit
  obtain ⟨d32, hdisp⟩ := dispVonFit (d - 4) (by omega) (by omega)
  have hwide : (ziel : Int) = (start : Int) + 6 + (d - 4) := by omega
  have hfitw : rel32Passt (d - 4) = true :=
    rel8_fallback_passt d 4 hfit (Or.inr rfl)
  have hzweig : zweigOk true ⟨start, 6, .weit, dispSigned d32, ziel⟩ = true :=
    zweigOk_weit true ⟨start, 6, .weit, dispSigned d32, ziel⟩ rfl rfl
      (by rw [hdisp]; exact hwide) (by rw [hdisp]; exact hfitw)
  have hstart64 : start < 2 ^ 64 := by omega
  have hnext2 : start + 2 < 2 ^ 64 := by omega
  have hnach : BitVec.ofNat 64 start + BitVec.ofNat 64 6 =
      BitVec.ofNat 64 (start + 6) := by
    apply BitVec.eq_of_toNat_eq
    rw [rel32_next_rip _ _ hstart64 (by decide) hnext, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hnext]
  have hnach2 : BitVec.ofNat 64 start + BitVec.ofNat 64 2 =
      BitVec.ofNat 64 (start + 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [rel32_next_rip _ _ hstart64 (by decide) hnext2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hnext2]
  have hdef : (ziel : Int) = ((start + 2 : Nat) : Int) + d := by omega
  have hadr := rel32_adress_gleichung (start + 2) ziel d hdef
    (by omega) (by omega)
  have hok2 : laengeOk 2 = true := by decide
  have hjcc_eq := jccKurzSchritt_genommen 2 s c b hok2 hbed
  rw [hjcc_eq] at hjcc
  cases hjcc
  have hkurz_ziel : kurzZiel s.rip 2 b = BitVec.ofNat 64 ziel := by
    rw [hrip]
    unfold kurzZiel ripNach
    rw [hnach2, dispWort8_bridge, hd]
    exact hadr.symm
  have hdefw : (ziel : Int) = ((start + 6 : Nat) : Int) + (d - 4) := by omega
  have hadrw := rel32_adress_gleichung (start + 6) ziel (d - 4) hdefw
    (by omega) (by omega)
  have hdz : direktZiel (BitVec.ofNat 64 start) 6 d32 =
      BitVec.ofNat 64 ziel := by
    unfold direktZiel ripNach
    rw [hnach, dispWort_bridge, hdisp]
    exact hadrw.symm
  have hzok : direktZielOk starts eintraege (BitVec.ofNat 64 start) 6 d32 =
      true := by
    unfold direktZielOk
    rw [hdz]
    unfold indirektZielOk at hstart
    exact hstart
  have hok6 : laengeOk 6 = true := by decide
  have hwidestep : schritt ⟨.jumpIf32 c d32, 6⟩ s =
      some { s with rip := BitVec.ofNat 64 ziel } := by
    have hs := schritt_jumpIf32_genommen ⟨.jumpIf32 c d32, 6⟩ s c d32 hok6
      rfl hbed
    have hripdz : ripNach s.rip 6 + dispWort d32 = BitVec.ofNat 64 ziel := by
      rw [hrip]
      unfold ripNach
      rw [hnach, dispWort_bridge, hdisp]
      exact hadrw.symm
    rw [hs, hripdz]
  exact ⟨d32, hdisp, hzweig, hzok, hkurz_ziel, _, hwidestep, rfl⟩

/-! ## Joint witness: decoded short bytes, both steps, memory change.

    All premises of `Rel8Reach_verbindung` are instantiated jointly
    on concrete values (start 4096, rel8 +16, target 4114, an admitted
    decoded start); the short step and the wide fallback step both
    land on the target word; and a return-address store reads back
    with an observably changed byte, beside a planted wide-form
    refusal for the out-of-range displacement. -/

/-- JOINT WITNESS for `Rel8Reach_verbindung`: one actual short
    displacement (+16) reaches the admitted target 4114 through both
    the reused short step and the wide fallback field, with a
    memory-changing store beside them. -/
theorem Rel8Reach_verbindung_zeuge :
    ∃ (s' : Zustand) (d32 : BitVec 32) (m : Speicher),
      jmpKurzSchritt 2 zeugeZustand (natByte 16) = some s' ∧
      s'.rip = BitVec.ofNat 64 4114 ∧
      dispSigned d32 = 16 - 3 ∧
      zweigOk false ⟨4096, 5, .weit, dispSigned d32, 4114⟩ = true ∧
      direktZielOk [BitVec.ofNat 64 4114] [] (BitVec.ofNat 64 4096) 5 d32 =
        true ∧
      write64 zeugeSpeicher (BitVec.ofNat 64 8184) 4101 = some m ∧
      read64 m (BitVec.ofNat 64 8184) = some 4101 ∧
      m.bytes (BitVec.ofNat 64 8184) ≠
        zeugeSpeicher.bytes (BitVec.ofNat 64 8184) := by
  have hfit : rel8Passt 16 = true := by decide
  have hgleich : ((4114 : Nat) : Int) = ((4096 : Nat) : Int) + 2 + 16 := by
    decide
  have hd : disp8Signed (natByte 16) = 16 := pin_disp8_vor
  have hstart : indirektZielOk [BitVec.ofNat 64 4114] []
      (BitVec.ofNat 64 4114) = true := by
    decide
  have hrip : zeugeZustand.rip = BitVec.ofNat 64 4096 := rfl
  have hok2 : laengeOk 2 = true := by decide
  obtain ⟨s'kurz, hkurz⟩ : ∃ s' : Zustand,
      jmpKurzSchritt 2 zeugeZustand (natByte 16) = some s' :=
    ⟨_, by unfold jmpKurzSchritt; simp only [hok2]; rfl⟩
  have hnext : 4096 + 5 < 2 ^ 64 := by decide
  obtain ⟨d32, hdisp, hzweig, hzok, hripz, t'', hstep, hripz2⟩ :=
    Rel8Reach_verbindung [BitVec.ofNat 64 4114] [] 4096 4114 16
      (natByte 16) zeugeZustand s'kurz hfit hgleich hd hstart hrip hkurz
      hnext
  have hwr : write64 zeugeSpeicher (BitVec.ofNat 64 8184) 4101 =
      some { zeugeSpeicher with
        bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8184) 4101 } := by
    unfold write64
    rw [if_pos zweig_schreibbar8]
  have hread := read64_nach_write64 _ _ _ _ hwr zweig_lesbar8
  have hhit := writeBytesN_hit zeugeSpeicher
    (BitVec.ofNat 64 8184) 4101 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  have hdiff : writeBytesN zeugeSpeicher (BitVec.ofNat 64 8184) 4101 8
      (BitVec.ofNat 64 8184) ≠ zeugeSpeicher.bytes (BitVec.ofNat 64 8184) := by
    rw [hhit]
    decide
  refine ⟨_, d32, _, hkurz, hripz, hdisp, hzweig, hzok, hwr, hread, ?_⟩
  show writeBytesN zeugeSpeicher (BitVec.ofNat 64 8184) 4101 8
      (BitVec.ofNat 64 8184) ≠ zeugeSpeicher.bytes (BitVec.ofNat 64 8184)
  exact hdiff

/- CUTS:
    Manual provenance (checked clone-locally, no network): Intel SDM
    combined volumes 1-4, edition 325462-093US (September 2026),
    `.tmp/HARDWARE-REFERENCES/` (`REFERENCES.json`, verified
    2026-10-02; AMD retrieval failed, no AMD claim). Headings read:
    Vol.2A Ch.3 `JMP-Jump` (`EB cb JMP rel8`, "Jump short, RIP = RIP +
    8-bit displacement sign extended to 64-bits", p.3-504),
    `Jcc-Jump if Condition Is Met` (`7x cb` rel8 table, "Jump short if",
    p.3-499), and the relative-offset rule ("encoded as a signed 8-,
    16-, or 32-bit immediate value … added to … the address of the
    instruction following the JMP instruction", pp.3-504-3-505).
    Proved here (all over REUSED canonical helpers and accepted
    modules -- no `Befehl` constructor, decoder row, executor, address
    model or interpreter is added; no pilot file touched):
    - reachability vocabulary (`rel8Passt`, `disp8Signed` with bounds,
      every rel8 byte passes width-level fit) with byte pins for +16,
      -5 and the signed-8 extremes plus the just-out-of-range edges;
    - the sign-extension bridge (`bit7_equiv` reusing the accepted
      `testBit_div_pow`; `dispWort8_bridge` mirroring the accepted
      `dispWort_bridge`), so relocation address equations speak about
      the reused short `kurzZiel` step;
    - the selection (`rel8Wahl` over the reused `indirektZielOk`
      decoded-start check) with acceptance, both wide-fallback
      refusals (out of range, unadmitted target) and the
      start-or-entry guarantee;
    - pinned short bytes on the reused lane-680 encoders (`EB 10`,
      `74 FB`, `EB 7F`, `EB 80`) and the fallback-fit fact;
    - `Rel8Reach_verbindung` (unconditional) and
      `Rel8Reach_verbindung_bedingt` (taken conditional): a reachable
      admitted short target has a wide rel32 field to the SAME target
      (via the reused `dispVonFit`), the reused `zweigOk` accepts it,
      the reused `direktZielOk` admits it, and BOTH reused steps land
      on the target machine word;
    - the joint witness `Rel8Reach_verbindung_zeuge` (concrete
      +16/4114 instance of every premise, both steps on the target,
      a return-address store that reads back with an observably
      changed byte).
    NOT proved here, and not claimed:
    - No hardware correspondence: byte shapes follow the manual rows
      above through the accepted lane-680 encoders, checked here only
      as self-consistency (pins, bridges, refusals), not silicon;
      timing, caches, TLBs, CET/shadow-stack and asynchronous effects
      are untouched.
    - No new decoder, encoder, step or admission: short bytes, steps
      and the target check are the accepted lane-680 forms
      (`encodeJmpKurz`/`encodeJccKurz`, `jmpKurzSchritt`/
      `jccKurzSchritt`, `indirektZielOk`); pilot/short collision
      refusals stay proved there (`pilot_verweigert_kurz`,
      `pilot_verweigert_jccKurz`, `unser_verweigert_jump32`), never
      re-decided here.
    - No layout iteration: selection is per site at carried
      start/displacement/target values; whole-function narrowing
      convergence stays future work.
    - No source, IR, checker, emitter, contract, ABI, loader, entry,
      budget, cost or goal claim; no `Befehl` constructor is added.
    - No TSO/GX, concurrency, atomicity or tearing claim; every fact
      is sequential over one `Speicher`; absence of a transition is
      never a termination statement.
-/

#print axioms rel8Passt_grenzen
#print axioms disp8Signed_schranke
#print axioms disp8Signed_passt
#print axioms pin_disp8_vor
#print axioms pin_disp8_zurueck
#print axioms pin_disp8_max
#print axioms pin_disp8_min
#print axioms pin_reichweite_oben
#print axioms pin_reichweite_unten
#print axioms bit7_equiv
#print axioms dispWort8_bridge
#print axioms rel8Wahl_kurz
#print axioms rel8Wahl_weit_aussen
#print axioms rel8Wahl_weit_ohne_start
#print axioms rel8Wahl_garantiert
#print axioms pin_rel8jmp_vor
#print axioms pin_rel8jcc_zurueck
#print axioms pin_rel8jmp_max
#print axioms pin_rel8jmp_min
#print axioms rel8_fallback_passt
#print axioms Rel8Reach_verbindung
#print axioms Rel8Reach_verbindung_bedingt
#print axioms Rel8Reach_verbindung_zeuge

end Gabbro.Grammatik.X86
