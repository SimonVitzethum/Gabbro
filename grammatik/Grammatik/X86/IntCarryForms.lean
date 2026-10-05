/-
  File:      Grammatik/X86/IntCarryForms.lean
  Subject:   ADC/SBB/INC/DEC connected to the coherent machine and the
             unified byte dispatcher.

  Lane 1275: lifts ADC/SBB (with carry/borrow) and INC/DEC (CF-preserving)
  over the canonical `Wort`/`Breite`/`Flags`/`Zustand` vocabulary into the
  unified dispatcher path (`decodeExt` first, never shadowing the pilot)
  and into a `HwAdapter` over `HwMaschine`/`HwSchritt`
  (`HardwareExecution`). Widths 8/16/32/64 with the architectural merge
  discipline (8/16-bit merge, 32-bit zero-extend, 64-bit full); REX.W and
  the 66H prefix select the width; ModRM register forms run the register
  path, memory forms are TSO byte-issue events, never the register plug.
  One-byte 40H-4FH forms are REX prefixes in 64-bit mode, never INC/DEC.
  No silicon proof beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.NarrowOps
import Grammatik.X86.ArchitecturalFlags
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.MulDiv
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.FeatureProfile
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Operation class: ADC/SBB consume CF, INC/DEC preserve it. -/
inductive CarryKlasse where
  | adc | sbb | inc | dec
  deriving DecidableEq, Repr

/-! ## 1. Value layer: ADC/SBB with carry/borrow, INC/DEC without.

   Values reuse `addB`/`subB` (modular at the named width); carries,
   borrows, overflows and auxiliary carries read the truncated operands
   through `toNat`, like `cfAdd`/`cfSub`/`afAdd`/`afSub` in `Wort.lean`.
   SDM provenance (Intel 325462-093US, checked in
   `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
   ADC/SBB set OF/SF/ZF/AF/CF/PF per result including the carry-in;
   INC/DEC preserve CF and update OF/SF/ZF/AF/PF. -/

/-- Carry-in as a number: ADC/SBB add the incoming CF. -/
def adcEingang (c : Bool) : Nat := if c then 1 else 0

/-- ADC value: modular sum of the truncated operands plus carry-in. -/
def adcWert (b : Breite) (x y : Wort) (c : Bool) : Wort :=
  addB b (addB b x y) (if c then 1 else 0)

/-- ADC carry out: the full sum leaves the width. -/
def adcTrag (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  decide (2 ^ b.bits ≤
    (trunc b x).toNat + (trunc b y).toNat + adcEingang c)

/-- ADC signed overflow from the width-correct operand/result signs. -/
def adcUeberlauf (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  ((negB b x == negB b y) && (negB b (adcWert b x y c) != negB b x))

/-- ADC auxiliary carry: nibble sum including the carry-in. -/
def adcHilf (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  decide (16 ≤ (trunc b x).toNat % 16 + (trunc b y).toNat % 16 +
    adcEingang c)

/-- ADC flag snapshot: all six status bits defined, like ADD. -/
def adcFlags (b : Breite) (x y : Wort) (c : Bool) : Flags :=
  let r := adcWert b x y c
  { cf := adcTrag b x y c, pf := parityEven r, af := some (adcHilf b x y c),
    zf := zfTest r, sf := negB b r, of := adcUeberlauf b x y c }

/-- SBB value: modular difference of the truncated operands minus borrow. -/
def sbbWert (b : Breite) (x y : Wort) (c : Bool) : Wort :=
  subB b (subB b x y) (if c then 1 else 0)

/-- SBB borrow out: the subtrahend plus borrow exceeds the minuend. -/
def sbbEntleihn (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  decide ((trunc b x).toNat <
    (trunc b y).toNat + adcEingang c)

/-- SBB signed overflow from the width-correct operand/result signs. -/
def sbbUeberlauf (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  ((negB b x != negB b y) && (negB b (sbbWert b x y c) != negB b x))

/-- SBB auxiliary borrow: nibble difference including the borrow-in. -/
def sbbHilf (b : Breite) (x y : Wort) (c : Bool) : Bool :=
  decide ((trunc b x).toNat % 16 <
    (trunc b y).toNat % 16 + adcEingang c)

/-- SBB flag snapshot: all six status bits defined, like SUB. -/
def sbbFlags (b : Breite) (x y : Wort) (c : Bool) : Flags :=
  let r := sbbWert b x y c
  { cf := sbbEntleihn b x y c, pf := parityEven r,
    af := some (sbbHilf b x y c),
    zf := zfTest r, sf := negB b r, of := sbbUeberlauf b x y c }

/-- INC value: modular successor at the named width. -/
def incWert (b : Breite) (x : Wort) : Wort := addB b x 1

/-- DEC value: modular predecessor at the named width. -/
def decWert (b : Breite) (x : Wort) : Wort := subB b x 1

/-- INC overflow: the signed maximum wraps to the minimum. -/
def incUeberlauf (b : Breite) (x : Wort) : Bool :=
  ((!negB b x) && negB b (incWert b x))

/-- DEC overflow: the signed minimum wraps to the maximum. -/
def decUeberlauf (b : Breite) (x : Wort) : Bool :=
  ((negB b x) && !(negB b (decWert b x)))

/-- INC auxiliary carry: the low nibble was `0xF`. -/
def incHilf (b : Breite) (x : Wort) : Bool :=
  decide ((trunc b x).toNat % 16 = 15)

/-- DEC auxiliary borrow: the low nibble was `0x0`. -/
def decHilf (b : Breite) (x : Wort) : Bool :=
  decide ((trunc b x).toNat % 16 = 0)

/-- INC flags: CF preserved from the incoming snapshot, the rest updated. -/
def incFlags (b : Breite) (x : Wort) (f : Flags) : Flags :=
  let r := incWert b x
  { cf := f.cf, pf := parityEven r, af := some (incHilf b x),
    zf := zfTest r, sf := negB b r, of := incUeberlauf b x }

/-- DEC flags: CF preserved from the incoming snapshot, the rest updated. -/
def decFlags (b : Breite) (x : Wort) (f : Flags) : Flags :=
  let r := decWert b x
  { cf := f.cf, pf := parityEven r, af := some (decHilf b x),
    zf := zfTest r, sf := negB b r, of := decUeberlauf b x }

/-- The carry-in counts 0 and 1. -/
theorem adcEingang_werte : adcEingang false = 0 ∧ adcEingang true = 1 :=
  ⟨rfl, rfl⟩

/-- The set carry-in counts 1 (rewrite form). -/
theorem adcEingang_true : adcEingang true = 1 := rfl

/-- The clear carry-in counts 0 (rewrite form). -/
theorem adcEingang_false : adcEingang false = 0 := rfl

/-- Truncation at 64 bits keeps the unsigned value
    (`negB_b64` itself is reused from `ShiftLogic.lean`). -/
theorem trunc_b64_nat (w : Wort) : (trunc .b64 w).toNat = w.toNat := by
  rw [trunc_b64]

/-- ADC without carry-in is the modular sum at 64 bits. -/
theorem adcWert_b64_ohne (x y : Wort) :
    adcWert .b64 x y false = x + y := by
  simp [adcWert, addB, trunc_b64]

/-- ADC carry without carry-in is the ADD carry at 64 bits. -/
theorem adcTrag_b64_ohne (x y : Wort) :
    adcTrag .b64 x y false = cfAdd x y := by
  have hb : Breite.bits .b64 = 64 := rfl
  simp [adcTrag, cfAdd, adcEingang, trunc_b64_nat, hb]

/-- ADC auxiliary carry without carry-in is the ADD one at 64 bits. -/
theorem adcHilf_b64_ohne (x y : Wort) :
    adcHilf .b64 x y false = afAdd x y := by
  simp [adcHilf, afAdd, adcEingang, trunc_b64_nat]

/-- ADC overflow without carry-in is the ADD one at 64 bits. -/
theorem adcUeberlauf_b64_ohne (x y : Wort) :
    adcUeberlauf .b64 x y false =
      ofAdd (sfTest x) (sfTest y) (sfTest (x + y)) := by
  have hv := adcWert_b64_ohne x y
  simp only [adcUeberlauf, ofAdd, hv, negB_b64]

/-- AGREEMENT (64-bit): ADC with CF=0 IS the accepted ADD snapshot. -/
theorem adcFlags_b64_ohne (x y : Wort) :
    adcFlags .b64 x y false = (add64 x y).2 := by
  have hv := adcWert_b64_ohne x y
  simp only [adcFlags, add64, hv, adcTrag_b64_ohne x y,
    adcHilf_b64_ohne x y, adcUeberlauf_b64_ohne x y, negB_b64]

/-- SBB without borrow-in is the modular difference at 64 bits. -/
theorem sbbWert_b64_ohne (x y : Wort) :
    sbbWert .b64 x y false = x - y := by
  simp [sbbWert, subB, trunc_b64]

/-- SBB borrow without borrow-in is the SUB borrow at 64 bits. -/
theorem sbbEntleihn_b64_ohne (x y : Wort) :
    sbbEntleihn .b64 x y false = cfSub x y := by
  simp [sbbEntleihn, cfSub, adcEingang, trunc_b64_nat]

/-- SBB auxiliary borrow without borrow-in is the SUB one at 64 bits. -/
theorem sbbHilf_b64_ohne (x y : Wort) :
    sbbHilf .b64 x y false = afSub x y := by
  simp [sbbHilf, afSub, adcEingang, trunc_b64_nat]

/-- SBB overflow without borrow-in is the SUB one at 64 bits. -/
theorem sbbUeberlauf_b64_ohne (x y : Wort) :
    sbbUeberlauf .b64 x y false =
      ofSub (sfTest x) (sfTest y) (sfTest (x - y)) := by
  have hv := sbbWert_b64_ohne x y
  simp only [sbbUeberlauf, ofSub, hv, negB_b64]

/-- AGREEMENT (64-bit): SBB with CF=0 IS the accepted SUB snapshot. -/
theorem sbbFlags_b64_ohne (x y : Wort) :
    sbbFlags .b64 x y false = (sub64 x y).2 := by
  have hv := sbbWert_b64_ohne x y
  simp only [sbbFlags, sub64, hv, sbbEntleihn_b64_ohne x y,
    sbbHilf_b64_ohne x y, sbbUeberlauf_b64_ohne x y, negB_b64]

/-- CF-PRESERVATION: INC keeps the incoming carry. -/
theorem incFlags_cf (b : Breite) (x : Wort) (f : Flags) :
    (incFlags b x f).cf = f.cf := rfl

/-- CF-PRESERVATION: DEC keeps the incoming carry. -/
theorem decFlags_cf (b : Breite) (x : Wort) (f : Flags) :
    (decFlags b x f).cf = f.cf := rfl

/-- Every ADC value fits its width. -/
theorem adcWert_fits (b : Breite) (x y : Wort) (c : Bool) :
    (adcWert b x y c).toNat < 2 ^ b.bits := by
  unfold adcWert addB
  rw [narrowTruncMod]
  exact Nat.mod_lt _ (by cases b <;> decide)

/-- Every SBB value fits its width. -/
theorem sbbWert_fits (b : Breite) (x y : Wort) (c : Bool) :
    (sbbWert b x y c).toNat < 2 ^ b.bits := by
  unfold sbbWert subB
  rw [narrowTruncMod]
  exact Nat.mod_lt _ (by cases b <;> decide)

/-- Pinned ADC facts: nibble carry, byte carry, carry-in chaining. -/
theorem probe_adc_wert :
    adcWert .b8 0x0F 0x01 false = 0x10 ∧
    adcTrag .b8 0xFF 0x01 false = true ∧
    adcWert .b8 0xFF 0x01 true = 0x01 ∧
    adcTrag .b8 0xFF 0x01 true = true ∧
    adcWert .b64 0x0F 0x01 false = 0x10 := by
  decide

/-- Pinned SBB facts: nibble borrow, byte borrow, borrow-in chaining. -/
theorem probe_sbb_wert :
    sbbWert .b8 0x10 0x01 false = 0x0F ∧
    sbbEntleihn .b8 0x00 0x01 false = true ∧
    sbbWert .b8 0x10 0x01 true = 0x0E ∧
    sbbEntleihn .b8 0x01 0x01 true = true ∧
    sbbWert .b64 0x10 0x01 false = 0x0F := by
  decide

/-- Pinned INC/DEC facts: wrap, overflow shapes, CF preservation. -/
theorem probe_incdec_wert :
    incWert .b8 0xFF = 0x00 ∧
    incUeberlauf .b8 0x7F = true ∧
    incUeberlauf .b8 0xFF = false ∧
    decWert .b8 0x00 = 0xFF ∧
    decUeberlauf .b8 0x80 = true ∧
    decUeberlauf .b8 0x00 = false ∧
    (incFlags .b8 0x7F
      { cf := true, pf := false, af := none, zf := false, sf := false,
        of := false }).cf = true ∧
    (decFlags .b8 0x80
      { cf := true, pf := false, af := none, zf := false, sf := false,
        of := false }).cf = true := by
  decide

/-! ## 2. Register step: the family over the canonical state.

   `carrySchritt` handles ONLY register forms, reusing the canonical
   `laengeOk`/`ripNach`/`regSet` shapes, the §1 value/flag layer and the
   architectural merge discipline (`mergeRegNarrow`: 8/16-bit writes
   merge, 32-bit writes zero-extend, 64-bit writes are full). Memory
   operands are NOT admitted here: they are TSO byte-issue events (§5),
   never the register plug. There is no trap: ADC/SBB/INC/DEC cannot
   fault, so outcomes are successor or decode refusal. -/

/-- Family operations over registers: ADC/SBB consume the incoming CF,
    immediate forms carry the already-extended operand word (extension
    per opcode form is pinned at decode, §3), INC/DEC keep the CF. -/
inductive CarryBefehl where
  | adcReg (b : Breite) (dst src : Register)
  | sbbReg (b : Breite) (dst src : Register)
  | adcImm (b : Breite) (dst : Register) (op : Wort)
  | sbbImm (b : Breite) (dst : Register) (op : Wort)
  | incReg (b : Breite) (dst : Register)
  | decReg (b : Breite) (dst : Register)
  deriving DecidableEq, Repr

/-- Decoded family instruction: operation plus checked length data. -/
structure CarryDecodiert where
  befehl : CarryBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-- Step outcome: successor or decode refusal. -/
inductive CarryErgebnis where
  | ok (nach : Zustand)
  | misslungen

/-- Destination write with the architectural merge discipline. -/
def carrySchreibe (s : Zustand) (b : Breite) (dst : Register)
    (v : Wort) : Register → Wort :=
  regSet s.register dst (mergeRegNarrow b (s.register dst) v)

/-- One family step over registers; memory is untouched by construction. -/
def carrySchritt (d : CarryDecodiert) (s : Zustand) : CarryErgebnis :=
  match laengeOk d.laenge with
  | false => .misslungen
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .adcReg b dst src =>
      let v := adcWert b (s.register dst) (s.register src) s.flags.cf
      .ok { s with register := carrySchreibe s b dst v, rip := nach, flags := adcFlags b (s.register dst) (s.register src) s.flags.cf }
    | .sbbReg b dst src =>
      let v := sbbWert b (s.register dst) (s.register src) s.flags.cf
      .ok { s with register := carrySchreibe s b dst v, rip := nach, flags := sbbFlags b (s.register dst) (s.register src) s.flags.cf }
    | .adcImm b dst op =>
      let v := adcWert b (s.register dst) op s.flags.cf
      .ok { s with register := carrySchreibe s b dst v, rip := nach, flags := adcFlags b (s.register dst) op s.flags.cf }
    | .sbbImm b dst op =>
      let v := sbbWert b (s.register dst) op s.flags.cf
      .ok { s with register := carrySchreibe s b dst v, rip := nach, flags := sbbFlags b (s.register dst) op s.flags.cf }
    | .incReg b dst =>
      .ok { s with register := carrySchreibe s b dst (incWert b (s.register dst)), rip := nach, flags := incFlags b (s.register dst) s.flags }
    | .decReg b dst =>
      .ok { s with register := carrySchreibe s b dst (decWert b (s.register dst)), rip := nach, flags := decFlags b (s.register dst) s.flags }

/-! ## Step equations for the six forms: each pins the full successor;
    every premise is used. -/

/-- `adcReg`: the destination takes the carry sum with the ADC flags. -/
theorem carry_adc_erfolg (d : CarryDecodiert) (s : Zustand) (b : Breite)
    (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .adcReg b dst src) :
    carrySchritt d s = .ok { s with register := carrySchreibe s b dst (adcWert b (s.register dst) (s.register src) s.flags.cf), rip := ripNach s.rip d.laenge, flags := adcFlags b (s.register dst) (s.register src) s.flags.cf } := by
  unfold carrySchritt
  rw [hok, h]

/-- `sbbReg`: the destination takes the borrow difference with SBB flags. -/
theorem carry_sbb_erfolg (d : CarryDecodiert) (s : Zustand) (b : Breite)
    (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .sbbReg b dst src) :
    carrySchritt d s = .ok { s with register := carrySchreibe s b dst (sbbWert b (s.register dst) (s.register src) s.flags.cf), rip := ripNach s.rip d.laenge, flags := sbbFlags b (s.register dst) (s.register src) s.flags.cf } := by
  unfold carrySchritt
  rw [hok, h]

/-- `adcImm`: the destination takes the sum with the extended operand. -/
theorem carry_adcImm_erfolg (d : CarryDecodiert) (s : Zustand) (b : Breite)
    (dst : Register) (op : Wort)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .adcImm b dst op) :
    carrySchritt d s = .ok { s with register := carrySchreibe s b dst (adcWert b (s.register dst) op s.flags.cf), rip := ripNach s.rip d.laenge, flags := adcFlags b (s.register dst) op s.flags.cf } := by
  unfold carrySchritt
  rw [hok, h]

/-- `sbbImm`: the destination takes the difference with the operand. -/
theorem carry_sbbImm_erfolg (d : CarryDecodiert) (s : Zustand) (b : Breite)
    (dst : Register) (op : Wort)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .sbbImm b dst op) :
    carrySchritt d s = .ok { s with register := carrySchreibe s b dst (sbbWert b (s.register dst) op s.flags.cf), rip := ripNach s.rip d.laenge, flags := sbbFlags b (s.register dst) op s.flags.cf } := by
  unfold carrySchritt
  rw [hok, h]

/-- `incReg`: the destination takes the successor with CF preserved. -/
theorem carry_inc_erfolg (d : CarryDecodiert) (s : Zustand) (b : Breite)
    (dst : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .incReg b dst) :
    carrySchritt d s = .ok { s with register := carrySchreibe s b dst (incWert b (s.register dst)), rip := ripNach s.rip d.laenge, flags := incFlags b (s.register dst) s.flags } := by
  unfold carrySchritt
  rw [hok, h]

/-- `decReg`: the destination takes the predecessor with CF preserved. -/
theorem carry_dec_erfolg (d : CarryDecodiert) (s : Zustand) (b : Breite)
    (dst : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .decReg b dst) :
    carrySchritt d s = .ok { s with register := carrySchreibe s b dst (decWert b (s.register dst)), rip := ripNach s.rip d.laenge, flags := decFlags b (s.register dst) s.flags } := by
  unfold carrySchritt
  rw [hok, h]

/-- A bad decode length refuses every form, unconditionally. -/
theorem carry_laenge_misslungen (d : CarryDecodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) :
    carrySchritt d s = .misslungen := by
  unfold carrySchritt
  simp [h]

/-! ## Memory discipline and step-level agreements.

    Every success arm carries `speicher := s.speicher`; refusals carry
    no state. At 64 bits with CF=0 the ADC/SBB steps ARE the accepted
    ADD/SUB steps; INC/DEC steps preserve CF. -/

/-- A successful family step leaves canonical memory alone. -/
theorem carrySchritt_speicher (d : CarryDecodiert) (s s' : Zustand)
    (h : carrySchritt d s = CarryErgebnis.ok s') :
    s'.speicher = s.speicher := by
  unfold carrySchritt at h
  cases hlen : laengeOk d.laenge with
  | false =>
    simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases hbef : d.befehl with
    | adcReg b dst src =>
      simp [hbef] at h
      cases h
      rfl
    | sbbReg b dst src =>
      simp [hbef] at h
      cases h
      rfl
    | adcImm b dst op =>
      simp [hbef] at h
      cases h
      rfl
    | sbbImm b dst op =>
      simp [hbef] at h
      cases h
      rfl
    | incReg b dst =>
      simp [hbef] at h
      cases h
      rfl
    | decReg b dst =>
      simp [hbef] at h
      cases h
      rfl

/-- STEP CF-PRESERVATION: a successful INC step keeps the carry. -/
theorem carry_inc_schritt_cf (d : CarryDecodiert) (s : Zustand) (b : Breite)
    (dst : Register) (s' : Zustand)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .incReg b dst)
    (hstep : carrySchritt d s = .ok s') :
    s'.flags.cf = s.flags.cf := by
  rw [carry_inc_erfolg d s b dst hok h] at hstep
  cases hstep
  rfl

/-- STEP CF-PRESERVATION: a successful DEC step keeps the carry. -/
theorem carry_dec_schritt_cf (d : CarryDecodiert) (s : Zustand) (b : Breite)
    (dst : Register) (s' : Zustand)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .decReg b dst)
    (hstep : carrySchritt d s = .ok s') :
    s'.flags.cf = s.flags.cf := by
  rw [carry_dec_erfolg d s b dst hok h] at hstep
  cases hstep
  rfl

/-- STEP AGREEMENT (64-bit): ADC with CF=0 runs the accepted ADD step. -/
theorem carry_adc64_ohne_schritt (d : CarryDecodiert) (s : Zustand)
    (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .adcReg .b64 dst src)
    (hcf : s.flags.cf = false) :
    carrySchritt d s = .ok { s with register := regSet s.register dst (add64 (s.register dst) (s.register src)).1, rip := ripNach s.rip d.laenge, flags := (add64 (s.register dst) (s.register src)).2 } := by
  have hstep := carry_adc_erfolg d s .b64 dst src hok h
  simp only [carrySchreibe, hcf, adcWert_b64_ohne, adcFlags_b64_ohne, mergeRegNarrow_b64, add64] at hstep ⊢
  exact hstep

/-- STEP AGREEMENT (64-bit): SBB with CF=0 runs the accepted SUB step. -/
theorem carry_sbb64_ohne_schritt (d : CarryDecodiert) (s : Zustand)
    (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .sbbReg .b64 dst src)
    (hcf : s.flags.cf = false) :
    carrySchritt d s = .ok { s with register := regSet s.register dst (sub64 (s.register dst) (s.register src)).1, rip := ripNach s.rip d.laenge, flags := (sub64 (s.register dst) (s.register src)).2 } := by
  have hstep := carry_sbb_erfolg d s .b64 dst src hok h
  simp only [carrySchreibe, hcf, sbbWert_b64_ohne, sbbFlags_b64_ohne, mergeRegNarrow_b64, sub64] at hstep ⊢
  exact hstep

/-! ## Word-level `toNat` bridges for the multiword chain.

    Each bridge pins the 64-bit value/carry against unsigned `toNat`
    arithmetic; the chain theorems below reuse them, never a second
    adder. -/

/-- The word added for the carry-in counts the `adcEingang` number. -/
theorem eingang_wort_nat (c : Bool) :
    ((if c then (1 : Wort) else 0)).toNat = adcEingang c := by
  cases c <;> decide

/-- ADC value at 64 bits as unsigned `toNat` arithmetic. -/
theorem adcWert_b64_nat (x y : Wort) (c : Bool) :
    (adcWert .b64 x y c).toNat =
      (x.toNat + y.toNat + adcEingang c) % 2 ^ 64 := by
  have hv : adcWert .b64 x y c = x + y + (if c then 1 else 0 : Wort) := by
    simp [adcWert, addB, trunc_b64]
  rw [hv, BitVec.toNat_add, BitVec.toNat_add, eingang_wort_nat,
    Nat.mod_add_mod]

/-- ADC carry at 64 bits as an unsigned range test. -/
theorem adcTrag_b64_nat (x y : Wort) (c : Bool) :
    adcTrag .b64 x y c =
      decide (2 ^ 64 ≤ x.toNat + y.toNat + adcEingang c) := by
  have hb : Breite.bits .b64 = 64 := rfl
  simp [adcTrag, trunc_b64_nat, hb]

/-- SBB value at 64 bits as unsigned `toNat` arithmetic. -/
theorem sbbWert_b64_nat (x y : Wort) (c : Bool) :
    (sbbWert .b64 x y c).toNat =
      (x.toNat + 2 ^ 64 - y.toNat - adcEingang c) % 2 ^ 64 := by
  have hv : sbbWert .b64 x y c = x - y - (if c then 1 else 0 : Wort) := by
    simp [sbbWert, subB, trunc_b64]
  have hx := x.isLt
  have hy := y.isLt
  rw [hv, BitVec.toNat_sub, BitVec.toNat_sub, eingang_wort_nat]
  cases c <;> simp only [adcEingang_false, adcEingang_true] <;> omega

/-- SBB borrow at 64 bits as an unsigned range test. -/
theorem sbbEntleihn_b64_nat (x y : Wort) (c : Bool) :
    sbbEntleihn .b64 x y c =
      decide (x.toNat < y.toNat + adcEingang c) := by
  simp [sbbEntleihn, trunc_b64_nat]

/-! ## Multiword chain: ADD then ADC (SUB then SBB) over 128 bits.

    The low words run through ADD/SUB (CF=0), the high words through
    ADC/SBB with the low carry/borrow; the pair is the 128-bit modular
    sum/difference (`u128` reused from `MulDiv.lean`) and the final
    carry/borrow is the 128-bit carry out/borrow. -/

/-- CHAIN (multiword ADD): ADD then ADC computes the 128-bit sum with
    the 128-bit carry out. -/
theorem adc_kette_128 (x0 x1 y0 y1 : Wort) :
    u128 (adcWert .b64 x1 y1 (adcTrag .b64 x0 y0 false)) (adcWert .b64 x0 y0 false) = (u128 x1 x0 + u128 y1 y0) % 2 ^ 128 ∧
    adcTrag .b64 x1 y1 (adcTrag .b64 x0 y0 false) = decide (2 ^ 128 ≤ u128 x1 x0 + u128 y1 y0) := by
  have hfalse : adcEingang false = 0 := rfl
  have hx0 := x0.isLt
  have hx1 := x1.isLt
  have hy0 := y0.isLt
  have hy1 := y1.isLt
  have hcNat := adcTrag_b64_nat x0 y0 false
  simp only [u128]
  rw [adcWert_b64_nat, adcWert_b64_nat, hfalse, hcNat]
  cases hc : decide (2 ^ 64 ≤ x0.toNat + y0.toNat + adcEingang false) with
  | false =>
    have hP := of_decide_eq_false hc
    rw [hfalse] at hP
    simp only [adcTrag_b64_nat, hfalse] at ⊢
    refine ⟨by omega, ?_⟩
    have g2 : (2 ^ 64 ≤ x1.toNat + y1.toNat + 0) ↔
        (2 ^ 128 ≤ x1.toNat * 2 ^ 64 + x0.toNat +
          (y1.toNat * 2 ^ 64 + y0.toNat)) := by
      constructor <;> intro h <;> omega
    simp only [g2]
    congr 1
  | true =>
    have hP := of_decide_eq_true hc
    rw [hfalse] at hP
    simp only [adcTrag_b64_nat, adcEingang_true] at ⊢
    refine ⟨by omega, ?_⟩
    have g2 : (2 ^ 64 ≤ x1.toNat + y1.toNat + 1) ↔
        (2 ^ 128 ≤ x1.toNat * 2 ^ 64 + x0.toNat +
          (y1.toNat * 2 ^ 64 + y0.toNat)) := by
      constructor <;> intro h <;> omega
    simp only [g2]
    congr 1

/-- CHAIN (multiword SUB): SUB then SBB computes the 128-bit difference
    with the 128-bit borrow out. -/
theorem sbb_kette_128 (x0 x1 y0 y1 : Wort) :
    u128 (sbbWert .b64 x1 y1 (sbbEntleihn .b64 x0 y0 false)) (sbbWert .b64 x0 y0 false) = (u128 x1 x0 + 2 ^ 128 - u128 y1 y0) % 2 ^ 128 ∧
    sbbEntleihn .b64 x1 y1 (sbbEntleihn .b64 x0 y0 false) = decide (u128 x1 x0 < u128 y1 y0) := by
  have hfalse : adcEingang false = 0 := rfl
  have hx0 := x0.isLt
  have hx1 := x1.isLt
  have hy0 := y0.isLt
  have hy1 := y1.isLt
  have hbNat := sbbEntleihn_b64_nat x0 y0 false
  simp only [u128]
  rw [sbbWert_b64_nat, sbbWert_b64_nat, hfalse, hbNat]
  cases hb : decide (x0.toNat < y0.toNat + adcEingang false) with
  | false =>
    have hP := of_decide_eq_false hb
    rw [hfalse] at hP
    simp only [sbbEntleihn_b64_nat, hfalse] at ⊢
    refine ⟨by omega, ?_⟩
    have g2 : (x1.toNat < y1.toNat + 0) ↔
        (x1.toNat * 2 ^ 64 + x0.toNat <
          y1.toNat * 2 ^ 64 + y0.toNat) := by
      constructor <;> intro h <;> omega
    simp only [g2]
    congr 1
  | true =>
    have hP := of_decide_eq_true hb
    rw [hfalse] at hP
    simp only [sbbEntleihn_b64_nat, adcEingang_true] at ⊢
    refine ⟨by omega, ?_⟩
    have g2 : (x1.toNat < y1.toNat + 1) ↔
        (x1.toNat * 2 ^ 64 + x0.toNat <
          y1.toNat * 2 ^ 64 + y0.toNat) := by
      constructor <;> intro h <;> omega
    simp only [g2]
    congr 1

/- CUTS:
    Value/flag layer (§1) and register step skeleton (§2) stand.
    NOT proved here, and not claimed: memory discipline of the step,
    64-bit step agreements, the multiword chain, decode/encode,
    the machine adapter, the witness (see lane task).
-/

#print axioms CarryKlasse

end Gabbro.Grammatik.X86
