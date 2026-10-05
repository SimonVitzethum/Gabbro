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

/-! ## 3. Codec: canonical bytes for the family.

   SDM opcode map (Intel 325462-093US, ADC/SBB/INC/DEC entries, checked
   against `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
   ADC 10H/11H/12H/13H (`/r`), 14H (`AL,Ib`), 15H (`eAX,Iz`), Group 1
   80H/81H/83H (`/2`); SBB 18H-1BH, 1CH, 1DH, Group 1 `/3`; INC/DEC
   FEH (`/0` INC, `/1` DEC, byte) and FFH (`/0` INC, `/1` DEC, Ev).
   40H-4FH are REX prefixes in 64-bit mode, never one-byte INC/DEC.
   Width: REX.W selects 64, 66H selects 16, else 32 (Ev forms); Eb
   forms are always 8-bit. Only register-direct (mod=11) ModRM runs
   the register path; mod/=11 decodes to a memory descriptor for the
   TSO path (§5), never the register plug. -/

/-- Memory-form class. -/
inductive MemKlasse where
  | adc | sbb | inc | dec
  deriving DecidableEq, Repr

/-- Memory operand descriptor: class, width, whether the destination
    is memory (store/RMW) or a register (load), the raw ModRM byte,
    displacement bytes, and the consumed length. SIB (`rm=4`) and
    RIP-relative (`mod=0,rm=5`) shapes decode but never resolve (§5). -/
structure CarryMem where
  klasse : MemKlasse
  breite : Breite
  speichernd : Bool
  modrm : Nat
  basis : Nat
  disp : List Byte
  laenge : Nat
  deriving DecidableEq, Repr

/-- One decoded family instruction: register form or memory form. -/
inductive CarryInstr where
  | reg : CarryDecodiert → CarryInstr
  | mem : CarryMem → CarryInstr
  deriving DecidableEq, Repr

/-- Width from prefix bits: REX.W selects 64, 66H selects 16, else 32. -/
def carryBreite (rexW op66 : Bool) : Breite :=
  if rexW then .b64 else if op66 then .b16 else .b32

/-- REX.W always means 64 bits. -/
theorem carryBreite_rexW (op66 : Bool) : carryBreite true op66 = .b64 :=
  rfl

/-- 66H without REX.W means 16 bits. -/
theorem carryBreite_16 : carryBreite false true = .b16 := rfl

/-- No prefix means 32 bits. -/
theorem carryBreite_32 : carryBreite false false = .b32 := rfl

/-- High-byte refusal: codes 4-7 name AH/CH/DH/BH (no REX) or
    SPL/BPL/SIL/DIL (REX), neither in the `Register` vocabulary
    (SDM Vol. 1 3.4.1.1). Codes 0-3 and 8-15 are always fine. -/
def hochbyteCode (code : Nat) : Bool := decide (4 ≤ code ∧ code < 8)

/-- Pinned high-byte classification. -/
theorem probe_hochbyteCode :
    hochbyteCode 3 = false ∧ hochbyteCode 4 = true ∧
    hochbyteCode 7 = true ∧ hochbyteCode 8 = false := by
  decide

/-- 8-bit immediate value (Group 80H, AL forms). -/
def imm8Wert (v : Byte) : Wort := BitVec.ofNat 64 (byteNat v)

/-- 16-bit immediate value, zero-extended (narrowing truncates anyway). -/
def imm16Wert (d : BitVec 16) : Wort := BitVec.ofNat 64 d.toNat

/-- 32-bit immediate value: plain at 16/32 bits, sign-extended at 64
    bits (REX.W `81 /id` and `15 id` take imm32, SDM Vol. 2A 3-14). -/
def imm32Wert (b : Breite) (d : BitVec 32) : Wort :=
  if b = .b64 then sext .b32 (BitVec.ofNat 64 d.toNat)
  else BitVec.ofNat 64 d.toNat

/-- Sign-extended 8-bit immediate (Group 83H); plain at 8 bits. -/
def imm8Sext (b : Breite) (v : Byte) : Wort :=
  if b = .b8 then BitVec.ofNat 64 (byteNat v)
  else sext .b8 (BitVec.ofNat 64 (byteNat v))

/-- Parse two little-endian bytes, returning the rest. -/
def parseLe16 : List Byte → Option (BitVec 16 × List Byte)
  | b0 :: b1 :: rest =>
    some (BitVec.ofNat 16 (byteNat b0 + byteNat b1 * 256), rest)
  | _ => none

/-- Canonical immediate operand: what decode reads back from the
    canonical encoding (§3b writes exactly these bytes). -/
def canonImm (b : Breite) (op : Wort) : Wort :=
  match b with
  | .b8 => imm8Wert (wortByte op 0)
  | .b16 => imm16Wert (BitVec.ofNat 16 (byteNat (wortByte op 0) + byteNat (wortByte op 1) * 256))
  | .b32 => imm32Wert .b32 (BitVec.ofNat 32 (byteNat (wortByte op 0) + byteNat (wortByte op 1) * 256 + byteNat (wortByte op 2) * 65536 + byteNat (wortByte op 3) * 16777216))
  | .b64 => imm32Wert .b64 (BitVec.ofNat 32 (byteNat (wortByte op 0) + byteNat (wortByte op 1) * 256 + byteNat (wortByte op 2) * 65536 + byteNat (wortByte op 3) * 16777216))

/-- Register operand from full codes with the high-byte refusal. -/
def decodeCarryReg (alu : Bool) (b : Breite) (dstCode srcCode : Nat)
    (len : Nat) :
    List Byte → Option (CarryInstr × List Byte)
  | rest =>
    if decide (b = .b8) && (hochbyteCode dstCode || hochbyteCode srcCode) then
      none
    else match codeReg dstCode, codeReg srcCode with
    | some dst, some src =>
      some (.reg ⟨if alu then .adcReg b dst src else .sbbReg b dst src, len⟩, rest)
    | _, _ => none

/-- INC/DEC register operand from the full code. -/
def decodeCarryIndee (inc : Bool) (b : Breite) (dstCode : Nat)
    (len : Nat) :
    List Byte → Option (CarryInstr × List Byte)
  | rest =>
    if decide (b = .b8) && hochbyteCode dstCode then none
    else match codeReg dstCode with
    | some dst =>
      some (.reg ⟨if inc then .incReg b dst else .decReg b dst, len⟩, rest)
    | none => none

/-- Immediate operand after its bytes: value plus consumed length. -/
def immLies (immKind : Nat) (b : Breite) :
    List Byte → Option (Wort × List Byte)
  | rest =>
    match immKind with
    | 0 =>
      match rest with
      | ib :: rest' => some (imm8Wert ib, rest')
      | _ => none
    | 1 =>
      match parseLe16 rest with
      | some (d, rest') => some (imm16Wert d, rest')
      | none => none
    | 2 =>
      match parseLe32 rest with
      | some (d, rest') => some (imm32Wert b d, rest')
      | none => none
    | _ =>
      match rest with
      | ib :: rest' => some (imm8Sext b ib, rest')
      | _ => none

/-- Immediate length by kind: imm8/imm16/imm32/sex8 (the 83H form
    carries one byte). -/
def immLenOf : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | _ => 1

/-- Group-1 register destination with the extended operand. -/
def decodeGruppe1Reg (adc : Bool) (b : Breite) (dstCode : Nat) (op : Wort)
    (len : Nat) :
    List Byte → Option (CarryInstr × List Byte)
  | rest =>
    if decide (b = .b8) && hochbyteCode dstCode then none
    else match codeReg dstCode with
    | some dst =>
      some (.reg ⟨if adc then .adcImm b dst op else .sbbImm b dst op, len⟩, rest)
    | none => none

/-- Group-1 ModRM: register destination runs the register path with
    the extended operand, memory goes to a descriptor (RMW store). -/
def decodeGruppe1 (adc : Bool) (b : Breite) (immKind : Nat) (bBit : Nat)
    (len : Nat) (m : Byte) :
    List Byte → Option (CarryInstr × List Byte)
  | rest =>
    let mod := byteNat m / 64
    let rm := byteNat m % 8
    if mod == 3 then
      match immLies immKind b rest with
      | some (op, rest') =>
        decodeGruppe1Reg adc b (bBit * 8 + rm) op (len + immLenOf immKind) rest'
      | none => none
    else
      let k := if adc then MemKlasse.adc else MemKlasse.sbb
      match mod, rm with
      | 1, _ =>
        match rest with
        | d0 :: rest1 =>
          match immLies immKind b rest1 with
          | some (_, rest') =>
            some (.mem ⟨k, b, true, byteNat m, bBit * 8 + rm, [d0], len + 1 + immLenOf immKind⟩, rest')
          | none => none
        | _ => none
      | 2, _ =>
        match rest with
        | d0 :: d1 :: d2 :: d3 :: rest1 =>
          match immLies immKind b rest1 with
          | some (_, rest') =>
            some (.mem ⟨k, b, true, byteNat m, bBit * 8 + rm, [d0, d1, d2, d3], len + 4 + immLenOf immKind⟩, rest')
          | none => none
        | _ => none
      | _, 5 =>
        match rest with
        | d0 :: d1 :: d2 :: d3 :: rest1 =>
          match immLies immKind b rest1 with
          | some (_, rest') =>
            some (.mem ⟨k, b, true, byteNat m, bBit * 8 + rm, [d0, d1, d2, d3], len + 4 + immLenOf immKind⟩, rest')
          | none => none
        | _ => none
      | _, _ =>
        match immLies immKind b rest with
        | some (_, rest') =>
          some (.mem ⟨k, b, true, byteNat m, bBit * 8 + rm, [], len + immLenOf immKind⟩, rest')
        | none => none

/-- ModRM dispatch for the `/r` forms: register-direct runs the
    register path (`dstRm` says whether r/m is the destination),
    anything else becomes a memory descriptor. -/
def decodeCarryModrm (alu : Bool) (b : Breite) (rBit bBit : Nat)
    (dstRm : Bool) (len : Nat) (m : Byte) :
    List Byte → Option (CarryInstr × List Byte)
  | rest =>
    let mod := byteNat m / 64
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    if mod == 3 then
      if dstRm then decodeCarryReg alu b (bBit * 8 + rm) (rBit * 8 + reg) len rest
      else decodeCarryReg alu b (rBit * 8 + reg) (bBit * 8 + rm) len rest
    else
      let k := if alu then MemKlasse.adc else MemKlasse.sbb
      match mod, rm with
      | 1, _ =>
        match rest with
        | d0 :: rest' =>
          some (.mem ⟨k, b, dstRm, byteNat m, bBit * 8 + rm, [d0], len + 1⟩, rest')
        | _ => none
      | 2, _ =>
        match rest with
        | d0 :: d1 :: d2 :: d3 :: rest' =>
          some (.mem ⟨k, b, dstRm, byteNat m, bBit * 8 + rm, [d0, d1, d2, d3], len + 4⟩, rest')
        | _ => none
      | _, 5 =>
        match rest with
        | d0 :: d1 :: d2 :: d3 :: rest' =>
          some (.mem ⟨k, b, dstRm, byteNat m, bBit * 8 + rm, [d0, d1, d2, d3], len + 4⟩, rest')
        | _ => none
      | _, _ => some (.mem ⟨k, b, dstRm, byteNat m, bBit * 8 + rm, [], len⟩, rest)

/-- INC/DEC ModRM: `/0` is INC, `/1` is DEC, anything else refuses
    (FF `/2` to `/7` are CALL/JMP/PUSH, never INC/DEC). -/
def decodeCarryIncDecModrm (b : Breite) (bBit : Nat) (len : Nat)
    (m : Byte) :
    List Byte → Option (CarryInstr × List Byte)
  | rest =>
    let mod := byteNat m / 64
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match reg with
    | 0 =>
      if mod == 3 then decodeCarryIndee true b (bBit * 8 + rm) len rest
      else
        match mod, rm with
        | 1, _ =>
          match rest with
          | d0 :: rest' =>
            some (.mem ⟨.inc, b, true, byteNat m, bBit * 8 + rm, [d0], len + 1⟩, rest')
          | _ => none
        | 2, _ =>
          match rest with
          | d0 :: d1 :: d2 :: d3 :: rest' =>
            some (.mem ⟨.inc, b, true, byteNat m, bBit * 8 + rm, [d0, d1, d2, d3], len + 4⟩, rest')
          | _ => none
        | _, 5 =>
          match rest with
          | d0 :: d1 :: d2 :: d3 :: rest' =>
            some (.mem ⟨.inc, b, true, byteNat m, bBit * 8 + rm, [d0, d1, d2, d3], len + 4⟩, rest')
          | _ => none
        | _, _ => some (.mem ⟨.inc, b, true, byteNat m, bBit * 8 + rm, [], len⟩, rest)
    | 1 =>
      if mod == 3 then decodeCarryIndee false b (bBit * 8 + rm) len rest
      else
        match mod, rm with
        | 1, _ =>
          match rest with
          | d0 :: rest' =>
            some (.mem ⟨.dec, b, true, byteNat m, bBit * 8 + rm, [d0], len + 1⟩, rest')
          | _ => none
        | 2, _ =>
          match rest with
          | d0 :: d1 :: d2 :: d3 :: rest' =>
            some (.mem ⟨.dec, b, true, byteNat m, bBit * 8 + rm, [d0, d1, d2, d3], len + 4⟩, rest')
          | _ => none
        | _, 5 =>
          match rest with
          | d0 :: d1 :: d2 :: d3 :: rest' =>
            some (.mem ⟨.dec, b, true, byteNat m, bBit * 8 + rm, [d0, d1, d2, d3], len + 4⟩, rest')
          | _ => none
        | _, _ => some (.mem ⟨.dec, b, true, byteNat m, bBit * 8 + rm, [], len⟩, rest)
    | _ => none

/-- Opcode dispatch after the prefix: every ADC/SBB/INC/DEC opcode
    of the family map, nothing else. `plen` is the consumed prefix
    length (0 or 1); `rBit`/`bBit` extend the ModRM fields. -/
def decodeCarryOp (rexW rexR rexB op66 : Bool) (plen : Nat) (op : Byte) :
    List Byte → Option (CarryInstr × List Byte)
  | rest =>
    let bEv := carryBreite rexW op66
    let rBit := if rexR then 1 else 0
    let bBit := if rexB then 1 else 0
    match byteNat op with
    | 16 =>
      match rest with
      | m :: rest' => decodeCarryModrm true .b8 rBit bBit true (plen + 2) m rest'
      | _ => none
    | 17 =>
      match rest with
      | m :: rest' => decodeCarryModrm true bEv rBit bBit true (plen + 2) m rest'
      | _ => none
    | 18 =>
      match rest with
      | m :: rest' => decodeCarryModrm true .b8 rBit bBit false (plen + 2) m rest'
      | _ => none
    | 19 =>
      match rest with
      | m :: rest' => decodeCarryModrm true bEv rBit bBit false (plen + 2) m rest'
      | _ => none
    | 20 =>
      match rest with
      | ib :: rest' => some (.reg ⟨.adcImm .b8 .rax (imm8Wert ib), plen + 2⟩, rest')
      | _ => none
    | 21 =>
      if op66 then
        match parseLe16 rest with
        | some (d, rest') => some (.reg ⟨.adcImm .b16 .rax (imm16Wert d), plen + 3⟩, rest')
        | none => none
      else
        match parseLe32 rest with
        | some (d, rest') => some (.reg ⟨.adcImm bEv .rax (imm32Wert bEv d), plen + 5⟩, rest')
        | none => none
    | 24 =>
      match rest with
      | m :: rest' => decodeCarryModrm false .b8 rBit bBit true (plen + 2) m rest'
      | _ => none
    | 25 =>
      match rest with
      | m :: rest' => decodeCarryModrm false bEv rBit bBit true (plen + 2) m rest'
      | _ => none
    | 26 =>
      match rest with
      | m :: rest' => decodeCarryModrm false .b8 rBit bBit false (plen + 2) m rest'
      | _ => none
    | 27 =>
      match rest with
      | m :: rest' => decodeCarryModrm false bEv rBit bBit false (plen + 2) m rest'
      | _ => none
    | 28 =>
      match rest with
      | ib :: rest' => some (.reg ⟨.sbbImm .b8 .rax (imm8Wert ib), plen + 2⟩, rest')
      | _ => none
    | 29 =>
      if op66 then
        match parseLe16 rest with
        | some (d, rest') => some (.reg ⟨.sbbImm .b16 .rax (imm16Wert d), plen + 3⟩, rest')
        | none => none
      else
        match parseLe32 rest with
        | some (d, rest') => some (.reg ⟨.sbbImm bEv .rax (imm32Wert bEv d), plen + 5⟩, rest')
        | none => none
    | 128 =>
      match rest with
      | m :: rest' =>
        match byteNat m / 8 % 8 with
        | 2 => decodeGruppe1 true .b8 0 bBit (plen + 2) m rest'
        | 3 => decodeGruppe1 false .b8 0 bBit (plen + 2) m rest'
        | _ => none
      | _ => none
    | 129 =>
      match rest with
      | m :: rest' =>
        match byteNat m / 8 % 8 with
        | 2 => decodeGruppe1 true bEv (if op66 then 1 else 2) bBit (plen + 2) m rest'
        | 3 => decodeGruppe1 false bEv (if op66 then 1 else 2) bBit (plen + 2) m rest'
        | _ => none
      | _ => none
    | 131 =>
      match rest with
      | m :: rest' =>
        match byteNat m / 8 % 8 with
        | 2 => decodeGruppe1 true bEv 3 bBit (plen + 2) m rest'
        | 3 => decodeGruppe1 false bEv 3 bBit (plen + 2) m rest'
        | _ => none
      | _ => none
    | 254 =>
      match rest with
      | m :: rest' => decodeCarryIncDecModrm .b8 bBit (plen + 2) m rest'
      | _ => none
    | 255 =>
      match rest with
      | m :: rest' => decodeCarryIncDecModrm bEv bBit (plen + 2) m rest'
      | _ => none
    | _ => none

/-- One family decoder: an optional 66H prefix (which may itself be
    followed by one REX prefix for extended 16-bit registers), or one
    REX prefix, then the opcode. Anything else in a prefix slot reads
    as the opcode and refuses below with a named reason. -/
def decodeCarry : List Byte → Option (CarryInstr × List Byte)
  | [] => none
  | b :: rest =>
    if byteNat b == 102 then
      match rest with
      | [] => none
      | b2 :: rest' =>
        if decide (64 ≤ byteNat b2 ∧ byteNat b2 < 80) then
          match rest' with
          | [] => none
          | op :: rest'' =>
            decodeCarryOp (byteNat b2 / 8 % 2 == 1)
              (byteNat b2 / 4 % 2 == 1) (byteNat b2 % 2 == 1) true 2 op
              rest''
        else decodeCarryOp false false false true 1 b2 rest'
    else if decide (64 ≤ byteNat b ∧ byteNat b < 80) then
      match rest with
      | [] => none
      | op :: rest' =>
        decodeCarryOp (byteNat b / 8 % 2 == 1) (byteNat b / 4 % 2 == 1)
          (byteNat b % 2 == 1) false 1 op rest'
    else decodeCarryOp false false false false 0 b rest

/-! ## Named refusal reasons.

    Shallow shapes (LOCK, address-size, double prefix, one-byte
    INC/DEC, truncation, non-carry opcodes) name their reason through
    `ablehnGrund`. Group shapes (wrong extension digit, high-byte
    codes) name theirs in the refusal theorems beside the pins, since
    the reason needs the ModRM byte. -/

/-- Named refusal reasons for unsupported encodings. -/
inductive AblehnGrund where
  | lock | adressGroesse | doppelPraefix | einByteIncDec | unvollstaendig
  | keinTrageform | falscheErweiterung | hochbyte
  deriving DecidableEq, Repr

/-- A prefix-class byte: 66H or any REX 40H-4FH. -/
def istPraefixByte (n : Nat) : Bool :=
  (n == 102) || decide (64 ≤ n ∧ n < 80)

/-! ## Canonical encode and round trips.

    The canonical encoding uses the `/r` ADC/SBB direction with the
    destination in r/m, Group-1 `/2`/`/3` for immediates, and FF/FE
    `/0`/`/1` for INC/DEC, with the minimal prefix (REX.W at 64, 66H
    at 16, REX0 exactly where extended registers occur). At 8 bits
    the high-byte codes 4-7 encode to the bytes the decoder refuses
    (named asymmetry, pinned below): the vocabulary has no AH/SPL. -/

/-- REX prefix without W (8/16/32-bit extended registers). -/
def rexByte0 (rh bh : Nat) : Byte := natByte (64 + 4 * rh + bh)

/-- Canonical prefix bytes for a width and extension bits. -/
def carryPrefix (b : Breite) (rh bh : Nat) : List Byte :=
  match b with
  | .b64 => [rexByte rh bh]
  | .b16 =>
    if rh == 1 || bh == 1 then [natByte 102, rexByte0 rh bh]
    else [natByte 102]
  | _ =>
    if rh == 1 || bh == 1 then [rexByte0 rh bh] else []

/-- Canonical encoding of one register-form operation. -/
def carryEncode : CarryBefehl → List Byte
  | .adcReg b dst src =>
    let pre := carryPrefix b (regHigh src) (regHigh dst)
    let opc := if b = .b8 then natByte 16 else natByte 17
    pre ++ [opc, modrmReg (regLow src) (regLow dst)]
  | .sbbReg b dst src =>
    let pre := carryPrefix b (regHigh src) (regHigh dst)
    let opc := if b = .b8 then natByte 24 else natByte 25
    pre ++ [opc, modrmReg (regLow src) (regLow dst)]
  | .adcImm b dst op =>
    let pre := carryPrefix b 0 (regHigh dst)
    match b with
    | .b8 => pre ++ [natByte 128, modrmReg 2 (regLow dst), wortByte op 0]
    | .b16 => pre ++ [natByte 129, modrmReg 2 (regLow dst), wortByte op 0, wortByte op 1]
    | _ => pre ++ [natByte 129, modrmReg 2 (regLow dst), wortByte op 0, wortByte op 1, wortByte op 2, wortByte op 3]
  | .sbbImm b dst op =>
    let pre := carryPrefix b 0 (regHigh dst)
    match b with
    | .b8 => pre ++ [natByte 128, modrmReg 3 (regLow dst), wortByte op 0]
    | .b16 => pre ++ [natByte 129, modrmReg 3 (regLow dst), wortByte op 0, wortByte op 1]
    | _ => pre ++ [natByte 129, modrmReg 3 (regLow dst), wortByte op 0, wortByte op 1, wortByte op 2, wortByte op 3]
  | .incReg b dst =>
    let pre := carryPrefix b 0 (regHigh dst)
    let opc := if b = .b8 then natByte 254 else natByte 255
    pre ++ [opc, modrmReg 0 (regLow dst)]
  | .decReg b dst =>
    let pre := carryPrefix b 0 (regHigh dst)
    let opc := if b = .b8 then natByte 254 else natByte 255
    pre ++ [opc, modrmReg 1 (regLow dst)]

/-- Round trip for 64-bit ADC register forms, over any suffix. -/
theorem roundtrip_adcReg64 (dst src : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.adcReg .b64 dst src) ++ suffix) =
      some (.reg ⟨.adcReg .b64 dst src, (carryEncode (.adcReg .b64 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 32-bit ADC register forms. -/
theorem roundtrip_adcReg32 (dst src : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.adcReg .b32 dst src) ++ suffix) =
      some (.reg ⟨.adcReg .b32 dst src, (carryEncode (.adcReg .b32 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 16-bit ADC register forms. -/
theorem roundtrip_adcReg16 (dst src : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.adcReg .b16 dst src) ++ suffix) =
      some (.reg ⟨.adcReg .b16 dst src, (carryEncode (.adcReg .b16 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 64-bit SBB register forms. -/
theorem roundtrip_sbbReg64 (dst src : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.sbbReg .b64 dst src) ++ suffix) =
      some (.reg ⟨.sbbReg .b64 dst src, (carryEncode (.sbbReg .b64 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 32-bit SBB register forms. -/
theorem roundtrip_sbbReg32 (dst src : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.sbbReg .b32 dst src) ++ suffix) =
      some (.reg ⟨.sbbReg .b32 dst src, (carryEncode (.sbbReg .b32 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 16-bit SBB register forms. -/
theorem roundtrip_sbbReg16 (dst src : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.sbbReg .b16 dst src) ++ suffix) =
      some (.reg ⟨.sbbReg .b16 dst src, (carryEncode (.sbbReg .b16 dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for 64-bit INC forms. -/
theorem roundtrip_incReg64 (dst : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.incReg .b64 dst) ++ suffix) =
      some (.reg ⟨.incReg .b64 dst, (carryEncode (.incReg .b64 dst)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 32-bit INC forms. -/
theorem roundtrip_incReg32 (dst : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.incReg .b32 dst) ++ suffix) =
      some (.reg ⟨.incReg .b32 dst, (carryEncode (.incReg .b32 dst)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 16-bit INC forms. -/
theorem roundtrip_incReg16 (dst : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.incReg .b16 dst) ++ suffix) =
      some (.reg ⟨.incReg .b16 dst, (carryEncode (.incReg .b16 dst)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 64-bit DEC forms. -/
theorem roundtrip_decReg64 (dst : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.decReg .b64 dst) ++ suffix) =
      some (.reg ⟨.decReg .b64 dst, (carryEncode (.decReg .b64 dst)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 32-bit DEC forms. -/
theorem roundtrip_decReg32 (dst : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.decReg .b32 dst) ++ suffix) =
      some (.reg ⟨.decReg .b32 dst, (carryEncode (.decReg .b32 dst)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 16-bit DEC forms. -/
theorem roundtrip_decReg16 (dst : Register) (suffix : List Byte) :
    decodeCarry (carryEncode (.decReg .b16 dst) ++ suffix) =
      some (.reg ⟨.decReg .b16 dst, (carryEncode (.decReg .b16 dst)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 64-bit ADC immediates: decode reads the canonical
    operand back (`canonImm`). -/
theorem roundtrip_adcImm64 (dst : Register) (op : Wort)
    (suffix : List Byte) :
    decodeCarry (carryEncode (.adcImm .b64 dst op) ++ suffix) =
      some (.reg ⟨.adcImm .b64 dst (canonImm .b64 op), (carryEncode (.adcImm .b64 dst op)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 32-bit ADC immediates. -/
theorem roundtrip_adcImm32 (dst : Register) (op : Wort)
    (suffix : List Byte) :
    decodeCarry (carryEncode (.adcImm .b32 dst op) ++ suffix) =
      some (.reg ⟨.adcImm .b32 dst (canonImm .b32 op), (carryEncode (.adcImm .b32 dst op)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 16-bit ADC immediates. -/
theorem roundtrip_adcImm16 (dst : Register) (op : Wort)
    (suffix : List Byte) :
    decodeCarry (carryEncode (.adcImm .b16 dst op) ++ suffix) =
      some (.reg ⟨.adcImm .b16 dst (canonImm .b16 op), (carryEncode (.adcImm .b16 dst op)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 64-bit SBB immediates. -/
theorem roundtrip_sbbImm64 (dst : Register) (op : Wort)
    (suffix : List Byte) :
    decodeCarry (carryEncode (.sbbImm .b64 dst op) ++ suffix) =
      some (.reg ⟨.sbbImm .b64 dst (canonImm .b64 op), (carryEncode (.sbbImm .b64 dst op)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 32-bit SBB immediates. -/
theorem roundtrip_sbbImm32 (dst : Register) (op : Wort)
    (suffix : List Byte) :
    decodeCarry (carryEncode (.sbbImm .b32 dst op) ++ suffix) =
      some (.reg ⟨.sbbImm .b32 dst (canonImm .b32 op), (carryEncode (.sbbImm .b32 dst op)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Round trip for 16-bit SBB immediates. -/
theorem roundtrip_sbbImm16 (dst : Register) (op : Wort)
    (suffix : List Byte) :
    decodeCarry (carryEncode (.sbbImm .b16 dst op) ++ suffix) =
      some (.reg ⟨.sbbImm .b16 dst (canonImm .b16 op), (carryEncode (.sbbImm .b16 dst op)).length⟩, suffix) := by
  cases dst <;> rfl

/-- Displacement length from ModRM mode bits: disp8/disp32/none. -/
def dispLaenge (mod rm : Nat) : Nat :=
  if mod == 1 then 1
  else if mod == 2 || (mod == 0 && rm == 5) then 4
  else 0

/-- Immediate kind by Group-1 opcode and 66H prefix. -/
def immKindVon (op : Nat) (op66 : Bool) : Nat :=
  if op == 128 then 0
  else if op == 129 then (if op66 then 1 else 2)
  else 3

/-- Split prefix/opcode/tail: 66H flag, opcode value, bytes after the
    opcode. At most one 66H (itself followed by at most one REX) or
    one REX is consumed. -/
def praefixOp : List Byte → Option (Bool × Nat × List Byte)
  | [] => none
  | b :: rest =>
    if byteNat b == 102 then
      match rest with
      | [] => none
      | b2 :: rest2 =>
        if decide (64 ≤ byteNat b2 ∧ byteNat b2 < 80) then
          match rest2 with
          | op :: tail => some (true, byteNat op, tail)
          | _ => none
        else some (true, byteNat b2, rest2)
    else if decide (64 ≤ byteNat b ∧ byteNat b < 80) then
      match rest with
      | op :: tail => some (false, byteNat op, tail)
      | _ => none
    else some (false, byteNat b, rest)

/-- High-byte reason without REX context: no-prefix or 66H-only
    inputs with a register-direct 8-bit ModRM naming code 4-7 refuse
    with `.hochbyte`. REX-involved shapes refuse in decode but carry
    no computed reason here (documented gap, see CUTS). -/
def hochbyteGrund (op : Nat) (ohneRex : Bool) (m : Nat) :
    Option AblehnGrund :=
  if !ohneRex then none
  else if decide (op = 16 ∨ op = 18 ∨ op = 128 ∨ op = 254) then
    if m / 64 == 3 then
      let rm := m % 8
      let reg := m / 8 % 8
      if op == 16 || op == 18 then
        if hochbyteCode rm || hochbyteCode reg then some .hochbyte
        else none
      else if hochbyteCode rm then some .hochbyte
      else none
    else none
  else none

/-- No REX byte participates: no prefix at all, or a lone 66H. Only
    then is the high-byte check computable without extension bits. -/
def ohneRexForm : List Byte → Bool
  | [] => true
  | b :: rest =>
    if byteNat b == 102 then
      match rest with
      | b2 :: _ => !(decide (64 ≤ byteNat b2 ∧ byteNat b2 < 80))
      | _ => true
    else !(decide (64 ≤ byteNat b ∧ byteNat b < 80))

/-- Deep reason from the prefix split: LOCK, address-size, a REX byte
    in the opcode slot, a wrong Group extension digit, a missing
    ModRM/displacement/immediate tail, a REX-free high-byte code, or
    nothing decodable. -/
def ablehnGrundTief (bs : List Byte) (op66 : Bool) (op : Nat)
    (tail : List Byte) : Option AblehnGrund :=
  if op == 240 then some .lock
  else if op == 103 then some .adressGroesse
  else if decide (64 ≤ op ∧ op < 80) then some .einByteIncDec
  else if decide (op = 128 ∨ op = 129 ∨ op = 131) then
    match tail with
    | [] => some .unvollstaendig
    | m :: tail2 =>
      let ext := byteNat m / 8 % 8
      if ext == 2 || ext == 3 then
        let need := dispLaenge (byteNat m / 64) (byteNat m % 8) +
          immLenOf (immKindVon op op66)
        if tail2.length < need then some .unvollstaendig
        else hochbyteGrund op (ohneRexForm bs) (byteNat m)
      else some .falscheErweiterung
  else if decide (op = 254 ∨ op = 255) then
    match tail with
    | [] => some .unvollstaendig
    | m :: tail2 =>
      let ext := byteNat m / 8 % 8
      if ext == 0 || ext == 1 then
        let need := dispLaenge (byteNat m / 64) (byteNat m % 8)
        if tail2.length < need then some .unvollstaendig
        else hochbyteGrund op (ohneRexForm bs) (byteNat m)
      else some .falscheErweiterung
  else if decide (op = 16 ∨ op = 17 ∨ op = 18 ∨ op = 19 ∨ op = 24 ∨
      op = 25 ∨ op = 26 ∨ op = 27) then
    match tail with
    | [] => some .unvollstaendig
    | m :: tail2 =>
      let need :=
        if byteNat m / 64 == 3 then 0
        else dispLaenge (byteNat m / 64) (byteNat m % 8)
      if tail2.length < need then some .unvollstaendig
      else hochbyteGrund op (ohneRexForm bs) (byteNat m)
  else if decide (op = 20 ∨ op = 28) then
    if tail.length < 1 then some .unvollstaendig else none
  else if decide (op = 21 ∨ op = 29) then
    if tail.length < (if op66 then 2 else 4) then some .unvollstaendig
    else none
  else some .keinTrageform

/-- Shallow refusal reason for a byte string. Family opcodes that
    decode carry none; every other refused shape names its reason. -/
def ablehnGrund : List Byte → Option AblehnGrund
  | [] => some .unvollstaendig
  | b :: rest =>
    if byteNat b == 240 then some .lock
    else if byteNat b == 103 then some .adressGroesse
    else match rest with
    | b2 :: _ =>
      if istPraefixByte (byteNat b) && byteNat b2 == 102 then
        some .doppelPraefix
      else match praefixOp (b :: rest) with
      | none => some .unvollstaendig
      | some (op66, op, tail) => ablehnGrundTief (b :: rest) op66 op tail
    | _ =>
      match praefixOp (b :: rest) with
      | none => some .unvollstaendig
      | some (op66, op, tail) => ablehnGrundTief (b :: rest) op66 op tail

/-! ## Pinned bytes: SDM spot checks, refusals, reasons.

    Each pin evaluates the decoder (or the reason classifier) on
    concrete bytes through `decide`: the accepted shapes below are
    the SDM rows of §3, and every refused shape pairs `decodeCarry`
    with its `ablehnGrund` reason. -/

/-- Pin: `11 /r` ADC Ev,Gv register-direct. -/
theorem pin_decode_adcReg32 :
    decodeCarry [natByte 17, natByte 193] =
      some (.reg ⟨.adcReg .b32 .rcx .rax, 2⟩, []) := by
  decide

/-- Pin: `10 /r` ADC Eb,Gb register-direct. -/
theorem pin_decode_adcReg8 :
    decodeCarry [natByte 16, natByte 200] =
      some (.reg ⟨.adcReg .b8 .rax .rcx, 2⟩, []) := by
  decide

/-- Pin: `14 ib` ADC AL,Ib. -/
theorem pin_decode_adcAL :
    decodeCarry [natByte 20, natByte 5] =
      some (.reg ⟨.adcImm .b8 .rax (imm8Wert (natByte 5)), 2⟩, []) := by
  decide

/-- Pin: `83 /2 ib` ADC Ev,Ib with a negative byte (sign-extended). -/
theorem pin_decode_adcImm83 :
    decodeCarry [natByte 131, natByte 208, natByte 253] =
      some (.reg ⟨.adcImm .b32 .rax (imm8Sext .b32 (natByte 253)), 3⟩,
        []) := by
  decide

/-- Pin: `FE /0` INC Eb. -/
theorem pin_decode_incReg8 :
    decodeCarry [natByte 254, natByte 192] =
      some (.reg ⟨.incReg .b8 .rax, 2⟩, []) := by
  decide

/-- Pin: REX.W `FF /0` INC Ev. -/
theorem pin_decode_incReg64 :
    decodeCarry [natByte 72, natByte 255, natByte 192] =
      some (.reg ⟨.incReg .b64 .rax, 3⟩, []) := by
  decide

/-- Pin: `11 /r` with a memory source decodes to a descriptor. -/
theorem pin_decode_mem :
    decodeCarry [natByte 17, natByte 1] =
      some (.mem ⟨.adc, .b32, true, 1, 1, [], 2⟩, []) := by
  decide

/-- Pin: `1B /r` SBB Gv,Ev with a memory source is a load. -/
theorem pin_decode_sbbMemLoad :
    decodeCarry [natByte 27, natByte 1] =
      some (.mem ⟨.sbb, .b32, false, 1, 1, [], 2⟩, []) := by
  decide

/-- Pin: `FF /1` DEC Ev with a memory destination is a store. -/
theorem pin_decode_decMem :
    decodeCarry [natByte 255, natByte 9] =
      some (.mem ⟨.dec, .b32, true, 9, 1, [], 2⟩, []) := by
  decide

/-- Pin: REX prefix, no width change for 32-bit forms. -/
theorem pin_decode_preRex :
    decodeCarry [natByte 64, natByte 17, natByte 193] =
      some (.reg ⟨.adcReg .b32 .rcx .rax, 3⟩, []) := by
  decide

/-- Pin: 66H prefix selects 16 bits. -/
theorem pin_decode_pre66 :
    decodeCarry [natByte 102, natByte 17, natByte 193] =
      some (.reg ⟨.adcReg .b16 .rcx .rax, 3⟩, []) := by
  decide

/-- Pin: 66H+REX pair selects 16 bits with plain registers. -/
theorem pin_decode_pre66Rex :
    decodeCarry [natByte 102, natByte 64, natByte 17, natByte 193] =
      some (.reg ⟨.adcReg .b16 .rcx .rax, 4⟩, []) := by
  decide

/-- Refusal: empty input. -/
theorem pin_nichts_leer : decodeCarry [] = none := rfl

/-- Refusal: lone REX prefix is truncated. -/
theorem pin_nichts_rexAllein : decodeCarry [natByte 64] = none := by
  decide

/-- Refusal: opcode without ModRM is truncated. -/
theorem pin_nichts_opAllein : decodeCarry [natByte 17] = none := by
  decide

/-- Refusal: Group-1 opcode without ModRM is truncated. -/
theorem pin_nichts_modrm80 : decodeCarry [natByte 128] = none := by
  decide

/-- Refusal: Group-1 with ModRM but without immediate is truncated. -/
theorem pin_nichts_imm81 :
    decodeCarry [natByte 129, natByte 208] = none := by
  decide

/-- Refusal: eAX-immediate opcode without immediate is truncated. -/
theorem pin_nichts_imm15 : decodeCarry [natByte 21] = none := by
  decide

/-- Refusal: disp8 mode without displacement is truncated. -/
theorem pin_nichts_disp1 :
    decodeCarry [natByte 17, natByte 65] = none := by
  decide

/-- Refusal: disp32 mode with a short tail is truncated. -/
theorem pin_nichts_disp2 :
    decodeCarry [natByte 17, natByte 133, natByte 1, natByte 2,
      natByte 3] = none := by
  decide

/-- Refusal: LOCK prefix is refused. -/
theorem pin_nichts_lock :
    decodeCarry [natByte 240, natByte 17, natByte 193] = none := by
  decide

/-- Refusal: address-size prefix is refused. -/
theorem pin_nichts_67 :
    decodeCarry [natByte 103, natByte 17, natByte 193] = none := by
  decide

/-- Refusal: doubled 66H prefix is refused. -/
theorem pin_nichts_doppel66 :
    decodeCarry [natByte 102, natByte 102, natByte 17, natByte 193] =
      none := by
  decide

/-- Refusal: REX byte in the opcode slot is refused. -/
theorem pin_nichts_rexAlsOp : decodeCarry [natByte 64, natByte 64] = none := by
  decide

/-- Refusal: REX byte after a full prefix pair is refused. -/
theorem pin_nichts_rex66Op :
    decodeCarry [natByte 102, natByte 64, natByte 192] = none := by
  decide

/-- Refusal: a non-carry opcode (ADD) is refused. -/
theorem pin_nichts_fremd : decodeCarry [natByte 0, natByte 192] = none := by
  decide

/-- Refusal: Group-1 extension `/5` is no carry form. -/
theorem pin_nichts_falsch80 :
    decodeCarry [natByte 128, natByte 232] = none := by
  decide

/-- Refusal: FF extension `/2` (CALL) is no INC/DEC form. -/
theorem pin_nichts_falschFF2 :
    decodeCarry [natByte 255, natByte 208] = none := by
  decide

/-- Refusal: FF extension `/3` (CALLF) is no INC/DEC form. -/
theorem pin_nichts_falschFF3 :
    decodeCarry [natByte 255, natByte 216] = none := by
  decide

/-- Refusal: high-byte source without REX is refused. -/
theorem pin_nichts_hoch10 :
    decodeCarry [natByte 16, natByte 224] = none := by
  decide

/-- Refusal: high-byte INC destination without REX is refused. -/
theorem pin_nichts_hochFE :
    decodeCarry [natByte 254, natByte 196] = none := by
  decide

/-- Asymmetry pin: the 8-bit high-byte code encodes but never
    decodes (no AH/SPL in the vocabulary, by silicon necessity). -/
theorem pin_nichts_b8Asym :
    decodeCarry (carryEncode (.adcReg .b8 .rsp .rax)) = none := by
  decide

/-- Reason: empty input is truncated. -/
theorem pin_grund_leer : ablehnGrund [] = some .unvollstaendig := rfl

/-- Reason: lone REX prefix is truncated. -/
theorem pin_grund_truncRex :
    ablehnGrund [natByte 64] = some .unvollstaendig := by
  decide

/-- Reason: opcode without ModRM is truncated. -/
theorem pin_grund_truncOp :
    ablehnGrund [natByte 17] = some .unvollstaendig := by
  decide

/-- Reason: Group-1 without ModRM is truncated. -/
theorem pin_grund_trunc80 :
    ablehnGrund [natByte 128] = some .unvollstaendig := by
  decide

/-- Reason: Group-1 with ModRM but without immediate is truncated. -/
theorem pin_grund_truncImm81 :
    ablehnGrund [natByte 129, natByte 208] = some .unvollstaendig := by
  decide

/-- Reason: LOCK names itself. -/
theorem pin_grund_lock :
    ablehnGrund [natByte 240, natByte 17, natByte 193] =
      some .lock := by
  decide

/-- Reason: address-size names itself. -/
theorem pin_grund_67 :
    ablehnGrund [natByte 103, natByte 17, natByte 193] =
      some .adressGroesse := by
  decide

/-- Reason: doubled 66H names itself. -/
theorem pin_grund_doppel66 :
    ablehnGrund [natByte 102, natByte 102, natByte 17, natByte 193] =
      some .doppelPraefix := by
  decide

/-- Reason: REX after REX names the double prefix. -/
theorem pin_grund_doppelRex66 :
    ablehnGrund [natByte 64, natByte 102, natByte 17, natByte 193] =
      some .doppelPraefix := by
  decide

/-- Reason: REX after a full prefix pair is no one-byte INC/DEC. -/
theorem pin_grund_einByte :
    ablehnGrund [natByte 102, natByte 64, natByte 64] =
      some .einByteIncDec := by
  decide

/-- Reason: REX in the opcode slot is no one-byte INC/DEC. -/
theorem pin_grund_einByte2 :
    ablehnGrund [natByte 64, natByte 64] = some .einByteIncDec := by
  decide

/-- Reason: a non-carry opcode names itself. -/
theorem pin_grund_fremd :
    ablehnGrund [natByte 0, natByte 192] = some .keinTrageform := by
  decide

/-- Reason: Group-1 extension `/5` names itself. -/
theorem pin_grund_falsch80 :
    ablehnGrund [natByte 128, natByte 232] =
      some .falscheErweiterung := by
  decide

/-- Reason: FF extension `/2` names itself. -/
theorem pin_grund_falschFF2 :
    ablehnGrund [natByte 255, natByte 208] =
      some .falscheErweiterung := by
  decide

/-- Reason: FF extension `/3` names itself. -/
theorem pin_grund_falschFF3 :
    ablehnGrund [natByte 255, natByte 216] =
      some .falscheErweiterung := by
  decide

/-- Reason: high-byte source names itself. -/
theorem pin_grund_hoch10 :
    ablehnGrund [natByte 16, natByte 224] = some .hochbyte := by
  decide

/-- Reason: high-byte INC destination names itself. -/
theorem pin_grund_hochFE :
    ablehnGrund [natByte 254, natByte 196] = some .hochbyte := by
  decide

/-- Reason: decodable register bytes carry no reason. -/
theorem pin_grund_ok :
    ablehnGrund [natByte 17, natByte 193] = none := by
  decide

/-- Reason: decodable memory bytes carry no reason. -/
theorem pin_grund_okMem : ablehnGrund [natByte 17, natByte 1] = none := by
  decide

/-! ## No shadowing: the unified chain refuses the family rows.

    Every family opcode (with a representative tail) is refused by
    the whole `decodeExt` chain, so the dispatcher below takes the
    family arm exactly once and no pilot or extension form is
    shadowed. Each pin evaluates the complete chain on concrete
    bytes. -/

/-- The unified chain refuses `10 /r`. -/
theorem ext_weist_carry10_zurueck :
    decodeExt [natByte 16, natByte 193] = none := by
  decide

/-- The unified chain refuses `11 /r`. -/
theorem ext_weist_carry11_zurueck :
    decodeExt [natByte 17, natByte 193] = none := by
  decide

/-- The unified chain refuses `12 /r`. -/
theorem ext_weist_carry12_zurueck :
    decodeExt [natByte 18, natByte 193] = none := by
  decide

/-- The unified chain refuses `13 /r`. -/
theorem ext_weist_carry13_zurueck :
    decodeExt [natByte 19, natByte 193] = none := by
  decide

/-- The unified chain refuses `14 ib`. -/
theorem ext_weist_carry14_zurueck :
    decodeExt [natByte 20, natByte 5] = none := by
  decide

/-- The unified chain refuses `15 iz`. -/
theorem ext_weist_carry15_zurueck :
    decodeExt [natByte 21, natByte 5, natByte 0, natByte 0, natByte 0] =
      none := by
  decide

/-- The unified chain refuses `18 /r`. -/
theorem ext_weist_carry18_zurueck :
    decodeExt [natByte 24, natByte 193] = none := by
  decide

/-- The unified chain refuses `19 /r`. -/
theorem ext_weist_carry19_zurueck :
    decodeExt [natByte 25, natByte 193] = none := by
  decide

/-- The unified chain refuses `1A /r`. -/
theorem ext_weist_carry1A_zurueck :
    decodeExt [natByte 26, natByte 193] = none := by
  decide

/-- The unified chain refuses `1B /r`. -/
theorem ext_weist_carry1B_zurueck :
    decodeExt [natByte 27, natByte 193] = none := by
  decide

/-- The unified chain refuses `1C ib`. -/
theorem ext_weist_carry1C_zurueck :
    decodeExt [natByte 28, natByte 5] = none := by
  decide

/-- The unified chain refuses `1D iz`. -/
theorem ext_weist_carry1D_zurueck :
    decodeExt [natByte 29, natByte 5, natByte 0, natByte 0, natByte 0] =
      none := by
  decide

/-- The unified chain refuses Group-1 `80 /2`. -/
theorem ext_weist_carry80_zurueck :
    decodeExt [natByte 128, natByte 208, natByte 1] = none := by
  decide

/-- The unified chain refuses Group-1 `81 /2`. -/
theorem ext_weist_carry81_zurueck :
    decodeExt [natByte 129, natByte 208, natByte 1, natByte 0, natByte 0,
      natByte 0] = none := by
  decide

/-- The unified chain refuses Group-1 `83 /2`. -/
theorem ext_weist_carry83_zurueck :
    decodeExt [natByte 131, natByte 208, natByte 253] = none := by
  decide

/-- The unified chain refuses `FE /0`. -/
theorem ext_weist_carryFE_zurueck :
    decodeExt [natByte 254, natByte 192] = none := by
  decide

/-- The unified chain refuses `FF /0`. -/
theorem ext_weist_carryFF_zurueck :
    decodeExt [natByte 255, natByte 192] = none := by
  decide

/-- The unified chain refuses REX.W `11 /r`. -/
theorem ext_weist_carryREX11_zurueck :
    decodeExt [natByte 72, natByte 17, natByte 193] = none := by
  decide

/-- The unified chain refuses 66H `11 /r`. -/
theorem ext_weist_carry6611_zurueck :
    decodeExt [natByte 102, natByte 17, natByte 193] = none := by
  decide

/-! ## 4. Dispatcher and machine step: the family beside the chain.

   The unified decoder runs first and keeps every accepted form (§3
   proves the family rows refused there); the family arm takes exactly
   those rows. The unified step runs Ext through `stepExt` and family
   register forms through `carrySchritt` on the core half; family
   memory forms refuse here and run the TSO path of §5. -/

/-- Unified dispatcher instruction: the accepted chain first, the
    family only where it refuses. -/
inductive CarryHwInstr where
  | ext : ExtInstr → CarryHwInstr
  | carry : CarryInstr → CarryHwInstr
  deriving DecidableEq, Repr

/-- Dispatcher: the unified decoder first, the family decoder only
    where the unified chain refuses. No accepted form is shadowed. -/
def decodeCarryHw : List Byte → Option (CarryHwInstr × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some (i, rest) => some (.ext i, rest)
    | none =>
      match decodeCarry bs with
      | some (d, rest) => some (.carry d, rest)
      | none => none

/-- Consumed length of one dispatcher instruction (checked data). -/
def carryHwLen : CarryHwInstr → Nat
  | .ext i => extLen i
  | .carry (.reg d) => d.laenge
  | .carry (.mem m) => m.laenge

/-- The dispatcher agrees with the unified chain wherever it accepts. -/
theorem decodeCarryHw_prefers_ext (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeCarryHw bs = some (.ext i, rest) := by
  unfold decodeCarryHw
  rw [h]

/-- Where the unified chain refuses, a covered family row is taken. -/
theorem decodeCarryHw_carry (bs : List Byte) (d : CarryInstr)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeCarry bs = some (d, rest)) :
    decodeCarryHw bs = some (.carry d, rest) := by
  unfold decodeCarryHw
  rw [h1, h2]

/-- Where both chains refuse, the dispatcher refuses. -/
theorem decodeCarryHw_nichts (bs : List Byte)
    (h1 : decodeExt bs = none) (h2 : decodeCarry bs = none) :
    decodeCarryHw bs = none := by
  unfold decodeCarryHw
  rw [h1, h2]

/-- Pin: the pilot row goes through unchanged. -/
theorem pin_hw_pilot_ret :
    decodeCarryHw (encode .ret) =
      some (.ext (.pilot ⟨.ret, 1⟩), []) :=
  decodeCarryHw_prefers_ext _ _ _ pin_ext_pilot_ret

/-- Pin: a family row takes the family arm. -/
theorem pin_hw_adcReg32 :
    decodeCarryHw [natByte 17, natByte 193] =
      some (.carry (.reg ⟨.adcReg .b32 .rcx .rax, 2⟩), []) :=
  decodeCarryHw_carry _ _ _ ext_weist_carry11_zurueck pin_decode_adcReg32

/-- One unified step: Ext through `stepExt`, family register forms
    through `carrySchritt` on the core half, family memory forms
    refuse (TSO path only). -/
def carryHwSchritt (i : CarryHwInstr) (t : FpZustand)
    (b : BereitProfil) : ExtAusgang :=
  match i with
  | .ext j => stepExt j t b
  | .carry (.reg d) =>
    match carrySchritt d t.kern with
    | .ok s' => .weiter { t with kern := s' }
    | .misslungen => .verweigert
  | .carry (.mem _) => .verweigert

/-- Selection: the unified arm IS the accepted unified step. -/
theorem carryHwSchritt_ext (j : ExtInstr) (t : FpZustand)
    (b : BereitProfil) (o : ExtAusgang)
    (h : stepExt j t b = o) :
    carryHwSchritt (.ext j) t b = o := by
  have e : carryHwSchritt (.ext j) t b = stepExt j t b := rfl
  rw [e, h]

/-- Selection: the family register arm IS the accepted family step. -/
theorem carryHwSchritt_reg_ok (d : CarryDecodiert) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : carrySchritt d t.kern = .ok s') :
    carryHwSchritt (.carry (.reg d)) t b =
      .weiter { t with kern := s' } := by
  unfold carryHwSchritt
  simp only [h]

/-- Selection: family register refusal is unified refusal. -/
theorem carryHwSchritt_reg_verweigert (d : CarryDecodiert)
    (t : FpZustand) (b : BereitProfil)
    (h : carrySchritt d t.kern = .misslungen) :
    carryHwSchritt (.carry (.reg d)) t b = .verweigert := by
  unfold carryHwSchritt
  simp only [h]

/-- Selection: family memory forms refuse the register step. -/
theorem carryHwSchritt_mem_verweigert (mm : CarryMem) (t : FpZustand)
    (b : BereitProfil) :
    carryHwSchritt (.carry (.mem mm)) t b = .verweigert := rfl

/-! ## 5. Machine adapter: the family on the coherent machine.

   The producer plug instantiates `HwAdapter CarryInstr` with the
   accepted API: a successful register step re-embeds core data over
   the shared memory; refusals and memory descriptors admit no
   successor state (memory runs the TSO path of §6). -/

/-- The family plug: one checked family event step on the coherent
    machine. `none` = refusal or memory form, never a silent step. -/
def adapterCarry : HwAdapter CarryInstr :=
  ⟨fun m c i =>
    match i with
    | .reg d =>
      match carrySchritt d (projZustand m c) with
      | .ok s' =>
        some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .misslungen => none
    | .mem _ => none⟩

/-- Agreement: the adapter succeeds exactly where the accepted
    family step succeeds, with the successor core data re-embedded. -/
theorem adapterCarry_ok (m : HwMaschine) (c : Nat) (d : CarryDecodiert)
    (s' : Zustand)
    (h : carrySchritt d (projZustand m c) = .ok s') :
    (adapterCarry).schritt m c (.reg d) =
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  unfold adapterCarry
  simp only [h]

/-- A refused family step admits no adapter successor. -/
theorem adapterCarry_verweigert (m : HwMaschine) (c : Nat)
    (d : CarryDecodiert)
    (h : carrySchritt d (projZustand m c) = .misslungen) :
    (adapterCarry).schritt m c (.reg d) = none := by
  unfold adapterCarry
  simp only [h]

/-- Memory descriptors never plug the register path. -/
theorem adapterCarry_mem_none (m : HwMaschine) (c : Nat)
    (mm : CarryMem) :
    (adapterCarry).schritt m c (.mem mm) = none := rfl

/-- A bad decode length admits no adapter step. -/
theorem adapterCarry_verweigert_bei_laenge (m : HwMaschine) (c : Nat)
    (d : CarryDecodiert)
    (h : laengeOk d.laenge = false) :
    (adapterCarry).schritt m c (.reg d) = none := by
  have hstep := carry_laenge_misslungen d (projZustand m c) h
  exact adapterCarry_verweigert m c d hstep

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterCarry_wf (m : HwMaschine) (c : Nat) (i : CarryInstr)
    (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterCarry).schritt m c i = some m') :
    HwWf m' := by
  cases i with
  | reg d =>
    cases hsch : carrySchritt d (projZustand m c) with
    | ok s' =>
      have h2 := adapterCarry_ok m c d s' hsch
      rw [h2] at h
      cases h
      unfold setKernVonFp
      exact setKernDaten_wf _ _ _ hwf
    | misslungen =>
      have h2 := adapterCarry_verweigert m c d hsch
      rw [h2] at h
      cases h
  | mem mm =>
    rw [adapterCarry_mem_none m c mm] at h
    cases h

/- CUTS:
    Value/flag layer (§1) and register step (§2) stand.
    NOT proved here, and not claimed: the opcode dispatch, encode,
    round trips, refusal reasons, the machine adapter, the witness.
-/

#print axioms CarryKlasse

end Gabbro.Grammatik.X86
