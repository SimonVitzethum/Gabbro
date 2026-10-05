/-
  File:      Grammatik/X86/IntByteForms.lean
  Subject:   8-bit operand forms across the new integer families.

  Lane 1319: byte-register selection with the architectural REX rule
  (AL/CL/DL/BL always; SPL/BPL/SIL/DIL only with REX; AH/CH/DH/BH
  only without REX, outside the `Register` vocabulary), the 8-bit
  merge discipline (merge into the low byte, never zero-extend),
  and the 8-bit rotate / ADC-SBB-INC-DEC / XCHG connections through
  the accepted evaluators with decode/encode round trips plus a
  `HwAdapter` over the coherent machine. Reuses the accepted
  definitions unchanged, never copies a model. No silicon proof
  beyond self-consistency (see CUTS).
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Wort
import Grammatik.X86.Kern.Codec
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Befehle.Ganzzahl.IntRotate
import Grammatik.X86.Befehle.Ganzzahl.IntCarryForms
import Grammatik.X86.TSO.Verriegelt.XchgOrderNeed
namespace Gabbro.Grammatik.X86

/-- Byte-register target of a full register code under a REX flag:
    codes 0-3 are AL/CL/DL/BL in every mode; codes 4-7 are
    SPL/BPL/SIL/DIL with REX and the high bytes AH/CH/DH/BH
    without REX (outside the `Register` vocabulary, so refused);
    codes 8-15 are R8B-R15B and need REX; the rest refuses. -/
def byteZielReg : Nat → Bool → Option Register
  | 0, _ => some .rax
  | 1, _ => some .rcx
  | 2, _ => some .rdx
  | 3, _ => some .rbx
  | 4, true => some .rsp
  | 5, true => some .rbp
  | 6, true => some .rsi
  | 7, true => some .rdi
  | 8, true => some .r8
  | 9, true => some .r9
  | 10, true => some .r10
  | 11, true => some .r11
  | 12, true => some .r12
  | 13, true => some .r13
  | 14, true => some .r14
  | 15, true => some .r15
  | _, _ => none

/-- Low codes name the classic low bytes with or without REX. -/
theorem byteZielReg_tief (code : Nat) (rex : Bool) (h : code < 4) :
    byteZielReg code rex = codeReg code := by
  cases code with
  | zero => cases rex <;> rfl
  | succ n =>
    cases n with
    | zero => cases rex <;> rfl
    | succ n =>
      cases n with
      | zero => cases rex <;> rfl
      | succ n =>
        cases n with
        | zero => cases rex <;> rfl
        | succ _ => omega

/-- REX switches codes 4-7 from the high bytes to SPL/BPL/SIL/DIL. -/
theorem byteZielReg_rex_schalter :
    byteZielReg 4 true = some .rsp ∧ byteZielReg 5 true = some .rbp ∧
    byteZielReg 6 true = some .rsi ∧ byteZielReg 7 true = some .rdi := by
  decide

/-- Without REX, codes 4-7 are the high bytes AH/CH/DH/BH: outside
    the `Register` vocabulary, so the selector refuses. -/
theorem byteZielReg_hochbyte_verweigert :
    byteZielReg 4 false = none ∧ byteZielReg 5 false = none ∧
    byteZielReg 6 false = none ∧ byteZielReg 7 false = none := by
  decide

/-- Extended codes need REX: R8B-R15B with it, refusal without. -/
theorem byteZielReg_erweitert :
    byteZielReg 8 true = some .r8 ∧ byteZielReg 15 true = some .r15 ∧
    byteZielReg 8 false = none ∧ byteZielReg 15 false = none := by
  decide

/-- Codes at and above 16 never name a byte register. -/
theorem byteZielReg_ausserhalb (code : Nat) (rex : Bool)
    (h : 16 ≤ code) :
    byteZielReg code rex = none := by
  match code with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | 4 => cases rex <;> omega
  | 5 => cases rex <;> omega
  | 6 => cases rex <;> omega
  | 7 => cases rex <;> omega
  | 8 => cases rex <;> omega
  | 9 => cases rex <;> omega
  | 10 => cases rex <;> omega
  | 11 => cases rex <;> omega
  | 12 => cases rex <;> omega
  | 13 => cases rex <;> omega
  | 14 => cases rex <;> omega
  | 15 => cases rex <;> omega
  | n + 16 => rfl

/-! ## 2. Merge discipline: the low byte is taken, upper bits kept.

    The accepted `mergeRegNarrow .b8` is reused unchanged (never a
    second merge): an 8-bit result merges into the low byte and never
    zero-extends, unlike the 32-bit form beside it. -/

/-- Pinned 8-bit merge: low byte taken, upper bits kept. -/
theorem byteMerge_tief_hoch :
    mergeRegNarrow .b8 0xABCDEF1234567890 0x11 = 0xABCDEF1234567811 ∧
    mergeRegNarrow .b8 0xFF00 0x00 = 0xFF00 := by
  decide

/-- An 8-bit merge never zero-extends: upper bits survive. -/
theorem byteMerge_nie_nullerweitert :
    mergeRegNarrow .b8 0xFFFFFFFFFFFFFFFF 0x00 =
      0xFFFFFFFFFFFFFF00 := by
  decide

/-- Contrast pin: the 32-bit merge clears the upper half. -/
theorem byteMerge_kontrast_b32 :
    mergeRegNarrow .b32 0xABCDEF1234567890 0x11 = 0x11 := by
  decide

/-- Admission of one full code at 8 bits under a REX flag. -/
def byteZulaessig (vollCode : Nat) (rex : Bool) : Bool :=
  match byteZielReg vollCode rex with
  | some _ => true
  | none => false

/-- Admitted exactly where the selector answers. -/
theorem byteZulaessig_antwort (vollCode : Nat) (rex : Bool)
    (r : Register) (h : byteZielReg vollCode rex = some r) :
    byteZulaessig vollCode rex = true := by
  unfold byteZulaessig
  rw [h]

/-- Refused exactly where the selector is silent; both premises used. -/
theorem byteZulaessig_verweigert (vollCode : Nat) (rex : Bool)
    (h : byteZielReg vollCode rex = none) :
    byteZulaessig vollCode rex = false := by
  unfold byteZulaessig
  rw [h]

/-! ## 3. Family lifts: the accepted 8-bit evaluators, never redefined.

    Rotate (`rolB`/`rorB`/`rclB`/`rcrB`), carry (`adcWert`/
    `sbbWert`/`incWert`/`decWert`) and the 8-bit exchange value all
    run at `.b8` through the accepted definitions; the thin wrappers
    below only fix the width, so every agreement is `rfl`. The 8-bit
    exchange has no accepted 8-bit evaluator (the accepted
    `xchgSchritt` swaps whole 64-bit words); its value is the
    low-byte swap under the accepted narrow merge, with flags
    untouched like the word form. -/

/-- 8-bit ROL value: the accepted evaluator at `.b8`. -/
def byteRol (x : Wort) (c : Nat) : Wort := rolB .b8 x c

/-- The lift IS the accepted 8-bit ROL. -/
theorem byteRol_agreement (x : Wort) (c : Nat) :
    byteRol x c = rolB .b8 x c := rfl

/-- 8-bit ROR value: the accepted evaluator at `.b8`. -/
def byteRor (x : Wort) (c : Nat) : Wort := rorB .b8 x c

/-- The lift IS the accepted 8-bit ROR. -/
theorem byteRor_agreement (x : Wort) (c : Nat) :
    byteRor x c = rorB .b8 x c := rfl

/-- 8-bit RCL value with incoming carry: the accepted pair at `.b8`. -/
def byteRcl (x : Wort) (cf : Bool) (c : Nat) : Wort × Bool :=
  rclB .b8 x cf c

/-- The lift IS the accepted 8-bit RCL. -/
theorem byteRcl_agreement (x : Wort) (cf : Bool) (c : Nat) :
    byteRcl x cf c = rclB .b8 x cf c := rfl

/-- 8-bit RCR value with incoming carry: the accepted pair at `.b8`. -/
def byteRcr (x : Wort) (cf : Bool) (c : Nat) : Wort × Bool :=
  rcrB .b8 x cf c

/-- The lift IS the accepted 8-bit RCR. -/
theorem byteRcr_agreement (x : Wort) (cf : Bool) (c : Nat) :
    byteRcr x cf c = rcrB .b8 x cf c := rfl

/-- 8-bit ADC value: the accepted evaluator at `.b8`. -/
def byteAdc (x y : Wort) (c : Bool) : Wort := adcWert .b8 x y c

/-- The lift IS the accepted 8-bit ADC. -/
theorem byteAdc_agreement (x y : Wort) (c : Bool) :
    byteAdc x y c = adcWert .b8 x y c := rfl

/-- 8-bit SBB value: the accepted evaluator at `.b8`. -/
def byteSbb (x y : Wort) (c : Bool) : Wort := sbbWert .b8 x y c

/-- The lift IS the accepted 8-bit SBB. -/
theorem byteSbb_agreement (x y : Wort) (c : Bool) :
    byteSbb x y c = sbbWert .b8 x y c := rfl

/-- 8-bit INC value: the accepted evaluator at `.b8`. -/
def byteInc (x : Wort) : Wort := incWert .b8 x

/-- The lift IS the accepted 8-bit INC. -/
theorem byteInc_agreement (x : Wort) : byteInc x = incWert .b8 x := rfl

/-- 8-bit DEC value: the accepted evaluator at `.b8`. -/
def byteDec (x : Wort) : Wort := decWert .b8 x

/-- The lift IS the accepted 8-bit DEC. -/
theorem byteDec_agreement (x : Wort) : byteDec x = decWert .b8 x := rfl

/-- 8-bit exchange value: the low bytes swap under the accepted
    narrow merge; upper bytes stay with their register. -/
def byteXchgWert (a b : Wort) : Wort × Wort :=
  (mergeRegNarrow .b8 a b, mergeRegNarrow .b8 b a)

/-- Pinned low-byte swap: lows cross, highs stay. -/
theorem byteXchgWert_pin :
    byteXchgWert 0xABCDEF1234567890 0x11 =
      (0xABCDEF1234567811, 0x90) := by
  decide

/-! ## 4. Codec connections: 8-bit forms through the selector.

    Rotate reuses the accepted codec (`rotEncode`/`decodeRot`):
    every admitted 8-bit form round-trips, and the admission is the
    selector. The accepted rotate decoder does NOT refuse the
    high-byte codes (it maps them to SPL/BPL/SIL/DIL without REX);
    that gap is pinned as a finding beside the selector refusal. -/

/-- Admitted 8-bit by-one rotate forms round-trip, with the
    selector admission beside the bytes; the admission premise is
    discharged into the admission conjunct. -/
theorem byteRotRundgang8_eins (o : RotOp) (dst : Register)
    (rex : Bool) (suffix : List Byte)
    (h : byteZielReg (regCode dst) rex = some dst) :
    decodeRot (rotEncode ⟨o, .b8, .eins, .reg dst⟩ ++ suffix) =
      some (⟨⟨o, .b8, .eins, .reg dst⟩,
        rotLaenge ⟨o, .b8, .eins, .reg dst⟩⟩, suffix) ∧
    byteZulaessig (regCode dst) rex = true := by
  refine ⟨rotRoundtrip_reg_eins o .b8 dst suffix, ?_⟩
  unfold byteZulaessig
  rw [h]

/-- Admitted 8-bit by-CL rotate forms round-trip, same shape. -/
theorem byteRotRundgang8_cl (o : RotOp) (dst : Register)
    (rex : Bool) (suffix : List Byte)
    (h : byteZielReg (regCode dst) rex = some dst) :
    decodeRot (rotEncode ⟨o, .b8, .cl, .reg dst⟩ ++ suffix) =
      some (⟨⟨o, .b8, .cl, .reg dst⟩,
        rotLaenge ⟨o, .b8, .cl, .reg dst⟩⟩, suffix) ∧
    byteZulaessig (regCode dst) rex = true := by
  refine ⟨rotRoundtrip_reg_cl o .b8 dst suffix, ?_⟩
  unfold byteZulaessig
  rw [h]

/-- FINDING (accepted-codec gap): the accepted rotate codec encodes
    `.rsp` at 8 bits with NO REX and decodes it back to `.rsp`,
    while the selector refuses code 4 without REX: on silicon those
    bytes mean AH, not SPL. Self-consistent, silicon-wrong; the
    selector side stays refused here. -/
theorem byteRot_ah_befund :
    decodeRot (rotEncode ⟨.rol, .b8, .eins, .reg .rsp⟩) =
      some (⟨⟨.rol, .b8, .eins, .reg .rsp⟩,
        rotLaenge ⟨.rol, .b8, .eins, .reg .rsp⟩⟩, []) ∧
    byteZielReg 4 false = none := by
  refine ⟨?_, rfl⟩
  have h := rotRoundtrip_reg_eins .rol .b8 .rsp []
  simpa using h

/-! ## 5. Carry 8-bit rows: round trip exactly where admitted.

    The accepted carry codec (`carryEncode`/`decodeCarry`) already
    refuses the high-byte codes at 8 bits (`hochbyteCode` in
    `decodeCarryReg`); the round trip below holds exactly where the
    selector admits, in both directions, over the no-prefix codes
    (`regHigh = 0` on both sides, the REX hypotheses discharge the
    extended registers). -/

/-- Without REX only the four classic low bytes are admitted. -/
theorem byteZulaessig_niedrig8 (r : Register)
    (h : byteZulaessig (regCode r) false = true) :
    r = .rax ∨ r = .rcx ∨ r = .rdx ∨ r = .rbx := by
  cases r <;> simp_all [byteZulaessig, byteZielReg, regCode]

/-- 8-bit ADC register rows round-trip exactly on admitted codes:
    the admission premises select the four low registers, each of
    which the accepted codec reads back definitionally. -/
theorem byteCarryRundgang_adc8 (dst src : Register)
    (suffix : List Byte)
    (h : byteZulaessig (regCode dst) false = true ∧
      byteZulaessig (regCode src) false = true) :
    decodeCarry (carryEncode (.adcReg .b8 dst src) ++ suffix) =
      some (.reg ⟨.adcReg .b8 dst src,
        (carryEncode (.adcReg .b8 dst src)).length⟩, suffix) ∧
    byteZulaessig (regCode dst) false = true ∧
      byteZulaessig (regCode src) false = true := by
  obtain ⟨hd, hs⟩ := h
  have hd' := byteZulaessig_niedrig8 dst hd
  have hs' := byteZulaessig_niedrig8 src hs
  rcases hd' with rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, hd, hs⟩ <;> rfl

/-- 8-bit SBB register rows round-trip exactly on admitted codes. -/
theorem byteCarryRundgang_sbb8 (dst src : Register)
    (suffix : List Byte)
    (h : byteZulaessig (regCode dst) false = true ∧
      byteZulaessig (regCode src) false = true) :
    decodeCarry (carryEncode (.sbbReg .b8 dst src) ++ suffix) =
      some (.reg ⟨.sbbReg .b8 dst src,
        (carryEncode (.sbbReg .b8 dst src)).length⟩, suffix) ∧
    byteZulaessig (regCode dst) false = true ∧
      byteZulaessig (regCode src) false = true := by
  obtain ⟨hd, hs⟩ := h
  have hd' := byteZulaessig_niedrig8 dst hd
  have hs' := byteZulaessig_niedrig8 src hs
  rcases hd' with rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, hd, hs⟩ <;> rfl

/-- 8-bit INC rows round-trip exactly on admitted codes. -/
theorem byteCarryRundgang_inc8 (dst : Register)
    (suffix : List Byte)
    (h : byteZulaessig (regCode dst) false = true) :
    decodeCarry (carryEncode (.incReg .b8 dst) ++ suffix) =
      some (.reg ⟨.incReg .b8 dst,
        (carryEncode (.incReg .b8 dst)).length⟩, suffix) ∧
    byteZulaessig (regCode dst) false = true := by
  have hd' := byteZulaessig_niedrig8 dst h
  rcases hd' with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, h⟩ <;> rfl

/-- 8-bit DEC rows round-trip exactly on admitted codes. -/
theorem byteCarryRundgang_dec8 (dst : Register)
    (suffix : List Byte)
    (h : byteZulaessig (regCode dst) false = true) :
    decodeCarry (carryEncode (.decReg .b8 dst) ++ suffix) =
      some (.reg ⟨.decReg .b8 dst,
        (carryEncode (.decReg .b8 dst)).length⟩, suffix) ∧
    byteZulaessig (regCode dst) false = true := by
  have hd' := byteZulaessig_niedrig8 dst h
  rcases hd' with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, h⟩ <;> rfl

/-- FINDING (high-byte gap, carry side): the canonical 8-bit
    encoding of `.rsp` carries no REX, and the accepted decoder
    refuses it by name (`hochbyteCode`); the selector agrees. -/
theorem byteCarry_hochbyte_befund :
    decodeCarry (carryEncode (.adcReg .b8 .rsp .rax)) = none ∧
    byteZielReg 4 false = none := by
  refine ⟨?_, rfl⟩
  decide

/-! ## 6. 8-bit exchange: value, canonical bytes, round trips.

    The accepted `xchgSchritt` swaps whole 64-bit words only; no
    accepted 8-bit XCHG evaluator or codec exists, so the 8-bit
    register exchange (opcode 86H, register-direct) is modelled here
    over the accepted narrow merge with flags untouched. The codec
    parses bytes, never encode-equality; high-byte codes without REX
    refuse through the selector. -/

/-- REX need of an 8-bit exchange pair: extension bits, or the low
    4-7 codes (SPL/BPL/SIL/DIL need REX on silicon). -/
def byteXchgBrauchtRex (dst src : Register) : Bool :=
  decide (regHigh dst = 1 ∨ regHigh src = 1 ∨
    regCode dst = 4 ∨ regCode dst = 5 ∨ regCode dst = 6 ∨
    regCode dst = 7 ∨ regCode src = 4 ∨ regCode src = 5 ∨
    regCode src = 6 ∨ regCode src = 7)

/-- Canonical REX for an 8-bit exchange pair (0x40 with no extension
    bits: REX.W stays clear at 8 bits, its presence alone switches
    codes 4-7 to the low bytes). -/
def byteXchgRex (dst src : Register) : List Byte :=
  if byteXchgBrauchtRex dst src then
    [natByte (64 + 4 * regHigh src + regHigh dst)]
  else []

/-- Canonical 8-bit exchange encoding of a register pair. -/
def encodeByteXchg (dst src : Register) : List Byte :=
  byteXchgRex dst src ++
    [natByte 134, modrmReg (regLow src) (regLow dst)]

/-- 8-bit exchange decoder: optional single REX, 86H,
    register-direct ModRM; every other shape refuses. -/
def decodeByteXchg : List Byte → Option ((Register × Register) × List Byte)
  | r :: rest =>
    if decide (64 ≤ byteNat r ∧ byteNat r < 80) then
      match rest with
      | o :: m :: rest' =>
        if byteNat o == 134 && byteNat m / 64 == 3 then
          match byteZielReg (byteNat r % 2 * 8 + byteNat m % 8) true,
                byteZielReg (byteNat r / 4 % 2 * 8 +
                  byteNat m / 8 % 8) true with
          | some dst, some src => some ((dst, src), rest')
          | _, _ => none
        else none
      | _ => none
    else if byteNat r == 134 then
      match rest with
      | m :: rest' =>
        if byteNat m / 64 == 3 then
          match byteZielReg (byteNat m % 8) false,
                byteZielReg (byteNat m / 8 % 8) false with
          | some dst, some src => some ((dst, src), rest')
          | _, _ => none
        else none
      | _ => none
    else none
  | [] => none

/-- Decoding inverts encoding on every register pair, over any
    suffix: all 256 combinations checked by kernel computation. -/
theorem byteXchgRundgang (dst src : Register)
    (suffix : List Byte) :
    decodeByteXchg (encodeByteXchg dst src ++ suffix) =
      some ((dst, src), suffix) := by
  cases dst <;> cases src <;> rfl

/-- Pinned bytes: `xchg al, cl` is 86H C8 with no prefix. -/
theorem byteXchg_pin_niedrig :
    encodeByteXchg .rax .rcx = [natByte 134, natByte 200] := by
  decide

/-- Pinned bytes: `xchg spl, al` carries a bare 0x40 REX. -/
theorem byteXchg_pin_rex40 :
    encodeByteXchg .rsp .rax =
      [natByte 64, natByte 134, natByte 196] := by
  decide

/-- Planted refusal: a bare high-byte row (AH) never decodes. -/
theorem byteXchg_hochbyte_verweigert :
    decodeByteXchg [natByte 134, natByte 196] = none := by
  decide

/-- Planted refusals: LOCK, wrong opcode, memory mode, truncation. -/
theorem byteXchg_sonde_verweigert :
    decodeByteXchg [natByte 240, natByte 134, natByte 200] = none ∧
    decodeByteXchg [natByte 135, natByte 200] = none ∧
    decodeByteXchg [natByte 134, natByte 8] = none ∧
    decodeByteXchg [natByte 134] = none ∧
    decodeByteXchg [] = none := by
  decide

/-! ## 7. Family step and machine adapter.

    One checked 8-bit event runs the accepted evaluator at `.b8`
    over the canonical state with the accepted merge discipline;
    REX admission rides along as checked data. Memory operands are
    NOT admitted here: 8-bit memory forms are TSO byte events,
    never the register plug (the witness in §8 issues and drains
    through the accepted TSO equations). -/

/-- 8-bit family operations over registers. -/
inductive ByteFamOp where
  | rol (dst : Register) (c : Nat)
  | ror (dst : Register) (c : Nat)
  | adc (dst src : Register)
  | sbb (dst src : Register)
  | inc (dst : Register)
  | dec (dst : Register)
  | xchg (dst src : Register)
  deriving DecidableEq, Repr

/-- One checked 8-bit family event: operation, REX presence, length. -/
structure ByteFamEreignis where
  op : ByteFamOp
  rex : Bool
  laenge : Nat
  deriving DecidableEq, Repr

/-- Admission of one operation under a REX flag: every touched full
    code passes the selector. -/
def byteOpZulaessig : ByteFamOp → Bool → Bool
  | .rol dst _, rex => byteZulaessig (regCode dst) rex
  | .ror dst _, rex => byteZulaessig (regCode dst) rex
  | .adc dst src, rex =>
    byteZulaessig (regCode dst) rex && byteZulaessig (regCode src) rex
  | .sbb dst src, rex =>
    byteZulaessig (regCode dst) rex && byteZulaessig (regCode src) rex
  | .inc dst, rex => byteZulaessig (regCode dst) rex
  | .dec dst, rex => byteZulaessig (regCode dst) rex
  | .xchg dst src, rex =>
    byteZulaessig (regCode dst) rex && byteZulaessig (regCode src) rex

/-- One 8-bit family step over registers; `none` is length or
    admission refusal, never a silent successor. -/
def byteFamSchritt (e : ByteFamEreignis) (s : Zustand) :
    Option Zustand :=
  match laengeOk e.laenge with
  | false => none
  | true =>
    match byteOpZulaessig e.op e.rex with
    | false => none
    | true =>
      let nach := ripNach s.rip e.laenge
      match e.op with
      | .rol dst c =>
        some (schrittRegister s nach
          (rotFlags .rol .b8 (s.register dst) s.flags.cf s.flags c)
          dst (mergeRegNarrow .b8 (s.register dst)
            (rolB .b8 (s.register dst) c)))
      | .ror dst c =>
        some (schrittRegister s nach
          (rotFlags .ror .b8 (s.register dst) s.flags.cf s.flags c)
          dst (mergeRegNarrow .b8 (s.register dst)
            (rorB .b8 (s.register dst) c)))
      | .adc dst src =>
        some (schrittRegister s nach
          (adcFlags .b8 (s.register dst) (s.register src) s.flags.cf)
          dst (mergeRegNarrow .b8 (s.register dst)
            (adcWert .b8 (s.register dst) (s.register src)
              s.flags.cf)))
      | .sbb dst src =>
        some (schrittRegister s nach
          (sbbFlags .b8 (s.register dst) (s.register src) s.flags.cf)
          dst (mergeRegNarrow .b8 (s.register dst)
            (sbbWert .b8 (s.register dst) (s.register src)
              s.flags.cf)))
      | .inc dst =>
        some (schrittRegister s nach
          (incFlags .b8 (s.register dst) s.flags)
          dst (mergeRegNarrow .b8 (s.register dst)
            (incWert .b8 (s.register dst))))
      | .dec dst =>
        some (schrittRegister s nach
          (decFlags .b8 (s.register dst) s.flags)
          dst (mergeRegNarrow .b8 (s.register dst)
            (decWert .b8 (s.register dst))))
      | .xchg dst src =>
        let zwischen := regSet s.register dst
          (mergeRegNarrow .b8 (s.register dst) (s.register src))
        let beide := regSet zwischen src
          (mergeRegNarrow .b8 (s.register src) (s.register dst))
        some { s with register := beide, rip := nach, flags := s.flags }

/-! ## 8. Step equations: each arm pins its accepted successor.

    Every equation reuses its accepted evaluator at `.b8` with the
    accepted merge; all three premises rewrite the two gates and the
    operation. -/

/-- `rol`: the destination merges the accepted ROL with its flags. -/
theorem byteFam_rol_erfolg (e : ByteFamEreignis) (s : Zustand)
    (dst : Register) (c : Nat)
    (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = true)
    (h : e.op = .rol dst c) :
    byteFamSchritt e s = some (schrittRegister s
      (ripNach s.rip e.laenge)
      (rotFlags .rol .b8 (s.register dst) s.flags.cf s.flags c) dst
      (mergeRegNarrow .b8 (s.register dst)
        (rolB .b8 (s.register dst) c))) := by
  unfold byteFamSchritt
  rw [hok, hz, h]

/-- `ror`: the destination merges the accepted ROR with its flags. -/
theorem byteFam_ror_erfolg (e : ByteFamEreignis) (s : Zustand)
    (dst : Register) (c : Nat)
    (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = true)
    (h : e.op = .ror dst c) :
    byteFamSchritt e s = some (schrittRegister s
      (ripNach s.rip e.laenge)
      (rotFlags .ror .b8 (s.register dst) s.flags.cf s.flags c) dst
      (mergeRegNarrow .b8 (s.register dst)
        (rorB .b8 (s.register dst) c))) := by
  unfold byteFamSchritt
  rw [hok, hz, h]

/-- `adc`: the destination merges the carry sum with ADC flags. -/
theorem byteFam_adc_erfolg (e : ByteFamEreignis) (s : Zustand)
    (dst src : Register)
    (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = true)
    (h : e.op = .adc dst src) :
    byteFamSchritt e s = some (schrittRegister s
      (ripNach s.rip e.laenge)
      (adcFlags .b8 (s.register dst) (s.register src) s.flags.cf) dst
      (mergeRegNarrow .b8 (s.register dst)
        (adcWert .b8 (s.register dst) (s.register src)
          s.flags.cf))) := by
  unfold byteFamSchritt
  rw [hok, hz, h]

/-- `sbb`: the destination merges the borrow difference. -/
theorem byteFam_sbb_erfolg (e : ByteFamEreignis) (s : Zustand)
    (dst src : Register)
    (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = true)
    (h : e.op = .sbb dst src) :
    byteFamSchritt e s = some (schrittRegister s
      (ripNach s.rip e.laenge)
      (sbbFlags .b8 (s.register dst) (s.register src) s.flags.cf) dst
      (mergeRegNarrow .b8 (s.register dst)
        (sbbWert .b8 (s.register dst) (s.register src)
          s.flags.cf))) := by
  unfold byteFamSchritt
  rw [hok, hz, h]

/-- `inc`: the destination merges the successor, CF preserved. -/
theorem byteFam_inc_erfolg (e : ByteFamEreignis) (s : Zustand)
    (dst : Register)
    (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = true)
    (h : e.op = .inc dst) :
    byteFamSchritt e s = some (schrittRegister s
      (ripNach s.rip e.laenge)
      (incFlags .b8 (s.register dst) s.flags) dst
      (mergeRegNarrow .b8 (s.register dst)
        (incWert .b8 (s.register dst)))) := by
  unfold byteFamSchritt
  rw [hok, hz, h]

/-- `dec`: the destination merges the predecessor, CF preserved. -/
theorem byteFam_dec_erfolg (e : ByteFamEreignis) (s : Zustand)
    (dst : Register)
    (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = true)
    (h : e.op = .dec dst) :
    byteFamSchritt e s = some (schrittRegister s
      (ripNach s.rip e.laenge)
      (decFlags .b8 (s.register dst) s.flags) dst
      (mergeRegNarrow .b8 (s.register dst)
        (decWert .b8 (s.register dst)))) := by
  unfold byteFamSchritt
  rw [hok, hz, h]

/-- `xchg`: both destinations merge the crossed low bytes. -/
theorem byteFam_xchg_erfolg (e : ByteFamEreignis) (s : Zustand)
    (dst src : Register)
    (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = true)
    (h : e.op = .xchg dst src) :
    byteFamSchritt e s =
      let zwischen := regSet s.register dst
        (mergeRegNarrow .b8 (s.register dst) (s.register src))
      let beide := regSet zwischen src
        (mergeRegNarrow .b8 (s.register src) (s.register dst))
      some { s with register := beide, rip := ripNach s.rip e.laenge, flags := s.flags } := by
  unfold byteFamSchritt
  rw [hok, hz, h]

/-- A bad decode length refuses every form, unconditionally. -/
theorem byteFam_laenge_misslungen (e : ByteFamEreignis) (s : Zustand)
    (h : laengeOk e.laenge = false) :
    byteFamSchritt e s = none := by
  unfold byteFamSchritt
  rw [h]

/-- A refused admission refuses every form: high-byte codes without
    REX never reach the evaluator. -/
theorem byteFam_unzulaessig_misslungen (e : ByteFamEreignis)
    (s : Zustand) (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = false) :
    byteFamSchritt e s = none := by
  unfold byteFamSchritt
  rw [hok, hz]

/-- A successful family step leaves canonical memory alone. -/
theorem byteFamSchritt_speicher (e : ByteFamEreignis) (s s' : Zustand)
    (h : byteFamSchritt e s = some s') :
    s'.speicher = s.speicher := by
  unfold byteFamSchritt at h
  cases hlen : laengeOk e.laenge with
  | false =>
    rw [hlen] at h
    cases h
  | true =>
    rw [hlen] at h
    cases hzul : byteOpZulaessig e.op e.rex with
    | false =>
      rw [hzul] at h
      cases h
    | true =>
      rw [hzul] at h
      cases hop : e.op with
      | rol dst c => rw [hop] at h; cases h; rfl
      | ror dst c => rw [hop] at h; cases h; rfl
      | adc dst src => rw [hop] at h; cases h; rfl
      | sbb dst src => rw [hop] at h; cases h; rfl
      | inc dst => rw [hop] at h; cases h; rfl
      | dec dst => rw [hop] at h; cases h; rfl
      | xchg dst src => rw [hop] at h; cases h; rfl

/-- A successful family step advances RIP past the decoded length. -/
theorem byteFamSchritt_rip (e : ByteFamEreignis) (s s' : Zustand)
    (h : byteFamSchritt e s = some s') :
    s'.rip = ripNach s.rip e.laenge := by
  unfold byteFamSchritt at h
  cases hlen : laengeOk e.laenge with
  | false =>
    rw [hlen] at h
    cases h
  | true =>
    rw [hlen] at h
    cases hzul : byteOpZulaessig e.op e.rex with
    | false =>
      rw [hzul] at h
      cases h
    | true =>
      rw [hzul] at h
      cases hop : e.op with
      | rol dst c => rw [hop] at h; cases h; rfl
      | ror dst c => rw [hop] at h; cases h; rfl
      | adc dst src => rw [hop] at h; cases h; rfl
      | sbb dst src => rw [hop] at h; cases h; rfl
      | inc dst => rw [hop] at h; cases h; rfl
      | dec dst => rw [hop] at h; cases h; rfl
      | xchg dst src => rw [hop] at h; cases h; rfl

/-! ## 9. Machine adapter: the 8-bit family on the coherent machine.

    The producer plug instantiates `HwAdapter ByteFamEreignis` with
    the accepted API: a successful family step re-embeds core data
    over the shared memory; length and admission refusals admit no
    successor. -/

/-- The 8-bit family plug: one checked event step on the coherent
    machine. `none` = length or admission refusal. -/
def adapterByteFam : HwAdapter ByteFamEreignis :=
  ⟨fun m c e =>
    match byteFamSchritt e (projZustand m c) with
    | some s' =>
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
    | none => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterByteFam_wf (m : HwMaschine) (c : Nat)
    (e : ByteFamEreignis) (m' : HwMaschine) (hwf : HwWf m)
    (h : adapterByteFam.schritt m c e = some m') :
    HwWf m' := by
  unfold adapterByteFam at h
  simp only at h
  cases hsch : byteFamSchritt e (projZustand m c) with
  | some s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | none =>
    rw [hsch] at h
    simp only at h
    cases h

/-- Agreement: the adapter succeeds exactly where the accepted
    family step succeeds, with the successor core data re-embedded. -/
theorem adapterByteFam_ok (m : HwMaschine) (c : Nat)
    (e : ByteFamEreignis) (s' : Zustand)
    (h : byteFamSchritt e (projZustand m c) = some s') :
    adapterByteFam.schritt m c e =
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  unfold adapterByteFam
  simp only [h]

/-- The successor core sees the accepted successor registers over
    the shared memory. -/
theorem adapterByteFam_proj (m : HwMaschine) (c : Nat)
    (e : ByteFamEreignis) (s' : Zustand)
    (h : byteFamSchritt e (projZustand m c) = some s') :
    ((setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).kerne c).register =
      s'.register ∧
    (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).mem = m.mem ∧
    s'.speicher = m.mem := by
  refine ⟨setKernVonFp_register m c _,
    setKernVonFp_speicher m c _, ?_⟩
  have hmem := byteFamSchritt_speicher e (projZustand m c) s' h
  have hproj : (projZustand m c).speicher = m.mem := rfl
  rw [hproj] at hmem
  exact hmem

/-- A bad decode length admits no adapter step. -/
theorem adapterByteFam_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (e : ByteFamEreignis)
    (h : laengeOk e.laenge = false) :
    adapterByteFam.schritt m c e = none := by
  have hstep := byteFam_laenge_misslungen e (projZustand m c) h
  unfold adapterByteFam
  simp only [hstep]

/-- A refused admission admits no adapter step: high-byte codes
    without REX never move core data. -/
theorem adapterByteFam_verweigert_ohne_zulassung (m : HwMaschine)
    (c : Nat) (e : ByteFamEreignis)
    (hok : laengeOk e.laenge = true)
    (hz : byteOpZulaessig e.op e.rex = false) :
    adapterByteFam.schritt m c e = none := by
  have hstep := byteFam_unzulaessig_misslungen e (projZustand m c) hok hz
  unfold adapterByteFam
  simp only [hstep]

/-! ## 10. Joint witness: two cores, family steps, buffered store.

    Core 0 runs 8-bit INC on AL (5 becomes 6, upper bytes kept);
    core 1 runs 8-bit DEC on CL (0 becomes 0xFF in the low byte);
    then core 0 issues its new low byte at the data cell, observes
    it by forwarding while core 1 still reads the old byte, and
    drains it into shared memory (0 becomes 6, observed from both
    cores). The family legs are register-only by construction
    (`byteFamSchritt_speicher`); the memory leg is the accepted
    TSO issue/flush. Every claim is a closed decidable observation;
    no machine equality is ever decided. -/

/-- Witness event on core 0: 8-bit INC on AL, no REX. -/
def byteWitE0 : ByteFamEreignis := ⟨.inc .rax, false, 3⟩

/-- Witness event on core 1: 8-bit DEC on CL, no REX. -/
def byteWitE1 : ByteFamEreignis := ⟨.dec .rcx, false, 2⟩

/-- Core-0 successor through the adapter. -/
def byteWitM1 : Option HwMaschine :=
  adapterByteFam.schritt hwWitStart 0 byteWitE0

/-- Core-1 successor through the adapter. -/
def byteWitM2 : Option HwMaschine :=
  adapterByteFam.schritt hwWitStart 1 byteWitE1

/-- Read a register out of a machine option. -/
def byteWitReg (m : Option HwMaschine) (c : Nat) (q : Register) :
    Option Wort :=
  match m with
  | some m' => some ((m'.kerne c).register q)
  | none => none

/-- Read a core RIP out of a machine option. -/
def byteWitRip (m : Option HwMaschine) (c : Nat) : Option Wort :=
  match m with
  | some m' => some ((m'.kerne c).rip)
  | none => none

/-- Read a shared-memory byte out of a machine option. -/
def byteWitMem (m : Option HwMaschine) (a : Adresse) : Option Byte :=
  match m with
  | some m' => some (m'.mem.bytes a)
  | none => none

/-- Core 0 AL becomes 6: the low byte increments, upper kept. -/
theorem byteWit_m1_rax :
    byteWitReg byteWitM1 0 .rax = some (BitVec.ofNat 64 6) := by
  decide

/-- Core 0 RIP advances past the 3-byte event. -/
theorem byteWit_m1_rip :
    byteWitRip byteWitM1 0 = some (BitVec.ofNat 64 4099) := by
  decide

/-- The family step leaves the shared byte alone. -/
theorem byteWit_m1_mem_still :
    byteWitMem byteWitM1 hwWitAdr = some (BitVec.ofNat 8 0) := by
  decide

/-- Core 1 CL becomes 0xFF in the low byte. -/
theorem byteWit_m2_rcx :
    byteWitReg byteWitM2 1 .rcx = some (BitVec.ofNat 64 0xFF) := by
  decide

/-- The issued byte is the new low byte of core-0 AL. -/
theorem byteWit_m1_tiefbyte :
    (match byteWitM1 with
    | some m' => wortByte ((m'.kerne 0).register .rax) 0
    | none => BitVec.ofNat 8 0xFF)
      = BitVec.ofNat 8 6 := by
  decide

/-- Core 0 issues its new low byte at the data cell. -/
def byteWitTso1 : Option TSOZustand :=
  match byteWitM1 with
  | some m1 =>
    issueByte (tsoAnsicht m1) 0 hwWitAdr (BitVec.ofNat 8 6)
  | none => none

/-- Core 0 observes its own byte (forwarding). -/
def byteWitLoadEigen : Option (Option Byte) :=
  match byteWitTso1 with
  | some s => some (loadByte s 0 hwWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def byteWitLoadFremd : Option (Option Byte) :=
  match byteWitTso1 with
  | some s => some (loadByte s 1 hwWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def byteWitTso2 : Option TSOZustand :=
  match byteWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def byteWitNachFlush : Option (Option Byte) :=
  match byteWitTso2 with
  | some s => some (some (s.mem.bytes hwWitAdr))
  | none => none

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem byteWit_weiterleitung :
    byteWitLoadEigen = some (some (BitVec.ofNat 8 6)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem byteWit_fremd_alt :
    byteWitLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 6. -/
theorem byteWit_spuelung_aendert_speicher :
    byteWitNachFlush = some (some (BitVec.ofNat 8 6)) := by
  decide

/-- The joint witness: well-formedness at the start, two reached
    family steps on two cores with register change, the family
    memory stillness, the low-byte link, owner-only forwarding and
    the memory-changing drain. Non-degenerate: AL 5 becomes 6 and
    the shared byte 0 becomes 6. -/
theorem byteFam_zeuge :
    HwWf hwWitStart ∧
    byteWitReg byteWitM1 0 .rax = some (BitVec.ofNat 64 6) ∧
    byteWitRip byteWitM1 0 = some (BitVec.ofNat 64 4099) ∧
    byteWitReg byteWitM2 1 .rcx = some (BitVec.ofNat 64 0xFF) ∧
    byteWitMem byteWitM1 hwWitAdr = some (BitVec.ofNat 8 0) ∧
    byteWitLoadEigen = some (some (BitVec.ofNat 8 6)) ∧
    byteWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
    byteWitNachFlush = some (some (BitVec.ofNat 8 6)) := by
  refine ⟨hwWitStart_wf, byteWit_m1_rax, byteWit_m1_rip,
    byteWit_m2_rcx, byteWit_m1_mem_still, byteWit_weiterleitung,
    byteWit_fremd_alt, byteWit_spuelung_aendert_speicher⟩

/- CUTS:
   Proved here (self-consistency only, no silicon proof):
   - byte-register selection with the architectural REX rule (§1)
     against the accepted `codeReg` file, with the high-byte and
     out-of-range refusals;
   - the 8-bit merge discipline through the accepted
     `mergeRegNarrow .b8` (§2), pinned merge/no-zero-extend;
   - the 8-bit rotate / ADC / SBB / INC / DEC lifts (§3): the old
     evaluators at `.b8`, never redefined;
   - rotate 8-bit round trips through the accepted codec (§4) with
     the selector admission beside the bytes;
   - carry 8-bit round trips exactly on admitted codes (§5) with
     the high-byte refusal;
   - the 8-bit register exchange value/codec/round trips (§6) with
     planted refusals;
   - one checked 8-bit family step (§7-§8) with per-arm equations,
     length/admission refusals, memory stillness and RIP advance;
   - a `HwAdapter` (§9) preserving `HwWf` with exact agreement and
     refusals, and a reached two-core witness with `_zeuge` (§10).
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the accepted
     canonical subsets (plus the new 86H row) with
     self-consistency only, not x86 truth. Provenance is the
     clone-local Intel SDM extract (see MUSE-REPORT-1319.md);
     no AMD provenance is claimed (rule 17).
   - FINDING (not hidden): the accepted rotate codec maps 8-bit
     codes 4-7 without REX to SPL/BPL/SIL/DIL (`byteRot_ah_befund`);
     on silicon those bytes mean AH/CH/DH/BH. The selector side
     stays refused here; the accepted file is untouched.
   - `IntSignXchg` is not in this tree, so no 8-bit form of it is
     connected here.
   - No LOCK/RMW path, no 8-bit memory forms (TSO events only),
     no SIB/addressed forms, no bridge to W/GX.
   Silicon/timing assumptions: none beyond the accepted lemmas
   reused; REX switching, merge-no-zero-extend and flag rows are
   the accepted definitions restated, checked against the SDM
   extract named in the report.
-/

#print axioms byteZielReg_tief
#print axioms byteZielReg_rex_schalter
#print axioms byteZielReg_hochbyte_verweigert
#print axioms byteRotRundgang8_eins
#print axioms byteRotRundgang8_cl
#print axioms byteRot_ah_befund
#print axioms byteCarryRundgang_adc8
#print axioms byteCarryRundgang_sbb8
#print axioms byteCarryRundgang_inc8
#print axioms byteCarryRundgang_dec8
#print axioms byteCarry_hochbyte_befund
#print axioms byteXchgRundgang
#print axioms byteFam_rol_erfolg
#print axioms byteFam_adc_erfolg
#print axioms byteFam_xchg_erfolg
#print axioms adapterByteFam_wf
#print axioms adapterByteFam_ok
#print axioms byteFam_zeuge

end Gabbro.Grammatik.X86
