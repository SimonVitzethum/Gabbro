/-
  File:      Grammatik/X86/MulDivWidthHardwareForms.lean
  Subject:   Essential 32/64-bit MUL/DIV/IDIV, two/three-operand IMUL
             with signed immediates, and dividend preparation (CBW/CWDE/
             CDQE/CWD/CDQ/CQO) as byte-facing hardware forms.

  Lane 700: admitted widths are 32 and 64 bits only; 8/16-bit multiply/
  divide stay explicitly refused (essential OPEN, see CUTS). Reuses the
  accepted `MulDiv` 64-bit execution, `Ganzzahl` width operations and
  the canonical `Zustand`/register/flag vocabulary. No new machine.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM 325462-093US Sep 2026, instruction reference text.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.FlagBeweis
import Grammatik.X86.MulDiv
import Grammatik.X86.MulDivCodec
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Admitted operand width: practical 32-bit and 64-bit forms. -/
inductive WdBreite where
  | w32
  | w64
  deriving DecidableEq, Repr

/-- Bit count of the admitted width. -/
def WdBreite.bits : WdBreite → Nat
  | WdBreite.w32 => 32
  | WdBreite.w64 => 64

/-- Architectural width backing an admitted width. -/
def WdBreite.breite : WdBreite → Breite
  | WdBreite.w32 => .b32
  | WdBreite.w64 => .b64

/-- Operand read at the admitted width: 32-bit reads truncate (upper
    bits are not part of the operand); 64-bit reads the full word. -/
def wdLesen (w : WdBreite) (v : Wort) : Wort :=
  match w with
  | WdBreite.w32 => trunc .b32 v
  | WdBreite.w64 => v

/-- Operand write at the admitted width: 32-bit writes zero-extend
    (upper 32 bits cleared, matching silicon); 64-bit writes whole. -/
def wdSchreiben (w : WdBreite) (v : Wort) : Wort :=
  match w with
  | WdBreite.w32 => trunc .b32 v
  | WdBreite.w64 => v

/-- Write is truncation at 32 bits. -/
theorem wdSchreiben_w32 (v : Wort) :
    wdSchreiben WdBreite.w32 v = trunc .b32 v := rfl

/-- Write is identity at 64 bits. -/
theorem wdSchreiben_w64 (v : Wort) : wdSchreiben WdBreite.w64 v = v := rfl

/-! ## 1. 32-bit dividends and checked wide division.

    DIV entry (txt line 50157): `EDX:EAX / r/m32`, quotient into EAX,
    remainder into EDX, `#DE` on divisor zero or quotient above
    `0xFFFFFFFF`. IDIV entry (txt line 58043): signed `EDX:EAX /
    r/m32` with truncation toward zero and the same `#DE` rule over
    the signed range. Reuses `trunc`/`sVal` from `Ganzzahl`. -/

/-- Unsigned value of the 32-bit EDX:EAX dividend. -/
def u64aus32 (hoch tief : Wort) : Nat :=
  (trunc .b32 hoch).toNat * 2 ^ 32 + (trunc .b32 tief).toNat

/-- Signed value of the 32-bit EDX:EAX dividend. -/
def s64aus32 (hoch tief : Wort) : Int :=
  sVal .b32 hoch * 2 ^ 32 + (trunc .b32 tief).toNat

/-- Unsigned 32-bit wide division: `none` on divisor zero or a
    quotient above 32 bits. -/
def divWeitU32 (hoch tief teiler : Wort) : Option (Wort × Wort) :=
  let dn := (trunc .b32 teiler).toNat
  if dn = 0 then none
  else
    let q := u64aus32 hoch tief / dn
    let r := u64aus32 hoch tief % dn
    if q < 2 ^ 32 then some (trunc .b32 (BitVec.ofNat 64 q),
      trunc .b32 (BitVec.ofNat 64 r))
    else none

/-- Signed 32-bit wide division: `none` on divisor zero or a quotient
    outside the signed 32-bit range; truncation toward zero. -/
def divWeitS32 (hoch tief teiler : Wort) : Option (Wort × Wort) :=
  let yn := sVal .b32 teiler
  if yn = 0 then none
  else
    let q := (s64aus32 hoch tief).tdiv yn
    let r := (s64aus32 hoch tief).tmod yn
    if -(((2 ^ 31 : Nat) : Int)) ≤ q ∧ q < (((2 ^ 31 : Nat) : Int)) then
      some (trunc .b32 (BitVec.ofNat 64 (q.emod ((2 ^ 32 : Nat) : Int)).toNat),
        trunc .b32 (BitVec.ofNat 64 (r.emod ((2 ^ 32 : Nat) : Int)).toNat))
    else none

/-- 32-bit unsigned division refuses on divisor zero. -/
theorem divWeitU32_verweigert_bei_null (hoch tief teiler : Wort)
    (h : (trunc .b32 teiler).toNat = 0) :
    divWeitU32 hoch tief teiler = none := by
  simp [divWeitU32, h]

/-- 32-bit unsigned division refuses when the quotient needs 33 bits. -/
theorem divWeitU32_verweigert_bei_ueberlauf (hoch tief teiler : Wort)
    (hpos : (trunc .b32 teiler).toNat ≠ 0)
    (hgross : ¬ u64aus32 hoch tief / (trunc .b32 teiler).toNat < 2 ^ 32) :
    divWeitU32 hoch tief teiler = none := by
  simp [divWeitU32, hpos, hgross]

/-- 32-bit unsigned division answers when divisor is nonzero and the
    quotient fits 32 bits. -/
theorem divWeitU32_antwortet (hoch tief teiler : Wort)
    (hpos : (trunc .b32 teiler).toNat ≠ 0)
    (hfit : u64aus32 hoch tief / (trunc .b32 teiler).toNat < 2 ^ 32) :
    ∃ q r, divWeitU32 hoch tief teiler = some (q, r) := by
  simp [divWeitU32, hpos, hfit]

/-- 32-bit signed division refuses on divisor zero. -/
theorem divWeitS32_verweigert_bei_null (hoch tief teiler : Wort)
    (h : sVal .b32 teiler = 0) : divWeitS32 hoch tief teiler = none := by
  simp [divWeitS32, h]

/-- Truncation is idempotent. -/
theorem wd_trunc_idem (b : Breite) (v : Wort) :
    trunc b (trunc b v) = trunc b v := by
  simp [trunc, BitVec.and_assoc, BitVec.and_self]

/-- 32-bit answers are zero-extended (upper halves cleared). -/
theorem divWeitU32_antwortet_zero_ext (hoch tief teiler q r : Wort)
    (h : divWeitU32 hoch tief teiler = some (q, r)) :
    q = trunc .b32 q ∧ r = trunc .b32 r := by
  have hdef := h
  unfold divWeitU32 at hdef
  by_cases h0 : (trunc .b32 teiler).toNat = 0
  · simp [h0] at hdef
  · simp [h0] at hdef
    by_cases hfit : u64aus32 hoch tief / (trunc .b32 teiler).toNat < 2 ^ 32
    · simp [hfit] at hdef
      obtain ⟨hq, hr⟩ := hdef
      rw [← hq, ← hr]
      exact ⟨(wd_trunc_idem .b32 _).symm, (wd_trunc_idem .b32 _).symm⟩
    · simp [hfit] at hdef

/-! ## 2. Width flag snapshots: defined bits pinned, the rest kept.

    MUL entries (txt line 70674): CF/OF set iff the upper half is
    nonzero, SF/ZF/AF/PF undefined. IMUL entries (txt line 58200):
    CF/OF set iff the truncated product differs from the full double-
    width signed product, other flags undefined. `Flags` stores all
    but AF as `Bool`, so following `MulDiv.lean` the snapshots pin
    exactly CF/OF (AF `none`) and KEEP incoming SF/ZF/PF: an explicit
    modelling choice for undefined bits, not hardware truth. DIV/IDIV
    leave every flag undefined and preserve the snapshot. -/

/-- Unsigned width MUL flag snapshot over incoming flags. -/
def wdMulFlagsU (w : WdBreite) (f : Flags) (x y : Wort) : Flags :=
  let c := mulTragU w.breite x y
  { f with cf := c, of := c, af := none }

/-- Signed width IMUL flag snapshot over incoming flags. -/
def wdMulFlagsS (w : WdBreite) (f : Flags) (x y : Wort) : Flags :=
  let c := mulTragS w.breite x y
  { f with cf := c, of := c, af := none }

/-- The unsigned snapshot satisfies the unsigned validity relation. -/
theorem wdMulFlagsU_gueltig (w : WdBreite) (f : Flags) (x y : Wort) :
    MulGueltigU w.breite x y (wdMulFlagsU w f x y) := by
  simp [wdMulFlagsU, MulGueltigU]

/-- The signed snapshot satisfies the signed validity relation. -/
theorem wdMulFlagsS_gueltig (w : WdBreite) (f : Flags) (x y : Wort) :
    MulGueltigS w.breite x y (wdMulFlagsS w f x y) := by
  simp [wdMulFlagsS, MulGueltigS]

/-- A width snapshot keeps the incoming zero flag (undefined kept). -/
theorem wdMulFlagsU_zf (w : WdBreite) (f : Flags) (x y : Wort) :
    (wdMulFlagsU w f x y).zf = f.zf := rfl

/-- A width snapshot keeps the incoming sign flag (undefined kept). -/
theorem wdMulFlagsS_sf (w : WdBreite) (f : Flags) (x y : Wort) :
    (wdMulFlagsS w f x y).sf = f.sf := rfl

/-! ## 3. The width step: how the admitted target semantics grows.

    MUL table (txt line 70674 Table 1-1): `AL*r/m8 -> AX`,
    `AX*r/m16 -> DX:AX`, `EAX*r/m32 -> EDX:EAX`, `RAX*r/m64 ->
    RDX:RAX`. Only the 32/64 rows are admitted here. DIV/IDIV tables
    above give the matching dividend/quotient registers. IMUL
    two/three-operand forms truncate into the destination; the
    immediate is sign-extended to the operand width first (txt line
    58200: `6B /r ib` imm8, `69 /r id` imm32, REX.W sign-extends the
    dword immediate to 64 bits). Preparation `98` (CBW/CWDE/CDQE, txt
    line 44283) and `99` (CWD/CDQ/CQO, txt line 49874) sign-extend
    into the dividend halves and affect no flag. Outcomes reuse
    `MulDivErgebnis`: `ok`, `hardwareHalt` (#DE class: divisor zero
    or quotient overflow, destinations undefined so NO register
    claim is made on that arm), `misslungen` (bad length). -/

/-- Admitted operation forms at an admitted width. `imul3` carries the
    already sign-extended immediate as an integer. `vor98`/`vor99`
    are the dividend-preparation forms (opcode 98/99). -/
inductive WdBefehl where
  | mul (w : WdBreite) (src : Register)
  | divWd (w : WdBreite) (src : Register)
  | idivWd (w : WdBreite) (src : Register)
  | imul2 (w : WdBreite) (dst src : Register)
  | imul3 (w : WdBreite) (dst src : Register) (imm : Int)
  | vor98 (w : WdBreite)
  | vor99 (w : WdBreite)
  deriving DecidableEq, Repr

/-- Decoded width instruction: operation plus checked length data. -/
structure WdDecodiert where
  befehl : WdBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-- Sign extension of a decoded immediate byte to an integer. -/
def imm8Erweitert (b : Byte) : Int :=
  sVal .b8 (BitVec.ofNat 64 b.toNat)

/-- Immediate value at width: truncated product operand for IMUL3. -/
def wdImmWort (w : WdBreite) (imm : Int) : Wort :=
  wdSchreiben w (BitVec.ofNat 64 (imm.emod ((2 ^ 64 : Nat) : Int)).toNat)

/-- Preparation 98: CBW (w16 would-be, kept as explicit refusal
    carrier), CWDE (w32: RAX := zero-extended sign of AX), CDQE (w64:
    RAX := sign of EAX). Only admitted widths execute. -/
def vor98Schritt (w : WdBreite) (s : Zustand) : Zustand :=
  match w with
  | WdBreite.w32 =>
    let v := trunc .b32 (sext .b16 (s.register Register.rax))
    { s with register := regSet s.register Register.rax v }
  | WdBreite.w64 =>
    let v := sext .b32 (s.register Register.rax)
    { s with register := regSet s.register Register.rax v }

/-- Preparation 99: CDQ (w32: EDX := broadcast sign of EAX,
    zero-extended into RDX), CQO (w64: RDX := sign of RAX). -/
def vor99Schritt (w : WdBreite) (s : Zustand) : Zustand :=
  match w with
  | WdBreite.w32 =>
    let v := if negB .b32 (s.register Register.rax) then
      BitVec.ofNat 64 4294967295 else BitVec.ofNat 64 0
    { s with register := regSet s.register Register.rdx v }
  | WdBreite.w64 =>
    let v := if (s.register Register.rax).toNat.testBit 63 then
      BitVec.ofNat 64 (2 ^ 64 - 1) else BitVec.ofNat 64 0
    { s with register := regSet s.register Register.rdx v }

/-- Successor register file for a width MUL: low word into the
    accumulator, high word into the extension register. -/
def wdMulRegs (w : WdBreite) (r : Register → Wort) (a v : Wort) :
    Register → Wort :=
  regSet (regSet r Register.rax (wdSchreiben w (mulLow w.breite a v))) Register.rdx (wdSchreiben w (mulHighU w.breite a v))

/-- Successor register file for a width divide: quotient into the
    accumulator, remainder into the extension register. -/
def wdDivRegs (r : Register → Wort) (q qq : Wort) : Register → Wort :=
  regSet (regSet r Register.rax q) Register.rdx qq

/-- Successor register file for a two-operand IMUL. -/
def wdImul2Regs (w : WdBreite) (r : Register → Wort) (dst : Register)
    (a v : Wort) : Register → Wort :=
  regSet r dst (wdSchreiben w (mulLow w.breite a v))

/-- Successor state for a width MUL with its flag snapshot. -/
def wdNachMul (w : WdBreite) (s : Zustand) (src : Register)
    (nach : Adresse) : Zustand :=
  let a := wdLesen w (s.register Register.rax)
  let v := wdLesen w (s.register src)
  { register := wdMulRegs w s.register a v, flags := wdMulFlagsU w s.flags a v, rip := nach, speicher := s.speicher }

/-- Successor state for a width divide with preserved flags. -/
def wdNachDiv (s : Zustand) (q r : Wort) (nach : Adresse) : Zustand :=
  { register := wdDivRegs s.register q r, flags := s.flags, rip := nach, speicher := s.speicher }

/-- Successor state for a two-operand IMUL. -/
def wdNachImul2 (w : WdBreite) (s : Zustand) (dst src : Register)
    (nach : Adresse) : Zustand :=
  let a := wdLesen w (s.register dst)
  let v := wdLesen w (s.register src)
  { register := wdImul2Regs w s.register dst a v, flags := wdMulFlagsS w s.flags a v, rip := nach, speicher := s.speicher }

/-- Successor state for a three-operand IMUL with its immediate. -/
def wdNachImul3 (w : WdBreite) (s : Zustand) (dst src : Register)
    (imm : Int) (nach : Adresse) : Zustand :=
  let a := wdLesen w (s.register src)
  let vv := wdLesen w (wdImmWort w imm)
  { register := wdImul2Regs w s.register dst a vv, flags := wdMulFlagsS w s.flags a vv, rip := nach, speicher := s.speicher }

/-- Single width step; the divide check is never folded away. -/
def wdSchritt (d : WdDecodiert) (s : Zustand) : MulDivErgebnis :=
  match laengeOk d.laenge with
  | false => .misslungen
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .mul WdBreite.w32 src => .ok (wdNachMul WdBreite.w32 s src nach)
    | .mul WdBreite.w64 src => .ok (wdNachMul WdBreite.w64 s src nach)
    | .divWd WdBreite.w32 src =>
      match divWeitU32 (s.register Register.rdx) (s.register Register.rax)
        (s.register src) with
      | some (q, r) => .ok (wdNachDiv s q r nach)
      | none => .hardwareHalt
    | .divWd WdBreite.w64 src =>
      match divWeitU (s.register Register.rdx) (s.register Register.rax)
        (s.register src) with
      | some (q, r) => .ok (wdNachDiv s q r nach)
      | none => .hardwareHalt
    | .idivWd WdBreite.w32 src =>
      match divWeitS32 (s.register Register.rdx) (s.register Register.rax)
        (s.register src) with
      | some (q, r) => .ok (wdNachDiv s q r nach)
      | none => .hardwareHalt
    | .idivWd WdBreite.w64 src =>
      match divWeitS (s.register Register.rdx) (s.register Register.rax)
        (s.register src) with
      | some (q, r) => .ok (wdNachDiv s q r nach)
      | none => .hardwareHalt
    | .imul2 w dst src => .ok (wdNachImul2 w s dst src nach)
    | .imul3 w dst src imm => .ok (wdNachImul3 w s dst src imm nach)
    | .vor98 w => .ok { (vor98Schritt w s) with rip := nach }
    | .vor99 w => .ok { (vor99Schritt w s) with rip := nach }

/-! ## Step equations for every admitted arm.

    Each equation pins the full successor or the trap; every premise
    is used. Divide checks stay in the step: a `none` quotient is a
    `hardwareHalt` with NO successor (destinations undefined per the
    DIV/IDIV entries, so no register claim is made on that arm). -/

/-- `mul w32`: EDX:EAX holds the 32-bit product, zero-extended. -/
theorem wd_mul32_erfolg (d : WdDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.mul WdBreite.w32 src) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachMul WdBreite.w32 s src (ripNach s.rip d.laenge)) := by
  unfold wdSchritt
  simp [hok, h]

/-- `mul w64` reuses the accepted 64-bit product. -/
theorem wd_mul64_erfolg (d : WdDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.mul WdBreite.w64 src) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachMul WdBreite.w64 s src (ripNach s.rip d.laenge)) := by
  unfold wdSchritt
  simp [hok, h]

/-- `div w32` success: EAX quotient, EDX remainder, flags kept. -/
theorem wd_div32_erfolg (d : WdDecodiert) (s : Zustand) (src : Register)
    (q r : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.divWd WdBreite.w32 src)
    (hqr : divWeitU32 (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r)) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachDiv s q r (ripNach s.rip d.laenge)) := by
  unfold wdSchritt
  simp [hok, h, hqr]

/-- `div w32` trap: undefined quotient halts with no successor. -/
theorem wd_div32_halt (d : WdDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.divWd WdBreite.w32 src)
    (hqr : divWeitU32 (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = none) :
    wdSchritt d s = MulDivErgebnis.hardwareHalt := by
  unfold wdSchritt
  simp [hok, h, hqr]

/-- `div w64` success reuses the accepted wide division. -/
theorem wd_div64_erfolg (d : WdDecodiert) (s : Zustand) (src : Register)
    (q r : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.divWd WdBreite.w64 src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r)) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachDiv s q r (ripNach s.rip d.laenge)) := by
  unfold wdSchritt
  simp [hok, h, hqr]

/-- `div w64` trap. -/
theorem wd_div64_halt (d : WdDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.divWd WdBreite.w64 src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = none) :
    wdSchritt d s = MulDivErgebnis.hardwareHalt := by
  unfold wdSchritt
  simp [hok, h, hqr]

/-- `idiv w32` success: truncated quotient, flags kept. -/
theorem wd_idiv32_erfolg (d : WdDecodiert) (s : Zustand) (src : Register)
    (q r : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.idivWd WdBreite.w32 src)
    (hqr : divWeitS32 (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r)) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachDiv s q r (ripNach s.rip d.laenge)) := by
  unfold wdSchritt
  simp [hok, h, hqr]

/-- `idiv w32` trap: zero divisor or overflow halts. -/
theorem wd_idiv32_halt (d : WdDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.idivWd WdBreite.w32 src)
    (hqr : divWeitS32 (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = none) :
    wdSchritt d s = MulDivErgebnis.hardwareHalt := by
  unfold wdSchritt
  simp [hok, h, hqr]

/-- `idiv w64` success reuses truncation toward zero. -/
theorem wd_idiv64_erfolg (d : WdDecodiert) (s : Zustand) (src : Register)
    (q r : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.idivWd WdBreite.w64 src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r)) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachDiv s q r (ripNach s.rip d.laenge)) := by
  unfold wdSchritt
  simp [hok, h, hqr]

/-- `idiv w64` trap. -/
theorem wd_idiv64_halt (d : WdDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.idivWd WdBreite.w64 src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = none) :
    wdSchritt d s = MulDivErgebnis.hardwareHalt := by
  unfold wdSchritt
  simp [hok, h, hqr]

/-- `imul2` success: truncated product into the destination. -/
theorem wd_imul2_erfolg (d : WdDecodiert) (s : Zustand) (w : WdBreite)
    (dst src : Register) (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.imul2 w dst src) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachImul2 w s dst src (ripNach s.rip d.laenge)) := by
  unfold wdSchritt
  simp [hok, h]

/-- `imul3` success: source times the width immediate, truncated. -/
theorem wd_imul3_erfolg (d : WdDecodiert) (s : Zustand) (w : WdBreite)
    (dst src : Register) (imm : Int) (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.imul3 w dst src imm) :
    wdSchritt d s = MulDivErgebnis.ok
      (wdNachImul3 w s dst src imm (ripNach s.rip d.laenge)) := by
  unfold wdSchritt
  simp [hok, h]

/-- `vor98` success: dividend half prepared, flags preserved. -/
theorem wd_vor98_erfolg (d : WdDecodiert) (s : Zustand) (w : WdBreite)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.vor98 w) :
    wdSchritt d s = MulDivErgebnis.ok
      { register := (vor98Schritt w s).register,
        flags := s.flags, rip := ripNach s.rip d.laenge,
        speicher := s.speicher } := by
  unfold wdSchritt
  simp [hok, h]
  cases w <;> (refine ⟨rfl, rfl⟩)

/-- `vor99` success: high dividend half prepared, flags preserved. -/
theorem wd_vor99_erfolg (d : WdDecodiert) (s : Zustand) (w : WdBreite)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.vor99 w) :
    wdSchritt d s = MulDivErgebnis.ok
      { register := (vor99Schritt w s).register,
        flags := s.flags, rip := ripNach s.rip d.laenge,
        speicher := s.speicher } := by
  unfold wdSchritt
  simp [hok, h]
  cases w <;> (refine ⟨rfl, rfl⟩)

/-- Preparation preserves every flag. -/
theorem wd_vor_flags (d : WdDecodiert) (s s' : Zustand) (w : WdBreite)
    (hok : laengeOk d.laenge = true)
    (h : d.befehl = WdBefehl.vor98 w ∨ d.befehl = WdBefehl.vor99 w)
    (hstep : wdSchritt d s = MulDivErgebnis.ok s') :
    s'.flags = s.flags := by
  cases h with
  | inl h98 =>
    rw [wd_vor98_erfolg d s w hok h98] at hstep
    cases hstep
    rfl
  | inr h99 =>
    rw [wd_vor99_erfolg d s w hok h99] at hstep
    cases hstep
    rfl

/-- A bad decode length refuses every width form. -/
theorem wd_laenge_misslungen (d : WdDecodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) :
    wdSchritt d s = MulDivErgebnis.misslungen := by
  unfold wdSchritt
  simp [h]

/-! ## 4. Canonical bytes and the byte parser.

    Opcodes (txt reference above): Group 3 `F7 /4 /6 /7` (MUL/DIV/
    IDIV; `/5` one-operand IMUL is not admitted and refuses),
    `F6` 8-bit forms refuse (essential OPEN: `Register` has no
    AL/AH/AX sub-registers), two-operand `0F AF /r` (IMUL),
    three-operand `6B /r ib` (imm8) and `69 /r id` (imm32, REX.W
    sign-extends the dword to 64), `98` (CBW/CWDE/CDQE) and `99`
    (CWD/CDQ/CQO). Default width is 32 bits; REX.W promotes to 64.
    The `0x66` prefix (16-bit) refuses everywhere here (essential
    OPEN), `0xF0` (LOCK) refuses (`#UD` per every entry), a doubled
    prefix or REX refuses, and REX.R over Group 3 / REX.X refuse as
    the non-canonical subset (an R bit over the opcode extension
    digit is `#UD` on silicon; X over mod=3 has no SIB to extend).
    REX bits over 98/99 are accepted with width from W only (no
    register operand exists, so nothing observable is hidden). -/

/-- Width from the REX.W bit (1 promotes to 64, else 32). -/
def wdAusBit (b : Nat) : WdBreite :=
  if b == 1 then WdBreite.w64 else WdBreite.w32

/-- Canonical REX for a width form: empty exactly when no bit is
    needed (32-bit over low registers), else W/R/B as required. -/
def wdRex (w : WdBreite) (rh bh : Nat) : List Byte :=
  match w with
  | WdBreite.w32 =>
    if rh == 0 && bh == 0 then [] else [natByte (64 + 4 * rh + bh)]
  | WdBreite.w64 => [natByte (72 + 4 * rh + bh)]

/-- A canonical REX is at most one byte. -/
theorem wdRex_len (w : WdBreite) (rh bh : Nat) :
    (wdRex w rh bh).length ≤ 1 := by
  cases w with
  | w32 =>
    unfold wdRex
    by_cases h : rh == 0 && bh == 0
    · simp [h]
    · simp [h]
  | w64 => simp [wdRex]

/-- REX bits from an optional REX byte: W/R/X/B extension bits. -/
def wdBits (rex : Option Nat) : Nat × Nat × Nat × Nat :=
  match rex with
  | none => (0, 0, 0, 0)
  | some v => let q := v - 64
    (q / 8, q / 4 % 2, q / 2 % 2, q % 2)

/-- Parsed prefix: 16-bit override flag, optional REX byte value and
    the consumed prefix length (0, 1 or 2). -/
structure WdPraefix where
  op16 : Bool
  rex : Option Nat
  n : Nat
  deriving DecidableEq, Repr

/-- Prefix parse after a `0x66` byte: at most one REX follows. -/
def nimmNach66 : List Byte → Option (WdPraefix × List Byte)
  | [] => none
  | b2 :: rest2 =>
    if byteNat b2 == 240 then none
    else if byteNat b2 / 16 == 4 then
      some (⟨true, some (byteNat b2), 2⟩, rest2)
    else some (⟨true, none, 1⟩, b2 :: rest2)

/-- Prefix parse: at most one `0x66` then at most one REX. LOCK
    (`0xF0`) refuses; a lone prefix byte is truncation. Anything
    else consumes no prefix and leaves opcode choice to the next
    layer (an unknown opcode byte then refuses there). Two arms
    only (`[]` vs cons) so canonical round trips reduce over any
    suffix: no canonical encoding starts with `0x66`. -/
def nimmPraefix : List Byte → Option (WdPraefix × List Byte)
  | [] => none
  | b1 :: rest =>
    if byteNat b1 == 240 then none
    else if byteNat b1 == 102 then nimmNach66 rest
    else if byteNat b1 / 16 == 4 then
      some (⟨false, some (byteNat b1), 1⟩, rest)
    else some (⟨false, none, 0⟩, b1 :: rest)

/-- Group-3 ModRM (`F7`, mod=3): `/4` MUL, `/6` DIV, `/7` IDIV over
    the admitted width. `/5` (one-operand IMUL) and every other
    digit refuse; memory modes refuse. -/
def decodeWdF7 (w : WdBreite) (bBit npfx : Nat) :
    List Byte → Option (WdDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then match byteNat m / 8 % 8 with
      | 4 => match codeReg (bBit * 8 + byteNat m % 8) with
        | some src => some (⟨WdBefehl.mul w src, npfx + 2⟩, rest)
        | none => none
      | 6 => match codeReg (bBit * 8 + byteNat m % 8) with
        | some src => some (⟨WdBefehl.divWd w src, npfx + 2⟩, rest)
        | none => none
      | 7 => match codeReg (bBit * 8 + byteNat m % 8) with
        | some src => some (⟨WdBefehl.idivWd w src, npfx + 2⟩, rest)
        | none => none
      | _ => none
    else none

/-- Two-operand IMUL ModRM (`0F AF`, mod=3): reg names the
    destination (REX.R), r/m the source (REX.B). -/
def decodeWdAF (w : WdBreite) (rBit bBit npfx : Nat) :
    List Byte → Option (WdDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeReg (rBit * 8 + byteNat m / 8 % 8),
        codeReg (bBit * 8 + byteNat m % 8) with
      | some dst, some src =>
        some (⟨WdBefehl.imul2 w dst src, npfx + 3⟩, rest)
      | _, _ => none
    else none

/-- Decode after the `0F` escape: the second opcode byte must be
    `AF` (175). -/
def decodeWdNach0F (w : WdBreite) (rBit bBit npfx : Nat) :
    List Byte → Option (WdDecodiert × List Byte)
  | [] => none
  | op2 :: rest =>
    if byteNat op2 == 175 then decodeWdAF w rBit bBit npfx rest
    else none

/-- Immediate tail of `6B`: one signed byte (opcode + ModRM + imm). -/
def decodeWdImm8Tail (w : WdBreite) (dst src : Register) (npfx : Nat) :
    List Byte → Option (WdDecodiert × List Byte)
  | [] => none
  | ib :: rest2 =>
    some (⟨WdBefehl.imul3 w dst src (imm8Erweitert ib), npfx + 3⟩, rest2)

/-- Three-operand IMUL ModRM (`6B`, mod=3) with its imm8 tail. -/
def decodeWd6B (w : WdBreite) (rBit bBit npfx : Nat) :
    List Byte → Option (WdDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeReg (rBit * 8 + byteNat m / 8 % 8),
        codeReg (bBit * 8 + byteNat m % 8) with
      | some dst, some src => decodeWdImm8Tail w dst src npfx rest
      | _, _ => none
    else none

/-- Little-endian dword value of four bytes. -/
def wdU32AusBytes (b0 b1 b2 b3 : Byte) : Nat :=
  byteNat b0 + 256 * (byteNat b1 + 256 * (byteNat b2 + 256 * byteNat b3))

/-- Signed reading of a dword immediate (sign-extended to 64 as the
    same integer for REX.W). -/
def imm32AusNat (n : Nat) : Int :=
  if n < 2 ^ 31 then (n : Int) else (n : Int) - 4294967296

/-- Immediate tail of `69`: four bytes, little-endian
    (opcode + ModRM + dword). -/
def decodeWdImm32Tail (w : WdBreite) (dst src : Register) (npfx : Nat) :
    List Byte → Option (WdDecodiert × List Byte)
  | i0 :: i1 :: i2 :: i3 :: rest =>
    some (⟨WdBefehl.imul3 w dst src
      (imm32AusNat (wdU32AusBytes i0 i1 i2 i3)), npfx + 6⟩, rest)
  | _ => none

/-- Three-operand IMUL ModRM (`69`, mod=3) with its imm32 tail. -/
def decodeWd69 (w : WdBreite) (rBit bBit npfx : Nat) :
    List Byte → Option (WdDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeReg (rBit * 8 + byteNat m / 8 % 8),
        codeReg (bBit * 8 + byteNat m % 8) with
      | some dst, some src => decodeWdImm32Tail w dst src npfx rest
      | _, _ => none
    else none

/-- Opcode dispatch after the prefix: F7/F6/0F/6B/69/98/99. The
    16-bit override refuses everywhere here (essential OPEN); `F6`
    (8-bit) and `/5` refuse inside the Group-3 layer. -/
def decodeWdNachPraefix (op16 : Bool) (wb rb xb bb npfx : Nat) :
    List Byte → Option (WdDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    if op16 then none
    else if byteNat op == 247 then
      if rb == 1 || xb == 1 then none
      else decodeWdF7 (wdAusBit wb) bb npfx rest
    else if byteNat op == 246 then none
    else if byteNat op == 15 then
      if xb == 1 then none
      else decodeWdNach0F (wdAusBit wb) rb bb npfx rest
    else if byteNat op == 107 then
      if xb == 1 then none
      else decodeWd6B (wdAusBit wb) rb bb npfx rest
    else if byteNat op == 105 then
      if xb == 1 then none
      else decodeWd69 (wdAusBit wb) rb bb npfx rest
    else if byteNat op == 152 then
      some (⟨WdBefehl.vor98 (wdAusBit wb), npfx + 1⟩, rest)
    else if byteNat op == 153 then
      some (⟨WdBefehl.vor99 (wdAusBit wb), npfx + 1⟩, rest)
    else none

/-- Full decode: prefix then opcode/ModRM/immediate. The parser reads
    bytes and never compares against encoder output. -/
def decodeWd : List Byte → Option (WdDecodiert × List Byte)
  | [] => none
  | b :: rest =>
    match nimmPraefix (b :: rest) with
    | none => none
    | some (pfx, tail) =>
      let bits := wdBits pfx.rex
      decodeWdNachPraefix pfx.op16 bits.1 bits.2.1 bits.2.2.1
        bits.2.2.2 pfx.n tail

/-- Canonical imm8 byte: low 8 bits of the integer. -/
def wdImm8Byte (imm : Int) : Byte := natByte ((imm.emod 256).toNat)

/-- One little-endian byte of a dword immediate. -/
def wdImm32Byte (k i : Nat) : Byte := natByte ((k / 256 ^ i) % 256)

/-- Canonical imm32 bytes of an integer. -/
def wdImm32Bytes (imm : Int) : List Byte :=
  let k := (imm.emod 4294967296).toNat
  [wdImm32Byte k 0, wdImm32Byte k 1, wdImm32Byte k 2, wdImm32Byte k 3]

/-- Canonical three-operand IMUL bytes: the compact `6B` form exactly
    when the immediate fits int8, else the `69` dword form. -/
def wdEncodeImul3 (w : WdBreite) (dst src : Register) (imm : Int) :
    List Byte :=
  if -128 ≤ imm ∧ imm < 128 then
    wdRex w (regHigh dst) (regHigh src) ++
      [natByte 107, modrmReg (regLow dst) (regLow src), wdImm8Byte imm]
  else
    wdRex w (regHigh dst) (regHigh src) ++
      [natByte 105, modrmReg (regLow dst) (regLow src)] ++ wdImm32Bytes imm

/-- Canonical bytes of one width operation (one encoding per form). -/
def wdEncode : WdBefehl → List Byte
  | WdBefehl.mul w src =>
    wdRex w 0 (regHigh src) ++ [natByte 247, modrmReg 4 (regLow src)]
  | WdBefehl.divWd w src =>
    wdRex w 0 (regHigh src) ++ [natByte 247, modrmReg 6 (regLow src)]
  | WdBefehl.idivWd w src =>
    wdRex w 0 (regHigh src) ++ [natByte 247, modrmReg 7 (regLow src)]
  | WdBefehl.imul2 w dst src =>
    wdRex w (regHigh dst) (regHigh src) ++
      [natByte 15, natByte 175, modrmReg (regLow dst) (regLow src)]
  | WdBefehl.imul3 w dst src imm => wdEncodeImul3 w dst src imm
  | WdBefehl.vor98 w => wdRex w 0 0 ++ [natByte 152]
  | WdBefehl.vor99 w => wdRex w 0 0 ++ [natByte 153]

/-! ## Round trips: decoding inverts encoding.

    Generic over every non-immediate form and any suffix; the two
    immediate forms (`6B`/`69`) share one `imul3` value with a
    form-choosing encoder, so they are pinned on concrete compact
    and dword immediates (a negative byte, a large dword) instead of
    a generic immediate round trip (see CUTS). -/

/-- Round trip for `mul` at either width. -/
theorem wdRoundtrip_mul (w : WdBreite) (src : Register)
    (suffix : List Byte) :
    decodeWd (wdEncode (WdBefehl.mul w src) ++ suffix) =
      some (⟨WdBefehl.mul w src, (wdEncode (WdBefehl.mul w src)).length⟩,
        suffix) := by
  cases w <;> cases src <;> rfl

/-- Round trip for `divWd` at either width. -/
theorem wdRoundtrip_div (w : WdBreite) (src : Register)
    (suffix : List Byte) :
    decodeWd (wdEncode (WdBefehl.divWd w src) ++ suffix) =
      some (⟨WdBefehl.divWd w src, (wdEncode (WdBefehl.divWd w src)).length⟩,
        suffix) := by
  cases w <;> cases src <;> rfl

/-- Round trip for `idivWd` at either width. -/
theorem wdRoundtrip_idiv (w : WdBreite) (src : Register)
    (suffix : List Byte) :
    decodeWd (wdEncode (WdBefehl.idivWd w src) ++ suffix) =
      some (⟨WdBefehl.idivWd w src,
        (wdEncode (WdBefehl.idivWd w src)).length⟩, suffix) := by
  cases w <;> cases src <;> rfl

/-- Round trip for two-operand `imul2` at either width. -/
theorem wdRoundtrip_imul2 (w : WdBreite) (dst src : Register)
    (suffix : List Byte) :
    decodeWd (wdEncode (WdBefehl.imul2 w dst src) ++ suffix) =
      some (⟨WdBefehl.imul2 w dst src,
        (wdEncode (WdBefehl.imul2 w dst src)).length⟩, suffix) := by
  cases w <;> cases dst <;> cases src <;> rfl

/-- Round trip for preparation `98` at either width. -/
theorem wdRoundtrip_vor98 (w : WdBreite) (suffix : List Byte) :
    decodeWd (wdEncode (WdBefehl.vor98 w) ++ suffix) =
      some (⟨WdBefehl.vor98 w, (wdEncode (WdBefehl.vor98 w)).length⟩,
        suffix) := by
  cases w <;> rfl

/-- Round trip for preparation `99` at either width. -/
theorem wdRoundtrip_vor99 (w : WdBreite) (suffix : List Byte) :
    decodeWd (wdEncode (WdBefehl.vor99 w) ++ suffix) =
      some (⟨WdBefehl.vor99 w, (wdEncode (WdBefehl.vor99 w)).length⟩,
        suffix) := by
  cases w <;> rfl

/-! ## Pinned bytes: one canonical encoding per admitted form,
    including the compact immediate, the dword immediate, the
    high-register and the preparation forms. -/

/-- Pinned bytes: 32-bit MUL over ECX (no REX, `F7 /4`). -/
theorem pin_wdmul_ecx :
    wdEncode (WdBefehl.mul WdBreite.w32 Register.rcx) =
      [natByte 247, natByte 225] := by
  decide

/-- Pinned decode: 32-bit MUL over ECX. -/
theorem pin_wdmul_ecx_dekode :
    decodeWd [natByte 247, natByte 225] =
      some ((⟨WdBefehl.mul WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert),
        []) := by
  decide

/-- Pinned bytes: 64-bit MUL over r8 (`REX.W+B, F7 /4`). -/
theorem pin_wdmul_r8 :
    wdEncode (WdBefehl.mul WdBreite.w64 Register.r8) =
      [natByte 73, natByte 247, natByte 224] := by
  decide

/-- Pinned decode: 64-bit MUL over r8. -/
theorem pin_wdmul_r8_dekode :
    decodeWd [natByte 73, natByte 247, natByte 224] =
      some ((⟨WdBefehl.mul WdBreite.w64 Register.r8, 3⟩ : WdDecodiert),
        []) := by
  decide

/-- Pinned bytes: 32-bit DIV over ECX. -/
theorem pin_wddiv_ecx :
    wdEncode (WdBefehl.divWd WdBreite.w32 Register.rcx) =
      [natByte 247, natByte 241] := by
  decide

/-- Pinned decode: 32-bit DIV over ECX. -/
theorem pin_wddiv_ecx_dekode :
    decodeWd [natByte 247, natByte 241] =
      some ((⟨WdBefehl.divWd WdBreite.w32 Register.rcx, 2⟩ : WdDecodiert),
        []) := by
  decide

/-- Pinned bytes: 64-bit IDIV over r11. -/
theorem pin_wdidiv_r11 :
    wdEncode (WdBefehl.idivWd WdBreite.w64 Register.r11) =
      [natByte 73, natByte 247, natByte 251] := by
  decide

/-- Pinned decode: 64-bit IDIV over r11. -/
theorem pin_wdidiv_r11_dekode :
    decodeWd [natByte 73, natByte 247, natByte 251] =
      some ((⟨WdBefehl.idivWd WdBreite.w64 Register.r11, 3⟩ : WdDecodiert),
        []) := by
  decide

/-- Pinned bytes: 64-bit IMUL r9, r15 (`REX.W+R+B, 0F AF`). -/
theorem pin_wdimul2_r9_r15 :
    wdEncode (WdBefehl.imul2 WdBreite.w64 Register.r9 Register.r15) =
      [natByte 77, natByte 15, natByte 175, natByte 207] := by
  decide

/-- Pinned decode: 64-bit IMUL r9, r15. -/
theorem pin_wdimul2_r9_r15_dekode :
    decodeWd [natByte 77, natByte 15, natByte 175, natByte 207] =
      some ((⟨WdBefehl.imul2 WdBreite.w64 Register.r9 Register.r15, 4⟩ :
        WdDecodiert), []) := by
  decide

/-- Pinned bytes: 32-bit compact IMUL r8d, ecx, -3 (`6B /r ib`). -/
theorem pin_wdimul3_kompakt :
    wdEncode (WdBefehl.imul3 WdBreite.w32 Register.r8 Register.rcx (-3)) =
      [natByte 68, natByte 107, natByte 193, natByte 253] := by
  decide

/-- Pinned decode: the compact immediate reads back as -3. -/
theorem pin_wdimul3_kompakt_dekode :
    decodeWd [natByte 68, natByte 107, natByte 193, natByte 253] =
      some ((⟨WdBefehl.imul3 WdBreite.w32 Register.r8 Register.rcx (-3),
        4⟩ : WdDecodiert), []) := by
  decide

/-- Pinned bytes: 64-bit compact IMUL rax, r15, -128. -/
theorem pin_wdimul3_kompakt64 :
    wdEncode (WdBefehl.imul3 WdBreite.w64 Register.rax Register.r15 (-128)) =
      [natByte 73, natByte 107, natByte 199, natByte 128] := by
  decide

/-- Pinned decode: the 64-bit compact immediate reads back as -128. -/
theorem pin_wdimul3_kompakt64_dekode :
    decodeWd [natByte 73, natByte 107, natByte 199, natByte 128] =
      some ((⟨WdBefehl.imul3 WdBreite.w64 Register.rax Register.r15 (-128),
        4⟩ : WdDecodiert), []) := by
  decide

/-- Pinned bytes: 32-bit dword IMUL edx, eax, 100000 (`69 /r id`). -/
theorem pin_wdimul3_wort :
    wdEncode (WdBefehl.imul3 WdBreite.w32 Register.rdx Register.rax 100000) =
      [natByte 105, natByte 208, natByte 160, natByte 134, natByte 1,
        natByte 0] := by
  decide

/-- Pinned decode: the dword immediate reads back as 100000. -/
theorem pin_wdimul3_wort_dekode :
    decodeWd [natByte 105, natByte 208, natByte 160, natByte 134, natByte 1,
      natByte 0] =
      some ((⟨WdBefehl.imul3 WdBreite.w32 Register.rdx Register.rax 100000,
        6⟩ : WdDecodiert), []) := by
  decide

/-- Pinned bytes: 64-bit dword IMUL r9, r8, -70000 (sign-extended). -/
theorem pin_wdimul3_wort64 :
    wdEncode
      (WdBefehl.imul3 WdBreite.w64 Register.r9 Register.r8 (-70000)) =
      [natByte 77, natByte 105, natByte 200, natByte 144, natByte 238,
        natByte 254, natByte 255] := by
  decide

/-- Pinned decode: the 64-bit dword immediate reads back as -70000. -/
theorem pin_wdimul3_wort64_dekode :
    decodeWd [natByte 77, natByte 105, natByte 200, natByte 144, natByte 238,
      natByte 254, natByte 255] =
      some ((⟨WdBefehl.imul3 WdBreite.w64 Register.r9 Register.r8 (-70000),
        7⟩ : WdDecodiert), []) := by
  decide

/-- Pinned bytes: CWDE (bare `98`) and CDQE (`REX.W + 98`). -/
theorem pin_wdvor98 :
    wdEncode (WdBefehl.vor98 WdBreite.w32) = [natByte 152] ∧
      wdEncode (WdBefehl.vor98 WdBreite.w64) =
        [natByte 72, natByte 152] := by
  decide

/-- Pinned decode: CWDE and CDQE. -/
theorem pin_wdvor98_dekode :
    decodeWd [natByte 152] =
      some ((⟨WdBefehl.vor98 WdBreite.w32, 1⟩ : WdDecodiert), []) ∧
      decodeWd [natByte 72, natByte 152] =
        some ((⟨WdBefehl.vor98 WdBreite.w64, 2⟩ : WdDecodiert), []) := by
  decide

/-- Pinned bytes: CDQ (bare `99`) and CQO (`REX.W + 99`). -/
theorem pin_wdvor99 :
    wdEncode (WdBefehl.vor99 WdBreite.w32) = [natByte 153] ∧
      wdEncode (WdBefehl.vor99 WdBreite.w64) =
        [natByte 72, natByte 153] := by
  decide

/-- Pinned decode: CDQ and CQO. -/
theorem pin_wdvor99_dekode :
    decodeWd [natByte 153] =
      some ((⟨WdBefehl.vor99 WdBreite.w32, 1⟩ : WdDecodiert), []) ∧
      decodeWd [natByte 72, natByte 153] =
        some ((⟨WdBefehl.vor99 WdBreite.w64, 2⟩ : WdDecodiert), []) := by
  decide

/-! ## Arbitrary-input length soundness.

    Every successful decode of ANY input consumes exactly its stated
    length within 1..15. Per-layer consumption facts compose into the
    generic statement; decoded lengths always pass `laengeOk`, so
    decoded bytes never carry a bad length into the step. -/

/-- Prefix after `0x66`: the stated count covers the already
    consumed `0x66` byte too, hence the `+ 1`. -/
theorem nimmNach66_len (bs : List Byte) (pfx : WdPraefix)
    (tail : List Byte) (h : nimmNach66 bs = some (pfx, tail)) :
    pfx.n + tail.length = bs.length + 1 ∧ pfx.n ≤ 2 ∧
      pfx.op16 = true := by
  cases bs with
  | nil => simp [nimmNach66] at h
  | cons b2 rest2 =>
    simp only [nimmNach66] at h
    by_cases hf0 : byteNat b2 == 240
    · rw [if_pos hf0] at h
      simp at h
    · rw [if_neg hf0] at h
      by_cases hrx : byteNat b2 / 16 == 4
      · rw [if_pos hrx] at h
        cases h
        dsimp only
        simp only [List.length_cons]
        exact ⟨by omega, by omega, trivial⟩
      · rw [if_neg hrx] at h
        cases h
        dsimp only
        simp only [List.length_cons]
        exact ⟨by omega, by omega, trivial⟩

/-- Prefix length: the stated count plus the tail is the input. -/
theorem nimmPraefix_len (bs : List Byte) (pfx : WdPraefix)
    (tail : List Byte) (h : nimmPraefix bs = some (pfx, tail)) :
    pfx.n + tail.length = bs.length ∧ pfx.n ≤ 2 := by
  cases bs with
  | nil => simp [nimmPraefix] at h
  | cons b1 rest =>
    simp only [nimmPraefix] at h
    by_cases hf0 : byteNat b1 == 240
    · rw [if_pos hf0] at h
      simp at h
    · rw [if_neg hf0] at h
      by_cases h66 : byteNat b1 == 102
      · rw [if_pos h66] at h
        obtain ⟨hlen, hle, _⟩ := nimmNach66_len rest pfx tail h
        refine ⟨?_, hle⟩
        simp only [List.length_cons]
        omega
      · rw [if_neg h66] at h
        by_cases hrx : byteNat b1 / 16 == 4
        · rw [if_pos hrx] at h
          cases h
          dsimp only
          simp only [List.length_cons]
          exact ⟨by omega, by omega⟩
        · rw [if_neg hrx] at h
          cases h
          dsimp only
          simp only [List.length_cons]
          exact ⟨by omega, by omega⟩

/-- Group-3 layer: length `npfx + 2`, one ModRM byte consumed. -/
theorem decodeWdF7_len (w : WdBreite) (bBit npfx : Nat) (bs : List Byte)
    (d : WdDecodiert) (rest : List Byte)
    (h : decodeWdF7 w bBit npfx bs = some (d, rest)) :
    d.laenge = npfx + 2 ∧ rest.length + 1 = bs.length := by
  cases bs with
  | nil => simp [decodeWdF7] at h
  | cons m t =>
    simp only [decodeWdF7] at h
    by_cases hmod : byteNat m / 64 == 3
    · rw [if_pos hmod] at h
      split at h
      · split at h
        · cases h
          exact ⟨rfl, by simp⟩
        · simp at h
      · split at h
        · cases h
          exact ⟨rfl, by simp⟩
        · simp at h
      · split at h
        · cases h
          exact ⟨rfl, by simp⟩
        · simp at h
      · simp at h
    · rw [if_neg hmod] at h
      simp at h

/-- IMUL `0F AF` layer: length `npfx + 3`, one ModRM byte consumed. -/
theorem decodeWdAF_len (w : WdBreite) (rBit bBit npfx : Nat)
    (bs : List Byte) (d : WdDecodiert) (rest : List Byte)
    (h : decodeWdAF w rBit bBit npfx bs = some (d, rest)) :
    d.laenge = npfx + 3 ∧ rest.length + 1 = bs.length := by
  cases bs with
  | nil => simp [decodeWdAF] at h
  | cons m t =>
    simp only [decodeWdAF] at h
    by_cases hmod : byteNat m / 64 == 3
    · rw [if_pos hmod] at h
      split at h
      · cases h
        exact ⟨rfl, by simp⟩
      · simp at h
    · rw [if_neg hmod] at h
      simp at h

/-- `0F` escape layer: length `npfx + 3`, escape plus ModRM consumed. -/
theorem decodeWdNach0F_len (w : WdBreite) (rBit bBit npfx : Nat)
    (bs : List Byte) (d : WdDecodiert) (rest : List Byte)
    (h : decodeWdNach0F w rBit bBit npfx bs = some (d, rest)) :
    d.laenge = npfx + 3 ∧ rest.length + 2 = bs.length := by
  cases bs with
  | nil => simp [decodeWdNach0F] at h
  | cons op2 t =>
    simp only [decodeWdNach0F] at h
    by_cases haf : byteNat op2 == 175
    · rw [if_pos haf] at h
      obtain ⟨hlen, hcon⟩ := decodeWdAF_len w rBit bBit npfx t d rest h
      refine ⟨hlen, ?_⟩
      simp only [List.length_cons]
      omega
    · rw [if_neg haf] at h
      simp at h

/-- `6B` immediate tail: length `npfx + 3`, one imm byte consumed. -/
theorem decodeWdImm8Tail_len (w : WdBreite) (dst src : Register)
    (npfx : Nat) (bs : List Byte) (d : WdDecodiert) (rest : List Byte)
    (h : decodeWdImm8Tail w dst src npfx bs = some (d, rest)) :
    d.laenge = npfx + 3 ∧ rest.length + 1 = bs.length := by
  cases bs with
  | nil => simp [decodeWdImm8Tail] at h
  | cons ib rest2 =>
    simp only [decodeWdImm8Tail] at h
    cases h
    exact ⟨rfl, by simp⟩

/-- `6B` layer: length `npfx + 3`, ModRM plus imm consumed. -/
theorem decodeWd6B_len (w : WdBreite) (rBit bBit npfx : Nat)
    (bs : List Byte) (d : WdDecodiert) (rest : List Byte)
    (h : decodeWd6B w rBit bBit npfx bs = some (d, rest)) :
    d.laenge = npfx + 3 ∧ rest.length + 2 = bs.length := by
  cases bs with
  | nil => simp [decodeWd6B] at h
  | cons m t =>
    simp only [decodeWd6B] at h
    by_cases hmod : byteNat m / 64 == 3
    · rw [if_pos hmod] at h
      split at h
      · obtain ⟨hlen, hcon⟩ :=
          decodeWdImm8Tail_len w _ _ npfx t d rest h
        refine ⟨hlen, ?_⟩
        simp only [List.length_cons]
        omega
      · simp at h
    · rw [if_neg hmod] at h
      simp at h

/-- `69` immediate tail: length `npfx + 6`, four imm bytes consumed. -/
theorem decodeWdImm32Tail_len (w : WdBreite) (dst src : Register)
    (npfx : Nat) (bs : List Byte) (d : WdDecodiert) (rest : List Byte)
    (h : decodeWdImm32Tail w dst src npfx bs = some (d, rest)) :
    d.laenge = npfx + 6 ∧ rest.length + 4 = bs.length := by
  cases bs with
  | nil => simp [decodeWdImm32Tail] at h
  | cons i0 t0 =>
    cases t0 with
    | nil => simp [decodeWdImm32Tail] at h
    | cons i1 t1 =>
      cases t1 with
      | nil => simp [decodeWdImm32Tail] at h
      | cons i2 t2 =>
        cases t2 with
        | nil => simp [decodeWdImm32Tail] at h
        | cons i3 rest3 =>
          simp only [decodeWdImm32Tail] at h
          cases h
          refine ⟨rfl, by simp⟩

/-- `69` layer: length `npfx + 6`, ModRM plus dword consumed. -/
theorem decodeWd69_len (w : WdBreite) (rBit bBit npfx : Nat)
    (bs : List Byte) (d : WdDecodiert) (rest : List Byte)
    (h : decodeWd69 w rBit bBit npfx bs = some (d, rest)) :
    d.laenge = npfx + 6 ∧ rest.length + 5 = bs.length := by
  cases bs with
  | nil => simp [decodeWd69] at h
  | cons m t =>
    simp only [decodeWd69] at h
    by_cases hmod : byteNat m / 64 == 3
    · rw [if_pos hmod] at h
      split at h
      · obtain ⟨hlen, hcon⟩ :=
          decodeWdImm32Tail_len w _ _ npfx t d rest h
        refine ⟨hlen, ?_⟩
        simp only [List.length_cons]
        omega
      · simp at h
    · rw [if_neg hmod] at h
      simp at h

/-- Opcode-dispatch layer: one of `npfx + 1/2/3/6` with the
    matching consumption equation. -/
theorem decodeWdNachPraefix_len (op16 : Bool) (wb rb xb bb npfx : Nat)
    (bs : List Byte) (d : WdDecodiert) (rest : List Byte)
    (h : decodeWdNachPraefix op16 wb rb xb bb npfx bs = some (d, rest)) :
    (d.laenge = npfx + 1 ∨ d.laenge = npfx + 2 ∨ d.laenge = npfx + 3 ∨
      d.laenge = npfx + 6) ∧
      d.laenge + rest.length = bs.length + npfx := by
  cases bs with
  | nil => simp [decodeWdNachPraefix] at h
  | cons op tail2 =>
    simp only [decodeWdNachPraefix] at h
    by_cases hop16 : op16 = true
    · rw [if_pos hop16] at h
      simp at h
    · rw [if_neg hop16] at h
      by_cases h247 : byteNat op == 247
      · rw [if_pos h247] at h
        by_cases hrx : rb == 1 || xb == 1
        · rw [if_pos hrx] at h
          simp at h
        · rw [if_neg hrx] at h
          obtain ⟨hlen, hcon⟩ :=
            decodeWdF7_len (wdAusBit wb) bb npfx tail2 d rest h
          refine ⟨Or.inr (Or.inl hlen), ?_⟩
          simp only [List.length_cons]
          omega
      · rw [if_neg h247] at h
        by_cases hf6 : byteNat op == 246
        · rw [if_pos hf6] at h
          simp at h
        · rw [if_neg hf6] at h
          by_cases h0f : byteNat op == 15
          · rw [if_pos h0f] at h
            by_cases hx0 : xb == 1
            · rw [if_pos hx0] at h
              simp at h
            · rw [if_neg hx0] at h
              obtain ⟨hlen, hcon⟩ :=
                decodeWdNach0F_len (wdAusBit wb) rb bb npfx tail2 d rest h
              refine ⟨Or.inr (Or.inr (Or.inl hlen)), ?_⟩
              simp only [List.length_cons]
              omega
          · rw [if_neg h0f] at h
            by_cases h6b : byteNat op == 107
            · rw [if_pos h6b] at h
              by_cases hx6 : xb == 1
              · rw [if_pos hx6] at h
                simp at h
              · rw [if_neg hx6] at h
                obtain ⟨hlen, hcon⟩ :=
                  decodeWd6B_len (wdAusBit wb) rb bb npfx tail2 d rest h
                refine ⟨Or.inr (Or.inr (Or.inl hlen)), ?_⟩
                simp only [List.length_cons]
                omega
            · rw [if_neg h6b] at h
              by_cases h69 : byteNat op == 105
              · rw [if_pos h69] at h
                by_cases hx9 : xb == 1
                · rw [if_pos hx9] at h
                  simp at h
                · rw [if_neg hx9] at h
                  obtain ⟨hlen, hcon⟩ :=
                    decodeWd69_len (wdAusBit wb) rb bb npfx tail2 d rest h
                  refine ⟨Or.inr (Or.inr (Or.inr hlen)), ?_⟩
                  simp only [List.length_cons]
                  omega
              · rw [if_neg h69] at h
                by_cases h98 : byteNat op == 152
                · rw [if_pos h98] at h
                  cases h
                  refine ⟨Or.inl rfl, ?_⟩
                  simp only [List.length_cons]
                  omega
                · rw [if_neg h98] at h
                  by_cases h99 : byteNat op == 153
                  · rw [if_pos h99] at h
                    cases h
                    refine ⟨Or.inl rfl, ?_⟩
                    simp only [List.length_cons]
                    omega
                  · rw [if_neg h99] at h
                    simp at h

/-- Generic consumed-length soundness: any successful decode of any
    input consumes exactly its stated length within 1..15. -/
theorem decodeWd_len_ok (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (h : decodeWd bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ 1 ≤ d.laenge ∧
      d.laenge ≤ 15 := by
  cases bs with
  | nil => simp [decodeWd] at h
  | cons b tail0 =>
    simp only [decodeWd] at h
    cases hpfx : nimmPraefix (b :: tail0) with
    | none =>
      rw [hpfx] at h
      simp at h
    | some val =>
      obtain ⟨pfx, tail⟩ := val
      obtain ⟨wb, rb, xb, bb, hbits⟩ :
        ∃ wb rb xb bb, wdBits pfx.rex = (wb, rb, xb, bb) :=
        ⟨_, _, _, _, rfl⟩
      rw [hpfx] at h
      simp only at h
      rw [hbits] at h
      simp only at h
      obtain ⟨hlen, hle⟩ := nimmPraefix_len (b :: tail0) pfx tail hpfx
      obtain ⟨hdis, heq⟩ :=
        decodeWdNachPraefix_len pfx.op16 wb rb xb bb pfx.n tail d rest h
      refine ⟨by omega, by omega, by omega⟩

/-- A decoded length is always a valid step length. -/
theorem decodiertWd_laenge_ok (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (h : decodeWd bs = some (d, rest)) :
    laengeOk d.laenge = true := by
  obtain ⟨_, hlo, hhi⟩ := decodeWd_len_ok bs d rest h
  simp only [laengeOk, decide_eq_true_eq]
  omega

/-- Canonical encodings fit the fetch window. -/
theorem wdEncode_len_ok (b : WdBefehl) :
    1 ≤ (wdEncode b).length ∧ (wdEncode b).length ≤ 15 := by
  cases b with
  | mul w src =>
    simp only [wdEncode, List.length_append]
    have hrex := wdRex_len w 0 (regHigh src)
    simp only [List.length_cons, List.length_nil]
    omega
  | divWd w src =>
    simp only [wdEncode, List.length_append]
    have hrex := wdRex_len w 0 (regHigh src)
    simp only [List.length_cons, List.length_nil]
    omega
  | idivWd w src =>
    simp only [wdEncode, List.length_append]
    have hrex := wdRex_len w 0 (regHigh src)
    simp only [List.length_cons, List.length_nil]
    omega
  | imul2 w dst src =>
    simp only [wdEncode, List.length_append]
    have hrex := wdRex_len w (regHigh dst) (regHigh src)
    simp only [List.length_cons, List.length_nil]
    omega
  | imul3 w dst src imm =>
    simp only [wdEncode]
    unfold wdEncodeImul3
    by_cases himm : -128 ≤ imm ∧ imm < 128
    · rw [if_pos himm]
      simp only [List.length_append]
      have hrex := wdRex_len w (regHigh dst) (regHigh src)
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [if_neg himm]
      simp only [List.length_append]
      have hrex := wdRex_len w (regHigh dst) (regHigh src)
      have himm4 : (wdImm32Bytes imm).length = 4 := by
        unfold wdImm32Bytes
        simp
      rw [himm4]
      simp only [List.length_cons, List.length_nil]
      omega
  | vor98 w =>
    simp only [wdEncode, List.length_append]
    have hrex := wdRex_len w 0 0
    simp only [List.length_cons, List.length_nil]
    omega
  | vor99 w =>
    simp only [wdEncode, List.length_append]
    have hrex := wdRex_len w 0 0
    simp only [List.length_cons, List.length_nil]
    omega

/-! ## Decode to execute: decoded bytes step through the width
    semantics with the implicit dividend halves and the divide
    refusal/trap distinction. Aliases resolve from the pre-state
    register file (32-bit reads truncate, writes zero-extend). -/

/-- Decoded `mul w32` steps the 32-bit product. -/
theorem decodeWd_exec_mul32 (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.mul WdBreite.w32 src) :
    wdSchritt d s =
      MulDivErgebnis.ok
        (wdNachMul WdBreite.w32 s src (ripNach s.rip d.laenge)) := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_mul32_erfolg d s src hok h

/-- Decoded `mul w64` steps the accepted 64-bit product. -/
theorem decodeWd_exec_mul64 (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.mul WdBreite.w64 src) :
    wdSchritt d s =
      MulDivErgebnis.ok
        (wdNachMul WdBreite.w64 s src (ripNach s.rip d.laenge)) := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_mul64_erfolg d s src hok h

/-- Decoded `div w32` success steps the 32-bit quotient/remainder. -/
theorem decodeWd_exec_div32_ok (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand) (q r : Wort)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.divWd WdBreite.w32 src)
    (hqr : divWeitU32 (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r)) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachDiv s q r (ripNach s.rip d.laenge)) := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_div32_erfolg d s src q r hok h hqr

/-- Decoded `div w32` trap: undefined quotient halts, never a value. -/
theorem decodeWd_exec_div32_halt (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.divWd WdBreite.w32 src)
    (hqr : divWeitU32 (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = none) :
    wdSchritt d s = MulDivErgebnis.hardwareHalt := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_div32_halt d s src hok h hqr

/-- Decoded `div w64` success. -/
theorem decodeWd_exec_div64_ok (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand) (q r : Wort)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.divWd WdBreite.w64 src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r)) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachDiv s q r (ripNach s.rip d.laenge)) := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_div64_erfolg d s src q r hok h hqr

/-- Decoded `div w64` trap. -/
theorem decodeWd_exec_div64_halt (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.divWd WdBreite.w64 src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = none) :
    wdSchritt d s = MulDivErgebnis.hardwareHalt := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_div64_halt d s src hok h hqr

/-- Decoded `idiv w32` success truncates toward zero. -/
theorem decodeWd_exec_idiv32_ok (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand) (q r : Wort)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.idivWd WdBreite.w32 src)
    (hqr : divWeitS32 (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r)) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachDiv s q r (ripNach s.rip d.laenge)) := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_idiv32_erfolg d s src q r hok h hqr

/-- Decoded `idiv w32` trap. -/
theorem decodeWd_exec_idiv32_halt (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.idivWd WdBreite.w32 src)
    (hqr : divWeitS32 (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = none) :
    wdSchritt d s = MulDivErgebnis.hardwareHalt := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_idiv32_halt d s src hok h hqr

/-- Decoded `idiv w64` success. -/
theorem decodeWd_exec_idiv64_ok (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand) (q r : Wort)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.idivWd WdBreite.w64 src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r)) :
    wdSchritt d s =
      MulDivErgebnis.ok (wdNachDiv s q r (ripNach s.rip d.laenge)) := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_idiv64_erfolg d s src q r hok h hqr

/-- Decoded `idiv w64` trap. -/
theorem decodeWd_exec_idiv64_halt (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (src : Register) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.idivWd WdBreite.w64 src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = none) :
    wdSchritt d s = MulDivErgebnis.hardwareHalt := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_idiv64_halt d s src hok h hqr

/-- Decoded `imul2` steps the truncated product. -/
theorem decodeWd_exec_imul2 (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (w : WdBreite) (dst src : Register) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.imul2 w dst src) :
    wdSchritt d s =
      MulDivErgebnis.ok
        (wdNachImul2 w s dst src (ripNach s.rip d.laenge)) := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_imul2_erfolg d s w dst src hok h

/-- Decoded `imul3` steps source times the width immediate. -/
theorem decodeWd_exec_imul3 (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (w : WdBreite) (dst src : Register) (imm : Int)
    (s : Zustand) (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.imul3 w dst src imm) :
    wdSchritt d s =
      MulDivErgebnis.ok
        (wdNachImul3 w s dst src imm (ripNach s.rip d.laenge)) := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_imul3_erfolg d s w dst src imm hok h

/-- Decoded preparation `98` prepares the dividend half. -/
theorem decodeWd_exec_vor98 (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (w : WdBreite) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.vor98 w) :
    wdSchritt d s =
      MulDivErgebnis.ok
        { register := (vor98Schritt w s).register, flags := s.flags,
          rip := ripNach s.rip d.laenge, speicher := s.speicher } := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_vor98_erfolg d s w hok h

/-- Decoded preparation `99` prepares the high dividend half. -/
theorem decodeWd_exec_vor99 (bs : List Byte) (d : WdDecodiert)
    (rest : List Byte) (w : WdBreite) (s : Zustand)
    (hdec : decodeWd bs = some (d, rest))
    (h : d.befehl = WdBefehl.vor99 w) :
    wdSchritt d s =
      MulDivErgebnis.ok
        { register := (vor99Schritt w s).register, flags := s.flags,
          rip := ripNach s.rip d.laenge, speicher := s.speicher } := by
  have hok := decodiertWd_laenge_ok bs d rest hdec
  exact wd_vor99_erfolg d s w hok h

/-- A faulting width step is never a successor: the manual leaves
    DIV/IDIV destinations undefined, so the halt carries no state
    and no register claim is made on that arm. -/
theorem wd_halt_ist_kein_ok (d : WdDecodiert) (s s' : Zustand)
    (h : wdSchritt d s = MulDivErgebnis.hardwareHalt) :
    wdSchritt d s ≠ MulDivErgebnis.ok s' := by
  rw [h]
  intro hc
  cases hc

/-! ## Fetch from real bytes: permission-checked fetch, decode and
    step from actual executable memory. -/

/-- The fetched window of a state: actual bytes at `rip`,
    executable prefix only, capped at 15. -/
def wdGeholt (s : Zustand) : List Byte :=
  holeFetchAux s.speicher s.rip 0 fetchCap

/-- Fetch and decode: decode the actual fetched bytes, then check
    consumed-length consistency, decode-length validity and execute
    permission of the consumed prefix. -/
def wdFetchDekodiert (s : Zustand) : Option (WdDecodiert × List Byte) :=
  match decodeWd (wdGeholt s) with
  | none => none
  | some (d, rest) =>
    if d.laenge + rest.length == (wdGeholt s).length &&
      laengeOk d.laenge && ausfuehrbarN s.speicher s.rip d.laenge
    then some (d, rest)
    else none

/-- Width byte-step outcome: success, divide trap, or refusal. -/
inductive WdAusgang where
  | weiter : Zustand → WdAusgang
  | halt : WdAusgang
  | verweigert : WdAusgang

/-- One width byte step from actual memory: fetch, decode, then the
    width step. No caller-supplied decoded value becomes trusted. -/
def wdByteschritt (s : Zustand) : WdAusgang :=
  match wdFetchDekodiert s with
  | none => WdAusgang.verweigert
  | some (d, _) =>
    match wdSchritt d s with
    | MulDivErgebnis.ok s' => WdAusgang.weiter s'
    | MulDivErgebnis.hardwareHalt => WdAusgang.halt
    | MulDivErgebnis.misslungen => WdAusgang.verweigert

/-- Register projection of a width byte-step outcome. -/
def wdAusgangReg (r : Register) : WdAusgang → Option Wort
  | WdAusgang.weiter s' => some (s'.register r)
  | _ => none

/-- A fetched step that the width step completes continues. -/
theorem wdByteschritt_weiter (s s' : Zustand) (d : WdDecodiert)
    (rest : List Byte)
    (hfetch : wdFetchDekodiert s = some (d, rest))
    (hstep : wdSchritt d s = MulDivErgebnis.ok s') :
    wdByteschritt s = WdAusgang.weiter s' := by
  have e : wdByteschritt s =
      match wdSchritt d s with
      | MulDivErgebnis.ok s' => WdAusgang.weiter s'
      | MulDivErgebnis.hardwareHalt => WdAusgang.halt
      | MulDivErgebnis.misslungen => WdAusgang.verweigert := by
    unfold wdByteschritt
    rw [hfetch]
  rw [e, hstep]

/-- A fetched step that the width step traps halts. -/
theorem wdByteschritt_halt (s : Zustand) (d : WdDecodiert)
    (rest : List Byte)
    (hfetch : wdFetchDekodiert s = some (d, rest))
    (hstep : wdSchritt d s = MulDivErgebnis.hardwareHalt) :
    wdByteschritt s = WdAusgang.halt := by
  have e : wdByteschritt s =
      match wdSchritt d s with
      | MulDivErgebnis.ok s' => WdAusgang.weiter s'
      | MulDivErgebnis.hardwareHalt => WdAusgang.halt
      | MulDivErgebnis.misslungen => WdAusgang.verweigert := by
    unfold wdByteschritt
    rw [hfetch]
  rw [e, hstep]

/-- Without fetch there is no step: refusal, never a fault claim. -/
theorem wdByteschritt_verweigert_ohne_fetch (s : Zustand)
    (h : wdFetchDekodiert s = none) :
    wdByteschritt s = WdAusgang.verweigert := by
  unfold wdByteschritt
  rw [h]

/-! ## Refusals: malformed, non-canonical and non-admitted inputs.

    Truncation refuses at every prefix length; LOCK, the 16-bit
    override, 8-bit forms, the one-operand IMUL digit, memory modes,
    bad REX bits, doubled prefixes and short immediates all refuse.
    Refusal is a validator verdict, never a fault claim. -/

/-- The empty input decodes to nothing. -/
theorem wd_nichts_leer : decodeWd [] = none := rfl

/-- A lone REX prefix is truncated. -/
theorem wd_nichts_rex_allein : decodeWd [natByte 72] = none := by
  decide

/-- A lone `0x66` is truncated. -/
theorem wd_nichts_66_allein : decodeWd [natByte 102] = none := by
  decide

/-- LOCK refuses: `#UD` on silicon for every form here. -/
theorem wd_nichts_lock :
    decodeWd [natByte 240, natByte 247, natByte 225] = none := by
  decide

/-- The 16-bit override refuses on Group 3 (essential OPEN). -/
theorem wd_nichts_op16_f7 :
    decodeWd [natByte 102, natByte 247, natByte 225] = none := by
  decide

/-- The 16-bit override refuses on the compact immediate. -/
theorem wd_nichts_op16_6b :
    decodeWd [natByte 102, natByte 107, natByte 193, natByte 253] =
      none := by
  decide

/-- The 16-bit override refuses on the dword immediate. -/
theorem wd_nichts_op16_69 :
    decodeWd [natByte 102, natByte 105, natByte 208, natByte 160,
      natByte 134, natByte 1, natByte 0] = none := by
  decide

/-- `F6` 8-bit forms refuse (essential OPEN: no sub-registers). -/
theorem wd_nichts_f6 :
    decodeWd [natByte 246, natByte 225] = none := by
  decide

/-- Extension digit `/5` (one-operand IMUL) is not admitted here. -/
theorem wd_nichts_schlag5 :
    decodeWd [natByte 72, natByte 247, natByte 237] = none := by
  decide

/-- A memory-mode ModRM refuses (register forms only). -/
theorem wd_nichts_speicher_modus :
    decodeWd [natByte 72, natByte 247, natByte 161] = none := by
  decide

/-- REX.R over Group 3 refuses (it would extend the opcode digit). -/
theorem wd_nichts_rex_r_gruppe3 :
    decodeWd [natByte 76, natByte 247, natByte 225] = none := by
  decide

/-- REX.X refuses on the register-only subset. -/
theorem wd_nichts_rex_x :
    decodeWd [natByte 66, natByte 247, natByte 225] = none := by
  decide

/-- A doubled REX refuses. -/
theorem wd_nichts_doppelt_rex :
    decodeWd [natByte 72, natByte 72, natByte 247, natByte 225] =
      none := by
  decide

/-- A wrong second opcode byte after `0F` refuses. -/
theorem wd_nichts_zweitop_falsch :
    decodeWd [natByte 72, natByte 15, natByte 174, natByte 193] =
      none := by
  decide

/-- The compact form without its immediate byte is truncated. -/
theorem wd_nichts_6b_imm_fehlt :
    decodeWd [natByte 68, natByte 107, natByte 193] = none := by
  decide

/-- The dword form with one of four immediate bytes is truncated. -/
theorem wd_nichts_69_imm_kurz :
    decodeWd [natByte 105, natByte 208, natByte 160] = none := by
  decide

/-! ## Execution probes: computed values through real steps.

    Witness states reuse the canonical witness memory and flags.
    Step results project to plain values before `decide` (states
    contain functions); the general equations already pin the full
    states. -/

/-- Witness registers for compact `7 * -3`: r8 scratched, ecx `7`. -/
def wdRegA : Register → Wort := fun q =>
  if q = Register.r8 then 100
  else if q = Register.rcx then 7
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the compact immediate probe. -/
def wdZustandA : Zustand :=
  { register := wdRegA, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness registers for `r15 * -3` with r15 = `-7`. -/
def wdRegB : Register → Wort := fun q =>
  if q = Register.r9 then 0
  else if q = Register.r15 then BitVec.ofNat 64 (2 ^ 64 - 7)
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the high-register 64-bit compact probe. -/
def wdZustandB : Zustand :=
  { register := wdRegB, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness registers for 32-bit `-7 / 2`: sign-extended dividend. -/
def wdRegC : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 (2 ^ 32 - 7)
  else if q = Register.rdx then BitVec.ofNat 64 (2 ^ 32 - 1)
  else if q = Register.rcx then 2
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the negative 32-bit division. -/
def wdZustandC : Zustand :=
  { register := wdRegC, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness registers for 32-bit `17 / 5`. -/
def wdRegD : Register → Wort := fun q =>
  if q = Register.rax then 17
  else if q = Register.rdx then 0
  else if q = Register.rcx then 5
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the positive 32-bit division. -/
def wdZustandD : Zustand :=
  { register := wdRegD, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness registers for 64-bit `INT_MIN / -1`. -/
def wdRegMin : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 (2 ^ 63)
  else if q = Register.rdx then BitVec.ofNat 64 (2 ^ 64 - 1)
  else if q = Register.rcx then BitVec.ofNat 64 (2 ^ 64 - 1)
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for the overflowing 64-bit division. -/
def wdZustandMin : Zustand :=
  { register := wdRegMin, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness state for 32-bit `17 * 5` through EDX:EAX. -/
def wdZustandMul32 : Zustand :=
  { register := wdRegD, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Step projection: one register plus CF of an `ok` outcome. -/
def wdOkReg (r : Register) : MulDivErgebnis → Option (Wort × Bool)
  | MulDivErgebnis.ok z => some (z.register r, z.flags.cf)
  | _ => none

/-- Compact probe: `7 * -3` lands r8d = `-21`, no carry. -/
theorem probe_wd_imul3_kompakt :
    wdOkReg Register.r8
      (wdSchritt
        ⟨WdBefehl.imul3 WdBreite.w32 Register.r8 Register.rcx (-3), 4⟩
        wdZustandA) =
      some (0xFFFFFFEB, false) := by
  decide

/-- High-register probe: `r15 * -3` with r15 = `-7` lands 21. -/
theorem probe_wd_imul3_hoch :
    wdOkReg Register.r9
      (wdSchritt
        ⟨WdBefehl.imul3 WdBreite.w64 Register.r9 Register.r15 (-3), 4⟩
        wdZustandB) =
      some (21, false) := by
  decide

/-- Negative 32-bit division truncates: `-7 / 2` lands EAX = `-3`,
    EDX = `-1`, flags kept (never floor). -/
theorem probe_wd_idiv32_negativ :
    okWerte
      (wdSchritt ⟨WdBefehl.idivWd WdBreite.w32 Register.rcx, 2⟩
        wdZustandC) =
      some (0xFFFFFFFD, 0xFFFFFFFF, false) := by
  decide

/-- Positive 32-bit division: `17 / 5` lands EAX = `3`, EDX = `2`. -/
theorem probe_wd_div32 :
    okWerte
      (wdSchritt ⟨WdBefehl.divWd WdBreite.w32 Register.rcx, 2⟩
        wdZustandD) =
      some (3, 2, false) := by
  decide

/-- 32-bit MUL probe: `17 * 5` lands EAX = `85`, EDX = `0`. -/
theorem probe_wd_mul32 :
    okWerte
      (wdSchritt ⟨WdBefehl.mul WdBreite.w32 Register.rcx, 2⟩
        wdZustandMul32) =
      some (85, 0, false) := by
  decide

/-- 64-bit overflow traps: `INT_MIN / -1` halts. -/
theorem probe_wd_idiv64_min_halt :
    istHalt
      (wdSchritt ⟨WdBefehl.idivWd WdBreite.w64 Register.rcx, 3⟩
        wdZustandMin) = true := by
  decide

/-- CWDE probe: AX = `0x8000` sign-extends EAX to `0xFFFF8000`. -/
theorem probe_wd_vor98_cwde :
    wdOkReg Register.rax
      (wdSchritt ⟨WdBefehl.vor98 WdBreite.w32, 1⟩
        { wdZustandA with
          register := fun q =>
            if q = Register.rax then 0xFFFFFFFFFFFF8000
            else wdRegA q }) =
      some (0xFFFF8000, false) := by
  decide

/-- CDQE probe: EAX = `0x80000000` sign-extends RAX fully. -/
theorem probe_wd_vor98_cdqe :
    wdOkReg Register.rax
      (wdSchritt ⟨WdBefehl.vor98 WdBreite.w64, 2⟩
        { wdZustandA with
          register := fun q =>
            if q = Register.rax then 0x0000000080000000
            else wdRegA q }) =
      some (0xFFFFFFFF80000000, false) := by
  decide

/-- CDQ probe: negative EAX fills EDX with ones (zero-extended). -/
theorem probe_wd_vor99_cdq :
    wdOkReg Register.rdx
      (wdSchritt ⟨WdBefehl.vor99 WdBreite.w32, 1⟩
        { wdZustandA with
          register := fun q =>
            if q = Register.rax then 0x0000000080000000
            else wdRegA q }) =
      some (0xFFFFFFFF, false) := by
  decide

/-- CQO probe: negative RAX fills RDX with ones. -/
theorem probe_wd_vor99_cqo :
    wdOkReg Register.rdx
      (wdSchritt ⟨WdBefehl.vor99 WdBreite.w64, 2⟩
        { wdZustandA with
          register := fun q =>
            if q = Register.rax then 0x8000000000000000
            else wdRegA q }) =
      some (0xFFFFFFFFFFFFFFFF, false) := by
  decide

/-! ## Fetched run: compact bytes execute from real RAM. -/

/-- Four code bytes holding the compact `6B` form at 4096. -/
def wdBildBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 68
  else if a.toNat = 4097 then natByte 107
  else if a.toNat = 4098 then natByte 193
  else if a.toNat = 4099 then natByte 253
  else BitVec.ofNat 8 0

/-- Image memory: the four compact bytes executable, writable data. -/
def wdBild : Speicher :=
  { bytes := wdBildBytes, lesbar := fun _ => false,
    schreibbar := zeugeWahr,
    ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4100) }

/-- Fetched start state over the compact image. -/
def wdBildStart : Zustand :=
  { register := wdRegA, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := wdBild }

/-- Fetch decodes the actual compact bytes with consumed length 4. -/
theorem probe_wd_geholt_fetch :
    wdFetchDekodiert wdBildStart =
      some ((⟨WdBefehl.imul3 WdBreite.w32 Register.r8 Register.rcx (-3),
        4⟩ : WdDecodiert), []) := by
  decide

/-- End to end: fetched compact bytes step r8d to `-21` in RAM. -/
theorem probe_wd_bytesschritt :
    wdAusgangReg Register.r8 (wdByteschritt wdBildStart) =
      some 0xFFFFFFEB := by
  decide

/-! ## Joint witness: decoded bytes, execution, memory and refusals.

    The canonical compact bytes decode and step to `-21` through the
    reused width execution; the high-register 64-bit compact step and
    the negative 32-bit division compute; the computed product goes
    through real permission-checked memory with an observable change;
    the overflowing division traps; LOCK, the wrong width and the
    short immediate refuse. The generic length and admission facts
    are instantiated on the same bytes. -/

/-- Witness memory: the compact product `-21` (as u32) at address 0. -/
def wdSpeicherProdukt : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 0xFFFFFFEB }

/-- JOINT WITNESS over decoded bytes, execution, memory and refusal. -/
theorem wd_zeuge_gemeinsam :
    decodeWd [natByte 68, natByte 107, natByte 193, natByte 253] =
        some ((⟨WdBefehl.imul3 WdBreite.w32 Register.r8 Register.rcx (-3),
          4⟩ : WdDecodiert), []) ∧
      wdOkReg Register.r9
        (wdSchritt
          ⟨WdBefehl.imul3 WdBreite.w64 Register.r9 Register.r15 (-3), 4⟩
          wdZustandB) =
        some (21, false) ∧
      okWerte
        (wdSchritt ⟨WdBefehl.idivWd WdBreite.w32 Register.rcx, 2⟩
          wdZustandC) =
        some (0xFFFFFFFD, 0xFFFFFFFF, false) ∧
      (∃ m1 : Speicher,
        write64 zeugenSpeicher 0 0xFFFFFFEB = some m1 ∧
        read64 m1 0 = some 0xFFFFFFEB ∧
        zeugenSpeicher.bytes 0 ≠ m1.bytes 0) ∧
      istHalt
        (wdSchritt ⟨WdBefehl.idivWd WdBreite.w64 Register.rcx, 3⟩
          wdZustandMin) = true ∧
      laengeOk 2 = true ∧
      decodeWd [natByte 240, natByte 247, natByte 225] = none ∧
      decodeWd [natByte 102, natByte 247, natByte 225] = none ∧
      decodeWd [natByte 105, natByte 208, natByte 160] = none := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, ?_, by decide,
    by decide, by decide⟩
  · refine ⟨wdSpeicherProdukt, ?_, ?_, ?_⟩
    · have hwr : write64 zeugenSpeicher 0 0xFFFFFFEB =
        some wdSpeicherProdukt := by
        unfold write64
        have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
        rw [if_pos hc]
        rfl
      exact hwr
    · have hwr : write64 zeugenSpeicher 0 0xFFFFFFEB =
        some wdSpeicherProdukt := by
        unfold write64
        have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
        rw [if_pos hc]
        rfl
      have hrd : lesbar8 zeugenSpeicher 0 = true := rfl
      exact read64_nach_write64 zeugenSpeicher _ 0 0xFFFFFFEB hwr hrd
    · have hhit := writeBytesN_hit zeugenSpeicher 0 0xFFFFFFEB
        8 0 (by decide) (by decide)
      rw [addrOff_null (0 : Adresse)] at hhit
      show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 0xFFFFFFEB 0
      unfold writeBytes
      rw [hhit]
      decide
  · exact decodiertWd_laenge_ok _ _ _ pin_wdmul_ecx_dekode

/- CUTS:
    Proved here: admitted 32/64-bit MUL/DIV/IDIV with EDX:EAX and
    RDX:RAX dividends (implicit halves from the pre-state, 32-bit
    reads truncate and writes zero-extend), two/three-operand IMUL
    with signed imm8/imm32 compact forms (6B/69, REX.W sign-extends
    the dword), dividend preparation CBW-refused/CWDE/CDQE and
    CWD-refused/CDQ/CQO (0x98/0x99 with width/REX effects, flags
    preserved), CF/OF multiplication effects with the width validity
    relations (other flags kept as the explicit undefined modelling
    choice), signed truncation toward zero with quotient/remainder,
    #DE on divisor zero and quotient overflow (halt carries no state,
    so destinations stay undefined and no register claim is made),
    canonical one-encoding-per-form bytes, an independent byte
    parser (never encode-equality), per-form and generic round trips
    for the non-immediate forms, pinned compact/dword immediates
    (negative byte, int8 minimum, large dword, negative dword),
    generic arbitrary-input consumed-length soundness with valid
    decoded lengths, generic decode-to-execute correspondence for
    all twelve arms, guard-free trap agreement (a `none` quotient is
    the halt), fetch from actual executable memory with the byte
    step, frame facts (preparation keeps flags, divide keeps flags),
    planted malformed-byte/fault/width/overlap refusals, probed
    compact/high-register/negative-division/preparation values and
    the joint decode/execute/memory/refusal witness
    `wd_zeuge_gemeinsam`.
    Manual provenance: Intel SDM 325462-093US Sep 2026, instruction
    reference text, local snapshot `.tmp/HARDWARE-REFERENCES/`:
    MUL opcode/operation/flags (txt lines 70674-70770, Table 1-1),
    IMUL forms/operation/flags (txt lines 58200-58360), DIV
    opcode/operation/flags (txt lines 50157-50300, Table 1-11),
    IDIV opcode/operation/flags (txt lines 58043-58200, Table 1-47),
    CBW/CWDE/CDQE (txt lines 44283-44340), CWD/CDQ/CQO (txt lines
    49874-49930), exception vectors Table 6-1 (txt lines 9641-9671).
    NOT proved here, and not claimed:
    - No 8/16-bit multiply/divide (`F6`, `0x66`-prefixed `F7`,
      `0F AF`, `6B`, `69`) and no 16-bit preparation (`CBW`, `CWD`):
      refused as essential OPEN. The obstruction is the register
      vocabulary: `Register` has no AL/AH/AX/DX sub-registers and no
      partial-write merge, so 8/16-bit forms have no carrier here.
    - No one-operand IMUL (`F7 /5`): refused; not an essential
      performance form for the admitted profile (covered neither
      here nor by `MulDivCodec`).
    - No memory-operand MUL/DIV/IDIV/IMUL (mod ≠ 3 refuses): address
      computation, segmentation and the memory fault order stay with
      the access lanes.
    - No generic immediate round trip: the form-choosing encoder
      (`6B` iff int8) is pinned on four concrete immediates; the
      bounded generic statement stays OPEN.
    - No hardware correspondence: encodings, the overflow rules, the
      truncation direction and the flag relations are stated
      canonical semantics, checked against the cited manual entries,
      not verified against silicon.
    - No fault delivery, priority, paging disambiguation, TSO bridge,
      source correspondence, cost or time transfer (see the module
      header and the step CUTS of `MulDiv.lean`/`MulDivCodec.lean`).
    - No new hardware or software assumptions and no checker rule: no
      diagnostic, poison-probe, example or CLI numbers are taken.
-/

#print axioms WdBreite.bits
#print axioms divWeitU32
#print axioms divWeitS32
#print axioms wdMulFlagsU_gueltig
#print axioms wdMulFlagsS_gueltig
#print axioms wd_mul32_erfolg
#print axioms wd_mul64_erfolg
#print axioms wd_div32_erfolg
#print axioms wd_div32_halt
#print axioms wd_div64_erfolg
#print axioms wd_div64_halt
#print axioms wd_idiv32_erfolg
#print axioms wd_idiv32_halt
#print axioms wd_idiv64_erfolg
#print axioms wd_idiv64_halt
#print axioms wd_imul2_erfolg
#print axioms wd_imul3_erfolg
#print axioms wd_vor98_erfolg
#print axioms wd_vor99_erfolg
#print axioms wd_vor_flags
#print axioms wd_laenge_misslungen
#print axioms wdRex_len
#print axioms wdRoundtrip_mul
#print axioms wdRoundtrip_div
#print axioms wdRoundtrip_idiv
#print axioms wdRoundtrip_imul2
#print axioms wdRoundtrip_vor98
#print axioms wdRoundtrip_vor99
#print axioms decodeWd_len_ok
#print axioms decodiertWd_laenge_ok
#print axioms wdEncode_len_ok
#print axioms decodeWd_exec_mul32
#print axioms decodeWd_exec_imul3
#print axioms decodeWd_exec_idiv32_ok
#print axioms decodeWd_exec_vor98
#print axioms wdByteschritt_weiter
#print axioms wdByteschritt_halt
#print axioms wd_halt_ist_kein_ok
#print axioms probe_wd_imul3_kompakt
#print axioms probe_wd_bytesschritt
#print axioms wd_zeuge_gemeinsam

end Gabbro.Grammatik.X86
