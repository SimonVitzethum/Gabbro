/-
  File:      Grammatik/X86/ShiftCodec.lean
  Subject:   Canonical byte codec and execution connection for 64-bit
    register shift forms (lane 564).

  Connects the accepted `ShiftLogic` value operations (`shlB`/`shrB`/
  `sarB` at `.b64`, `SchiebeNachweis`/`SchiebeGueltig`) to a bounded
  canonical byte decoder/encoder for two 64-bit register-direct forms:
  shift-by-immediate-8 (`REX.W C1 /r ib`) and shift-by-CL
  (`REX.W D3 /r`). Only the rows admitted here count as connected;
  hardware correspondence of the rows is NOT claimed (see CUTS).
-/
import Grammatik.X86.ShiftLogic
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- The three shift directions with a canonical byte row in this file. -/
inductive ShiftRichtung where
  | shl | shr | sar
  deriving DecidableEq, Repr

/-- Group-2 ModRM extension digit: SHL is /4, SHR is /5, SAR is /7. -/
def richtungFeld : ShiftRichtung → Nat
  | .shl => 4 | .shr => 5 | .sar => 7

/-- 64-bit register-direct shift forms with a canonical encoding below:
    immediate-8 (`REX.W C1 /r ib`) or CL (`REX.W D3 /r`). -/
inductive ShiftForm where
  | imm (r : ShiftRichtung) (dst : Register) (imm8 : Nat)
  | cl (r : ShiftRichtung) (dst : Register)
  deriving DecidableEq, Repr

/-! ## 1. Canonical encoding and decoded length.

    `REX.W` carries only the B extension bit (R must be 0: REX.R would
    rewrite the Group-2 extension digit into an unadmitted row, so
    prefixes 76/77 never encode here). ModRM is register-direct
    (mod = 3) with the direction digit in the reg field. -/

/-- Canonical byte encoding of one 64-bit register shift form. -/
def encodeShift : ShiftForm → List Byte
  | .imm r dst n =>
    [rexByte 0 (regHigh dst), natByte 193,
     natByte (192 + 8 * richtungFeld r + regLow dst), natByte n]
  | .cl r dst =>
    [rexByte 0 (regHigh dst), natByte 211,
     natByte (192 + 8 * richtungFeld r + regLow dst)]

/-- Decoded length of one shift form: 4 with the immediate byte, 3
    with the CL form. -/
def shiftLaenge : ShiftForm → Nat
  | .imm _ _ _ => 4
  | .cl _ _ => 3

/-- The encoding is exactly the decoded length. -/
theorem encodeShift_laenge (f : ShiftForm) :
    (encodeShift f).length = shiftLaenge f := by
  cases f <;> rfl

/-- Every shift encoding fits the 1..15 instruction bound. -/
theorem encodeShift_len_ok (f : ShiftForm) :
    1 ≤ (encodeShift f).length ∧ (encodeShift f).length ≤ 15 := by
  cases f with
  | imm r dst n => exact show 1 ≤ 4 ∧ 4 ≤ 15 from by decide
  | cl r dst => exact show 1 ≤ 3 ∧ 3 ≤ 15 from by decide

/-- The decoded length passes the pilot length guard. -/
theorem shiftLaenge_ok (f : ShiftForm) :
    laengeOk (shiftLaenge f) = true := by
  cases f <;> rfl

/-! ## 2. Canonical decoder.

    The decoder parses bytes, never encode-equality. Only REX.W rows
    with R = 0 are admitted (72/73); REX.R rows would rewrite the
    Group-2 extension digit and are refused, as are register-indirect
    ModRM modes and extension digits outside /4, /5, /7. -/

/-- Direction back from a Group-2 extension digit. -/
def feldRichtung : Nat → Option ShiftRichtung
  | 4 => some .shl | 5 => some .shr | 7 => some .sar
  | _ => none

/-- Decoding inverts encoding on every direction digit. -/
theorem feldRichtung_richtungFeld (r : ShiftRichtung) :
    feldRichtung (richtungFeld r) = some r := by
  cases r <;> rfl

/-- Decode one register-direct ModRM byte after an admitted REX
    prefix and group opcode: mod must be 3, the reg field a shift
    digit. Returns the direction, the destination and the rest. -/
def decodeShiftModrm (bBit : Nat) : List Byte →
    Option (ShiftRichtung × Register × List Byte)
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match feldRichtung (byteNat m / 8 % 8),
          codeReg (bBit * 8 + byteNat m % 8) with
      | some r, some dst => some (r, dst, rest)
      | _, _ => none
    else none
  | [] => none

/-- Decode after an admitted REX prefix: opcode 193 is the immediate
    form, 211 the CL form; anything else is refused with `none`
    WITHOUT touching later bytes, so pilot rows refuse independently
    of their operands. -/
def decodeShiftOp (bBit op : Nat) : List Byte → Option (ShiftForm × List Byte)
  | rest =>
    if op == 193 then
      match decodeShiftModrm bBit rest with
      | some (r, dst, i :: rest') => some ((.imm r dst (byteNat i)), rest')
      | _ => none
    else if op == 211 then
      match decodeShiftModrm bBit rest with
      | some (r, dst, rest') => some ((.cl r dst), rest')
      | _ => none
    else none

/-- Decode the first canonical shift row: an admitted REX.W prefix,
    then the group opcode, then ModRM (plus the immediate byte). The
    first byte alone discriminates non-shift rows, so a one-byte pilot
    row refuses without touching the suffix. -/
def decodeShift : List Byte → Option (ShiftForm × List Byte)
  | r :: rest =>
    if byteNat r == 72 then
      match rest with
      | op :: rest' => decodeShiftOp 0 (byteNat op) rest'
      | [] => none
    else if byteNat r == 73 then
      match rest with
      | op :: rest' => decodeShiftOp 1 (byteNat op) rest'
      | [] => none
    else none
  | [] => none

/-! ## 3. Round trips: decoding inverts encoding with the suffix.

    The immediate form needs `n < 256` (one byte carries the count);
    the premise is discharged by the byte round trip itself. -/

/-- Round trip for the immediate form, over any suffix. -/
theorem roundtripShiftImm (r : ShiftRichtung) (dst : Register) (n : Nat)
    (h : n < 256) (suffix : List Byte) :
    decodeShift (encodeShift (.imm r dst n) ++ suffix) =
      some ((.imm r dst n), suffix) := by
  cases r <;> cases dst <;>
    simp [encodeShift, decodeShift, decodeShiftOp, decodeShiftModrm,
      rexByte, regHigh,
      regLow, regCode, richtungFeld, feldRichtung, codeReg,
      (byteNat_natByte_of_lt n h)]

/-- Round trip for the CL form, over any suffix. -/
theorem roundtripShiftCl (r : ShiftRichtung) (dst : Register)
    (suffix : List Byte) :
    decodeShift (encodeShift (.cl r dst) ++ suffix) =
      some ((.cl r dst), suffix) := by
  cases r <;> cases dst <;>
    simp [encodeShift, decodeShift, decodeShiftOp, decodeShiftModrm,
      rexByte, regHigh,
      regLow, regCode, richtungFeld, feldRichtung, codeReg]

/-- A successful immediate round trip consumes exactly its decoded
    length, within 1..15. -/
theorem roundtripShiftImm_len_ok (r : ShiftRichtung) (dst : Register)
    (n : Nat) (h : n < 256) (suffix : List Byte) :
    decodeShift (encodeShift (.imm r dst n) ++ suffix) =
        some ((.imm r dst n), suffix) ∧
      shiftLaenge (.imm r dst n) + suffix.length =
        (encodeShift (.imm r dst n) ++ suffix).length ∧
      1 ≤ shiftLaenge (.imm r dst n) ∧
      shiftLaenge (.imm r dst n) ≤ 15 := by
  refine ⟨roundtripShiftImm r dst n h suffix, ?_, ?_, ?_⟩
  · rw [List.length_append, encodeShift_laenge]
  · exact show 1 ≤ 4 from by decide
  · exact show 4 ≤ 15 from by decide

/-- A successful CL round trip consumes exactly its decoded length,
    within 1..15. -/
theorem roundtripShiftCl_len_ok (r : ShiftRichtung) (dst : Register)
    (suffix : List Byte) :
    decodeShift (encodeShift (.cl r dst) ++ suffix) =
        some ((.cl r dst), suffix) ∧
      shiftLaenge (.cl r dst) + suffix.length =
        (encodeShift (.cl r dst) ++ suffix).length ∧
      1 ≤ shiftLaenge (.cl r dst) ∧
      shiftLaenge (.cl r dst) ≤ 15 := by
  refine ⟨roundtripShiftCl r dst suffix, ?_, ?_, ?_⟩
  · rw [List.length_append, encodeShift_laenge]
  · exact show 1 ≤ 3 from by decide
  · exact show 3 ≤ 15 from by decide

/-! ## 4. Execution connection.

    Values reuse the accepted `ShiftLogic` operations at `.b64`; flag
    evidence reuses `SchiebeNachweis`/`SchiebeGueltig`. A masked count
    of zero preserves flags (hardware updates nothing there, and §2 of
    `ShiftLogic` claims no snapshot for it); only nonzero counts
    install the evidence snapshot. Memory is never touched. -/

/-- Direction as accepted `ShiftLogic` dispatch tag. -/
def richtungOp : ShiftRichtung → ShiftOp
  | .shl => .shl | .shr => .shr | .sar => .sar

/-- Value dispatch at full width: the reused canonical operations. -/
def richtungWert : ShiftRichtung → Wort → Nat → Wort
  | .shl, x, c => shlB .b64 x c
  | .shr, x, c => shrB .b64 x c
  | .sar, x, c => sarB .b64 x c

/-- The value routes to the accepted `ShiftLogic` dispatch. -/
theorem richtungWert_routen (r : ShiftRichtung) (x : Wort) (c : Nat) :
    richtungWert r x c =
      shiftOpWert (richtungOp r) .b64 x 0 c := by
  cases r <;> rfl

/-- Raw shift count of a form in a state: the immediate byte, or the
    low CL byte (`rcx` modulo 256, masked to six bits later by
    `schiebeZaehler`). -/
def shiftZaehler : ShiftForm → Zustand → Nat
  | .imm _ _ n, _ => n
  | .cl _ _, s => (s.register .rcx).toNat % 256

/-- Evidence dispatch: the reused per-direction `SchiebeNachweis`. -/
def richtungNachweis : ShiftRichtung → Wort → Nat → SchiebeNachweis
  | .shl, x, c => shlNachweis .b64 x c
  | .shr, x, c => shrNachweis .b64 x c
  | .sar, x, c => sarNachweis .b64 x c

/-- Defined evidence of a form in a state. -/
def shiftNachweis (f : ShiftForm) (s : Zustand) : SchiebeNachweis :=
  match f with
  | .imm r dst n => richtungNachweis r (s.register dst) n
  | .cl r dst =>
    richtungNachweis r (s.register dst) ((s.register .rcx).toNat % 256)

/-- Flag snapshot from defined evidence: carry out, undefined
    auxiliary, width-correct result flags, overflow exactly where the
    evidence defines it (`none` becomes cleared, never invented). -/
def shiftFlags (n : SchiebeNachweis) : Flags :=
  { cf := n.trag, pf := parityEven n.ergebnis, af := none,
    zf := zfTest n.ergebnis, sf := negB .b64 n.ergebnis,
    of := n.ueberlauf.getD false }

/-- Destination register of a form. -/
def shiftDst : ShiftForm → Register
  | .imm _ dst _ => dst
  | .cl _ dst => dst

/-- A decoded shift instruction: the form with its consumed length,
    checked against `shiftLaenge` at step time. -/
structure ShiftDecodiert where
  befehl : ShiftForm
  laenge : Nat
  deriving DecidableEq, Repr

/-- One shift step: refuse on length mismatch; on a zero masked count
    advance RIP with flags untouched; otherwise write the routed value
    with the evidence snapshot, reusing `schrittRegister`/`ripNach`. -/
def shiftSchritt (d : ShiftDecodiert) (s : Zustand) : Option Zustand :=
  if d.laenge == shiftLaenge d.befehl then
    let c := shiftZaehler d.befehl s
    let n := shiftNachweis d.befehl s
    let nach := ripNach s.rip d.laenge
    if schiebeZaehler .b64 c == 0 then
      some ({ s with rip := nach })
    else
      some (schrittRegister s nach (shiftFlags n) (shiftDst d.befehl)
        n.ergebnis)
  else none

/-! ## 5. Prefix dispatch: no collision with the pilot decoder.

    Neither decoder is rewritten: the pilot `decode` refuses every
    shift row (its REX dispatch admits no group opcode 193/211), and
    `decodeShift` refuses every pilot row (no pilot row starts with an
    admitted REX followed by a group opcode). -/

/-- The pilot decoder refuses every shift row, over any suffix. -/
theorem pilot_verweigert_shift (f : ShiftForm) (suffix : List Byte) :
    decode (encodeShift f ++ suffix) = none := by
  cases f with
  | imm r dst n => cases dst <;> rfl
  | cl r dst => cases dst <;> rfl

/-- The shift decoder refuses every pilot row, over any suffix. -/
theorem shift_verweigert_pilot (b : Befehl) (suffix : List Byte) :
    decodeShift (encode b ++ suffix) = none := by
  cases b with
  | movImm64 dst v => cases dst <;> rfl
  | movReg64 dst src => cases dst <;> cases src <;> rfl
  | addReg64 dst src => cases dst <;> cases src <;> rfl
  | subReg64 dst src => cases dst <;> cases src <;> rfl
  | xorReg64 dst src => cases dst <;> cases src <;> rfl
  | cmpReg64 lhs rhs => cases lhs <;> cases rhs <;> rfl
  | load64 dst base d => cases dst <;> cases base <;> rfl
  | store64 base src d => cases base <;> cases src <;> rfl
  | jump32 d => rfl
  | jumpIf32 c d => cases c <;> rfl
  | call32 d => rfl
  | push64 src => cases src <;> rfl
  | pop64 dst => cases dst <;> rfl
  | ret => rfl

/-- The evidence snapshot satisfies the accepted validity relation:
    overflow is pinned exactly for a masked count of one and left
    unconstrained otherwise (never invented). -/
theorem shiftFlags_gueltig (r : ShiftRichtung) (x : Wort) (c : Nat) :
    SchiebeGueltig .b64 (richtungNachweis r x c) c
      (shiftFlags (richtungNachweis r x c)) := by
  cases r with
  | shl =>
    unfold SchiebeGueltig richtungNachweis shiftFlags
    simp only [shlNachweis]
    refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
    · intro h1
      simp [shlUeberlauf, h1]
    · intro hn
      simp [shlUeberlauf] at hn
      exact hn
  | shr =>
    unfold SchiebeGueltig richtungNachweis shiftFlags
    simp only [shrNachweis]
    refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
    · intro h1
      simp [shrUeberlauf, h1]
    · intro hn
      simp [shrUeberlauf] at hn
      exact hn
  | sar =>
    unfold SchiebeGueltig richtungNachweis shiftFlags
    simp only [sarNachweis]
    refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
    · intro h1
      simp [sarUeberlauf, h1]
    · intro hn
      simp [sarUeberlauf] at hn
      exact hn

/-- Length mismatch refuses: the consumed length is checked data. -/
theorem shiftSchritt_laenge (d : ShiftDecodiert) (s : Zustand)
    (h : d.laenge ≠ shiftLaenge d.befehl) :
    shiftSchritt d s = none := by
  unfold shiftSchritt
  rw [if_neg (by simpa [beq_iff_eq] using h)]

/-- Zero masked count: RIP advances, flags and registers untouched. -/
theorem shiftSchritt_null (d : ShiftDecodiert) (s : Zustand)
    (h : d.laenge == shiftLaenge d.befehl)
    (h0 : schiebeZaehler .b64 (shiftZaehler d.befehl s) == 0) :
    shiftSchritt d s = some ({ s with rip := ripNach s.rip d.laenge }) := by
  unfold shiftSchritt
  rw [if_pos h, if_pos h0]

/-- Nonzero masked count: the routed value with the evidence snapshot. -/
theorem shiftSchritt_weiter (d : ShiftDecodiert) (s : Zustand)
    (h : d.laenge == shiftLaenge d.befehl)
    (h0 : schiebeZaehler .b64 (shiftZaehler d.befehl s) ≠ 0) :
    shiftSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (shiftFlags (shiftNachweis d.befehl s)) (shiftDst d.befehl)
        (shiftNachweis d.befehl s).ergebnis) := by
  unfold shiftSchritt
  rw [if_pos h, if_neg (by simpa [beq_iff_eq] using h0)]

/-- A successful shift step never touches memory. -/
theorem shiftSchritt_speicher (d : ShiftDecodiert) (s s' : Zustand)
    (h : shiftSchritt d s = some s') : s'.speicher = s.speicher := by
  unfold shiftSchritt at h
  by_cases hl : d.laenge == shiftLaenge d.befehl
  · rw [if_pos hl] at h
    by_cases h0 : schiebeZaehler .b64 (shiftZaehler d.befehl s) == 0
    · rw [if_pos h0] at h
      cases h
      rfl
    · rw [if_neg h0] at h
      cases h
      rfl
  · rw [if_neg hl] at h
    cases h

/-- A successful shift step advances RIP past the decoded length. -/
theorem shiftSchritt_rip (d : ShiftDecodiert) (s s' : Zustand)
    (h : shiftSchritt d s = some s') :
    s'.rip = ripNach s.rip d.laenge := by
  unfold shiftSchritt at h
  by_cases hl : d.laenge == shiftLaenge d.befehl
  · rw [if_pos hl] at h
    by_cases h0 : schiebeZaehler .b64 (shiftZaehler d.befehl s) == 0
    · rw [if_pos h0] at h
      cases h
      rfl
    · rw [if_neg h0] at h
      cases h
      rfl
  · rw [if_neg hl] at h
    cases h

/-- A successful shift step keeps every other register. -/
theorem shiftSchritt_fremd (d : ShiftDecodiert) (s s' : Zustand)
    (h : shiftSchritt d s = some s') (q : Register)
    (hq : q ≠ shiftDst d.befehl) :
    s'.register q = s.register q := by
  unfold shiftSchritt at h
  by_cases hl : d.laenge == shiftLaenge d.befehl
  · rw [if_pos hl] at h
    by_cases h0 : schiebeZaehler .b64 (shiftZaehler d.befehl s) == 0
    · rw [if_pos h0] at h
      cases h
      rfl
    · rw [if_neg h0] at h
      cases h
      exact regSet_fremd s.register (shiftDst d.befehl) q _ hq
  · rw [if_neg hl] at h
    cases h

/-- A successful shift step passed the length check. -/
theorem shiftSchritt_laenge_eq (d : ShiftDecodiert) (s s' : Zustand)
    (h : shiftSchritt d s = some s') :
    ((d.laenge == shiftLaenge d.befehl) = true) := by
  unfold shiftSchritt at h
  by_cases hl : (d.laenge == shiftLaenge d.befehl) = true
  · exact hl
  · rw [if_neg hl] at h
    cases h

/-- On a nonzero masked count the result carries the evidence flags. -/
theorem shiftSchritt_flags (d : ShiftDecodiert) (s s' : Zustand)
    (h : shiftSchritt d s = some s')
    (h0 : schiebeZaehler .b64 (shiftZaehler d.befehl s) ≠ 0) :
    s'.flags = shiftFlags (shiftNachweis d.befehl s) := by
  have heq := shiftSchritt_weiter d s (shiftSchritt_laenge_eq d s s' h) h0
  rw [heq] at h
  cases h
  rfl

/-- On a zero masked count flags are preserved (no snapshot
    installed, as `ShiftLogic` §2 requires). -/
theorem shiftSchritt_null_flags (d : ShiftDecodiert) (s s' : Zustand)
    (h : shiftSchritt d s = some s')
    (h0 : schiebeZaehler .b64 (shiftZaehler d.befehl s) == 0) :
    s'.flags = s.flags := by
  have heq := shiftSchritt_null d s
    (shiftSchritt_laenge_eq d s s' h) h0
  rw [heq] at h
  cases h
  rfl

/-- On a nonzero masked count the destination holds the evidence value. -/
theorem shiftSchritt_wert (d : ShiftDecodiert) (s s' : Zustand)
    (h : shiftSchritt d s = some s')
    (h0 : schiebeZaehler .b64 (shiftZaehler d.befehl s) ≠ 0) :
    s'.register (shiftDst d.befehl) =
      (shiftNachweis d.befehl s).ergebnis := by
  have heq := shiftSchritt_weiter d s
    (shiftSchritt_laenge_eq d s s' h) h0
  rw [heq] at h
  cases h
  exact regSet_gleich s.register (shiftDst d.befehl) _

/-- The installed snapshot satisfies the accepted validity relation
    against the masked count: overflow pinned exactly at count one. -/
theorem shiftSchritt_nachweis_gueltig (d : ShiftDecodiert) (s s' : Zustand)
    (h : shiftSchritt d s = some s')
    (c : Nat) (hc : c = shiftZaehler d.befehl s)
    (h0 : schiebeZaehler .b64 c ≠ 0) :
    SchiebeGueltig .b64 (shiftNachweis d.befehl s) c s'.flags := by
  have hfl : s'.flags = shiftFlags (shiftNachweis d.befehl s) :=
    shiftSchritt_flags d s s' h (by rw [← hc]; exact h0)
  cases df : d.befehl with
  | imm r dst n =>
    rw [df] at hc
    have hdf : shiftNachweis (ShiftForm.imm r dst n) s =
        richtungNachweis r (s.register dst) n := rfl
    rw [hfl, df, hdf, hc]
    exact shiftFlags_gueltig r (s.register dst) n
  | cl r dst =>
    rw [df] at hc
    have hdf : shiftNachweis (ShiftForm.cl r dst) s =
        richtungNachweis r (s.register dst)
          ((s.register .rcx).toNat % 256) := rfl
    rw [hfl, df, hdf, hc]
    exact shiftFlags_gueltig r (s.register dst)
      ((s.register .rcx).toNat % 256)

/-! ## 6. Pins and probes: bytes, counts, mutations, truncations. -/

/-- Pinned bytes: `shl rax, 1` is REX.W, C1, E0, 01. -/
theorem pin_shift_imm_rax :
    encodeShift (.imm .shl .rax 1) =
      [natByte 72, natByte 193, natByte 224, natByte 1] := by
  decide

/-- Pinned decode: `shl rax, 1`. -/
theorem pin_shift_imm_rax_dekode :
    decodeShift [natByte 72, natByte 193, natByte 224, natByte 1] =
      some (((.imm .shl .rax 1) : ShiftForm), []) := by
  decide

/-- Pinned bytes: `shr r9, 65` carries the B extension bit. -/
theorem pin_shift_imm_r9 :
    encodeShift (.imm .shr .r9 65) =
      [natByte 73, natByte 193, natByte 233, natByte 65] := by
  decide

/-- Pinned decode: `shr r9, 65`. -/
theorem pin_shift_imm_r9_dekode :
    decodeShift [natByte 73, natByte 193, natByte 233, natByte 65] =
      some (((.imm .shr .r9 65) : ShiftForm), []) := by
  decide

/-- Pinned bytes: `sar rcx, cl` is REX.W, D3, F9. -/
theorem pin_shift_cl_rcx :
    encodeShift (.cl .sar .rcx) =
      [natByte 72, natByte 211, natByte 249] := by
  decide

/-- Pinned decode: `sar rcx, cl`. -/
theorem pin_shift_cl_rcx_dekode :
    decodeShift [natByte 72, natByte 211, natByte 249] =
      some (((.cl .sar .rcx) : ShiftForm), []) := by
  decide

/-- Count 0 through the form: raw and masked counts vanish. -/
theorem probe_zaehler_null (s : Zustand) :
    shiftZaehler (.imm .shl .rax 0) s = 0 ∧
    schiebeZaehler .b64 (shiftZaehler (.imm .shl .rax 0) s) = 0 :=
  ⟨rfl, rfl⟩

/-- Count 1 through the form: the overflow-defining count. -/
theorem probe_zaehler_eins (s : Zustand) :
    shiftZaehler (.imm .shr .rax 1) s = 1 ∧
    schiebeZaehler .b64 (shiftZaehler (.imm .shr .rax 1) s) = 1 ∧
    shrUeberlauf .b64 0x8000000000000000 1 = some true :=
  ⟨rfl, rfl, by decide⟩

/-- A large count through bytes: immediate 65 masks to 1 and the
    value follows the masked count. -/
theorem probe_gross_ueber_byte :
    decodeShift [natByte 72, natByte 193, natByte 224, natByte 65] =
        some (((.imm .shl .rax 65) : ShiftForm), []) ∧
      schiebeZaehler .b64 65 = 1 ∧ shlB .b64 1 65 = 2 := by
  decide

/-- Value pins at count 1: no masking, plain shifts. -/
theorem probe_schiebe_werte :
    shlB .b64 1 1 = 2 ∧ shrB .b64 8 1 = 4 ∧
    sarB .b64 (BitVec.ofNat 64 (2 ^ 64 - 3)) 1 =
      BitVec.ofNat 64 (2 ^ 64 - 2) := by
  decide

/-- Truncated rows refuse: empty, lone REX, opcode without ModRM,
    ModRM without the immediate byte, CL form without ModRM. -/
theorem sonde_abgeschnitten :
    decodeShift [] = none ∧
    decodeShift [natByte 72] = none ∧
    decodeShift [natByte 72, natByte 193] = none ∧
    decodeShift [natByte 72, natByte 193, natByte 224] = none ∧
    decodeShift [natByte 72, natByte 211] = none := by
  decide

/-- Mutated rows refuse or change meaning, never silently keep it: a
    REX.R prefix, a /0 digit and a mod-2 ModRM refuse; flipping the
    opcode turns the immediate form into the CL form (the immediate
    byte becomes trailing suffix); flipping the digit turns SHL into
    SHR. -/
theorem sonde_mutation :
    decodeShift [natByte 76, natByte 193, natByte 224, natByte 1] =
        none ∧
      decodeShift [natByte 72, natByte 193, natByte 192, natByte 1] =
        none ∧
      decodeShift [natByte 72, natByte 193, natByte 160, natByte 1] =
        none ∧
      decodeShift [natByte 72, natByte 211, natByte 224, natByte 1] =
        some (((.cl .shl .rax) : ShiftForm), [natByte 1]) ∧
      decodeShift [natByte 72, natByte 193, natByte 232, natByte 1] =
        some (((.imm .shr .rax 1) : ShiftForm), []) := by
  decide

/-- A wrong consumed length refuses on any state. -/
theorem probe_laenge_falsch (s : Zustand) :
    shiftSchritt ⟨.imm .shl .rax 1, 3⟩ s = none :=
  shiftSchritt_laenge _ s (by decide)

/-! ## 7. Joint witness: decoded shift feeding a memory store.

    `shl rax, 1` (4 bytes) followed by the pilot `store [rbx], rax`
    (7 bytes) in actual code memory: the decoded form steps `rax`
    from 1 to 2, and the existing `schritt` stores the shifted value
    into the data cell, observably changing its byte. -/

/-- Witness program: shift bytes then the pilot store bytes. -/
def shiftKetteProg : List Byte :=
  [natByte 72, natByte 193, natByte 224, natByte 1,
   natByte 72, natByte 137, natByte 131,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- Program bytes over addresses from 4096; zero elsewhere. -/
def shiftKetteBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else shiftKetteProg.getD (a.toNat - 4096) (BitVec.ofNat 8 0)

/-- Code window executable: 4096..4128. -/
def shiftKetteExec (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4128)

/-- Data cell readable and writable: 8192..8200. -/
def shiftKetteDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness registers: `rax` holds 1, `rbx` the data cell. -/
def shiftKetteReg : Register → Wort := fun q =>
  if q = Register.rax then 1
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness flags: nothing set. -/
def shiftZeugenFlags : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false,
    of := false }

/-- Witness start state: shift program at 4096, data cell at 8192. -/
def shiftKetteStart : Zustand :=
  { register := shiftKetteReg
    flags := shiftZeugenFlags
    rip := BitVec.ofNat 64 4096
    speicher :=
      { bytes := shiftKetteBytes
        lesbar := shiftKetteDaten
        schreibbar := shiftKetteDaten
        ausfuehrbar := shiftKetteExec } }

/-- The two-step end state: shift, then the pilot store of `rax`. -/
def shiftKetteEnde : Option Zustand :=
  (shiftSchritt ⟨.imm .shl .rax 1, 4⟩ shiftKetteStart).bind
    (schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩)

/-- The executed bytes decode to the stepped form. -/
theorem shift_kette_dekode :
    decodeShift shiftKetteProg =
      some (((.imm .shl .rax 1) : ShiftForm),
        shiftKetteProg.drop 4) := by
  decide

/-- The shift step moves 1 to 2, advances past its 4 bytes and leaves
    carry cleared (bit 63 of 1 is no carry out). -/
theorem shift_kette_schritt :
    (shiftSchritt ⟨.imm .shl .rax 1, 4⟩ shiftKetteStart).map
        (fun s => s.register .rax) = some 2 ∧
      (shiftSchritt ⟨.imm .shl .rax 1, 4⟩ shiftKetteStart).map
        (fun s => s.rip) = some (BitVec.ofNat 64 4100) ∧
      (shiftSchritt ⟨.imm .shl .rax 1, 4⟩ shiftKetteStart).map
        (fun s => s.flags.cf) = some false := by
  decide

/-- The shifted value reaches memory: the data cell reads 2 and its
    byte observably changed from zero; a wrong consumed length on the
    same bytes refuses. -/
theorem shift_kette_speicher :
    shiftKetteEnde.map (fun s =>
        read64 s.speicher (BitVec.ofNat 64 8192)) =
        some (some 2) ∧
      shiftKetteEnde.map (fun s =>
        s.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (natByte 2) ∧
      shiftKetteStart.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      shiftSchritt ⟨.imm .shl .rax 1, 5⟩ shiftKetteStart = none := by
  decide

/- CUTS:
    Proved here: canonical byte encoding of the 64-bit register-direct
    immediate and CL shift forms (`encodeShift`, lengths 4/3 within
    1..15), a byte-parsing decoder (`decodeShift` over admitted REX.W
    rows 72/73, group opcodes 193/211, mod-3 ModRM with digits /4 /5
    /7), generic round trips with decoded-length/suffix consistency,
    two-sided prefix dispatch against the pilot decoder without
    rewriting it, value/evidence reuse of the accepted `ShiftLogic`
    operations (`richtungWert`, `shiftNachweis`, `shiftFlags` with
    `SchiebeGueltig`, overflow pinned exactly at masked count one),
    a length-checked step (`shiftSchritt`) that preserves flags on a
    zero masked count and otherwise installs the evidence snapshot
    while never touching memory, count-0/1/large pins, byte
    mutation/truncation probes, and a joint witness chaining a decoded
    shift into a pilot store with an observably changed data byte.
    NOT proved here, and not claimed:
    - No hardware correspondence: the rows are self-consistent
      canonical bytes, not verified against silicon; the architectural
      mapping of opcodes/digits/flags is assumed open.
    - No source correspondence, no TSO bridge, no whole-image
      coverage, no cost transfer, no entry/ABI/relocation claim.
    - Narrow widths, memory-operand shifts, rotates and multi-bit
      flag subtleties beyond the reused `SchiebeGueltig` stay open.
    - `verweigert`-style termination claims are untouched; refusal here
      is explicit `none`.
-/

#print axioms richtungFeld
#print axioms richtungWert_routen
#print axioms roundtripShiftImm
#print axioms roundtripShiftCl
#print axioms roundtripShiftImm_len_ok
#print axioms roundtripShiftCl_len_ok
#print axioms pilot_verweigert_shift
#print axioms shift_verweigert_pilot
#print axioms shiftFlags_gueltig
#print axioms shiftSchritt_laenge
#print axioms shiftSchritt_null
#print axioms shiftSchritt_weiter
#print axioms shiftSchritt_speicher
#print axioms shiftSchritt_rip
#print axioms shiftSchritt_fremd
#print axioms shiftSchritt_flags
#print axioms shiftSchritt_null_flags
#print axioms shiftSchritt_wert
#print axioms shiftSchritt_nachweis_gueltig
#print axioms probe_gross_ueber_byte
#print axioms sonde_mutation
#print axioms sonde_abgeschnitten
#print axioms shift_kette_dekode
#print axioms shift_kette_schritt
#print axioms shift_kette_speicher

end Gabbro.Grammatik.X86
