/-
  File:      Grammatik/X86/CompactImm8Add.lean
  Subject:   Canonical byte codec and execution connection for the compact
    64-bit ADD with sign-extended imm8 (lane 748).

  Covers exactly one row: `REX.W + 83 /0 ib`, ADD r64, imm8, register-direct
  (ModRM mod = 3, extension digit /0). Provenance: Intel SDM combined
  volumes 1-4, edition 325462-093US (September 2026), local snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`, Vol. 2A 3-14
  "ADD-Add": opcode table "REX.W + 83 /0 ib  ADD r/m64, imm8 ... Add
  sign-extended imm8 to r/m64"; Description "When an immediate value is used
  as an operand, it is sign-extended to the length of the destination
  operand format"; Operation "DEST := DEST + SRC"; Flags Affected "The OF,
  SF, ZF, AF, CF, and PF flags are set according to the result."

  Scope: register destination only (r/m64 with a register; memory forms,
  16/32-bit 83 rows, the 81 imm32 row and the 05/04 accumulator rows stay
  open and refuse here). Value and flags reuse the canonical `Wort`
  vocabulary (`sext`, `trunc`, `cfAdd`, `ofAdd`, `zfTest`, `sfTest`,
  `parityEven`) and the accepted `add64` identities; AF is modelled as
  undefined (`none`), never invented -- a deliberate conservative gap
  against the manual, booked in CUTS. No new word/register/state types, no
  `Befehl` change, no second evaluator of the pilot ADD: at 64 bits the
  value and every defined flag ARE the accepted `add64` ones.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.ShiftLogic

namespace Gabbro.Grammatik.X86

/-- Sign-extended imm8 as a full word: the low byte sign-extended through
    the canonical `sext .b8` (Vol. 2A 3-14 Description: the immediate "is
    sign-extended to the length of the destination operand format"). -/
def immSext (n : Nat) : Wort := sext .b8 (BitVec.ofNat 64 n)

/-- Pin: the largest positive imm8 stays positive. -/
theorem pin_immSext_7f : immSext 127 = 127 := by
  decide

/-- Pin: the smallest negative imm8 fills with ones. -/
theorem pin_immSext_80 : immSext 128 = 0xFFFFFFFFFFFFFF80 := by
  decide

/-- Pin: imm8 -1 (0xFF) fills the whole word. -/
theorem pin_immSext_ff : immSext 255 = 0xFFFFFFFFFFFFFFFF := by
  decide

/-- Pin: imm8 zero extends to zero. -/
theorem pin_immSext_00 : immSext 0 = 0 := by
  decide

/-! ## Width-generic value and flags.

  The REX.W row runs at `.b64`; the helpers take the width explicitly so
  the per-width CF/OF/SF/ZF/PF shape is stated once (Vol. 2A 3-14
  Operation "DEST := DEST + SRC" with the immediate sign-extended).
  Carry and overflow read the truncated operands at the named width;
  SF is the width-correct `negB b` (bit 63 alone misclassifies narrow
  results). AF is `none` at every width: undefined is left undefined,
  never invented (the manual lists AF among the affected flags; leaving
  it `none` is the deliberate conservative gap booked in CUTS). -/

/-- Width-generic ADD-with-imm8 value: truncated operands added, result
    truncated to the named width. -/
def addImmOp (b : Breite) (x : Wort) (n : Nat) : Wort :=
  trunc b (trunc b x + immSext n)

/-- Width-generic ADD-with-imm8 flags: CF/OF/SF/ZF/PF from the canonical
    tests at the named width, AF always `none`. -/
def addImmFlags (b : Breite) (x : Wort) (n : Nat) : Flags :=
  let r := addImmOp b x n
  { cf := decide ((trunc b x).toNat + (trunc b (immSext n)).toNat ≥ 2 ^ b.bits)
    pf := parityEven r, af := none, zf := zfTest r, sf := negB b r,
    of := ofAdd (negB b (trunc b x)) (negB b (trunc b (immSext n)))
      (negB b r) }

/-! ## Per-width identities: AF stays none, 64-bit value is plain addition. -/

/-- AF stays `none` at every width: undefined, never invented. -/
theorem addImmFlags_af (b : Breite) (x : Wort) (n : Nat) :
    (addImmFlags b x n).af = none := rfl

/-- At 64 bits the value is the plain modular sum with the
    sign-extended immediate: no truncation, no second evaluator. -/
theorem addImmOp_b64 (x : Wort) (n : Nat) :
    addImmOp .b64 x n = x + immSext n := by
  simp [addImmOp, trunc_b64]

/-! ## 64-bit flag identities: every defined flag IS the accepted
  `add64` flag on the sign-extended immediate. -/

/-- CF identity: the carry out is the accepted unsigned carry. -/
theorem addImmFlags_cf (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).cf = (add64 x (immSext n)).2.cf := by
  simp [addImmFlags, addImmOp, add64, cfAdd, trunc_b64, Breite.bits]

/-- OF identity: the signed overflow is the accepted one. -/
theorem addImmFlags_of (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).of = (add64 x (immSext n)).2.of := by
  simp [addImmFlags, addImmOp, add64, ofAdd, trunc_b64, negB_b64]

/-- SF identity: the sign is the accepted top-bit test. -/
theorem addImmFlags_sf (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).sf = (add64 x (immSext n)).2.sf := by
  simp [addImmFlags, addImmOp, add64, trunc_b64, negB_b64]

/-- ZF identity: zero is the accepted zero test. -/
theorem addImmFlags_zf (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).zf = (add64 x (immSext n)).2.zf := by
  simp [addImmFlags, addImmOp, add64, trunc_b64]

/-- PF identity: parity is the accepted even-parity test. -/
theorem addImmFlags_pf (x : Wort) (n : Nat) :
    (addImmFlags .b64 x n).pf = (add64 x (immSext n)).2.pf := by
  simp [addImmFlags, addImmOp, add64, trunc_b64]

/-! ## Canonical codec: exactly the REX.W 83 /0 ib register row.

  Bytes (Vol. 2A 3-14 opcode table "REX.W + 83 /0 ib"): REX.W with only
  the B extension bit (72/73; REX.R would rewrite the /0 extension digit
  into an unadmitted row, so 76/77 refuse), opcode 131, ModRM
  register-direct (mod = 3) with the /0 digit in the reg field, then the
  imm8 byte. Length 4. The encoder takes the immediate as a `Nat` and
  refuses anything outside a byte (`none`): no silent truncation. -/

/-- The one covered compact form: ADD r64, imm8 with the immediate as
    an unbounded `Nat` (range-checked at encode time). -/
inductive CompactAddForm where
  | addImm8 (dst : Register) (imm : Nat)
  deriving DecidableEq, Repr

/-- Canonical byte encoding of the covered row, or `none` outside i8. -/
def encodeCompactAdd : CompactAddForm → Option (List Byte)
  | .addImm8 dst n =>
    if n < 256 then
      some [rexByte 0 (regHigh dst), natByte 131,
        natByte (192 + regLow dst), natByte n]
    else none

/-- Decoded length of the covered row: 4. -/
def compactAddLaenge : CompactAddForm → Nat
  | .addImm8 _ _ => 4

/-- The covered row fits the 1..15 instruction bound. -/
theorem compactAddLaenge_ok (f : CompactAddForm) :
    laengeOk (compactAddLaenge f) = true := by
  cases f <;> rfl

/-- Decode after an admitted REX prefix: opcode 131 is the compact ADD;
    ModRM must be register-direct (mod = 3) with the /0 extension digit
    in the reg field. Anything else refuses with `none` WITHOUT touching
    later bytes. -/
def decodeCompactAddOp (bBit op : Nat) :
    List Byte → Option (CompactAddForm × List Byte)
  | rest =>
    if op == 131 then
      match rest with
      | m :: i :: rest' =>
        if byteNat m / 64 == 3 && byteNat m / 8 % 8 == 0 then
          match codeReg (bBit * 8 + byteNat m % 8) with
          | some dst => some ((.addImm8 dst (byteNat i)), rest')
          | none => none
        else none
      | _ => none
    else none

/-- Decode the covered row: an admitted REX.W prefix (72/73, R = 0 so
    the /0 digit is untouched), then opcode 131, ModRM and imm8. -/
def decodeCompactAdd : List Byte → Option (CompactAddForm × List Byte)
  | r :: rest =>
    if byteNat r == 72 then
      match rest with
      | op :: rest' => decodeCompactAddOp 0 (byteNat op) rest'
      | [] => none
    else if byteNat r == 73 then
      match rest with
      | op :: rest' => decodeCompactAddOp 1 (byteNat op) rest'
      | [] => none
    else none
  | [] => none

/-! ## Round trip: decoding inverts encoding with the suffix.

  The immediate form needs `n < 256` (one byte carries it); the same
  premise is discharged by the byte round trip itself. -/

/-- Round trip over any suffix: the four canonical bytes decode back to
    the form with the immediate intact. -/
theorem roundtripCompactAdd (dst : Register) (n : Nat) (h : n < 256)
    (suffix : List Byte) :
    decodeCompactAdd ([rexByte 0 (regHigh dst), natByte 131,
      natByte (192 + regLow dst), natByte n] ++ suffix) =
      some ((.addImm8 dst n), suffix) := by
  cases dst <;>
    simp [decodeCompactAdd, decodeCompactAddOp, rexByte, regHigh,
      regLow, regCode, codeReg, (byteNat_natByte_of_lt n h)]

/-! ## Encoder range: inside i8 four bytes, outside i8 refusal. -/

/-- Inside i8 the encoder answers with exactly the four canonical bytes. -/
theorem encodeCompactAdd_some (dst : Register) (n : Nat) (h : n < 256) :
    encodeCompactAdd (.addImm8 dst n) =
      some [rexByte 0 (regHigh dst), natByte 131,
        natByte (192 + regLow dst), natByte n] := by
  simp [encodeCompactAdd, h]

/-- Outside i8 the encoder refuses: no silent truncation into a byte. -/
theorem encodeCompactAdd_verweigert (dst : Register) (n : Nat)
    (h : 256 ≤ n) :
    encodeCompactAdd (.addImm8 dst n) = none := by
  simp [encodeCompactAdd, Nat.not_lt.mpr h]

/-- Refusal cause: `none` means the immediate is outside i8. -/
theorem encodeCompactAdd_ursache (dst : Register) (n : Nat)
    (h : encodeCompactAdd (.addImm8 dst n) = none) : 256 ≤ n := by
  by_cases h' : n < 256
  · exfalso
    rw [encodeCompactAdd_some dst n h'] at h
    simp at h
  · exact Nat.le_of_not_lt h'

/-! ## Pinned bytes. -/

/-- Pinned bytes: `ADD rax, 5` is REX.W, 83, C0, 05. -/
theorem pin_addImm_rax_5 :
    encodeCompactAdd (.addImm8 .rax 5) =
      some [natByte 72, natByte 131, natByte 192, natByte 5] := by
  decide

/-- Pinned decode: `ADD rax, 5`. -/
theorem pin_addImm_rax_5_dekode :
    decodeCompactAdd [natByte 72, natByte 131, natByte 192, natByte 5] =
      some (((.addImm8 .rax 5) : CompactAddForm), []) := by
  decide

/-- Pinned bytes: `ADD r9, 255` carries the B extension bit. -/
theorem pin_addImm_r9_ff :
    encodeCompactAdd (.addImm8 .r9 255) =
      some [natByte 73, natByte 131, natByte 193, natByte 255] := by
  decide

/-- Pinned decode: `ADD r9, 255`. -/
theorem pin_addImm_r9_ff_dekode :
    decodeCompactAdd [natByte 73, natByte 131, natByte 193, natByte 255] =
      some (((.addImm8 .r9 255) : CompactAddForm), []) := by
  decide

/-! ## Explicit refusals: truncations, neighbours, non-canonical prefixes. -/

/-- Truncated rows refuse: empty, lone REX, opcode without ModRM,
    ModRM without the immediate byte. -/
theorem compactAdd_sonde_abgeschnitten :
    decodeCompactAdd [] = none ∧
    decodeCompactAdd [natByte 72] = none ∧
    decodeCompactAdd [natByte 72, natByte 131] = none ∧
    decodeCompactAdd [natByte 72, natByte 131, natByte 192] = none := by
  decide

/-- Unsupported neighbours refuse: the imm32 opcode (129), a digit
    other than /0 (/1 OR, /7 CMP), a memory ModRM (mod = 2), the
    accumulator row (REX.W + 05), and prefixes outside 72/73 (REX.R,
    missing REX.W, no REX at all). -/
theorem compactAdd_sonde_nachbarn :
    decodeCompactAdd [natByte 72, natByte 129, natByte 192, natByte 5] =
        none ∧
    decodeCompactAdd [natByte 72, natByte 131, natByte 200, natByte 5] =
        none ∧
    decodeCompactAdd [natByte 72, natByte 131, natByte 248, natByte 5] =
        none ∧
    decodeCompactAdd [natByte 72, natByte 131, natByte 131, natByte 5] =
        none ∧
    decodeCompactAdd
        [natByte 72, natByte 5, natByte 1, natByte 0, natByte 0,
          natByte 0] = none ∧
    decodeCompactAdd [natByte 76, natByte 131, natByte 192, natByte 5] =
        none ∧
    decodeCompactAdd [natByte 64, natByte 131, natByte 192, natByte 5] =
        none ∧
    decodeCompactAdd [natByte 131, natByte 192, natByte 5] = none := by
  decide

/-! ## Prefix dispatch: no collision with the pilot decoder.

  Neither decoder is rewritten: the pilot `decode` refuses the covered
  row (its REX dispatch admits no group opcode 131), and
  `decodeCompactAdd` refuses every pilot row (no pilot row is an
  admitted REX followed by opcode 131 with a /0 register-direct
  ModRM). -/

/-- The pilot decoder refuses the covered row for every immediate,
    over any suffix. -/
theorem pilot_verweigert_compactAdd (dst : Register) (n : Nat)
    (suffix : List Byte) :
    decode ([rexByte 0 (regHigh dst), natByte 131,
      natByte (192 + regLow dst), natByte n] ++ suffix) = none := by
  cases dst <;> rfl

/-- The compact decoder refuses every pilot row, over any suffix. -/
theorem compactAdd_verweigert_pilot (b : Befehl) (suffix : List Byte) :
    decodeCompactAdd (encode b ++ suffix) = none := by
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

/-! ## Execution connection: the accepted register step plus advance.

  The register form touches no memory (no permissions, no #GP/#PF/#AC
  surface), raises no arithmetic fault (addition has no divide error;
  contrast MulDiv's `hardwareHalt`), and installs no AF. The only
  refusal is a length mismatch against the decoded length. -/

/-- A decoded compact ADD: the form with its consumed length, checked
    against `compactAddLaenge` at step time. -/
structure CompactAddDec where
  befehl : CompactAddForm
  laenge : Nat
  deriving DecidableEq, Repr

/-- One compact ADD step: refuse on length mismatch; otherwise write the
    64-bit value with its flag snapshot through the accepted
    `schrittRegister`, advancing RIP past the decoded length. -/
def compactAddSchritt (d : CompactAddDec) (s : Zustand) : Option Zustand :=
  if d.laenge == compactAddLaenge d.befehl then
    match d.befehl with
    | .addImm8 dst n =>
      some (schrittRegister s (ripNach s.rip d.laenge)
        (addImmFlags .b64 (s.register dst) n) dst
        (addImmOp .b64 (s.register dst) n))
  else none

/-- Length mismatch refuses: the consumed length is checked data. -/
theorem compactAddSchritt_laenge (d : CompactAddDec) (s : Zustand)
    (h : d.laenge ≠ compactAddLaenge d.befehl) :
    compactAddSchritt d s = none := by
  unfold compactAddSchritt
  rw [if_neg (by simpa [beq_iff_eq] using h)]

/-- The step equation: a matching length runs the value-plus-flags
    update through the accepted register step. -/
theorem compactAddSchritt_weiter (d : CompactAddDec) (s : Zustand)
    (dst : Register) (n : Nat) (h : d.befehl = .addImm8 dst n)
    (hlen : d.laenge == compactAddLaenge d.befehl) :
    compactAddSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (addImmFlags .b64 (s.register dst) n) dst
        (addImmOp .b64 (s.register dst) n)) := by
  unfold compactAddSchritt
  rw [if_pos hlen, h]

/-- At the canonical length the register form never refuses: addition
    has no divide error and the register destination has no fault
    surface (contrast memory forms, whose #GP/#PF/#AC stay open). -/
theorem compactAddSchritt_immer (dst : Register) (n : Nat)
    (s : Zustand) :
    ∃ s', compactAddSchritt ⟨.addImm8 dst n, 4⟩ s = some s' := by
  refine ⟨schrittRegister s (ripNach s.rip 4)
    (addImmFlags .b64 (s.register dst) n) dst
    (addImmOp .b64 (s.register dst) n), ?_⟩
  exact compactAddSchritt_weiter _ s dst n rfl rfl

/-- Frame: the destination holds the sum, flags carry the snapshot,
    memory and every other register are kept, RIP advances past the
    decoded length. -/
theorem compactAddSchritt_rahmen (d : CompactAddDec) (s s' : Zustand)
    (dst : Register) (n : Nat) (h : d.befehl = .addImm8 dst n)
    (hlen : d.laenge == compactAddLaenge d.befehl)
    (hstep : compactAddSchritt d s = some s') :
    s'.register dst = s.register dst + immSext n ∧
      s'.flags = addImmFlags .b64 (s.register dst) n ∧
      s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip d.laenge ∧
      (∀ q : Register, q ≠ dst → s'.register q = s.register q) := by
  rw [compactAddSchritt_weiter d s dst n h hlen] at hstep
  cases hstep
  refine ⟨?_, rfl, rfl, rfl, ?_⟩
  · unfold schrittRegister
    rw [addImmOp_b64]
    exact regSet_gleich _ _ _
  · intro q hq
    unfold schrittRegister
    exact regSet_fremd _ _ _ _ hq

/-! ## Byte-to-memory connection.

  The four canonical bytes decode to the stepped form, the encoder
  answers inside i8, the step lands the sign-extended sum with the
  accepted flags (AF none), and the pilot store carries the sum into
  real byte memory with a word read-back. Decode, value, flags and the
  memory handoff in one jointly inhabited statement. -/

/-- CONNECTION: canonical bytes decode to the form, the form steps to
    the sign-extended sum with the accepted flags, and the pilot store
    moves the sum into memory with a word read-back. -/
theorem CompactImm8Add_verbindung (dst base : Register) (n : Nat)
    (hn : n < 256) (s s' : Zustand) (disp : BitVec 32) (m : Speicher)
    (hadd : compactAddSchritt ⟨.addImm8 dst n, 4⟩ s = some s')
    (hwr : write64 s'.speicher (effAddr s' base disp) (s'.register dst) =
      some m)
    (hrd : lesbar8 s'.speicher (effAddr s' base disp) = true) :
    decodeCompactAdd [rexByte 0 (regHigh dst), natByte 131,
        natByte (192 + regLow dst), natByte n] =
        some ((.addImm8 dst n), []) ∧
      encodeCompactAdd (.addImm8 dst n) ≠ none ∧
      s'.register dst = s.register dst + immSext n ∧
      s'.flags.af = none ∧
      s'.flags.cf = (add64 (s.register dst) (immSext n)).2.cf ∧
      s'.flags.of = (add64 (s.register dst) (immSext n)).2.of ∧
      s'.flags.sf = (add64 (s.register dst) (immSext n)).2.sf ∧
      s'.flags.zf = (add64 (s.register dst) (immSext n)).2.zf ∧
      s'.flags.pf = (add64 (s.register dst) (immSext n)).2.pf ∧
      schritt ⟨.store64 base dst disp, 7⟩ s' =
        some ({ s' with speicher := m, rip := ripNach s'.rip 7 }) ∧
      read64 m (effAddr s' base disp) = some (s'.register dst) := by
  have hrt : decodeCompactAdd [rexByte 0 (regHigh dst), natByte 131,
      natByte (192 + regLow dst), natByte n] =
      some ((.addImm8 dst n), []) := by
    have h := roundtripCompactAdd dst n hn []
    rwa [List.append_nil] at h
  have henc : encodeCompactAdd (.addImm8 dst n) ≠ none := by
    rw [encodeCompactAdd_some dst n hn]
    simp
  have hr := compactAddSchritt_rahmen ⟨.addImm8 dst n, 4⟩ s s' dst n
    rfl rfl hadd
  obtain ⟨hval, hflags, -, -, -⟩ := hr
  have hok7 : laengeOk 7 = true := by decide
  have hstore := schritt_store64_erfolg ⟨.store64 base dst disp, 7⟩ s'
    base dst disp m hok7 rfl hwr
  have hread := read64_nach_write64 _ _ _ _ hwr hrd
  have haf : s'.flags.af = none := by
    rw [hflags]; exact addImmFlags_af _ _ _
  have hcf : s'.flags.cf = (add64 (s.register dst) (immSext n)).2.cf := by
    rw [hflags]; exact addImmFlags_cf _ _
  have hof : s'.flags.of = (add64 (s.register dst) (immSext n)).2.of := by
    rw [hflags]; exact addImmFlags_of _ _
  have hsf : s'.flags.sf = (add64 (s.register dst) (immSext n)).2.sf := by
    rw [hflags]; exact addImmFlags_sf _ _
  have hzf : s'.flags.zf = (add64 (s.register dst) (immSext n)).2.zf := by
    rw [hflags]; exact addImmFlags_zf _ _
  have hpf : s'.flags.pf = (add64 (s.register dst) (immSext n)).2.pf := by
    rw [hflags]; exact addImmFlags_pf _ _
  exact ⟨hrt, henc, hval, haf, hcf, hof, hsf, hzf, hpf, hstore, hread⟩

/-! ## Reached witness: decoded ADD feeding a memory store.

  `ADD rax, 5` (4 bytes) followed by the pilot `store [rbx], rax`
  (7 bytes): the decoded form steps `rax` from 10 to 15, and the
  existing `schritt` stores the sum into the data cell, observably
  changing its byte. Code bytes are pinned through the decoder;
  execution reuses the accepted pilot store on the same `Zustand`. -/

/-- Witness program: ADD bytes then the pilot store bytes. -/
def addKetteProg : List Byte :=
  [natByte 72, natByte 131, natByte 192, natByte 5] ++
    encode (.store64 .rbx .rax (BitVec.ofNat 32 0))

/-- The executed bytes decode to the stepped form, leaving the pilot
    store bytes as the suffix. -/
theorem add_kette_dekode :
    decodeCompactAdd addKetteProg =
      some (((.addImm8 .rax 5) : CompactAddForm),
        encode (.store64 .rbx .rax (BitVec.ofNat 32 0))) := by
  decide

/-- Witness registers: `rax` holds 10, `rbx` the data cell. -/
def addKetteReg : Register → Wort := fun q =>
  if q = Register.rax then 10
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness start state: sum input in `rax`, data cell at 8192. -/
def addKetteStart : Zustand :=
  { register := addKetteReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugenSpeicher }

/-- Witness mid state: after the ADD (`rax` 10 goes to 15). -/
def addKetteMitte : Zustand :=
  schrittRegister addKetteStart (ripNach addKetteStart.rip 4)
    (addImmFlags .b64 (addKetteStart.register .rax) 5) .rax
    (addImmOp .b64 (addKetteStart.register .rax) 5)

/-- Witness memory after the store: the sum lands in the data cell
    (stated with the explicit constructor, field for field what the
    accepted `write64` produces). -/
def addKetteNach : Speicher :=
  Speicher.mk (writeBytes addKetteMitte.speicher
    (effAddr addKetteMitte .rbx (BitVec.ofNat 32 0))
    (addKetteMitte.register .rax))
    addKetteMitte.speicher.lesbar addKetteMitte.speicher.schreibbar
    addKetteMitte.speicher.ausfuehrbar

/-- The ADD step moves 10 to 15, advances past its 4 bytes and leaves
    carry cleared. -/
theorem add_kette_schritt :
    (compactAddSchritt ⟨.addImm8 .rax 5, 4⟩ addKetteStart).map
        (fun s => s.register .rax) = some 15 ∧
      (compactAddSchritt ⟨.addImm8 .rax 5, 4⟩ addKetteStart).map
        (fun s => s.rip) = some (BitVec.ofNat 64 4100) ∧
      (compactAddSchritt ⟨.addImm8 .rax 5, 4⟩ addKetteStart).map
        (fun s => s.flags.cf) = some false := by
  decide

/-- The two-step end state: ADD, then the pilot store of `rax`. -/
def addKetteEnde : Option Zustand :=
  (compactAddSchritt ⟨.addImm8 .rax 5, 4⟩ addKetteStart).bind
    (schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩)

/-- The sum reaches memory: the data cell reads 15 and its byte
    observably changed from zero; a wrong consumed length on the same
    form refuses. -/
theorem add_kette_speicher :
    addKetteEnde.map (fun s =>
        read64 s.speicher (BitVec.ofNat 64 8192)) =
        some (some 15) ∧
      addKetteEnde.map (fun s =>
        s.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (natByte 15) ∧
      addKetteStart.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      compactAddSchritt ⟨.addImm8 .rax 5, 5⟩ addKetteStart = none := by
  decide

/-- JOINT witness for `CompactImm8Add_verbindung`: every premise on
    concrete values (imm 5 inside i8; the ADD step from the witness
    start; the write plus readability at the data cell) with the
    memory run observably changing the data byte from zero to 15.
    Non-degenerate: a reached two-step run whose second step changes
    actual memory, plus a planted length refusal above. -/
theorem CompactImm8Add_verbindung_zeuge :
    ∃ (s' : Zustand) (m : Speicher),
      compactAddSchritt ⟨.addImm8 .rax 5, 4⟩ addKetteStart = some s' ∧
      write64 s'.speicher (effAddr s' .rbx (BitVec.ofNat 32 0))
        (s'.register .rax) = some m ∧
      lesbar8 s'.speicher (effAddr s' .rbx (BitVec.ofNat 32 0)) = true ∧
      s'.register .rax = 15 ∧
      s'.flags.af = none ∧
      addKetteStart.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      m.bytes (BitVec.ofNat 64 8192) ≠
        addKetteStart.speicher.bytes (BitVec.ofNat 64 8192) := by
  have hperm : schreibbar8 addKetteMitte.speicher
      (effAddr addKetteMitte .rbx (BitVec.ofNat 32 0)) = true := by
    decide
  have hwr : write64 addKetteMitte.speicher
      (effAddr addKetteMitte .rbx (BitVec.ofNat 32 0))
      (addKetteMitte.register .rax) = some addKetteNach := by
    unfold write64 addKetteNach
    rw [if_pos hperm]
  refine ⟨addKetteMitte, addKetteNach,
    compactAddSchritt_weiter _ _ .rax 5 rfl rfl, hwr, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide

/- CUTS:
    Proved here, over the ACTUAL accepted vocabulary (`Typen`,
    `Wort.sext`/`trunc`/`cfAdd`/`ofAdd`/`zfTest`/`sfTest`/`parityEven`/
    `add64`, `ShiftLogic.negB_b64`, `Codec.rexByte`/`natByte`/`byteNat`/
    `codeReg`/`regHigh`/`regLow`/`decode`/`encode`,
    `Ausfuehrung.laengeOk`/`ripNach`/`regSet`/`schrittRegister`/
    `schritt`/`effAddr`/`zeugeFlags`, `Speicher.zeugenSpeicher`/
    `write64`/`read64`/`lesbar8`): exactly one row, `REX.W + 83 /0 ib`
    register-direct ADD r64, imm8 (Vol. 2A 3-14), with the sign-extended
    immediate (`immSext` reusing canonical `sext .b8`, four pins),
    width-generic value and flags (`addImmOp`/`addImmFlags`) whose AF is
    `none` at every width and whose 64-bit value and CF/OF/SF/ZF/PF ARE
    the accepted `add64` ones (no second evaluator), a canonical
    Option encoder (four bytes inside i8, `none` outside with proved
    cause), a byte-parsing decoder (admitted REX.W 72/73, opcode 131,
    mod-3 /0 ModRM) with a generic round trip, pinned bytes for
    `rax, 5` and `r9, 255`, explicit refusals (truncations, imm32
    opcode, other digits, memory ModRM, accumulator row, REX.R,
    missing REX.W, bare opcode), two-sided pilot dispatch without
    rewriting either decoder, a length-checked step
    (`compactAddSchritt`) through the accepted register step that never
    faults at canonical length, per-form frame facts, and the joint
    connection (`CompactImm8Add_verbindung`: bytes decode, encoder
    answers, step lands the sum with the accepted flags, pilot store
    hands the sum to memory with word read-back) with its jointly
    inhabited companion (`CompactImm8Add_verbindung_zeuge`: concrete
    imm 5, reached two-step run changing the data byte 0 to 15, plus a
    planted length refusal).
    NOT proved here, and not claimed:
    - No hardware verification: encodings, sign-extension, flag rules
      and the AF-undefined modelling are STATED executable semantics
      grounded in the cited manual lines, not verified against silicon;
      the manual lists AF among the affected flags while this file
      leaves it `none` (deliberate conservative gap: undefined is never
      invented, following the `Ganzzahl` §4 discipline).
    - No full ADD family: memory-destination 83 rows, 16/32-bit rows,
      the 81 imm32 row and the accumulator rows refuse loudly here;
      each new row needs its own encoding, coverage and execution proof.
    - No fetch wiring: `Byteschritt.fetchDekodiert` and the
      `ExtendedExecution` dispatcher still serve the pilot rows only;
      routing the covered bytes through them waits on those owners and
      is the next integration (no dispatcher was rewritten here).
    - No source correspondence, no TSO/W/GX bridge, no image/ABI/
      entry/relocation/budget/cost claim: the register form touches no
      memory (no permissions, no TSO entry, no fault surface) and the
      memory handoff reuses the accepted pilot store sequentially;
      per-access granularity and concurrency stay with the TSO bridge.
    - `verweigert`/`none` is the absence of a transition, never a halt
      claim; 64-bit mode (REX.W) is the assumed selected profile.
-/

#print axioms pin_immSext_7f
#print axioms pin_immSext_80
#print axioms pin_immSext_ff
#print axioms pin_immSext_00
#print axioms addImmFlags_af
#print axioms addImmOp_b64
#print axioms addImmFlags_cf
#print axioms addImmFlags_of
#print axioms addImmFlags_sf
#print axioms addImmFlags_zf
#print axioms addImmFlags_pf
#print axioms compactAddLaenge_ok
#print axioms roundtripCompactAdd
#print axioms encodeCompactAdd_some
#print axioms encodeCompactAdd_verweigert
#print axioms encodeCompactAdd_ursache
#print axioms pin_addImm_rax_5
#print axioms pin_addImm_rax_5_dekode
#print axioms pin_addImm_r9_ff
#print axioms pin_addImm_r9_ff_dekode
#print axioms compactAdd_sonde_abgeschnitten
#print axioms compactAdd_sonde_nachbarn
#print axioms pilot_verweigert_compactAdd
#print axioms compactAdd_verweigert_pilot
#print axioms compactAddSchritt_laenge
#print axioms compactAddSchritt_weiter
#print axioms compactAddSchritt_immer
#print axioms compactAddSchritt_rahmen
#print axioms CompactImm8Add_verbindung
#print axioms add_kette_dekode
#print axioms add_kette_schritt
#print axioms add_kette_speicher
#print axioms CompactImm8Add_verbindung_zeuge

end Gabbro.Grammatik.X86
