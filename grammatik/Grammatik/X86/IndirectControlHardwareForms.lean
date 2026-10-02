/-
  File:      Grammatik/X86/IndirectControlHardwareForms.lean
  Subject:   Indirect and compact control byte forms over canonical state.

  Lane 680 (hardware completion): selected-profile indirect near CALL/JMP
  (FF /2, FF /4, r/m64, register-direct and checked base+disp32 memory) and
  short branches (EB rel8, 70+cc rel8) with fetched canonical execution reusing
  the accepted `schritt` constructors. See CUTS for scope.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ControlFlow
import Grammatik.X86.EffectiveAddress

namespace Gabbro.Grammatik.X86

/-! ## 0. Manual provenance and selected profile.

    Official input (clone-local, no network): Intel SDM combined volumes 1-4,
    edition 325462-093US (September 2026), snapshot
    `.tmp/HARDWARE-REFERENCES/` (`REFERENCES.json`, verified 2026-10-02,
    sha256 `a4a62e6a…f9168ee`; AMD retrieval failed, no AMD claim).
    Checked headings: Vol.2A Chapter 3 `CALL-Call Procedure` (opcode table
    `FF /2 CALL r/m64`, near-call absolute operation, `Vol.2A 3-121`),
    `JMP-Jump` (`FF /4 JMP r/m64`, `EB cb JMP rel8`, `Vol.2A 3-504`),
    `Jcc-Jump if Condition Is Met` (`70+cc cb` rel8 table, short-jump
    operation `RIP = RIP + 8-bit offset sign extended to 64 bits`,
    `Vol.2A 3-499/3-502`), Vol.2B `RET-Return From Procedure` (`C3` near,
    `Vol.2B 4-569`), Vol.1 `6.4.1 Near CALL and RET Operation` (push next-RIP,
    branch; `[ESP]` base read is the pre-instruction value).

    Selected profile claimed here (64-bit mode only):
    - near indirect `CALL r/m64` (`FF /2`) and `JMP r/m64` (`FF /4`),
      register-direct (ModRM mod=3) for all 16 registers and checked
      base+displacement-32 memory (ModRM mod=2, the accepted `effAddr`
      shape, SIB `0x24` where the pilot requires it);
    - short `JMP rel8` (`EB cb`, 2 bytes) and short `Jcc rel8`
      (`70+cond cb`, 2 bytes, all 16 conditions);
    - near `RET` (`C3`, 1 byte) stays with the pilot: reused, never
      re-decoded here.
    Explicitly OUTSIDE the profile (refused by construction, never silently
    admitted): far forms (`9A`, `EA`, `FF /3`, `FF /5`), `RET imm16`
    (`C2`/`CA`), `JCXZ`/`JECXZ`/`JRCXZ` (`E3`), LOCK-prefixed branches,
    CET/shadow-stack behaviour, REX.R/X/W variants outside the canonical
    rows below (hardware may accept more; the profile selects the rows
    below and refuses the rest loudly). -/

/-- Manual provenance for every form claimed here. -/
def indirektHandbuch : String :=
  "Intel SDM 325462-093US Vol.2A Ch.3 CALL (FF /2 r/m64, p.3-121), JMP (FF /4 r/m64, p.3-504), Jcc rel8 (70+cc cb, p.3-499), JMP rel8 (EB cb, p.3-504); Vol.2B RET (C3 near, p.4-569); Vol.1 s.6.4.1 near CALL/RET. Local snapshot .tmp/HARDWARE-REFERENCES (intel-instruction-reference.txt)."

/-! ## 1. Forms, widths and sign extension.

    Lengths are carried data checked against decoding, never emitter notes.
    `indLen` is the consumed prefix length of one form. -/

/-- Selected indirect/compact control form. Register/memory indirect calls
    and jumps carry their consumed length; short branches carry the rel8
    byte; `retBleibt` marks the pilot-owned return (no second decoder). -/
inductive IndForm where
  | callReg : Register → Nat → IndForm
  | callMem : Register → BitVec 32 → Nat → IndForm
  | jmpReg : Register → Nat → IndForm
  | jmpMem : Register → BitVec 32 → Nat → IndForm
  | jmpKurz : Byte → IndForm
  | jccKurz : Bedingung → Byte → IndForm
  deriving DecidableEq, Repr

/-- Consumed length of one form (checked data). -/
def indLen : IndForm → Nat
  | .callReg _ l => l
  | .callMem _ _ l => l
  | .jmpReg _ l => l
  | .jmpMem _ _ l => l
  | .jmpKurz _ => 2
  | .jccKurz _ _ => 2

/-- Sign extension of an 8-bit displacement to a full word (short-branch
    target math: `RIP = RIP + sign_extend(rel8)`). -/
def dispWort8 (b : Byte) : Wort := sext .b8 (BitVec.ofNat 64 b.toNat)

/-- Short unconditional target from decoded length only. -/
def kurzZiel (rip : Adresse) (len : Nat) (d8 : Byte) : Adresse :=
  ripNach rip len + dispWort8 d8

/-- `0xFF` as a natural number (the indirect opcode byte). -/
theorem byteNat_ff : byteNat (natByte 255) = 255 :=
  byteNat_natByte_of_lt 255 (by decide)

/-- The rel8 sign extension agrees with the 32-bit one on embedded values:
    a zero-extended rel8 displacement sign-extends identically. -/
theorem dispWort8_beispiel :
    dispWort8 (natByte 16) = BitVec.ofNat 64 16 ∧
    dispWort8 (natByte 251) + 5 = BitVec.ofNat 64 0 := by
  decide

/-! ## 2. Canonical encoders.

    Register-direct indirect: bare `FF` for low registers, `REX.B` (`0x41`)
    for high registers; REX.R/X/W variants are refused (profile selects
    these canonical rows; hardware acceptance beyond them is not claimed).
    Memory indirect: mandatory `REX.W` (`0x48`/`0x49`, R=0 since the reg
    field is the `/2`/`/4` extension), ModRM mod=2, SIB `0x24` exactly
    where the pilot requires it (`regLow base = 4`). -/

/-- Canonical register-direct indirect bytes: `FF /2` (call) or `FF /4`
    (jmp), mod=3. Low registers need no REX, high registers take `0x41`. -/
def encodeIndReg (isCall : Bool) (tgt : Register) : List Byte :=
  let ext : Nat := if isCall then 2 else 4
  let m := modrmReg ext (regLow tgt)
  match regHigh tgt with
  | 0 => [natByte 255, m]
  | _ => [natByte 65, natByte 255, m]

/-- Canonical memory-indirect bytes: `REX.W FF /2|/4` mod=2 base+disp32,
    SIB `0x24` exactly where the pilot requires it. -/
def encodeIndMem (isCall : Bool) (base : Register)
    (d : BitVec 32) : List Byte :=
  let ext : Nat := if isCall then 2 else 4
  let rex := natByte (72 + regHigh base)
  let head := [rex, natByte 255, modrmMem ext (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- Canonical short unconditional bytes: `EB cb`. -/
def encodeJmpKurz (d8 : Byte) : List Byte := [natByte 235, d8]

/-- Canonical short conditional bytes: `70+cond cb`. -/
def encodeJccKurz (c : Bedingung) (d8 : Byte) : List Byte :=
  [natByte (112 + condCode c), d8]

/-- Register-indirect length: 2 without REX, 3 with `REX.B`. -/
theorem encodeIndReg_len (isCall : Bool) (tgt : Register) :
    (encodeIndReg isCall tgt).length = 2 ∨
    (encodeIndReg isCall tgt).length = 3 := by
  cases tgt <;> simp [encodeIndReg, regHigh, regCode]

/-- Memory-indirect length: 7 without SIB, 8 with SIB. -/
theorem encodeIndMem_len (isCall : Bool) (base : Register)
    (d : BitVec 32) :
    (encodeIndMem isCall base d).length = 7 ∨
    (encodeIndMem isCall base d).length = 8 := by
  unfold encodeIndMem
  split
  · split
    · simp [length_leBytes32]
    · simp [length_leBytes32]
  · split
    · simp [length_leBytes32]
    · simp [length_leBytes32]

/-- Short forms are 2 bytes. -/
theorem encodeKurz_len (d8 : Byte) :
    (encodeJmpKurz d8).length = 2 := by
  rfl

/-- Short conditional forms are 2 bytes. -/
theorem encodeJccKurz_len (c : Bedingung) (d8 : Byte) :
    (encodeJccKurz c d8).length = 2 := by
  cases c <;> rfl

/-! ## 3. Decoders: canonical rows only, everything else refused.

    Short forms first (first-byte disjoint: `EB`, `70-7F`); then
    register-direct `FF /2|/4` mod=3 (2 bytes bare, 3 with `REX.B`);
    then checked memory `REX.W FF /2|/4` mod=2 base+disp32 (7/8 bytes).
    Far extensions (`/3`, `/5`), other ModRM modes, other REX bytes and
    the `E3` counter family have no arm: refused by construction. -/

/-- Decode a ModRM byte into mod/reg/rm fields. -/
def modrmFelder (m : Byte) : Nat × Nat × Nat :=
  (byteNat m / 64, byteNat m / 8 % 8, byteNat m % 8)

/-- Decode after a register-direct ModRM (`bBit` is the REX.B extension,
    `ext` the required reg field: 2 for call, 4 for jump). -/
def decodeIndRegNach (bBit ext rm : Nat) (rest : List Byte) :
    Option ((Register × Nat) × List Byte) :=
  match codeReg (bBit * 8 + rm) with
  | some tgt =>
    if ext == 2 ∨ ext == 4 then some ((tgt, 2 + bBit), rest)
    else none
  | none => none

/-- Decode a checked memory target after the ModRM (`bBit` is REX.B,
    `ext` the required reg field). Length 8 with SIB, 7 without. -/
def decodeIndMemNach (bBit ext rm : Nat) (tail : List Byte) :
    Option ((Register × BitVec 32 × Nat) × List Byte) :=
  if rm == 4 then
    match tail with
    | [] => none
    | sib :: rest =>
      if byteNat sib == 36 then
        match parseLe32 rest with
        | some (d, rest') =>
          match codeReg (bBit * 8 + rm) with
          | some base =>
            if ext == 2 ∨ ext == 4 then
              some ((base, d, 8), rest')
            else none
          | none => none
        | none => none
      else none
  else
    match parseLe32 tail with
    | some (d, rest') =>
      match codeReg (bBit * 8 + rm) with
      | some base =>
        if ext == 2 ∨ ext == 4 then
          some ((base, d, 7), rest')
        else none
      | none => none
    | none => none

/-- Memory-tail decode without SIB reads the displacement and the base. -/
theorem decodeIndMemNach_ohneSIB (bBit ext rm : Nat) (d : BitVec 32)
    (suffix : List Byte) (base : Register)
    (hcode : codeReg (bBit * 8 + rm) = some base)
    (hrm : rm ≠ 4) (hext : ext == 2 ∨ ext == 4) :
    decodeIndMemNach bBit ext rm (leBytes32 d ++ suffix) =
      some ((base, d, 7), suffix) := by
  have h4 : (rm == 4) = false := beq_eq_false_iff_ne.mpr hrm
  unfold decodeIndMemNach
  rw [h4, parseLe32_leBytes32, hcode]
  cases hext with
  | inl h => simp [h]
  | inr h => simp [h]

/-- Selected-profile indirect/compact decoder. Anything else is refused
    with `none`: far forms, other modes, other REX bytes, `E3`. -/
def decodeIndirekt : List Byte → Option (IndForm × List Byte)
  | [] => none
  | b1 :: rest =>
    match byteNat b1 with
    | 235 =>
      match rest with
      | d8 :: rest' => some ((.jmpKurz d8), rest')
      | [] => none
    | n =>
      if 112 ≤ n ∧ n < 128 then
        match rest with
        | d8 :: rest' =>
          match codeCond (n - 112) with
          | some c => some ((.jccKurz c d8), rest')
          | none => none
        | [] => none
      else
        match n with
        | 255 =>
          match rest with
          | [] => none
          | m :: rest' =>
            let (md, rg, rm) := modrmFelder m
            match md with
            | 3 =>
              if rg == 2 then
                match decodeIndRegNach 0 2 rm rest' with
                | some ((tgt, _), r) => some ((.callReg tgt 2), r)
                | none => none
              else if rg == 4 then
                match decodeIndRegNach 0 4 rm rest' with
                | some ((tgt, _), r) => some ((.jmpReg tgt 2), r)
                | none => none
              else none
            | 2 => none
            | _ => none
        | 65 =>
          match rest with
          | [] => none
          | b2 :: rest' =>
            if byteNat b2 == 255 then
              match rest' with
              | [] => none
              | m :: rest'' =>
                let (md, rg, rm) := modrmFelder m
                match md with
                | 3 =>
                  if rg == 2 then
                    match decodeIndRegNach 1 2 rm rest'' with
                    | some ((tgt, _), r) => some ((.callReg tgt 3), r)
                    | none => none
                  else if rg == 4 then
                    match decodeIndRegNach 1 4 rm rest'' with
                    | some ((tgt, _), r) => some ((.jmpReg tgt 3), r)
                    | none => none
                  else none
                | _ => none
            else none
        | 72 =>
          match rest with
          | [] => none
          | b2 :: rest' =>
            if byteNat b2 == 255 then
              match rest' with
              | [] => none
              | m :: tail =>
                let (md, rg, rm) := modrmFelder m
                match md with
                | 2 =>
                  match decodeIndMemNach 0 rg rm tail with
                  | some ((base, d, l), r) =>
                    if rg == 2 then some ((.callMem base d l), r)
                    else if rg == 4 then some ((.jmpMem base d l), r)
                    else none
                  | none => none
                | _ => none
            else none
        | 73 =>
          match rest with
          | [] => none
          | b2 :: rest' =>
            if byteNat b2 == 255 then
              match rest' with
              | [] => none
              | m :: tail =>
                let (md, rg, rm) := modrmFelder m
                match md with
                | 2 =>
                  match decodeIndMemNach 1 rg rm tail with
                  | some ((base, d, l), r) =>
                    if rg == 2 then some ((.callMem base d l), r)
                    else if rg == 4 then some ((.jmpMem base d l), r)
                    else none
                  | none => none
                | _ => none
            else none
        | _ => none

/-! ## 4. Round trips: canonical bytes decode to their form.

    Lengths carried in the form equal the consumed prefix length. -/

/-- Round trip: register-direct indirect call bytes decode. -/
theorem roundtrip_indReg_call (tgt : Register) (suffix : List Byte) :
    decodeIndirekt (encodeIndReg true tgt ++ suffix) =
      some (((.callReg tgt (2 + regHigh tgt))), suffix) := by
  cases tgt <;> rfl

/-- Round trip: register-direct indirect jump bytes decode. -/
theorem roundtrip_indReg_jmp (tgt : Register) (suffix : List Byte) :
    decodeIndirekt (encodeIndReg false tgt ++ suffix) =
      some (((.jmpReg tgt (2 + regHigh tgt))), suffix) := by
  cases tgt <;> rfl

/-- Round trip: memory-indirect call bytes decode (7/8 by SIB). -/
theorem roundtrip_indMem_call (base : Register) (d : BitVec 32)
    (suffix : List Byte) :
    decodeIndirekt (encodeIndMem true base d ++ suffix) =
      some (((.callMem base d
        (if regLow base == 4 then 8 else 7))), suffix) := by
  cases base <;>
    simp [encodeIndMem, regLow, regCode, regHigh, decodeIndirekt,
      modrmFelder, modrmMem, codeReg, decodeIndMemNach,
      parseLe32_leBytes32]

/-- Round trip: memory-indirect jump bytes decode (7/8 by SIB). -/
theorem roundtrip_indMem_jmp (base : Register) (d : BitVec 32)
    (suffix : List Byte) :
    decodeIndirekt (encodeIndMem false base d ++ suffix) =
      some (((.jmpMem base d
        (if regLow base == 4 then 8 else 7))), suffix) := by
  cases base <;>
    simp [encodeIndMem, regLow, regCode, regHigh, decodeIndirekt,
      modrmFelder, modrmMem, codeReg, decodeIndMemNach,
      parseLe32_leBytes32]

/-- Round trip: short unconditional bytes decode. -/
theorem roundtrip_jmpKurz (d8 : Byte) (suffix : List Byte) :
    decodeIndirekt (encodeJmpKurz d8 ++ suffix) =
      some (((.jmpKurz d8)), suffix) := by
  simp [encodeJmpKurz, decodeIndirekt,
    byteNat_natByte_of_lt 235 (by decide)]

/-- Round trip: short conditional bytes decode. -/
theorem roundtrip_jccKurz (c : Bedingung) (d8 : Byte)
    (suffix : List Byte) :
    decodeIndirekt (encodeJccKurz c d8 ++ suffix) =
      some (((.jccKurz c d8)), suffix) := by
  cases c <;> simp [encodeJccKurz, decodeIndirekt, condCode, codeCond]

/-! ## 5. Execution over the accepted constructors.

    No new interpreter: indirect calls reuse `schrittCall` with the
    next-RIP return word (Vol.1 6.4.1: the pushed value is the address of
    the instruction FOLLOWING the call); indirect jumps write the
    pre-state target into RIP; short branches add the sign-extended rel8
    to the post-decode address. The memory-indirect target is read FIRST
    through permission-checked `read64` from the PRE-state (including an
    RSP base, whose value is the pre-instruction top, per the manual);
    only then is the return word stored. A faulting target read refuses
    on every path: no speculation of the fault away. -/

/-- Register-indirect call step: the next-RIP word is stored below the
    pre-state top, control moves to the pre-state register word. -/
def callRegSchritt (len : Nat) (s : Zustand) (tgt : Register) :
    Option Zustand :=
  match laengeOk len with
  | false => none
  | true =>
    match write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip len) with
    | some m =>
      some (schrittCall s Register.rsp m
        (s.register Register.rsp - BitVec.ofNat 64 8) (s.register tgt))
    | none => none

/-- Memory-indirect call step: the target word is read first from the
    pre-state effective address, then the next-RIP word is stored. -/
def callMemSchritt (len : Nat) (s : Zustand) (base : Register)
    (disp : BitVec 32) : Option Zustand :=
  match laengeOk len with
  | false => none
  | true =>
    match read64 s.speicher (effAddr s base disp) with
    | none => none
    | some ziel =>
      match write64 s.speicher
          (s.register Register.rsp - BitVec.ofNat 64 8)
          (ripNach s.rip len) with
      | some m =>
        some (schrittCall s Register.rsp m
          (s.register Register.rsp - BitVec.ofNat 64 8) ziel)
      | none => none

/-- Register-indirect jump step: control moves to the pre-state
    register word; flags, memory and registers kept. -/
def jmpRegSchritt (len : Nat) (s : Zustand) (tgt : Register) :
    Option Zustand :=
  match laengeOk len with
  | false => none
  | true => some ({ s with rip := s.register tgt })

/-- Memory-indirect jump step: the target word is read first from the
    pre-state effective address, then control moves to it. -/
def jmpMemSchritt (len : Nat) (s : Zustand) (base : Register)
    (disp : BitVec 32) : Option Zustand :=
  match laengeOk len with
  | false => none
  | true =>
    match read64 s.speicher (effAddr s base disp) with
    | none => none
    | some ziel => some ({ s with rip := ziel })

/-- Short unconditional step: post-decode address plus sign-extended
    rel8; flags, memory and registers kept. -/
def jmpKurzSchritt (len : Nat) (s : Zustand) (d8 : Byte) :
    Option Zustand :=
  match laengeOk len with
  | false => none
  | true => some ({ s with rip := kurzZiel s.rip len d8 })

/-- Short conditional step: taken moves past decode by sign-extended
    rel8, untaken falls through to the post-decode address. -/
def jccKurzSchritt (len : Nat) (s : Zustand) (c : Bedingung)
    (d8 : Byte) : Option Zustand :=
  match laengeOk len with
  | false => none
  | true => some ({ s with rip := (if bedingung c s.flags then kurzZiel s.rip len d8 else ripNach s.rip len) })

/-- One form step: exact evaluation selection over the constructors. -/
def indSchritt (i : IndForm) (s : Zustand) : Option Zustand :=
  match i with
  | .callReg tgt l => callRegSchritt l s tgt
  | .callMem base d l => callMemSchritt l s base d
  | .jmpReg tgt l => jmpRegSchritt l s tgt
  | .jmpMem base d l => jmpMemSchritt l s base d
  | .jmpKurz d8 => jmpKurzSchritt 2 s d8
  | .jccKurz c d8 => jccKurzSchritt 2 s c d8

/-! ## 6. Step equations: success, access order, refusal, frames.

    The stored return word is ALWAYS `ripNach` of the pre-state RIP
    (never a hand-built address); the stack slot is ALWAYS the pre-state
    `rsp` minus 8 (so an RSP-relative memory target reads the
    pre-instruction top, per Vol.2A). Memory-indirect success carries
    BOTH the target read and the stack write: the read is evaluated on
    the pre-state, before the write. -/

/-- Register-indirect call success: return word stored, control at the
    pre-state register word. -/
theorem callRegSchritt_erfolg (len : Nat) (s : Zustand) (tgt : Register)
    (m : Speicher)
    (hok : laengeOk len = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip len) = some m) :
    callRegSchritt len s tgt =
      some (schrittCall s Register.rsp m
        (s.register Register.rsp - BitVec.ofNat 64 8) (s.register tgt)) := by
  unfold callRegSchritt
  rw [hok, hwr]

/-- Register-indirect call refusal: a failed stack write is explicit. -/
theorem callRegSchritt_verweigert (len : Nat) (s : Zustand)
    (tgt : Register)
    (hok : laengeOk len = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip len) = none) :
    callRegSchritt len s tgt = none := by
  unfold callRegSchritt
  rw [hok, hwr]

/-- Memory-indirect call success: the pre-state target read comes first,
    then the return-word store; control moves to the read word. -/
theorem callMemSchritt_erfolg (len : Nat) (s : Zustand) (base : Register)
    (disp : BitVec 32) (ziel : Wort) (m : Speicher)
    (hok : laengeOk len = true)
    (hrd : read64 s.speicher (effAddr s base disp) = some ziel)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip len) = some m) :
    callMemSchritt len s base disp =
      some (schrittCall s Register.rsp m
        (s.register Register.rsp - BitVec.ofNat 64 8) ziel) := by
  unfold callMemSchritt
  rw [hok, hrd, hwr]

/-- NO-SPECULATION: a faulting memory-indirect target refuses even when
    the stack slot is writable. The target fault is never stored past. -/
theorem callMemSchritt_lesefehler (len : Nat) (s : Zustand)
    (base : Register) (disp : BitVec 32)
    (hok : laengeOk len = true)
    (hrd : read64 s.speicher (effAddr s base disp) = none) :
    callMemSchritt len s base disp = none := by
  unfold callMemSchritt
  rw [hok, hrd]

/-- Memory-indirect call with a good target but a guarded stack refuses
    at the store: the read alone admits no transition. -/
theorem callMemSchritt_schreibfehler (len : Nat) (s : Zustand)
    (base : Register) (disp : BitVec 32) (ziel : Wort)
    (hok : laengeOk len = true)
    (hrd : read64 s.speicher (effAddr s base disp) = some ziel)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip len) = none) :
    callMemSchritt len s base disp = none := by
  unfold callMemSchritt
  rw [hok, hrd, hwr]

/-- Register-indirect jump success with its frame: flags, memory and
    every register kept, RIP at the pre-state word. -/
theorem jmpRegSchritt_erfolg (len : Nat) (s s' : Zustand) (tgt : Register)
    (hok : laengeOk len = true)
    (hstep : jmpRegSchritt len s tgt = some s') :
    s'.rip = s.register tgt ∧ s'.flags = s.flags ∧
    s'.speicher = s.speicher ∧
    ∀ (q : Register), s'.register q = s.register q := by
  unfold jmpRegSchritt at hstep
  rw [hok] at hstep
  cases hstep
  exact ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-- Memory-indirect jump success: control moves to the read word. -/
theorem jmpMemSchritt_erfolg (len : Nat) (s : Zustand) (base : Register)
    (disp : BitVec 32) (ziel : Wort)
    (hok : laengeOk len = true)
    (hrd : read64 s.speicher (effAddr s base disp) = some ziel) :
    jmpMemSchritt len s base disp = some ({ s with rip := ziel }) := by
  unfold jmpMemSchritt
  rw [hok, hrd]

/-- Memory-indirect jump refusal: a faulting target read admits no
    transition. -/
theorem jmpMemSchritt_verweigert (len : Nat) (s : Zustand)
    (base : Register) (disp : BitVec 32)
    (hok : laengeOk len = true)
    (hrd : read64 s.speicher (effAddr s base disp) = none) :
    jmpMemSchritt len s base disp = none := by
  unfold jmpMemSchritt
  rw [hok, hrd]

/-- Short unconditional success: RIP at post-decode plus sign-extended
    rel8, everything else kept. -/
theorem jmpKurzSchritt_erfolg (len : Nat) (s s' : Zustand) (d8 : Byte)
    (hok : laengeOk len = true)
    (hstep : jmpKurzSchritt len s d8 = some s') :
    s'.rip = kurzZiel s.rip len d8 ∧ s'.flags = s.flags ∧
    s'.speicher = s.speicher := by
  unfold jmpKurzSchritt at hstep
  rw [hok] at hstep
  cases hstep
  exact ⟨rfl, rfl, rfl⟩

/-- Short conditional taken: RIP at post-decode plus sign-extended rel8. -/
theorem jccKurzSchritt_genommen (len : Nat) (s : Zustand) (c : Bedingung)
    (d8 : Byte)
    (hok : laengeOk len = true)
    (hbed : bedingung c s.flags = true) :
    jccKurzSchritt len s c d8 =
      some ({ s with rip := kurzZiel s.rip len d8 }) := by
  unfold jccKurzSchritt
  rw [hok]
  simp [hbed]

/-- Short conditional untaken: RIP falls through to post-decode. -/
theorem jccKurzSchritt_nicht (len : Nat) (s : Zustand) (c : Bedingung)
    (d8 : Byte)
    (hok : laengeOk len = true)
    (hbed : bedingung c s.flags = false) :
    jccKurzSchritt len s c d8 =
      some ({ s with rip := ripNach s.rip len }) := by
  unfold jccKurzSchritt
  rw [hok]
  simp [hbed]

/-! ## 7. Fetch from actual bytes, admission, pilot separation, adapter.

    Fetch follows the `Byteschritt` discipline: the fetched window is the
    state's ACTUAL bytes at RIP (executable prefix, capped at 15); the
    consumed length, the decode-length guard and execute permission of the
    consumed prefix are checked at runtime. `indirektZielOk` is
    compiler/validator target provenance (decoded-start admission), NOT a
    hardware fault: an unadmitted target still executes (no #GP is
    modelled for it), and an admitted target still refuses on a guarded
    stack or non-readable memory (the actual #PF-like permission gates).
    `RET` stays with the pilot: our decoder refuses `C3`. -/

/-- Unified admission: consumed length plus suffix is the fetched window,
    the length passes the guard, the consumed prefix is executable. -/
def indZugelassen (s : Zustand) (fenster : List Byte) (i : IndForm)
    (rest : List Byte) : Bool :=
  decide (indLen i + rest.length = fenster.length) &&
    laengeOk (indLen i) &&
    ausfuehrbarN s.speicher s.rip (indLen i)

/-- Admission carries the length equation. -/
theorem indZugelassen_summe (s : Zustand) (fenster : List Byte)
    (i : IndForm) (rest : List Byte)
    (h : indZugelassen s fenster i rest = true) :
    indLen i + rest.length = fenster.length := by
  unfold indZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsum, _⟩, _⟩ := h
  exact of_decide_eq_true hsum

/-- Admission carries the length guard. -/
theorem indZugelassen_laenge (s : Zustand) (fenster : List Byte)
    (i : IndForm) (rest : List Byte)
    (h : indZugelassen s fenster i rest = true) :
    laengeOk (indLen i) = true := by
  unfold indZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨_, hlen⟩, _⟩ := h
  exact hlen

/-- Admission carries execute permission of the consumed prefix. -/
theorem indZugelassen_ausfuehrbar (s : Zustand) (fenster : List Byte)
    (i : IndForm) (rest : List Byte)
    (h : indZugelassen s fenster i rest = true) :
    ausfuehrbarN s.speicher s.rip (indLen i) = true := by
  unfold indZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hexe⟩ := h
  exact hexe

/-- Fetch and decode over a given window, gated by admission. -/
def fetchInd (s : Zustand) (fenster : List Byte) :
    Option (IndForm × List Byte) :=
  match decodeIndirekt fenster with
  | none => none
  | some p =>
    if indZugelassen s fenster p.1 p.2 then some p else none

/-- A successful fetch decodes the window with all admission facts. -/
theorem fetchInd_erfolg (s : Zustand) (fenster : List Byte)
    (i : IndForm) (rest : List Byte)
    (h : fetchInd s fenster = some (i, rest)) :
    decodeIndirekt fenster = some (i, rest) ∧
      indLen i + rest.length = fenster.length ∧
      laengeOk (indLen i) = true ∧
      ausfuehrbarN s.speicher s.rip (indLen i) = true := by
  have e : fetchInd s fenster =
      match decodeIndirekt fenster with
      | none => (none : Option (IndForm × List Byte))
      | some p =>
        if indZugelassen s fenster p.1 p.2 then some p else none := rfl
  rw [e] at h
  cases hdec : decodeIndirekt fenster with
  | none =>
    simp [hdec] at h
  | some p =>
    rw [hdec] at h
    by_cases hz : indZugelassen s fenster p.1 p.2 = true
    · simp [hz] at h
      rw [h] at hz
      exact ⟨by rw [h],
        indZugelassen_summe s fenster _ _ hz,
        indZugelassen_laenge s fenster _ _ hz,
        indZugelassen_ausfuehrbar s fenster _ _ hz⟩
    · simp [hz] at h

/-- One byte step from actual memory: fetch, decode, then the form step.
    Takes ONLY the state: no caller-supplied form is trusted. -/
def indByteschritt (s : Zustand) : Option Zustand :=
  match fetchInd s (geholt s) with
  | none => none
  | some (i, _) => indSchritt i s

/-- A fetched form steps through the form step. -/
theorem indByteschritt_weiter (s : Zustand) (i : IndForm)
    (rest : List Byte) (s' : Zustand)
    (hf : fetchInd s (geholt s) = some (i, rest))
    (hs : indSchritt i s = some s') :
    indByteschritt s = some s' := by
  have e : indByteschritt s =
      match fetchInd s (geholt s) with
      | none => (none : Option Zustand)
      | some (j, _) => indSchritt j s := rfl
  rw [e, hf]
  exact hs

/-- Fetch refusal is byte-step refusal. -/
theorem indByteschritt_verweigert (s : Zustand)
    (hf : fetchInd s (geholt s) = none) :
    indByteschritt s = none := by
  have e : indByteschritt s =
      match fetchInd s (geholt s) with
      | none => (none : Option Zustand)
      | some (j, _) => indSchritt j s := rfl
  rw [e, hf]

/-- Validator admission for an indirect target: the decoded target must
    be a known instruction start or a listed entry. This `Bool` is
    compiler target provenance, NOT a hardware fault. -/
def indirektZielOk (starts eintraege : List Adresse)
    (ziel : Adresse) : Bool :=
  decide (ziel ∈ starts ++ eintraege)

/-- ADMISSION GUARANTEE: an admitted indirect target is a decoded
    instruction start or a listed entry. -/
theorem indirektZielOk_garantiert (starts eintraege : List Adresse)
    (ziel : Adresse)
    (h : indirektZielOk starts eintraege ziel = true) :
    ziel ∈ starts ∨ ziel ∈ eintraege := by
  unfold indirektZielOk at h
  rw [decide_eq_true_eq] at h
  rw [List.mem_append] at h
  exact h

/-- SEPARATION (unadmitted still executes): provenance refusal is not a
    hardware fault — the register-indirect call below steps although its
    target is admitted nowhere. -/
theorem zielOhneHerkunft_fuehrt_aus :
    indirektZielOk [BitVec.ofNat 64 4096] [] (BitVec.ofNat 64 4200) =
      false ∧
    callRegSchritt 2 zeugeZustand Register.rbx ≠ none := by
  refine ⟨by decide, ?_⟩
  have hok : laengeOk 2 = true := by decide
  have hschr : schreibbar8 zeugeZustand.speicher
      (zeugeZustand.register Register.rsp - BitVec.ofNat 64 8) = true := by
    decide
  have hwr : write64 zeugeZustand.speicher
      (zeugeZustand.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach zeugeZustand.rip 2) =
      some { zeugeZustand.speicher with
        bytes := writeBytes zeugeZustand.speicher
          (zeugeZustand.register Register.rsp - BitVec.ofNat 64 8)
          (ripNach zeugeZustand.rip 2) } := by
    unfold write64
    rw [if_pos hschr]
  rw [callRegSchritt_erfolg 2 zeugeZustand Register.rbx _ hok hwr]
  exact Option.some_ne_none _

/-- RET stays with the pilot: our decoder refuses `C3` over any suffix. -/
theorem unser_verweigert_ret (suffix : List Byte) :
    decodeIndirekt (encode .ret ++ suffix) = none := by
  simp [encode, decodeIndirekt,
    byteNat_natByte_of_lt 195 (by decide)]

/-- Our decoder refuses direct `call32` bytes over any suffix. -/
theorem unser_verweigert_call32 (d : BitVec 32) (suffix : List Byte) :
    decodeIndirekt (encode (.call32 d) ++ suffix) = none := by
  have h232 : byteNat (natByte 232) = 232 :=
    byteNat_natByte_of_lt 232 (by decide)
  simp [encode, decodeIndirekt, h232]

/-- Our decoder refuses direct `jump32` bytes over any suffix. -/
theorem unser_verweigert_jump32 (d : BitVec 32) (suffix : List Byte) :
    decodeIndirekt (encode (.jump32 d) ++ suffix) = none := by
  have h233 : byteNat (natByte 233) = 233 :=
    byteNat_natByte_of_lt 233 (by decide)
  simp [encode, decodeIndirekt, h233]

/-- The pilot refuses every register-indirect byte string over any
    suffix: no existing form is reinterpreted. -/
theorem pilot_verweigert_indReg (isCall : Bool) (tgt : Register)
    (suffix : List Byte) :
    decode (encodeIndReg isCall tgt ++ suffix) = none := by
  cases tgt <;> cases isCall <;>
    simp [encodeIndReg, regHigh, regCode, decode]

/-- The pilot refuses every memory-indirect byte string over any suffix. -/
theorem pilot_verweigert_indMem (isCall : Bool) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    decode (encodeIndMem isCall base d ++ suffix) = none := by
  cases base <;> cases isCall <;>
    simp [encodeIndMem, regLow, regCode, regHigh, modrmMem, decode,
      decodeRex]

/-- The pilot refuses every short-branch byte string over any suffix
    (short forms are not canonical pilot: `decode_nichts_kurzsprung`). -/
theorem pilot_verweigert_kurz (d8 : Byte) (suffix : List Byte) :
    decode (encodeJmpKurz d8 ++ suffix) = none := by
  simp [encodeJmpKurz, decode,
    byteNat_natByte_of_lt 235 (by decide)]

/-- The pilot refuses every short-conditional byte string over any
    suffix: the `70-7F` range is no pilot opcode. -/
theorem pilot_verweigert_jccKurz (c : Bedingung) (d8 : Byte)
    (suffix : List Byte) :
    decode (encodeJccKurz c d8 ++ suffix) = none := by
  cases c <;> simp [encodeJccKurz, decode, condCode]

/-! ## 8. Decoder/byte-step adapter for consumers 660/670.

    The adapter tries the pilot FIRST and falls through to the indirect
    decoder only where the pilot refuses (pilot-first dispatch, proved
    disjoint above). It imports no unmerged draft: both producers are
    accepted (`Codec.decode`, `decodeIndirekt` here). Address consumers
    use the accepted `EffectiveAddress` vocabulary (`effAddr`); wider
    essential memory encodings (SIB scales, RIP-relative, mod=0/1) remain
    OPEN (see CUTS). -/

/-- Adapted instruction: a pilot form or an indirect/compact form. -/
inductive IndAdaptiert where
  | pilot : Decodiert → IndAdaptiert
  | indirekt : IndForm → IndAdaptiert
  deriving DecidableEq, Repr

/-- Pilot-first dispatch: the pilot decoder first, the indirect decoder
    only where the pilot refuses. -/
def indAdapterDecode (bs : List Byte) :
    Option (IndAdaptiert × List Byte) :=
  match decode bs with
  | some (d, rest) => some (.pilot d, rest)
  | none =>
    match decodeIndirekt bs with
    | some (i, rest) => some (.indirekt i, rest)
    | none => none

/-- Pilot agreement: whatever the pilot accepts keeps its meaning. -/
theorem indAdapter_pilot (bs : List Byte) (d : Decodiert)
    (rest : List Byte) (h : decode bs = some (d, rest)) :
    indAdapterDecode bs = some ((.pilot d), rest) := by
  unfold indAdapterDecode
  rw [h]

/-- Indirect fall-through: where the pilot refuses and our decoder
    accepts, the adapter selects the indirect form. -/
theorem indAdapter_indirekt (bs : List Byte) (i : IndForm)
    (rest : List Byte) (hpilot : decode bs = none)
    (hdec : decodeIndirekt bs = some (i, rest)) :
    indAdapterDecode bs = some ((.indirekt i), rest) := by
  unfold indAdapterDecode
  rw [hpilot, hdec]

/-- Canonical register-indirect call bytes dispatch to the call form. -/
theorem indAdapter_callReg_bytes (tgt : Register) (suffix : List Byte) :
    indAdapterDecode (encodeIndReg true tgt ++ suffix) =
      some ((.indirekt (.callReg tgt (2 + regHigh tgt))), suffix) :=
  indAdapter_indirekt _ _ _ (pilot_verweigert_indReg true tgt suffix)
    (roundtrip_indReg_call tgt suffix)

/-- Canonical short-conditional bytes dispatch to the compact form. -/
theorem indAdapter_jccKurz_bytes (c : Bedingung) (d8 : Byte)
    (suffix : List Byte) :
    indAdapterDecode (encodeJccKurz c d8 ++ suffix) =
      some ((.indirekt (.jccKurz c d8)), suffix) :=
  indAdapter_indirekt _ _ _ (pilot_verweigert_jccKurz c d8 suffix)
    (roundtrip_jccKurz c d8 suffix)

/-! ## 9. Pinned bytes and decode-level refusals.

    Every fact below is a closed machine-byte computation (`decide`):
    high-register indirect calls, the RSP/SIB memory shape, short-branch
    pins, far-extension (`/3`) refusal, wrong-REX refusal (REX.R set,
    REX.W on a register form), counter-family (`E3`) refusal, truncated
    displacement refusal, non-canonical mode (`mod=0`) refusal. -/

/-- PIN: register-indirect call through `rbx` is `FF D3`. -/
theorem pin_callReg_rbx :
    encodeIndReg true .rbx = [natByte 255, natByte 211] := by
  decide

/-- PIN: it decodes to the `rbx` call form with length 2. -/
theorem pin_callReg_rbx_dekode :
    decodeIndirekt [natByte 255, natByte 211] =
      some (((.callReg .rbx 2)), []) := by
  decide

/-- PIN: register-indirect call through high register `r9` carries
    `REX.B` (`41 FF D1`). -/
theorem pin_callReg_r9 :
    encodeIndReg true .r9 =
      [natByte 65, natByte 255, natByte 209] := by
  decide

/-- PIN: it decodes to the `r9` call form with length 3. -/
theorem pin_callReg_r9_dekode :
    decodeIndirekt [natByte 65, natByte 255, natByte 209] =
      some (((.callReg .r9 3)), []) := by
  decide

/-- PIN: memory-indirect jump through `rsp` needs the SIB byte
    (`REX.W FF /4` mod=2 plus `24` plus disp32). -/
theorem pin_jmpMem_rsp :
    encodeIndMem false .rsp (BitVec.ofNat 32 16) =
      [natByte 72, natByte 255, natByte 164, natByte 36,
        natByte 16, natByte 0, natByte 0, natByte 0] := by
  decide

/-- PIN: short unconditional `+16` is `EB 10`. -/
theorem pin_jmpKurz :
    encodeJmpKurz (natByte 16) = [natByte 235, natByte 16] := by
  rfl

/-- PIN: short conditional `e +16` is `74 10`. -/
theorem pin_jccKurz_e :
    encodeJccKurz .e (natByte 16) = [natByte 116, natByte 16] := by
  rfl

/-- REFUSAL: far-call extension `/3` is no near form. -/
theorem far_erweiterung_verweigert :
    decodeIndirekt [natByte 255, natByte 216] = none := by
  decide

/-- REFUSAL: a REX with the R bit set (`4C`) is outside the profile. -/
theorem rexR_verweigert :
    decodeIndirekt [natByte 76, natByte 255, natByte 211] = none := by
  decide

/-- REFUSAL: `REX.W` on a register-direct form is outside the profile
    (register indirect is bare-`FF` or `REX.B` only). -/
theorem rexW_auf_register_verweigert :
    decodeIndirekt [natByte 72, natByte 255, natByte 211] = none := by
  decide

/-- REFUSAL: the counter family (`E3`, `JRCXZ`) has no compact arm. -/
theorem zaehler_verweigert :
    decodeIndirekt [natByte 227, natByte 5] = none := by
  decide

/-- REFUSAL: truncated short branch (opcode alone). -/
theorem kurz_abgeschnitten_verweigert :
    decodeIndirekt ((encodeJmpKurz (natByte 5)).take 1) = none := by
  decide

/-- REFUSAL: truncated memory displacement (five of seven bytes). -/
theorem mem_abgeschnitten_verweigert :
    decodeIndirekt
      ((encodeIndMem true .rax (BitVec.ofNat 32 0)).take 5) = none := by
  decide

/-- REFUSAL: non-canonical `mod=0` memory shape has no arm. -/
theorem modus0_verweigert :
    decodeIndirekt [natByte 255, natByte 16] = none := by
  decide

/-- REFUSAL: the empty input decodes to nothing. -/
theorem indirekt_leer_verweigert :
    decodeIndirekt [] = none :=
  rfl

/-! ## 10. Reached fetched witness: indirect call, callee store, return.

    Closed concrete machine: `CALL rbx` (`FF D3`, 2 bytes) at 4096 with
    `rbx = 4200`; the callee at 4200 is the pilot
    `store [rcx], rax` (7 bytes, `rcx = 8192`, `rax = 42`) followed by
    `ret` (`C3`) at 4207. Stack top 8192; data/stack 8176..8208
    read/write; code windows execute-only. Every `write64 ... = some`
    fact below is closed by unfolding plus the decided permission fact
    (no `Speicher` equality is ever decided: `rfl` closes definitional
    ones, never a claim about silicon). -/

/-- Witness code bytes: `FF D3` at 4096, pilot store at 4200, `C3`. -/
def indCodeBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 255
  else if a.toNat = 4097 then natByte 211
  else if a.toNat = 4200 then natByte 72
  else if a.toNat = 4201 then natByte 137
  else if a.toNat = 4202 then natByte 129
  else if a.toNat = 4203 then natByte 0
  else if a.toNat = 4204 then natByte 0
  else if a.toNat = 4205 then natByte 0
  else if a.toNat = 4206 then natByte 0
  else if a.toNat = 4207 then natByte 195
  else BitVec.ofNat 8 0

/-- Witness execute permission: the 2-byte call window and the 8-byte
    callee window. -/
def indExec (a : Adresse) : Bool :=
  decide ((4096 ≤ a.toNat ∧ a.toNat < 4098) ∨
    (4200 ≤ a.toNat ∧ a.toNat < 4208))

/-- Witness data/stack permission: 8176..8208 readable and writable. -/
def indDaten (a : Adresse) : Bool :=
  decide (8176 ≤ a.toNat ∧ a.toNat < 8208)

/-- Witness memory: code execute-only, data/stack read/write-only. -/
def indSpeicher : Speicher :=
  { bytes := indCodeBytes
    lesbar := indDaten
    schreibbar := indDaten
    ausfuehrbar := indExec }

/-- Witness registers: `rax = 42`, `rbx = 4200`, `rcx = 8192`,
    stack top 8192. -/
def indReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 42
  else if q = Register.rbx then BitVec.ofNat 64 4200
  else if q = Register.rcx then BitVec.ofNat 64 8192
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness start: indirect call at 4096, stack top at 8192. -/
def indS0 : Zustand :=
  { register := indReg
    flags := zeugeFlags
    rip := BitVec.ofNat 64 4096
    speicher := indSpeicher }

/-- Memory after the call: return word 4098 below the old top. -/
def indM1 : Speicher :=
  { indSpeicher with
    bytes := writeBytes indSpeicher (BitVec.ofNat 64 8184)
      (BitVec.ofNat 64 4098) }

/-- State after the fetched indirect call: control at 4200. -/
def indS1 : Zustand :=
  schrittCall indS0 Register.rsp indM1
    (indS0.register Register.rsp - BitVec.ofNat 64 8)
    (indS0.register Register.rbx)

/-- CALL-SITE FETCH: the actual 2 bytes at 4096 are the canonical
    `CALL rbx` encoding with nothing after. -/
theorem indS0_fetch :
    fetchInd indS0 (geholt indS0) =
      some (((.callReg Register.rbx 2)), []) := by
  decide

/-- The call installs the post-decode address 4098 below the old top. -/
theorem indS0_schreibt :
    write64 indSpeicher (BitVec.ofNat 64 8184)
      (BitVec.ofNat 64 4098) = some indM1 := by
  unfold write64 indM1
  rw [if_pos (by decide : schreibbar8 indSpeicher
    (BitVec.ofNat 64 8184) = true)]

/-- FETCHED INDIRECT CALL: from actual bytes, the byte step stores the
    next-RIP word and transfers control to the register word. -/
theorem indS0_schritt : indByteschritt indS0 = some indS1 := by
  have hf : fetchInd indS0 (geholt indS0) =
      some (((.callReg Register.rbx 2)), []) :=
    indS0_fetch
  have hschr : schreibbar8 indS0.speicher
      (indS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
    decide
  have hwr : write64 indS0.speicher
      (indS0.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach indS0.rip 2) = some indM1 := by
    unfold write64 indM1
    rw [if_pos hschr]
    rfl
  have hok : laengeOk 2 = true := by decide
  have hs : indSchritt (.callReg Register.rbx 2) indS0 = some indS1 := by
    have e := callRegSchritt_erfolg 2 indS0 Register.rbx indM1 hok hwr
    unfold indSchritt indS1
    exact e
  exact indByteschritt_weiter indS0 _ _ _ hf hs

/-- Memory after the callee store: data word 42 at 8192. -/
def indM2 : Speicher :=
  { indM1 with
    bytes := writeBytes indM1 (BitVec.ofNat 64 8192)
      (BitVec.ofNat 64 42) }

/-- State after the fetched callee store (pilot, length 7). -/
def indS2 : Zustand :=
  { indS1 with speicher := indM2, rip := ripNach indS1.rip 7 }

/-- CALLEE FETCH: the actual bytes at 4200 are the canonical pilot
    store followed by the `ret` byte. -/
theorem indS1_fetch :
    fetchDekodiert indS1 =
      some ((⟨.store64 Register.rcx Register.rax
        (BitVec.ofNat 32 0), 7⟩), [natByte 195]) := by
  decide

/-- FETCHED CALLEE STORE: the reached callee stores 42 at 8192. -/
theorem indS1_schritt : byteschritt indS1 = .weiter indS2 := by
  have hf := indS1_fetch
  have hschr : schreibbar8 indS1.speicher
      (effAddr indS1 Register.rcx (BitVec.ofNat 32 0)) = true := by
    decide
  have hwr : write64 indS1.speicher
      (effAddr indS1 Register.rcx (BitVec.ofNat 32 0))
      (indS1.register Register.rax) = some indM2 := by
    unfold write64 indM2
    rw [if_pos hschr]
    rfl
  have hok : laengeOk 7 = true := by decide
  have hs : schritt (⟨.store64 Register.rcx Register.rax
      (BitVec.ofNat 32 0), 7⟩ : Decodiert) indS1 = some indS2 := by
    have e := schritt_store64_erfolg
      (⟨.store64 Register.rcx Register.rax
        (BitVec.ofNat 32 0), 7⟩ : Decodiert)
      indS1 Register.rcx
      Register.rax (BitVec.ofNat 32 0) indM2 hok rfl hwr
    unfold indS2
    exact e
  exact byteschritt_weiter _ _ _ _ hf hs

/-- State after the fetched return: control back at 4098. -/
def indS3 : Zustand :=
  schrittRet indS2 Register.rsp
    (indS2.register Register.rsp + BitVec.ofNat 64 8)
    (ripNach indS0.rip 2)

/-- RETURN FETCH: the actual byte at 4207 is the canonical `ret`. -/
theorem indS2_fetch :
    fetchDekodiert indS2 = some ((⟨.ret, 1⟩), []) := by
  decide

/-- The stored return address reads back at the outer slot. -/
theorem indS2_liest :
    read64 indS2.speicher (indS2.register Register.rsp) =
      some (ripNach indS0.rip 2) := by
  decide

/-- FETCHED RETURN: control moves to the popped next-RIP word. -/
theorem indS2_schritt : byteschritt indS2 = .weiter indS3 := by
  have hf := indS2_fetch
  have hok : laengeOk 1 = true := by decide
  have hs : schritt (⟨.ret, 1⟩ : Decodiert) indS2 = some indS3 := by
    have e := schritt_ret_erfolg (⟨.ret, 1⟩ : Decodiert) indS2
      (ripNach indS0.rip 2)
      hok rfl indS2_liest
    unfold indS3
    exact e
  exact byteschritt_weiter _ _ _ _ hf hs

/-- JOINT WITNESS (fetched indirect call, callee store, return): the
    three byte steps chain from actual executable bytes; the stack slot
    observably changed (zero to return word 4098), the data cell changed
    (zero to 42) and reads back; the stack pointer is restored and
    control lands on the correct next-RIP word; the callee start is an
    admitted decoded start. -/
theorem indKette_zeuge :
    indByteschritt indS0 = some indS1 ∧
    byteschritt indS1 = .weiter indS2 ∧
    byteschritt indS2 = .weiter indS3 ∧
    indS3.rip = BitVec.ofNat 64 4098 ∧
    indS3.register Register.rsp = BitVec.ofNat 64 8192 ∧
    read64 indS3.speicher (BitVec.ofNat 64 8192) = some 42 ∧
    indSpeicher.bytes (BitVec.ofNat 64 8184) =
      BitVec.ofNat 8 0 ∧
    indM1.bytes (BitVec.ofNat 64 8184) ≠
      indSpeicher.bytes (BitVec.ofNat 64 8184) ∧
    indirektZielOk [BitVec.ofNat 64 4200] []
      (BitVec.ofNat 64 4200) = true := by
  refine ⟨indS0_schritt, indS1_schritt, indS2_schritt, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ## 11. Short-branch witnesses and the RSP-based memory call.

    Taken (`e +16` with `zf`) lands at post-decode plus 16; untaken
    falls through. The memory-indirect call below reads its target
    through the RSP base at the pre-instruction top (`rsp + 0`), the
    shape the manual calls out for `[ESP]`-based operands. -/

/-- Short-branch code bytes: `74 10` (`e +16`) at 4096. -/
def kurzBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 116
  else if a.toNat = 4097 then natByte 16
  else BitVec.ofNat 8 0

/-- Short-branch execute permission: exactly the 2-byte window. -/
def kurzExec (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4098)

/-- Short-branch memory: code execute-only, data inert. -/
def kurzSpeicher : Speicher :=
  { bytes := kurzBytes
    lesbar := fun _ => false
    schreibbar := fun _ => false
    ausfuehrbar := kurzExec }

/-- Short-branch state over the given flag snapshot. -/
def kurzS (fl : Flags) : Zustand :=
  { register := fun _ => BitVec.ofNat 64 0
    flags := fl
    rip := BitVec.ofNat 64 4096
    speicher := kurzSpeicher }

/-- TAKEN: `e +16` with the zero flag set lands at 4114. -/
theorem kurz_genommen :
    (indByteschritt (kurzS witFlagsTrue)).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4114) := by
  decide

/-- UNTAKEN: `e +16` with the zero flag clear falls to 4098. -/
theorem kurz_nicht :
    (indByteschritt (kurzS witFlagsFalse)).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4098) := by
  decide

/-- JOINT taken/not-taken witness: both flag snapshots fetch the same
    2 bytes and observably diverge, with the memory-changing call chain
    beside them. -/
theorem kurz_zeuge :
    (indByteschritt (kurzS witFlagsTrue)).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4114) ∧
    (indByteschritt (kurzS witFlagsFalse)).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4098) ∧
    read64 indS3.speicher (BitVec.ofNat 64 8192) = some 42 := by
  exact ⟨kurz_genommen, kurz_nicht, indKette_zeuge.2.2.2.2.2.1⟩

/-- Memory-call code bytes: `REX.W FF /2` mod=2 through `rsp`,
    SIB `24`, disp32 0 (8 bytes) at 4096. -/
def memCallBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 72
  else if a.toNat = 4097 then natByte 255
  else if a.toNat = 4098 then natByte 148
  else if a.toNat = 4099 then natByte 36
  else if a.toNat = 4100 then natByte 0
  else if a.toNat = 4101 then natByte 0
  else if a.toNat = 4102 then natByte 0
  else if a.toNat = 4103 then natByte 0
  else if a.toNat = 8200 then natByte 104
  else if a.toNat = 8201 then natByte 16
  else if a.toNat = 8202 then natByte 0
  else if a.toNat = 8203 then natByte 0
  else if a.toNat = 8204 then natByte 0
  else if a.toNat = 8205 then natByte 0
  else if a.toNat = 8206 then natByte 0
  else if a.toNat = 8207 then natByte 0
  else BitVec.ofNat 8 0

/-- Memory-call execute permission: exactly the 8-byte window. -/
def memCallExec (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4104)

/-- Memory-call data/stack permission: 8184..8208. -/
def memCallDaten (a : Adresse) : Bool :=
  decide (8184 ≤ a.toNat ∧ a.toNat < 8208)

/-- Memory-call memory: the target word 4200 sits at 8200
    (`0x1068` little-endian). -/
def memCallSpeicher : Speicher :=
  { bytes := memCallBytes
    lesbar := memCallDaten
    schreibbar := memCallDaten
    ausfuehrbar := memCallExec }

/-- Memory-call start: stack top 8200, so `rsp + 0` is the target cell. -/
def memS0 : Zustand :=
  { register := fun q =>
      if q = Register.rsp then BitVec.ofNat 64 8200
      else BitVec.ofNat 64 0
    flags := zeugeFlags
    rip := BitVec.ofNat 64 4096
    speicher := memCallSpeicher }

/-- RSP FETCH: the actual 8 bytes decode to the `rsp`-based call. -/
theorem memS0_fetch :
    fetchInd memS0 (geholt memS0) =
      some (((.callMem Register.rsp (BitVec.ofNat 32 0) 8)), []) := by
  decide

/-- The RSP base reads the pre-instruction top: `rsp + 0 = 8200`. -/
theorem memS0_adresse :
    effAddr memS0 Register.rsp (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 8200 := by
  decide

/-- The target word reads back as 4200. -/
theorem memS0_liest :
    read64 memS0.speicher
      (effAddr memS0 Register.rsp (BitVec.ofNat 32 0)) =
      some (BitVec.ofNat 64 4200) := by
  decide

/-- Memory after the RSP-based call: return word 4104 at 8192. -/
def memM1 : Speicher :=
  { memCallSpeicher with
    bytes := writeBytes memCallSpeicher (BitVec.ofNat 64 8192)
      (BitVec.ofNat 64 4104) }

/-- State after the RSP-based call: control at the read word 4200. -/
def memS1 : Zustand :=
  schrittCall memS0 Register.rsp memM1
    (memS0.register Register.rsp - BitVec.ofNat 64 8)
    (BitVec.ofNat 64 4200)

/-- FETCHED RSP-BASED CALL: target read first, return store second. -/
theorem memS0_schritt : indByteschritt memS0 = some memS1 := by
  have hf := memS0_fetch
  have hschr : schreibbar8 memS0.speicher
      (memS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
    decide
  have hwr : write64 memS0.speicher
      (memS0.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach memS0.rip 8) = some memM1 := by
    unfold write64 memM1
    rw [if_pos hschr]
    rfl
  have hok : laengeOk 8 = true := by decide
  have hs : indSchritt
      (.callMem Register.rsp (BitVec.ofNat 32 0) 8) memS0 =
      some memS1 := by
    have e := callMemSchritt_erfolg 8 memS0 Register.rsp
      (BitVec.ofNat 32 0) (BitVec.ofNat 64 4200) memM1 hok
      memS0_liest hwr
    unfold indSchritt memS1
    exact e
  exact indByteschritt_weiter memS0 _ _ _ hf hs

/-- JOINT WITNESS (RSP-based memory call): fetch, pre-state RSP read,
    target value, return store with read-back and observed change. -/
theorem memCall_zeuge :
    indByteschritt memS0 = some memS1 ∧
    memS1.rip = BitVec.ofNat 64 4200 ∧
    read64 memS1.speicher (BitVec.ofNat 64 8192) =
      some (BitVec.ofNat 64 4104) ∧
    memCallSpeicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 ∧
    memM1.bytes (BitVec.ofNat 64 8192) ≠
      memCallSpeicher.bytes (BitVec.ofNat 64 8192) := by
  refine ⟨memS0_schritt, by decide, by decide, by decide, by decide⟩

/-! ## 12. Execution-level refusals: guard, data target, overlap.

    A guarded stack refuses the fetched call (loud `none`, never a
    silent fallthrough); a jump into data executes at step level but
    the FOLLOWING fetch refuses (the architectural execute gate, not
    provenance); a store into the code window changes the fetched
    window (no fetch preservation across overlap). -/

/-- Guard memory: same code bytes, nothing writable. -/
def wacheSpeicher : Speicher :=
  { indSpeicher with schreibbar := fun _ => false }

/-- Guard start: indirect call at 4096, stack top at 8192. -/
def wacheS : Zustand :=
  { indS0 with speicher := wacheSpeicher }

/-- GUARD FETCH: code bytes and execute rights are kept, so the actual
    call bytes still fetch. -/
theorem wache_fetch :
    fetchInd wacheS (geholt wacheS) =
      some (((.callReg Register.rbx 2)), []) := by
  decide

/-- The stack slot below the top is guard-protected. -/
theorem wache_guard :
    schreibbar8 wacheS.speicher
      (wacheS.register Register.rsp - BitVec.ofNat 64 8) = false := by
  decide

/-- GUARD REFUSAL: the fetched call loudly refuses at the store. -/
theorem wache_ruf_verweigert : indByteschritt wacheS = none := by
  have hf := wache_fetch
  have hs : indSchritt (.callReg Register.rbx 2) wacheS = none := by
    have hok : laengeOk 2 = true := by decide
    have hwr : write64 wacheS.speicher
        (wacheS.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach wacheS.rip 2) = none :=
      write64_verweigert _ _ _ wache_guard
    unfold indSchritt
    exact callRegSchritt_verweigert 2 wacheS Register.rbx hok hwr
  unfold indByteschritt
  rw [hf]
  exact hs

/-- A register-indirect jump into DATA executes at step level
    (provenance is not a step gate) but lands where nothing executes. -/
theorem daten_sprung_aber_fetch_verweigert :
    indSchritt (.jmpReg Register.rcx 2) indS0 =
      some ({ indS0 with rip := BitVec.ofNat 64 8192 }) ∧
    indByteschritt { indS0 with rip := BitVec.ofNat 64 8192 } =
      none := by
  have hok : laengeOk 2 = true := by decide
  have hreg : indS0.register Register.rcx = BitVec.ofNat 64 8192 := by
    decide
  have hs : jmpRegSchritt 2 indS0 Register.rcx =
      some ({ indS0 with rip := BitVec.ofNat 64 8192 }) := by
    unfold jmpRegSchritt
    rw [hok, hreg]
  refine ⟨by simpa [indSchritt] using hs, ?_⟩
  have hg : geholt { indS0 with rip := BitVec.ofNat 64 8192 } = [] := by
    decide
  have hf : fetchInd { indS0 with rip := BitVec.ofNat 64 8192 }
      (geholt { indS0 with rip := BitVec.ofNat 64 8192 }) = none := by
    rw [hg]
    rfl
  exact indByteschritt_verweigert _ hf

/-- Writable-code start: the call bytes with universal write rights. -/
def codeS0 : Zustand :=
  { indS0 with
    speicher := { indSpeicher with schreibbar := fun _ => true } }

/-- Memory after a code write: first code byte zeroed (8-byte word). -/
def codeM : Speicher :=
  { codeS0.speicher with
    bytes := writeBytes codeS0.speicher (BitVec.ofNat 64 4096)
      (BitVec.ofNat 64 0) }

/-- OVERLAP: a store into the code window is a real write, the fetched
    window observably changes, and the call form no longer fetches. -/
theorem codeSchreib_ueberlappt :
    write64 codeS0.speicher (BitVec.ofNat 64 4096)
        (BitVec.ofNat 64 0) = some codeM ∧
    fetchInd codeS0 (geholt codeS0) =
      some (((.callReg Register.rbx 2)), []) ∧
    fetchInd { codeS0 with speicher := codeM }
        (geholt { codeS0 with speicher := codeM }) = none ∧
    geholt { codeS0 with speicher := codeM } ≠ geholt codeS0 := by
  have hschr : schreibbar8 codeS0.speicher
      (BitVec.ofNat 64 4096) = true := by
    decide
  have hwr : write64 codeS0.speicher (BitVec.ofNat 64 4096)
      (BitVec.ofNat 64 0) = some codeM := by
    unfold write64 codeM
    rw [if_pos hschr]
  refine ⟨hwr, by decide, by decide, by decide⟩

/- CUTS:
    Manual provenance (checked clone-locally, no network): Intel SDM
    combined volumes 1-4, edition 325462-093US (September 2026),
    `.tmp/HARDWARE-REFERENCES/` (`REFERENCES.json`, verified
    2026-10-02; AMD retrieval failed, no AMD claim). Headings read:
    Vol.2A Ch.3 `CALL-Call Procedure` (`FF /2 CALL r/m64`, near-call
    absolute operation incl. the `[ESP]` pre-value rule, p.3-121),
    `JMP-Jump` (`FF /4 JMP r/m64`, `EB cb JMP rel8`, pp.3-504-3-505),
    `Jcc-Jump if Condition Is Met` (`70+cc cb` rel8 table, short-jump
    operation `RIP = RIP + 8-bit offset sign extended to 64 bits`,
    pp.3-499/3-502), Vol.2B `RET-Return From Procedure` (`C3` near,
    p.4-569), Vol.1 6.4.1 near CALL/RET (push next-RIP, branch).
    Proved here (all over the REUSED `Codec` byte helpers, the REUSED
    `Ausfuehrung` constructors `schrittCall`/`schrittRet`, the REUSED
    permission-checked `read64`/`write64` and the REUSED `effAddr`:
    no pilot file touched, no second interpreter, no second address
    model):
    - selected-profile canonical bytes (`FF /2` call, `FF /4` jump,
      register-direct mod=3 bare or `REX.B`, checked memory mod=2
      `REX.W` base+disp32 with SIB `0x24` exactly where the pilot
      requires it, `EB cb`, `70+cond cb`) with generic round trips
      (decoded length is the consumed prefix: 2/3, 7/8, 2, 2);
    - execution reusing the accepted constructors (return word is
      ALWAYS `ripNach` of the pre-state RIP; the stack slot is ALWAYS
      the pre-state `rsp` minus 8; the memory-indirect target is read
      FIRST from the pre-state effective address — including an RSP
      base at the pre-instruction top — then the return word is
      stored; faulting target reads refuse on every path);
    - fetched execution under the `Byteschritt` discipline
      (`fetchInd_erfolg`, `indByteschritt_weiter/verweigert`);
      validator admission (`indirektZielOk_garantiert`) kept SEPARATE
      from architectural gates (an unadmitted target still steps,
      `zielOhneHerkunft_fuehrt_aus`; a data target steps but its fetch
      refuses; `RET` stays pilot-owned);
    - pilot-first adapter (`indAdapterDecode` with agreement on both
      sides) for consumers 660/670 over accepted producers only;
      generic pilot-refusal of every new byte string and ours-refusal
      of direct call/jump/return bytes;
    - closed-byte pins (high-register `REX.B` call, RSP/SIB memory
      jump, short-branch bytes) and decode refusals (far `/3`,
      REX.R, REX.W-on-register, `E3` counter family, truncations,
      `mod=0`, empty);
    - joint non-degenerate witnesses with reached memory-changing
      runs from actual executable bytes (fetched indirect
      call/callee-store/return with changed stack AND data, restored
      `rsp`, correct next-RIP; RSP-based memory call reading the
      pre-state top; taken/untaken short branches diverging) and
      planted execution refusals (guarded stack, data-target fetch,
      code-store overlap changing the window).
    NOT proved here, and not claimed:
    - No hardware correspondence: byte shapes follow the manual rows
      above, checked here only as self-consistency (round trips,
      pins, refusals), not silicon; `#GP`/`#PF` exception codes are
      not modelled (permission `none` is the refusal vocabulary);
      timing, caches, TLBs, CET/shadow-stack and asynchronous effects
      are untouched.
    - No far forms, no `RET imm16`, no `JCXZ`/`JECXZ`/`JRCXZ`, no LOCK
      prefix, no REX.R/X/W variants outside the canonical rows: all
      refused by construction; hardware acceptance beyond the profile
      is explicitly OPEN, never silently admitted.
    - Actual essential memory-encoding coverage is OPEN where stated:
      only base+disp32 (mod=2, accepted `effAddr`) is admitted;
      scaled-index SIB, RIP-relative and mod=0/1 memory targets have
      no arm (consumer 664 owns addresses; this module uses the
      accepted `EffectiveAddress` vocabulary until 664 lands).
    - No source, IR, checker, emitter, contract, ABI, loader, entry,
      budget, cost or goal claim; no `Befehl` constructor is added.
    - No TSO/GX, concurrency, atomicity or tearing claim; every fact
      is sequential over one `Speicher`; absence of a transition is
      never a termination statement.
-/

#print axioms dispWort8_beispiel
#print axioms encodeIndReg_len
#print axioms encodeIndMem_len
#print axioms encodeKurz_len
#print axioms encodeJccKurz_len
#print axioms roundtrip_indReg_call
#print axioms roundtrip_indReg_jmp
#print axioms roundtrip_indMem_call
#print axioms roundtrip_indMem_jmp
#print axioms roundtrip_jmpKurz
#print axioms roundtrip_jccKurz
#print axioms decodeIndMemNach_ohneSIB
#print axioms callRegSchritt_erfolg
#print axioms callRegSchritt_verweigert
#print axioms callMemSchritt_erfolg
#print axioms callMemSchritt_lesefehler
#print axioms callMemSchritt_schreibfehler
#print axioms jmpRegSchritt_erfolg
#print axioms jmpMemSchritt_erfolg
#print axioms jmpMemSchritt_verweigert
#print axioms jmpKurzSchritt_erfolg
#print axioms jccKurzSchritt_genommen
#print axioms jccKurzSchritt_nicht
#print axioms indZugelassen_summe
#print axioms indZugelassen_laenge
#print axioms indZugelassen_ausfuehrbar
#print axioms fetchInd_erfolg
#print axioms indByteschritt_weiter
#print axioms indByteschritt_verweigert
#print axioms indirektZielOk_garantiert
#print axioms zielOhneHerkunft_fuehrt_aus
#print axioms unser_verweigert_ret
#print axioms unser_verweigert_call32
#print axioms unser_verweigert_jump32
#print axioms pilot_verweigert_indReg
#print axioms pilot_verweigert_indMem
#print axioms pilot_verweigert_kurz
#print axioms pilot_verweigert_jccKurz
#print axioms indAdapter_pilot
#print axioms indAdapter_indirekt
#print axioms indAdapter_callReg_bytes
#print axioms indAdapter_jccKurz_bytes
#print axioms pin_callReg_rbx
#print axioms pin_callReg_rbx_dekode
#print axioms pin_callReg_r9
#print axioms pin_callReg_r9_dekode
#print axioms pin_jmpMem_rsp
#print axioms pin_jmpKurz
#print axioms pin_jccKurz_e
#print axioms far_erweiterung_verweigert
#print axioms rexR_verweigert
#print axioms rexW_auf_register_verweigert
#print axioms zaehler_verweigert
#print axioms kurz_abgeschnitten_verweigert
#print axioms mem_abgeschnitten_verweigert
#print axioms modus0_verweigert
#print axioms indirekt_leer_verweigert
#print axioms indS0_fetch
#print axioms indS0_schreibt
#print axioms indS0_schritt
#print axioms indS1_fetch
#print axioms indS1_schritt
#print axioms indS2_fetch
#print axioms indS2_liest
#print axioms indS2_schritt
#print axioms indKette_zeuge
#print axioms kurz_genommen
#print axioms kurz_nicht
#print axioms kurz_zeuge
#print axioms memS0_fetch
#print axioms memS0_adresse
#print axioms memS0_liest
#print axioms memS0_schritt
#print axioms memCall_zeuge
#print axioms wache_fetch
#print axioms wache_guard
#print axioms wache_ruf_verweigert
#print axioms daten_sprung_aber_fetch_verweigert
#print axioms codeSchreib_ueberlappt

end Gabbro.Grammatik.X86
