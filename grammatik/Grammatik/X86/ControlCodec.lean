/-
  File:      Grammatik/X86/ControlCodec.lean
  Subject:   Canonical bytes for register-only SETcc / CMOVcc over the
              accepted ControlFlow/ConditionalMove evaluators.

  Lane 566 (connection): the pilot `Befehl` has no conditional-select
  constructor and `Codec.decode` refuses every non-canonical byte, so the
  accepted `setCCAnwenden` / `cmovAnwenden` evaluators had no byte path.
  This module adds the selected-profile byte path WITHOUT touching the
  pilot: new canonical encodings (SETcc `REX 0F 90+cc /0 mod=3`, CMOVcc
  `REX.W 0F 40+cc /r mod=3`), decoders parsing REX/condition/ModRM and
  the actual length, and steps reusing the accepted evaluators. Memory
  CMOV and indirect targets have no decoder arm (refused by
  construction). Pilot bytes keep decoding through `Codec.decode`.
-/
import Grammatik.X86.Codec
import Grammatik.X86.ConditionalMove

namespace Gabbro.Grammatik.X86

/-- SETcc second opcode byte: `0F 90+cc` (144 + condition code). -/
def setccSecond (c : Bedingung) : Nat := 144 + condCode c

/-- CMOVcc second opcode byte: `0F 40+cc` (64 + condition code). -/
def cmovSecond (c : Bedingung) : Nat := 64 + condCode c

/-- SETcc REX byte: W=0, R=0, X=0, B is the destination extension.
    The profile always emits REX so the low byte is uniformly
    spl/bpl/sil/dil/r8b-r15b (never ah/ch/dh/bh). -/
def setccRex (dst : Register) : Byte := natByte (64 + regHigh dst)

/-- CMOVcc REX.W byte: R is the destination extension, B the source. -/
def cmovRex (dst src : Register) : Byte :=
  natByte (72 + 4 * regHigh dst + regHigh src)

/-- Canonical SETcc bytes: `REX 0F 90+cc /0 mod=3` (4 bytes). -/
def encodeSetCC (c : Bedingung) (dst : Register) : List Byte :=
  [setccRex dst, natByte 15, natByte (setccSecond c),
    modrmReg 0 (regLow dst)]

/-- Canonical CMOVcc bytes: `REX.W 0F 40+cc /r mod=3` (4 bytes). -/
def encodeCmov (c : Bedingung) (dst src : Register) : List Byte :=
  [cmovRex dst src, natByte 15, natByte (cmovSecond c),
    modrmReg (regLow dst) (regLow src)]

/-! ## 1. SETcc decoder: REX / condition / ModRM / actual length.

    Only `REX 0F 90+cc /0 mod=3` is accepted: REX must be `0x40`/`0x41`
    (W=0, R=0, X=0), the ModRM mod field must be 3 (register-direct)
    and its reg field 0 (the `/0` opcode extension). -/

/-- Decode after the SETcc REX byte (`bBit` is its B extension). -/
def decodeSetCCNach (bBit : Nat) (p1 p2 m : Byte)
    (rest : List Byte) :
    Option ((Bedingung × Register) × List Byte) :=
  match byteNat p1 with
  | 15 =>
    let c := byteNat p2
    if 144 ≤ c ∧ c < 160 then
      match codeCond (c - 144) with
      | some cond =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        match byteNat m / 64 with
        | 3 =>
          if reg == 0 then
            match codeReg (bBit * 8 + rm) with
            | some dst => some ((cond, dst), rest)
            | none => none
          else none
        | _ => none
      | none => none
    else none
  | _ => none

/-- Decode canonical SETcc bytes, returning condition, destination
    and the remaining bytes. Anything else is refused with `none`. -/
def decodeSetCC : List Byte → Option ((Bedingung × Register) × List Byte)
  | r :: p1 :: p2 :: m :: rest =>
    match byteNat r with
    | 64 => decodeSetCCNach 0 p1 p2 m rest
    | 65 => decodeSetCCNach 1 p1 p2 m rest
    | _ => none
  | _ => none

/-- Round trip: canonical SETcc bytes decode to their condition and
    destination over any suffix. -/
theorem roundtrip_setCC (c : Bedingung) (dst : Register)
    (suffix : List Byte) :
    decodeSetCC (encodeSetCC c dst ++ suffix) =
      some ((c, dst), suffix) := by
  cases c <;> cases dst <;> rfl

/-- Canonical SETcc bytes are 4 long: the actual decoded length. -/
theorem encodeSetCC_len (c : Bedingung) (dst : Register) :
    (encodeSetCC c dst).length = 4 := rfl

/-- The actual SETcc length passes the decode-length guard. -/
theorem setccLaenge_ok (c : Bedingung) (dst : Register) :
    laengeOk (encodeSetCC c dst).length = true := by
  rw [encodeSetCC_len c dst]
  decide

/-! ## 2. CMOVcc decoder: REX.W / condition / ModRM / actual length.

    Only `REX.W 0F 40+cc /r mod=3` is accepted: REX must be
    `0x48+4*R+B` (W=1, X=0), the ModRM mod field must be 3
    (register-direct); the reg field is the destination, r/m the
    source (Intel `CMOVcc r, r/m` form). A memory source has no arm:
    it is refused by construction, so no fault speculation exists. -/

/-- Decode after the CMOVcc REX.W byte (`rBit`/`bBit` extensions). -/
def decodeCmovNach (rBit bBit : Nat) (p1 p2 m : Byte)
    (rest : List Byte) :
    Option ((Bedingung × Register × Register) × List Byte) :=
  match byteNat p1 with
  | 15 =>
    let c := byteNat p2
    if 64 ≤ c ∧ c < 80 then
      match codeCond (c - 64) with
      | some cond =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        match byteNat m / 64 with
        | 3 =>
          match codeReg (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
          | some dst, some src => some ((cond, dst, src), rest)
          | _, _ => none
        | _ => none
      | none => none
    else none
  | _ => none

/-- Decode canonical CMOVcc bytes, returning condition, destination,
    source and the remaining bytes. Anything else is refused. -/
def decodeCmov : List Byte → Option ((Bedingung × Register × Register) × List Byte)
  | r :: p1 :: p2 :: m :: rest =>
    match byteNat r with
    | 72 => decodeCmovNach 0 0 p1 p2 m rest
    | 73 => decodeCmovNach 0 1 p1 p2 m rest
    | 76 => decodeCmovNach 1 0 p1 p2 m rest
    | 77 => decodeCmovNach 1 1 p1 p2 m rest
    | _ => none
  | _ => none

-- Round trip over all 16 x 16 x 16 condition/register combinations
-- needs a larger heartbeat budget (same as the Codec pilot round trips).
set_option maxHeartbeats 4000000 in
/-- Round trip: canonical CMOVcc bytes decode to their condition,
    destination and source over any suffix. -/
theorem roundtrip_cmov (c : Bedingung) (dst src : Register)
    (suffix : List Byte) :
    decodeCmov (encodeCmov c dst src ++ suffix) =
      some ((c, dst, src), suffix) := by
  cases c <;> cases dst <;> cases src <;> rfl

/-- Canonical CMOVcc bytes are 4 long: the actual decoded length. -/
theorem encodeCmov_len (c : Bedingung) (dst src : Register) :
    (encodeCmov c dst src).length = 4 := rfl

/-- The actual CMOVcc length passes the decode-length guard. -/
theorem cmovLaenge_ok (c : Bedingung) (dst src : Register) :
    laengeOk (encodeCmov c dst src).length = true := by
  rw [encodeCmov_len c dst src]
  decide

/-! ## 3. Byte-level steps over the accepted evaluators.

    No new interpreter: `setccSchrittBytes` applies the accepted
    `setCCAnwenden`, `cmovSchrittBytes` applies the accepted
    `cmovAnwenden`; both add only the actual decoded-length RIP
    advance. `cmovSchrittBytes_gleich` shows the CMOVcc byte step IS
    the accepted `cmovSchritt` with the actual length carried in the
    reused `Decodiert` length field (which is all `cmovSchritt`
    reads). -/

/-- SETcc byte step: accepted application plus actual-length advance. -/
def setccSchrittBytes (len : Nat) (s : Zustand) (dst : Register)
    (c : Bedingung) : Option Zustand :=
  match laengeOk len with
  | false => none
  | true => some ({ setCCAnwenden s dst c with rip := ripNach s.rip len })

/-- CMOVcc byte step: accepted application plus actual-length advance. -/
def cmovSchrittBytes (len : Nat) (s : Zustand) (dst src : Register)
    (c : Bedingung) : Option Zustand :=
  match laengeOk len with
  | false => none
  | true => some ({ cmovAnwenden s dst src c with rip := ripNach s.rip len })

/-- The CMOVcc byte step is the accepted `cmovSchritt` with the actual
    decoded length: one semantics, not two. -/
theorem cmovSchrittBytes_gleich (len : Nat) (s : Zustand)
    (dst src : Register) (c : Bedingung) :
    cmovSchrittBytes len s dst src c =
      cmovSchritt ⟨.movReg64 dst src, len⟩ s dst src c := by
  unfold cmovSchrittBytes cmovSchritt
  cases laengeOk len <;> rfl

/-! ## 4. Actual value, register, flags and source-free frame.

    Value comes from the reused condition reader `bedingung` through
    the accepted evaluators; the frame (flags, memory, RIP, untouched
    registers) is proved per step. Memory is never read or written by
    either byte step: the frame is source-free. -/

/-- SETcc byte value: the destination takes the low-byte select over
    the pre-state flags, upper bits preserved. -/
theorem setccSchrittBytes_wert (len : Nat) (s s' : Zustand)
    (dst : Register) (c : Bedingung)
    (hok : laengeOk len = true)
    (hstep : setccSchrittBytes len s dst c = some s') :
    s'.register dst =
      setLowByte (s.register dst) (setCCByte c s.flags) := by
  unfold setccSchrittBytes at hstep
  rw [hok] at hstep
  cases hstep
  simp [setCCAnwenden, regSet]

/-- SETcc byte frame: flags and memory kept, RIP past the actual
    decoded bytes, every other register kept. -/
theorem setccSchrittBytes_rahmen (len : Nat) (s s' : Zustand)
    (dst : Register) (c : Bedingung)
    (hok : laengeOk len = true)
    (hstep : setccSchrittBytes len s dst c = some s') :
    s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
    s'.rip = ripNach s.rip len ∧
    ∀ (q : Register), q ≠ dst → s'.register q = s.register q := by
  unfold setccSchrittBytes at hstep
  rw [hok] at hstep
  cases hstep
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro q hq
  simp [setCCAnwenden, regSet, hq]

/-- CMOVcc byte value when taken: the destination takes the pre-state
    source word (reused accepted equation). -/
theorem cmovSchrittBytes_genommen (len : Nat) (s s' : Zustand)
    (dst src : Register) (c : Bedingung)
    (hok : laengeOk len = true)
    (hbed : bedingung c s.flags = true)
    (hstep : cmovSchrittBytes len s dst src c = some s') :
    s'.register dst = s.register src := by
  unfold cmovSchrittBytes at hstep
  rw [hok] at hstep
  cases hstep
  exact cmovAnwenden_genommen_wert s dst src c hbed

/-- CMOVcc byte value when untaken: the destination keeps its word. -/
theorem cmovSchrittBytes_nicht (len : Nat) (s s' : Zustand)
    (dst src : Register) (c : Bedingung)
    (hok : laengeOk len = true)
    (hbed : bedingung c s.flags = false)
    (hstep : cmovSchrittBytes len s dst src c = some s') :
    s'.register dst = s.register dst := by
  unfold cmovSchrittBytes at hstep
  rw [hok] at hstep
  cases hstep
  exact cmovAnwenden_nicht_wert s dst src c hbed

/-- CMOVcc byte frame: flags and memory kept, RIP past the actual
    decoded bytes, every other register kept. -/
theorem cmovSchrittBytes_rahmen (len : Nat) (s s' : Zustand)
    (dst src : Register) (c : Bedingung)
    (hok : laengeOk len = true)
    (hstep : cmovSchrittBytes len s dst src c = some s') :
    s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
    s'.rip = ripNach s.rip len ∧
    ∀ (q : Register), q ≠ dst → s'.register q = s.register q := by
  unfold cmovSchrittBytes at hstep
  rw [hok] at hstep
  cases hstep
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro q hq
  exact cmovAnwenden_fremd _ dst src q c hq

/-! ## 5. Decoded length is the consumed prefix length.

    A successful decode consumes exactly its four canonical bytes:
    the tail returned is the input tail. This ties the actual
    execution length (`pfx.length - rest.length = 4`) to decoding,
    never to an emitter note. -/

/-- A successful SETcc decode consumes exactly four bytes. -/
theorem decodeSetCC_laenge (c : Bedingung) (dst : Register)
    (pfx rest : List Byte)
    (hdec : decodeSetCC pfx = some ((c, dst), rest)) :
    pfx.length = 4 + rest.length := by
  cases pfx with
  | nil => simp [decodeSetCC] at hdec
  | cons r t =>
    cases t with
    | nil => simp [decodeSetCC] at hdec
    | cons p1 t =>
      cases t with
      | nil => simp [decodeSetCC] at hdec
      | cons p2 t =>
        cases t with
        | nil => simp [decodeSetCC] at hdec
        | cons m t =>
          simp only [decodeSetCC] at hdec
          split at hdec
          all_goals
            (try simp only [decodeSetCCNach] at hdec
             try repeat split at hdec
             simp_all
             try omega
             all_goals cases hdec)

/-- A successful CMOVcc decode consumes exactly four bytes. -/
theorem decodeCmov_laenge (c : Bedingung) (dst src : Register)
    (pfx rest : List Byte)
    (hdec : decodeCmov pfx = some ((c, dst, src), rest)) :
    pfx.length = 4 + rest.length := by
  cases pfx with
  | nil => simp [decodeCmov] at hdec
  | cons r t =>
    cases t with
    | nil => simp [decodeCmov] at hdec
    | cons p1 t =>
      cases t with
      | nil => simp [decodeCmov] at hdec
      | cons p2 t =>
        cases t with
        | nil => simp [decodeCmov] at hdec
        | cons m t =>
          simp only [decodeCmov] at hdec
          split at hdec
          all_goals
            (try simp only [decodeCmovNach] at hdec
             try repeat split at hdec
             simp_all
             try omega
             all_goals cases hdec)

/-! ## 6. End to end: decoded bytes execute.

    Decode success fixes the consumed length at four actual bytes
    (the inversion above); the step at that length gives the value
    and the source-free frame. Every premise is used. -/

/-- End to end SETcc: decoded canonical bytes execute to the
    condition-selected low byte with the source-free frame. -/
theorem setccBytes_endzuende (s s' : Zustand) (dst : Register)
    (c : Bedingung) (pfx rest : List Byte)
    (hdec : decodeSetCC pfx = some ((c, dst), rest))
    (hstep : setccSchrittBytes (pfx.length - rest.length) s dst c =
      some s') :
    s'.register dst = setLowByte (s.register dst) (setCCByte c s.flags) ∧
    s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
    s'.rip = ripNach s.rip (pfx.length - rest.length) := by
  have hlen : pfx.length - rest.length = 4 := by
    have h := decodeSetCC_laenge c dst pfx rest hdec
    omega
  have hok : laengeOk 4 = true := by decide
  rw [hlen] at hstep ⊢
  obtain ⟨hfl, hmem, hrip, _⟩ :=
    setccSchrittBytes_rahmen 4 s s' dst c hok hstep
  exact ⟨setccSchrittBytes_wert 4 s s' dst c hok hstep,
    hfl, hmem, hrip⟩

/-- End to end CMOVcc when taken: decoded canonical bytes move the
    pre-state source word with the source-free frame. -/
theorem cmovBytes_genommen (s s' : Zustand) (dst src : Register)
    (c : Bedingung) (pfx rest : List Byte)
    (hdec : decodeCmov pfx = some ((c, dst, src), rest))
    (hbed : bedingung c s.flags = true)
    (hstep : cmovSchrittBytes (pfx.length - rest.length) s dst src c =
      some s') :
    s'.register dst = s.register src ∧
    s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
    s'.rip = ripNach s.rip (pfx.length - rest.length) := by
  have hlen : pfx.length - rest.length = 4 := by
    have h := decodeCmov_laenge c dst src pfx rest hdec
    omega
  have hok : laengeOk 4 = true := by decide
  rw [hlen] at hstep ⊢
  obtain ⟨hfl, hmem, hrip, _⟩ :=
    cmovSchrittBytes_rahmen 4 s s' dst src c hok hstep
  exact ⟨cmovSchrittBytes_genommen 4 s s' dst src c hok hbed hstep,
    hfl, hmem, hrip⟩

/-- End to end CMOVcc when untaken: the destination keeps its word. -/
theorem cmovBytes_nicht (s s' : Zustand) (dst src : Register)
    (c : Bedingung) (pfx rest : List Byte)
    (hdec : decodeCmov pfx = some ((c, dst, src), rest))
    (hbed : bedingung c s.flags = false)
    (hstep : cmovSchrittBytes (pfx.length - rest.length) s dst src c =
      some s') :
    s'.register dst = s.register dst ∧
    s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
    s'.rip = ripNach s.rip (pfx.length - rest.length) := by
  have hlen : pfx.length - rest.length = 4 := by
    have h := decodeCmov_laenge c dst src pfx rest hdec
    omega
  have hok : laengeOk 4 = true := by decide
  rw [hlen] at hstep ⊢
  obtain ⟨hfl, hmem, hrip, _⟩ :=
    cmovSchrittBytes_rahmen 4 s s' dst src c hok hstep
  exact ⟨cmovSchrittBytes_nicht 4 s s' dst src c hok hbed hstep,
    hfl, hmem, hrip⟩

/-! ## 7. Independently pinned high-register and taken/untaken forms.

    Byte values below are concrete machine bytes (`decide`), pinned
    independently of the generic round trips: SETcc `e` on `r9b`
    (`REX.B 0F 94 /0 r9`) and CMOVcc `e` from `r15` to `r9`
    (`REX.WRB 0F 44 /r r9,r15`). Taken/untaken reuse the accepted
    witness split (`cmov_witness_unterscheidet`), not restated. -/

/-- Pinned bytes: SETcc `e` on the high register `r9b`. -/
theorem pin_setCC_r9b :
    encodeSetCC .e .r9 =
      [natByte 65, natByte 15, natByte 148, natByte 193] := by
  decide

/-- Pinned decode: SETcc `e` on `r9b`. -/
theorem pin_setCC_r9b_dekode :
    decodeSetCC [natByte 65, natByte 15, natByte 148, natByte 193] =
      some (((.e, .r9)), []) := by
  decide

/-- Pinned bytes: CMOVcc `e` from `r15` to `r9`. -/
theorem pin_cmov_r9_r15 :
    encodeCmov .e .r9 .r15 =
      [natByte 77, natByte 15, natByte 68, natByte 207] := by
  decide

/-- Pinned decode: CMOVcc `e` from `r15` to `r9`. -/
theorem pin_cmov_r9_r15_dekode :
    decodeCmov [natByte 77, natByte 15, natByte 68, natByte 207] =
      some (((.e, .r9, .r15)), []) := by
  decide

/-- Pinned taken execution: the high-register CMOVcc byte step moves
    the pre-state source word (taken split reused). -/
theorem pin_cmovBytes_taken :
    cmovSchrittBytes 4 witTrue .r9 .r15 .e =
      some ({ cmovAnwenden witTrue .r9 .r15 .e with
        rip := ripNach witTrue.rip 4 }) ∧
    (cmovAnwenden witTrue .r9 .r15 .e).register .r9 =
      witTrue.register .r15 := by
  have hbed : bedingung .e witTrue.flags = true := by decide
  have hok : laengeOk 4 = true := by decide
  have hstep : cmovSchrittBytes 4 witTrue .r9 .r15 .e =
      some ({ cmovAnwenden witTrue .r9 .r15 .e with
        rip := ripNach witTrue.rip 4 }) := by
    unfold cmovSchrittBytes
    rw [hok]
  exact ⟨hstep, cmovAnwenden_genommen_wert _ _ _ _ hbed⟩

/-- Pinned untaken execution: SETcc `e` on `rax` with the zero flag
    clear writes a zero low byte over the pre-state word 10. -/
theorem pin_setccBytes_untaken :
    setccSchrittBytes 4 witFalse .rax .e =
      some ({ setCCAnwenden witFalse .rax .e with
        rip := ripNach witFalse.rip 4 }) ∧
    (setCCAnwenden witFalse .rax .e).register .rax =
      BitVec.ofNat 64 0 := by
  have hok : laengeOk 4 = true := by decide
  have hstep : setccSchrittBytes 4 witFalse .rax .e =
      some ({ setCCAnwenden witFalse .rax .e with
        rip := ripNach witFalse.rip 4 }) := by
    unfold setccSchrittBytes
    rw [hok]
  exact ⟨hstep, by decide⟩

/-! ## 8. Mutation and truncation refusal.

    Every refusal below is a concrete mutated or shortened byte string
    (`decide`): a flipped condition bit is observably a DIFFERENT
    condition (never a silent same), a wrong ModRM extension or mode
    refuses, a wrong REX refuses, and a short prefix refuses. -/

/-- MUTATION: second byte `0x95` instead of `0x94` is observably
    condition `ne`, never a silent `e`. -/
theorem mut_setCC_bedingung :
    decodeSetCC [natByte 64, natByte 15, natByte 149, natByte 192] =
      some (((.ne, .rax)), []) := by
  decide

/-- REFUSAL: SETcc with a nonzero ModRM reg field (not `/0`). -/
theorem mut_setCC_regfeld_verweigert :
    decodeSetCC [natByte 64, natByte 15, natByte 148, natByte 200] =
      none := by
  decide

/-- REFUSAL: SETcc with a memory-mode ModRM (mod=2, not register). -/
theorem mut_setCC_modus_verweigert :
    decodeSetCC [natByte 64, natByte 15, natByte 148, natByte 128] =
      none := by
  decide

/-- REFUSAL: SETcc with a W=1 REX (not the profile form). -/
theorem mut_setCC_rex_verweigert :
    decodeSetCC [natByte 72, natByte 15, natByte 148, natByte 192] =
      none := by
  decide

/-- REFUSAL: CMOVcc with a memory-mode ModRM (no memory arm exists). -/
theorem mut_cmov_modus_verweigert :
    decodeCmov [natByte 72, natByte 15, natByte 68, natByte 129] =
      none := by
  decide

/-- REFUSAL: CMOVcc without REX.W (not the profile form). -/
theorem mut_cmov_rex_verweigert :
    decodeCmov [natByte 64, natByte 15, natByte 68, natByte 195] =
      none := by
  decide

/-- REFUSAL: truncated SETcc (three of four bytes). -/
theorem kurz_setCC_verweigert :
    decodeSetCC ((encodeSetCC .e .rax).take 3) = none := by
  decide

/-- REFUSAL: truncated CMOVcc (three of four bytes). -/
theorem kurz_cmov_verweigert :
    decodeCmov ((encodeCmov .e .rax .rbx).take 3) = none := by
  decide

/-- REFUSAL: the empty input decodes to nothing on both decoders. -/
theorem leer_verweigert :
    decodeSetCC [] = none ∧ decodeCmov [] = none :=
  ⟨rfl, rfl⟩

/-- COLLISION PIN: the new decoders refuse a pilot register move
    (its REX prefix is followed by a non-`0F` opcode). -/
theorem ours_refuses_movReg :
    decodeSetCC (encode (.movReg64 .rax .rbx)) = none ∧
    decodeCmov (encode (.movReg64 .rax .rbx)) = none := by
  decide

/-- COLLISION PIN: the new decoders refuse a high-register push
    (it shares the `0x41` first byte with SETcc on `r8b`-`r15b`). -/
theorem ours_refuses_push_r8 :
    decodeSetCC (encode (.push64 .r8)) = none ∧
    decodeCmov (encode (.push64 .r8)) = none := by
  decide

/-- COLLISION PIN: the new decoders refuse a pilot conditional jump
    (it shares the `0F` prefix but lives in the `0x80` range). -/
theorem ours_refuses_jumpIf :
    decodeSetCC (encode (.jumpIf32 .e (BitVec.ofNat 32 16))) = none ∧
    decodeCmov (encode (.jumpIf32 .e (BitVec.ofNat 32 16))) = none := by
  decide

/-- COLLISION PIN: the new decoders refuse a pilot return. -/
theorem ours_refuses_ret :
    decodeSetCC (encode .ret) = none ∧
    decodeCmov (encode .ret) = none := by
  decide

/-! ## 9. Collision-free selected-profile dispatch.

    Second-byte ranges after `0F` are disjoint by construction:
    pilot `jumpIf32` takes `0x80..0x8F`, CMOVcc takes `0x40..0x4F`,
    SETcc takes `0x90..0x9F`. The pilot decoder therefore refuses
    every conditional-select byte string (proved generically over any
    suffix below), so the dispatch below tries the pilot FIRST and
    only falls through to the new decoders: no existing form is ever
    reinterpreted. Memory CMOV and indirect targets have no arm
    anywhere, so they cannot enter through either path. -/

/-- The pilot decoder refuses any input starting with `0x40`. -/
theorem decode_nach_40 (t : List Byte) :
    decode (natByte 64 :: t) = none := by
  have h64 : byteNat (natByte 64) = 64 :=
    byteNat_natByte_of_lt 64 (by decide)
  simp [decode, h64]

/-- The pilot decoder refuses `0x41 0F` (high-byte-register push/pop
    takes only `0x50..0x5F` as its second byte). -/
theorem decode_nach_41_15 (t : List Byte) :
    decode (natByte 65 :: natByte 15 :: t) = none := by
  have h65 : byteNat (natByte 65) = 65 :=
    byteNat_natByte_of_lt 65 (by decide)
  have h15 : byteNat (natByte 15) = 15 :=
    byteNat_natByte_of_lt 15 (by decide)
  simp [decode, h65, h15]

/-- The pilot decoder refuses `REX.W 0F` with no following opcode it
    knows (`0x0F` is no REX successor in the pilot). -/
theorem decode_nach_48_15 (t : List Byte) :
    decode (natByte 72 :: natByte 15 :: t) = none := by
  have h72 : byteNat (natByte 72) = 72 :=
    byteNat_natByte_of_lt 72 (by decide)
  have h15 : byteNat (natByte 15) = 15 :=
    byteNat_natByte_of_lt 15 (by decide)
  simp [decode, decodeRex, h72, h15]

/-- The pilot decoder refuses `REX.WB 0F`. -/
theorem decode_nach_49_15 (t : List Byte) :
    decode (natByte 73 :: natByte 15 :: t) = none := by
  have h73 : byteNat (natByte 73) = 73 :=
    byteNat_natByte_of_lt 73 (by decide)
  have h15 : byteNat (natByte 15) = 15 :=
    byteNat_natByte_of_lt 15 (by decide)
  simp [decode, decodeRex, h73, h15]

/-- The pilot decoder refuses `REX.WR 0F`. -/
theorem decode_nach_4c_15 (t : List Byte) :
    decode (natByte 76 :: natByte 15 :: t) = none := by
  have h76 : byteNat (natByte 76) = 76 :=
    byteNat_natByte_of_lt 76 (by decide)
  have h15 : byteNat (natByte 15) = 15 :=
    byteNat_natByte_of_lt 15 (by decide)
  simp [decode, decodeRex, h76, h15]

/-- The pilot decoder refuses `REX.WRB 0F`. -/
theorem decode_nach_4d_15 (t : List Byte) :
    decode (natByte 77 :: natByte 15 :: t) = none := by
  have h77 : byteNat (natByte 77) = 77 :=
    byteNat_natByte_of_lt 77 (by decide)
  have h15 : byteNat (natByte 15) = 15 :=
    byteNat_natByte_of_lt 15 (by decide)
  simp [decode, decodeRex, h77, h15]

/-- Every canonical SETcc encoding starts with `0x40 0F` or
    `0x41 0F`: the first two bytes are fixed by the profile. -/
theorem encodeSetCC_form (c : Bedingung) (dst : Register) :
    (∃ t, encodeSetCC c dst = natByte 64 :: natByte 15 :: t) ∨
    (∃ t, encodeSetCC c dst = natByte 65 :: natByte 15 :: t) := by
  cases dst with
  | rax => exact Or.inl ⟨_, rfl⟩
  | rcx => exact Or.inl ⟨_, rfl⟩
  | rdx => exact Or.inl ⟨_, rfl⟩
  | rbx => exact Or.inl ⟨_, rfl⟩
  | rsp => exact Or.inl ⟨_, rfl⟩
  | rbp => exact Or.inl ⟨_, rfl⟩
  | rsi => exact Or.inl ⟨_, rfl⟩
  | rdi => exact Or.inl ⟨_, rfl⟩
  | r8 => exact Or.inr ⟨_, rfl⟩
  | r9 => exact Or.inr ⟨_, rfl⟩
  | r10 => exact Or.inr ⟨_, rfl⟩
  | r11 => exact Or.inr ⟨_, rfl⟩
  | r12 => exact Or.inr ⟨_, rfl⟩
  | r13 => exact Or.inr ⟨_, rfl⟩
  | r14 => exact Or.inr ⟨_, rfl⟩
  | r15 => exact Or.inr ⟨_, rfl⟩

/-- The pilot decoder refuses every canonical SETcc byte string,
    over any suffix: no existing form is reinterpreted. -/
theorem pilot_refuses_setCC (c : Bedingung) (dst : Register)
    (suffix : List Byte) :
    decode (encodeSetCC c dst ++ suffix) = none := by
  obtain ⟨t, ht⟩ | ⟨t, ht⟩ := encodeSetCC_form c dst
  · rw [ht]
    simp only [List.cons_append]
    exact decode_nach_40 _
  · rw [ht]
    simp only [List.cons_append]
    exact decode_nach_41_15 _

/-- Every canonical CMOVcc encoding starts with `REX.W 0F` for one
    of the four extension combinations. -/
theorem encodeCmov_form (c : Bedingung) (dst src : Register) :
    (∃ t, encodeCmov c dst src = natByte 72 :: natByte 15 :: t) ∨
    (∃ t, encodeCmov c dst src = natByte 73 :: natByte 15 :: t) ∨
    (∃ t, encodeCmov c dst src = natByte 76 :: natByte 15 :: t) ∨
    (∃ t, encodeCmov c dst src = natByte 77 :: natByte 15 :: t) := by
  cases dst <;> cases src <;>
    first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr (Or.inl ⟨_, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))

/-- The pilot decoder refuses every canonical CMOVcc byte string,
    over any suffix: no existing form is reinterpreted. -/
theorem pilot_refuses_cmov (c : Bedingung) (dst src : Register)
    (suffix : List Byte) :
    decode (encodeCmov c dst src ++ suffix) = none := by
  obtain ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ :=
    encodeCmov_form c dst src
  · rw [ht]
    simp only [List.cons_append]
    exact decode_nach_48_15 _
  · rw [ht]
    simp only [List.cons_append]
    exact decode_nach_49_15 _
  · rw [ht]
    simp only [List.cons_append]
    exact decode_nach_4c_15 _
  · rw [ht]
    simp only [List.cons_append]
    exact decode_nach_4d_15 _

/-! ## 10. Selected-profile dispatch.

    Pilot first, then the conditional-select decoders: `dispatch`
    reuses `Codec.decode` for its own 14 forms and only falls through
    where the pilot refuses. `dispatch_pilot` keeps every pilot
    meaning; `dispatch_setCC_bytes` / `dispatch_cmov_bytes` route the
    new canonical bytes to the accepted evaluators' forms. -/

/-- A conditional-select form: register-only SETcc or CMOVcc. -/
inductive CondForm where
  | setcc : Bedingung → Register → CondForm
  | cmov : Bedingung → Register → Register → CondForm
  deriving DecidableEq, Repr

/-- A dispatched instruction: a pilot form or a conditional select. -/
inductive Dispatched where
  | pilot : Decodiert → Dispatched
  | cond : CondForm → Dispatched
  deriving DecidableEq, Repr

/-- Selected-profile dispatch: the pilot decoder first, then SETcc,
    then CMOVcc. Anything else is refused with `none`. -/
def dispatch (bs : List Byte) : Option (Dispatched × List Byte) :=
  match decode bs with
  | some (d, rest) => some (.pilot d, rest)
  | none =>
    match decodeSetCC bs with
    | some ((c, dst), rest) => some (.cond (.setcc c dst), rest)
    | none =>
      match decodeCmov bs with
      | some ((c, dst, src), rest) =>
        some (.cond (.cmov c dst src), rest)
      | none => none

/-- Pilot agreement: whatever the pilot decoder accepts keeps its
    pilot meaning under dispatch. -/
theorem dispatch_pilot (pfx rest : List Byte) (d : Decodiert)
    (h : decode pfx = some (d, rest)) :
    dispatch pfx = some ((.pilot d), rest) := by
  unfold dispatch
  rw [h]

/-- SETcc fall-through: where the pilot refuses and SETcc decodes,
    dispatch selects the SETcc form. -/
theorem dispatch_setCC (pfx rest : List Byte) (c : Bedingung)
    (dst : Register)
    (hpilot : decode pfx = none)
    (hdec : decodeSetCC pfx = some ((c, dst), rest)) :
    dispatch pfx = some ((.cond (.setcc c dst)), rest) := by
  unfold dispatch
  rw [hpilot, hdec]

/-- CMOVcc fall-through: where pilot and SETcc refuse and CMOVcc
    decodes, dispatch selects the CMOVcc form. -/
theorem dispatch_cmov (pfx rest : List Byte) (c : Bedingung)
    (dst src : Register)
    (hpilot : decode pfx = none)
    (hset : decodeSetCC pfx = none)
    (hdec : decodeCmov pfx = some ((c, dst, src), rest)) :
    dispatch pfx = some ((.cond (.cmov c dst src)), rest) := by
  unfold dispatch
  rw [hpilot, hset, hdec]

/-- SETcc refuses any input whose first byte is neither `0x40` nor
    `0x41`: the REX check comes before any length is consumed. -/
theorem decodeSetCC_fremd_rex (b : Byte) (t : List Byte)
    (h64 : byteNat b ≠ 64) (h65 : byteNat b ≠ 65) :
    decodeSetCC (b :: t) = none := by
  cases t with
  | nil => rfl
  | cons p1 t =>
    cases t with
    | nil => rfl
    | cons p2 t =>
      cases t with
      | nil => rfl
      | cons m rest =>
        -- The premises discharge the two match arms from the local
        -- context; only the refusal arm remains.
        simp_all only [decodeSetCC]

/-- Canonical SETcc bytes dispatch to the SETcc form (the pilot
    refuses them, so they fall through). -/
theorem dispatch_setCC_bytes (c : Bedingung) (dst : Register)
    (suffix : List Byte) :
    dispatch (encodeSetCC c dst ++ suffix) =
      some ((.cond (.setcc c dst)), suffix) :=
  dispatch_setCC _ _ c dst
    (pilot_refuses_setCC c dst suffix)
    (roundtrip_setCC c dst suffix)

/-- CMOVcc bytes are no SETcc bytes: the first REX byte is outside
    `0x40`/`0x41`, so the SETcc stage refuses them outright. -/
theorem setCC_refuses_cmov (c : Bedingung) (dst src : Register)
    (suffix : List Byte) :
    decodeSetCC (encodeCmov c dst src ++ suffix) = none := by
  obtain ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ :=
    encodeCmov_form c dst src
  · rw [ht]
    simp only [List.cons_append]
    exact decodeSetCC_fremd_rex _ _ (by decide) (by decide)
  · rw [ht]
    simp only [List.cons_append]
    exact decodeSetCC_fremd_rex _ _ (by decide) (by decide)
  · rw [ht]
    simp only [List.cons_append]
    exact decodeSetCC_fremd_rex _ _ (by decide) (by decide)
  · rw [ht]
    simp only [List.cons_append]
    exact decodeSetCC_fremd_rex _ _ (by decide) (by decide)

/-- Canonical CMOVcc bytes dispatch to the CMOVcc form (pilot and
    SETcc refuse them, so they fall through both stages). -/
theorem dispatch_cmov_bytes (c : Bedingung) (dst src : Register)
    (suffix : List Byte) :
    dispatch (encodeCmov c dst src ++ suffix) =
      some ((.cond (.cmov c dst src)), suffix) :=
  dispatch_cmov _ _ c dst src
    (pilot_refuses_cmov c dst src suffix)
    (setCC_refuses_cmov c dst src suffix)
    (roundtrip_cmov c dst src suffix)

/-- Pilot bytes keep their pilot meaning under dispatch. -/
theorem dispatch_pilot_bytes (b : Befehl) (suffix : List Byte) :
    dispatch (encode b ++ suffix) =
      some ((.pilot ⟨b, (encode b).length⟩), suffix) :=
  dispatch_pilot _ _ _ (roundtrip b suffix)

/-! ## 11. Joint witnesses: decoded bytes, execution, memory change.

    Each witness instantiates ALL premises of its end-to-end theorem
    on concrete values, pairs the conclusion with a real
    memory-changing run (a stored word that reads back and observably
    changes a byte), and plants a truncation refusal. Taken/untaken
    value splits are reused from the accepted witnesses. -/

/-- JOINT witness for `cmovBytes_genommen`: concrete taken CMOVcc
    bytes decode, execute to the source word, and the moved word
    observably changes memory; a truncated prefix is refused. -/
theorem cmovBytes_genommen_zeuge :
    ∃ (s' : Zustand) (m : Speicher),
      decodeCmov (encodeCmov .e .rax .rbx) =
        some (((.e, .rax, .rbx)), []) ∧
      cmovSchrittBytes 4 witTrue .rax .rbx .e = some s' ∧
      s'.register .rax = witTrue.register .rbx ∧
      write64 witSpeicher (BitVec.ofNat 64 8192) (s'.register .rax) =
        some m ∧
      read64 m (BitVec.ofNat 64 8192) = some 20 ∧
      m.bytes (BitVec.ofNat 64 8192) ≠
        witSpeicher.bytes (BitVec.ofNat 64 8192) ∧
      decodeCmov ((encodeCmov .e .rax .rbx).take 3) = none := by
  have hdec : decodeCmov (encodeCmov .e .rax .rbx) =
      some (((.e, .rax, .rbx)), []) := by
    simpa using roundtrip_cmov .e .rax .rbx []
  have hbed : bedingung .e witTrue.flags = true := by decide
  have hok : laengeOk 4 = true := by decide
  have hstep : cmovSchrittBytes 4 witTrue .rax .rbx .e =
      some ({ cmovAnwenden witTrue .rax .rbx .e with
        rip := ripNach witTrue.rip 4 }) := by
    unfold cmovSchrittBytes
    rw [hok]
  have hlen4 : (encodeCmov .e .rax .rbx).length -
      ([] : List Byte).length = 4 := by
    simp [encodeCmov_len]
  have hstep4 : cmovSchrittBytes
      ((encodeCmov .e .rax .rbx).length - ([] : List Byte).length)
      witTrue .rax .rbx .e =
      some ({ cmovAnwenden witTrue .rax .rbx .e with
        rip := ripNach witTrue.rip 4 }) := by
    rw [hlen4]
    exact hstep
  obtain ⟨hval, _, _, _⟩ := cmovBytes_genommen witTrue _
    .rax .rbx .e (encodeCmov .e .rax .rbx) [] hdec hbed hstep4
  have hsrc : witTrue.register .rbx = BitVec.ofNat 64 20 := by decide
  have hsel : (cmovAnwenden witTrue .rax .rbx .e).register .rax = 20 :=
    cmov_witness_unterscheidet.1
  obtain ⟨m, hwr, hread, hdiff⟩ := cmov_speicher_zeuge
  rw [hsel] at hwr
  refine ⟨_, m, hdec, hstep, hval, ?_, hread, hdiff,
    kurz_cmov_verweigert⟩
  show write64 witSpeicher (BitVec.ofNat 64 8192)
    ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m
  exact hwr

/-- JOINT witness for `setccBytes_endzuende` (taken): concrete SETcc
    bytes decode, execute to the selected low byte 1, and the selected
    word observably changes memory; a truncated prefix is refused. -/
theorem setccBytes_endzuende_zeuge :
    ∃ (s' : Zustand) (m : Speicher),
      decodeSetCC (encodeSetCC .e .rax) =
        some (((.e, .rax)), []) ∧
      setccSchrittBytes 4 witTrue .rax .e = some s' ∧
      s'.register .rax =
        setLowByte (witTrue.register .rax)
          (setCCByte .e witTrue.flags) ∧
      s'.register .rax = 1 ∧
      write64 witSpeicher (BitVec.ofNat 64 8192) (s'.register .rax) =
        some m ∧
      read64 m (BitVec.ofNat 64 8192) = some 1 ∧
      m.bytes (BitVec.ofNat 64 8192) ≠
        witSpeicher.bytes (BitVec.ofNat 64 8192) ∧
      decodeSetCC ((encodeSetCC .e .rax).take 3) = none := by
  have hdec : decodeSetCC (encodeSetCC .e .rax) =
      some (((.e, .rax)), []) := by
    simpa using roundtrip_setCC .e .rax []
  have hok : laengeOk 4 = true := by decide
  have hstep : setccSchrittBytes 4 witTrue .rax .e =
      some ({ setCCAnwenden witTrue .rax .e with
        rip := ripNach witTrue.rip 4 }) := by
    unfold setccSchrittBytes
    rw [hok]
  have hlen4 : (encodeSetCC .e .rax).length -
      ([] : List Byte).length = 4 := by
    simp [encodeSetCC_len]
  have hstep4 : setccSchrittBytes
      ((encodeSetCC .e .rax).length - ([] : List Byte).length)
      witTrue .rax .e =
      some ({ setCCAnwenden witTrue .rax .e with
        rip := ripNach witTrue.rip 4 }) := by
    rw [hlen4]
    exact hstep
  obtain ⟨hval, _, _, _⟩ := setccBytes_endzuende witTrue _
    .rax .e (encodeSetCC .e .rax) [] hdec hstep4
  have hval1 : setLowByte (witTrue.register .rax)
      (setCCByte .e witTrue.flags) = 1 := by
    decide
  have hwr : write64 witSpeicher (BitVec.ofNat 64 8192) 1 =
      some { witSpeicher with
        bytes := writeBytes witSpeicher (BitVec.ofNat 64 8192) 1 } := by
    unfold write64
    rw [if_pos wit_schreibbar8]
  have hread := read64_nach_write64 _ _ _ _ hwr wit_lesbar8
  have hhit := writeBytesN_hit witSpeicher
    (BitVec.ofNat 64 8192) 1 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  have hdiff : writeBytesN witSpeicher (BitVec.ofNat 64 8192) 1 8
      (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
    rw [hhit]
    decide
  refine ⟨{ setCCAnwenden witTrue .rax .e with
      rip := ripNach witTrue.rip 4 },
    { witSpeicher with
      bytes := writeBytes witSpeicher (BitVec.ofNat 64 8192) 1 },
    hdec, hstep, hval, ?_, ?_, ?_, ?_,
    kurz_setCC_verweigert⟩
  · rw [hval]
    exact hval1
  · rw [hval, hval1]
    exact hwr
  · exact hread
  · show writeBytesN witSpeicher (BitVec.ofNat 64 8192) 1 8
        (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192)
    exact hdiff

/- CUTS:
    Proved here (all over the REUSED `Codec` byte helpers and the
    REUSED accepted `ControlFlow`/`ConditionalMove` evaluators --
    no pilot file touched, no second interpreter):
    - canonical register-only byte shapes (`REX 0F 90+cc /0 mod=3`
      for SETcc, `REX.W 0F 40+cc /r mod=3` for CMOVcc) with generic
      round trips (decoded length is the consumed 4-byte prefix),
      actual-length guard facts, and decoder-length inversions (a
      successful decode consumes exactly four bytes);
    - byte-level steps applying exactly the accepted evaluators
      (`cmovSchrittBytes_gleich` shows the CMOVcc byte step IS the
      accepted `cmovSchritt` at the actual length), with actual
      condition-selected values and the source-free frame (flags,
      memory, RIP past the decoded bytes, untouched registers);
    - end-to-end bytes-to-execution theorems (decode success fixes
      the consumed length; the step at that length gives value and
      frame; every premise used);
    - independently pinned high-register byte/decode pairs
      (`SETE r9b`, `CMOVe r9,r15`) and taken/untaken execution pins
      (taken split reused from `cmov_witness_unterscheidet`);
    - concrete mutation (a flipped condition bit is observably a
      different condition) and truncation refusals, wrong
      ModRM-extension/mode and wrong-REX refusals;
    - collision-free selected-profile dispatch: disjoint `0F`
      second-byte ranges (pilot `0x80-0x8F`, CMOV `0x40-0x4F`,
      SETcc `0x90-0x9F`), GENERIC pilot-refusal of every new byte
      string over any suffix, pilot-first dispatch with agreement
      theorems on both sides, and collision pins for the
      byte-overlapping pilot forms (`push r8` shares `0x41`,
      `jumpIf32` shares `0F`);
    - joint non-degenerate witnesses (concrete decode plus a
      memory-changing run that reads back, plus a planted
      truncation refusal) for the taken CMOVcc and taken SETcc
      end-to-end theorems.
    NOT proved here, and not claimed:
    - No hardware correspondence: the byte shapes follow the Intel
      manual (`SETcc r/m8`: `0F 90+cc /0`; `CMOVcc r,r/m`: `REX.W`
      `0F 40+cc /r`, reg=destination), checked here only as
      self-consistency (round trips, pins, refusals), not silicon.
    - No memory CMOV and no indirect-target admission: neither
      decoder has such an arm (refused by construction); the
      accepted fault-keeping `cmovMemSchritt` is reused, never
      re-decided, and no speculation claim is made.
    - No generic ours-refuses-pilot theorem: the reverse refusal is
      pinned on the four byte-overlapping pilot forms only. Routing
      stays unambiguous because dispatch is pilot-first and the
      generic pilot-refuses-ours direction IS proved; the full
      14-form reverse generic is open.
    - No source, IR, checker, emitter or goal claim: no `Befehl`
      constructor is added (the pilot syntax is untouched), nothing
      speaks about Gabbro source ranges, contracts, duties or
      lowering, and no budget/time/termination statement is made.
    - No TSO/GX, concurrency, atomicity, cost or time claim; every
      fact here is sequential over one `Speicher`; absence of a
      transition is never a termination statement.
-/

#print axioms roundtrip_setCC
#print axioms encodeSetCC_len
#print axioms setccLaenge_ok
#print axioms roundtrip_cmov
#print axioms encodeCmov_len
#print axioms cmovLaenge_ok
#print axioms cmovSchrittBytes_gleich
#print axioms setccSchrittBytes_wert
#print axioms setccSchrittBytes_rahmen
#print axioms cmovSchrittBytes_genommen
#print axioms cmovSchrittBytes_nicht
#print axioms cmovSchrittBytes_rahmen
#print axioms decodeSetCC_laenge
#print axioms decodeCmov_laenge
#print axioms setccBytes_endzuende
#print axioms cmovBytes_genommen
#print axioms cmovBytes_nicht
#print axioms pin_setCC_r9b
#print axioms pin_setCC_r9b_dekode
#print axioms pin_cmov_r9_r15
#print axioms pin_cmov_r9_r15_dekode
#print axioms pin_cmovBytes_taken
#print axioms pin_setccBytes_untaken
#print axioms mut_setCC_bedingung
#print axioms mut_setCC_regfeld_verweigert
#print axioms mut_setCC_modus_verweigert
#print axioms mut_setCC_rex_verweigert
#print axioms mut_cmov_modus_verweigert
#print axioms mut_cmov_rex_verweigert
#print axioms kurz_setCC_verweigert
#print axioms kurz_cmov_verweigert
#print axioms leer_verweigert
#print axioms ours_refuses_movReg
#print axioms ours_refuses_push_r8
#print axioms ours_refuses_jumpIf
#print axioms ours_refuses_ret
#print axioms decode_nach_40
#print axioms decode_nach_41_15
#print axioms decode_nach_48_15
#print axioms decode_nach_49_15
#print axioms decode_nach_4c_15
#print axioms decode_nach_4d_15
#print axioms encodeSetCC_form
#print axioms pilot_refuses_setCC
#print axioms encodeCmov_form
#print axioms pilot_refuses_cmov
#print axioms dispatch_pilot
#print axioms dispatch_setCC
#print axioms dispatch_cmov
#print axioms decodeSetCC_fremd_rex
#print axioms dispatch_setCC_bytes
#print axioms setCC_refuses_cmov
#print axioms dispatch_cmov_bytes
#print axioms dispatch_pilot_bytes
#print axioms cmovBytes_genommen_zeuge
#print axioms setccBytes_endzuende_zeuge

end Gabbro.Grammatik.X86
