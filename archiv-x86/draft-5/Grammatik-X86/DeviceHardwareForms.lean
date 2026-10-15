/-
  File:      Grammatik/X86/DeviceHardwareForms.lean
  Subject:   Selected port-IO and device-memory profiles with exact byte
             encode/decode and fetched execution over canonical state.

  Lane 676: exact selected port instructions (IN/OUT, widths 8/16/32,
  immediate-port versus DX-port forms) with accumulator width effects,
  privilege/fault outcomes and ordered IO events over a GENERIC
  hardware device-response interface; MMIO/DMA distinguished from
  ordinary RAM by a typed admission interface and refused until their
  memory-type/order rules are modelled. No OS/library contracts, no
  number-to-pointer conversion, no syscall/interrupt scope (lane 672).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.NarrowOps
import Grammatik.X86.ScalarFloat

namespace Gabbro.Grammatik.X86

/-- Selected port widths: 8, 16 or 32 bits through the accumulator. -/
inductive IoBreite where
  | p8 | p16 | p32
  deriving DecidableEq, Repr

/-- Port direction: device read (`ein`, IN) or device write (`aus`, OUT). -/
inductive IoDir where
  | ein | aus
  deriving DecidableEq, Repr

/-- Port addressing: an 8-bit immediate port or the DX register. -/
inductive PortQuelle where
  | imm (port : Nat)
  | dx
  deriving DecidableEq, Repr

/-- One selected port operation: direction, width and port source. -/
structure IoOp where
  dir : IoDir
  breite : IoBreite
  quelle : PortQuelle
  deriving DecidableEq, Repr

/-- A decoded port instruction with its consumed length. -/
structure IoDec where
  op : IoOp
  laenge : Nat
  deriving DecidableEq, Repr

/-! ## Widths: bits, bytes and explicit admission. -/

/-- Data bits carried by one port width. -/
def ioBreiteBits : IoBreite → Nat
  | .p8 => 8 | .p16 => 16 | .p32 => 32

/-- Data bytes carried by one port width. -/
def ioBreiteBytes : IoBreite → Nat
  | .p8 => 1 | .p16 => 2 | .p32 => 4

/-- Explicit width admission: only 8, 16 and 32 are selected forms.
    Any other width (for example 24 or 64) is refused with `none`. -/
def breiteAusNat : Nat → Option IoBreite
  | 8 => some .p8
  | 16 => some .p16
  | 32 => some .p32
  | _ => none

/-- The admitted widths carry their stated bit counts. -/
theorem breiteAusNat_bits (b : IoBreite) :
    breiteAusNat (ioBreiteBits b) = some b := by
  cases b <;> rfl

/-- A non-selected width is refused: 24 has no port form here. -/
theorem breiteAusNat_24_verweigert : breiteAusNat 24 = none := rfl

/-- A non-selected width is refused: 64 has no port form here. -/
theorem breiteAusNat_64_verweigert : breiteAusNat 64 = none := rfl

/-! ## Canonical byte encoding of the twelve selected forms.

   Stated canonical subset (self-consistency only, not silicon truth):
   the OUT/IN opcode pairs E6/E4 (imm8, 8 bit), E7/E5 (imm8, 32 bit)
   and EE/EC, EF/ED (DX port, 8/32 bit), with the 0x66 operand-size
   prefix selecting the 16-bit accumulator forms. No local hardware
   manual was present (`.tmp/HARDWARE-REFERENCES/REFERENCES.json`
   absent), so hardware correspondence stays OPEN (see CUTS). -/

/-- Canonical byte encoding of one selected port operation.
    The immediate port is truncated to one byte at encode time. -/
def encodeIo : IoOp → List Byte
  | ⟨.aus, .p8, .imm p⟩ => [natByte 230, natByte (p % 256)]
  | ⟨.aus, .p16, .imm p⟩ => [natByte 102, natByte 231, natByte (p % 256)]
  | ⟨.aus, .p32, .imm p⟩ => [natByte 231, natByte (p % 256)]
  | ⟨.aus, .p8, .dx⟩ => [natByte 238]
  | ⟨.aus, .p16, .dx⟩ => [natByte 102, natByte 239]
  | ⟨.aus, .p32, .dx⟩ => [natByte 239]
  | ⟨.ein, .p8, .imm p⟩ => [natByte 228, natByte (p % 256)]
  | ⟨.ein, .p16, .imm p⟩ => [natByte 102, natByte 229, natByte (p % 256)]
  | ⟨.ein, .p32, .imm p⟩ => [natByte 229, natByte (p % 256)]
  | ⟨.ein, .p8, .dx⟩ => [natByte 236]
  | ⟨.ein, .p16, .dx⟩ => [natByte 102, natByte 237]
  | ⟨.ein, .p32, .dx⟩ => [natByte 237]

/-- Consumed length of one selected port operation. -/
def ioLen : IoOp → Nat
  | ⟨_, .p8, .imm _⟩ => 2
  | ⟨_, .p16, .imm _⟩ => 3
  | ⟨_, .p32, .imm _⟩ => 2
  | ⟨_, .p8, .dx⟩ => 1
  | ⟨_, .p16, .dx⟩ => 2
  | ⟨_, .p32, .dx⟩ => 1

/-- Every selected encoding fits the 15-byte instruction cap. -/
theorem encodeIo_len (op : IoOp) :
    1 ≤ (encodeIo op).length ∧ (encodeIo op).length ≤ 15 := by
  cases op with
  | mk dir breite quelle =>
    cases dir <;> cases breite <;> cases quelle <;>
      simp only [encodeIo, List.length_cons, List.length_nil] <;> decide

/-- The encoding consumes exactly its stated length. -/
theorem encodeIo_len_ok (op : IoOp) :
    (encodeIo op).length = ioLen op := by
  cases op with
  | mk dir breite quelle =>
    cases dir <;> cases breite <;> cases quelle <;> rfl

/-! ## Bounded independent decoder for the twelve selected forms. -/

/-- Decode one selected port instruction, returning it with its
    consumed length and the remaining bytes. Only canonical encodings
    are accepted; anything else (truncated, unknown, pilot bytes,
    operand-size prefixes outside the selected rows) refuses. -/
def decodeIo : List Byte → Option (IoDec × List Byte)
  | [] => none
  | b :: rest =>
    match byteNat b with
    | 230 =>
      match rest with
      | p :: rest' => some (⟨⟨.aus, .p8, .imm (byteNat p)⟩, 2⟩, rest')
      | [] => none
    | 228 =>
      match rest with
      | p :: rest' => some (⟨⟨.ein, .p8, .imm (byteNat p)⟩, 2⟩, rest')
      | [] => none
    | 231 =>
      match rest with
      | p :: rest' => some (⟨⟨.aus, .p32, .imm (byteNat p)⟩, 2⟩, rest')
      | [] => none
    | 229 =>
      match rest with
      | p :: rest' => some (⟨⟨.ein, .p32, .imm (byteNat p)⟩, 2⟩, rest')
      | [] => none
    | 238 => some (⟨⟨.aus, .p8, .dx⟩, 1⟩, rest)
    | 236 => some (⟨⟨.ein, .p8, .dx⟩, 1⟩, rest)
    | 239 => some (⟨⟨.aus, .p32, .dx⟩, 1⟩, rest)
    | 237 => some (⟨⟨.ein, .p32, .dx⟩, 1⟩, rest)
    | 102 =>
      match rest with
      | [] => none
      | b2 :: rest2 =>
        match byteNat b2 with
        | 231 =>
          match rest2 with
          | p :: rest' =>
            some (⟨⟨.aus, .p16, .imm (byteNat p)⟩, 3⟩, rest')
          | [] => none
        | 229 =>
          match rest2 with
          | p :: rest' =>
            some (⟨⟨.ein, .p16, .imm (byteNat p)⟩, 3⟩, rest')
          | [] => none
        | 239 => some (⟨⟨.aus, .p16, .dx⟩, 2⟩, rest2)
        | 237 => some (⟨⟨.ein, .p16, .dx⟩, 2⟩, rest2)
        | _ => none
    | _ => none

/-- Round trip: OUT 8 bit through an immediate port. -/
theorem roundtrip_io_aus_p8_imm (p : Nat) (suffix : List Byte) :
    decodeIo (encodeIo ⟨.aus, .p8, .imm p⟩ ++ suffix) =
      some (⟨⟨.aus, .p8, .imm (p % 256)⟩, 2⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: OUT 16 bit through an immediate port. -/
theorem roundtrip_io_aus_p16_imm (p : Nat) (suffix : List Byte) :
    decodeIo (encodeIo ⟨.aus, .p16, .imm p⟩ ++ suffix) =
      some (⟨⟨.aus, .p16, .imm (p % 256)⟩, 3⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: OUT 32 bit through an immediate port. -/
theorem roundtrip_io_aus_p32_imm (p : Nat) (suffix : List Byte) :
    decodeIo (encodeIo ⟨.aus, .p32, .imm p⟩ ++ suffix) =
      some (⟨⟨.aus, .p32, .imm (p % 256)⟩, 2⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: IN 8 bit through an immediate port. -/
theorem roundtrip_io_ein_p8_imm (p : Nat) (suffix : List Byte) :
    decodeIo (encodeIo ⟨.ein, .p8, .imm p⟩ ++ suffix) =
      some (⟨⟨.ein, .p8, .imm (p % 256)⟩, 2⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: IN 16 bit through an immediate port. -/
theorem roundtrip_io_ein_p16_imm (p : Nat) (suffix : List Byte) :
    decodeIo (encodeIo ⟨.ein, .p16, .imm p⟩ ++ suffix) =
      some (⟨⟨.ein, .p16, .imm (p % 256)⟩, 3⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: IN 32 bit through an immediate port. -/
theorem roundtrip_io_ein_p32_imm (p : Nat) (suffix : List Byte) :
    decodeIo (encodeIo ⟨.ein, .p32, .imm p⟩ ++ suffix) =
      some (⟨⟨.ein, .p32, .imm (p % 256)⟩, 2⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: OUT 8 bit through DX. -/
theorem roundtrip_io_aus_p8_dx (suffix : List Byte) :
    decodeIo (encodeIo ⟨.aus, .p8, .dx⟩ ++ suffix) =
      some (⟨⟨.aus, .p8, .dx⟩, 1⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: OUT 16 bit through DX. -/
theorem roundtrip_io_aus_p16_dx (suffix : List Byte) :
    decodeIo (encodeIo ⟨.aus, .p16, .dx⟩ ++ suffix) =
      some (⟨⟨.aus, .p16, .dx⟩, 2⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: OUT 32 bit through DX. -/
theorem roundtrip_io_aus_p32_dx (suffix : List Byte) :
    decodeIo (encodeIo ⟨.aus, .p32, .dx⟩ ++ suffix) =
      some (⟨⟨.aus, .p32, .dx⟩, 1⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: IN 8 bit through DX. -/
theorem roundtrip_io_ein_p8_dx (suffix : List Byte) :
    decodeIo (encodeIo ⟨.ein, .p8, .dx⟩ ++ suffix) =
      some (⟨⟨.ein, .p8, .dx⟩, 1⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: IN 16 bit through DX. -/
theorem roundtrip_io_ein_p16_dx (suffix : List Byte) :
    decodeIo (encodeIo ⟨.ein, .p16, .dx⟩ ++ suffix) =
      some (⟨⟨.ein, .p16, .dx⟩, 2⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Round trip: IN 32 bit through DX. -/
theorem roundtrip_io_ein_p32_dx (suffix : List Byte) :
    decodeIo (encodeIo ⟨.ein, .p32, .dx⟩ ++ suffix) =
      some (⟨⟨.ein, .p32, .dx⟩, 1⟩, suffix) := by
  simp [encodeIo, decodeIo]

/-- Decoding inverts encoding on every selected form (ports normalised
    to one byte), over any suffix. -/
theorem roundtripIo (op : IoOp) (suffix : List Byte) :
    decodeIo (encodeIo op ++ suffix) =
      some (⟨⟨op.dir, op.breite,
        match op.quelle with
        | .imm p => .imm (p % 256)
        | .dx => .dx⟩, ioLen op⟩, suffix) := by
  cases op with
  | mk dir breite quelle =>
    cases dir <;> cases breite <;> cases quelle with
    | imm p =>
      simp only
      first
        | exact roundtrip_io_aus_p8_imm p suffix
        | exact roundtrip_io_aus_p16_imm p suffix
        | exact roundtrip_io_aus_p32_imm p suffix
        | exact roundtrip_io_ein_p8_imm p suffix
        | exact roundtrip_io_ein_p16_imm p suffix
        | exact roundtrip_io_ein_p32_imm p suffix
    | dx =>
      simp only
      first
        | exact roundtrip_io_aus_p8_dx suffix
        | exact roundtrip_io_aus_p16_dx suffix
        | exact roundtrip_io_aus_p32_dx suffix
        | exact roundtrip_io_ein_p8_dx suffix
        | exact roundtrip_io_ein_p16_dx suffix
        | exact roundtrip_io_ein_p32_dx suffix

/-! ## Explicit refusals: truncated, unknown and foreign bytes. -/

/-- The empty input decodes to nothing. -/
theorem io_nichts_leer : decodeIo [] = none := rfl

/-- A lone OUT opcode without its port byte is truncated. -/
theorem io_nichts_aus_kurz : decodeIo [natByte 230] = none := rfl

/-- A lone operand-size prefix is truncated. -/
theorem io_nichts_praefix_allein : decodeIo [natByte 102] = none := rfl

/-- A prefix plus opcode without the port byte is truncated. -/
theorem io_nichts_praefix_opcode_kurz :
    decodeIo [natByte 102, natByte 231] = none := rfl

/-- An unknown opcode is refused. -/
theorem io_nichts_unbekannt : decodeIo [natByte 255] = none := rfl

/-- A pilot RET byte is no port instruction here. -/
theorem io_nichts_pilot_ret : decodeIo [natByte 195] = none := rfl

/-- A non-selected second byte after the prefix refuses. -/
theorem io_nichts_praefix_falsch :
    decodeIo [natByte 102, natByte 0] = none := rfl

/-- A 16-bit OUT through DX with a forged trailing byte still decodes
    the prefix form and leaves the byte (no over-consumption). -/
theorem io_dx_laesst_rest :
    decodeIo [natByte 102, natByte 239, natByte 7] =
      some (⟨⟨.aus, .p16, .dx⟩, 2⟩, [natByte 7]) := by
  decide

/-- DECODER COVERAGE: every successful `decodeIo` of an ARBITRARY byte
    list consumes exactly its stated length within 1..15. Proved from
    the decoder side only, by splitting the opcode dispatch. -/
theorem decodeIo_consumes (bs : List Byte) (d : IoDec) (rest : List Byte)
    (h : decodeIo bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
  cases bs with
  | nil => simp [decodeIo] at h
  | cons b t =>
    simp only [decodeIo] at h
    split at h
    · cases t with
      | nil => simp at h
      | cons p t' =>
        cases h
        refine ⟨by simp; omega, by simp, by simp⟩
    · cases t with
      | nil => simp at h
      | cons p t' =>
        cases h
        refine ⟨by simp; omega, by simp, by simp⟩
    · cases t with
      | nil => simp at h
      | cons p t' =>
        cases h
        refine ⟨by simp; omega, by simp, by simp⟩
    · cases t with
      | nil => simp at h
      | cons p t' =>
        cases h
        refine ⟨by simp; omega, by simp, by simp⟩
    · cases h
      refine ⟨by simp; omega, by simp, by simp⟩
    · cases h
      refine ⟨by simp; omega, by simp, by simp⟩
    · cases h
      refine ⟨by simp; omega, by simp, by simp⟩
    · cases h
      refine ⟨by simp; omega, by simp, by simp⟩
    · cases t with
      | nil => simp at h
      | cons b2 t2 =>
        dsimp only at h
        split at h
        · cases t2 with
          | nil => simp at h
          | cons p t' =>
            cases h
            refine ⟨by simp; omega, by simp, by simp⟩
        · cases t2 with
          | nil => simp at h
          | cons p t' =>
            cases h
            refine ⟨by simp; omega, by simp, by simp⟩
        · cases h
          refine ⟨by simp; omega, by simp, by simp⟩
        · cases h
          refine ⟨by simp; omega, by simp, by simp⟩
        · simp at h
    · simp at h

/- CUTS:
   Proved codec half: exact 12-form encode/decode with generic
   round trips, arbitrary-input length coverage and planted refusals.
   Profiles, device interface and fetched execution are still OPEN.
-/

/-! ## Privilege profile: CPL against IOPL plus a per-port bitmap.

   Selected rule (stated, fail-closed): a port access is admitted
   exactly when the master switch is on, CPL <= IOPL, and the port
   bitmap names the port. Denial is an explicit fault outcome
   (`none` at the step), never a silent skip. The TSS permission
   bitmap itself is the `erlaubt` field; its OS-side population is
   user logic and OPEN. -/

/-- Port privilege profile: current privilege level, IO privilege
    level, the master switch, and the per-port permission bitmap. -/
structure IoProfil where
  cpl : Nat
  iopl : Nat
  ioErlaubt : Bool
  erlaubt : Nat → Bool

/-- Privilege admission at one port: switch on, CPL <= IOPL, bitmap. -/
def ioZugelassen (p : IoProfil) (port : Nat) : Bool :=
  p.ioErlaubt && decide (p.cpl ≤ p.iopl) && p.erlaubt port

/-- Admission means all three sides hold. -/
theorem ioZugelassen_heisst_alle (p : IoProfil) (port : Nat)
    (h : ioZugelassen p port = true) :
    p.ioErlaubt = true ∧ p.cpl ≤ p.iopl ∧ p.erlaubt port = true := by
  unfold ioZugelassen at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hsw, hle⟩, hbit⟩ := h
  exact ⟨hsw, of_decide_eq_true hle, hbit⟩

/-- A denied switch refuses every port. -/
theorem ioZugelassen_schalter_aus (p : IoProfil) (port : Nat)
    (h : p.ioErlaubt = false) :
    ioZugelassen p port = false := by
  unfold ioZugelassen
  rw [h]
  simp

/-- Insufficient privilege refuses, at every bitmap. -/
theorem ioZugelassen_privileg_verweigert (p : IoProfil) (port : Nat)
    (h : ¬ p.cpl ≤ p.iopl) :
    ioZugelassen p port = false := by
  have hle : decide (p.cpl ≤ p.iopl) = false := by simp [h]
  unfold ioZugelassen
  rw [hle]
  simp

/-- An unnamed port refuses, at every privilege level. -/
theorem ioZugelassen_port_verweigert (p : IoProfil) (port : Nat)
    (h : p.erlaubt port = false) :
    ioZugelassen p port = false := by
  unfold ioZugelassen
  rw [h]
  simp

/-- Witness profile: user CPL 3 with IOPL 3, switch on, only port
    0x60 (96) named. -/
def ioProfilZeuge : IoProfil :=
  { cpl := 3, iopl := 3, ioErlaubt := true,
    erlaubt := fun q => decide (q = 96) }

/-- The witness profile admits port 0x60. -/
theorem ioProfilZeuge_laesst_60_zu :
    ioZugelassen ioProfilZeuge 96 = true := by
  decide

/-- The witness profile refuses the neighbouring port 0x61. -/
theorem ioProfilZeuge_weist_61_zurueck :
    ioZugelassen ioProfilZeuge 97 = false := by
  decide

/-- Joint privilege _zeuge: admitted at 0x60 AND refused at 0x61
    under reduced IOPL, with every premise proved jointly. -/
theorem ioZugelassen_zeuge :
    ioZugelassen ioProfilZeuge 96 = true ∧
    ioZugelassen { ioProfilZeuge with iopl := 0 } 96 = false ∧
    ioZugelassen { ioProfilZeuge with ioErlaubt := false } 96 = false ∧
    ioZugelassen ioProfilZeuge 97 = false := by
  refine ⟨ioProfilZeuge_laesst_60_zu, ?_, ?_, ioProfilZeuge_weist_61_zurueck⟩
  · apply ioZugelassen_privileg_verweigert
    decide
  · apply ioZugelassen_schalter_aus
    rfl

/-! ## Memory-kind admission: RAM versus device memory.

   Typed finite interface: ordinary RAM is admitted; memory-mapped IO
   and DMA are refused until their precise memory-type/order rules are
   modelled. Device-MMIO NEVER reuses the write-back RAM TSO ordering:
   port-IO events below are strongly ordered program-order entries, and
   no `TSOZustand` buffer ever carries a device byte (see CUTS). -/

/-- Memory kinds: ordinary RAM, memory-mapped IO, DMA. -/
inductive SpeicherArt where
  | ram | mmio | dma
  deriving DecidableEq, Repr

/-- Memory-kind profile: which non-RAM kinds are admitted. RAM is
    admitted unconditionally; both switches start refused. -/
structure SpeicherProfil where
  mmioZugelassen : Bool
  dmaZugelassen : Bool
  deriving DecidableEq, Repr

/-- Kind admission: RAM always, device kinds only when named. -/
def speicherArtZugelassen (m : SpeicherProfil) : SpeicherArt → Bool
  | .ram => true
  | .mmio => m.mmioZugelassen
  | .dma => m.dmaZugelassen

/-- The default profile admits RAM and refuses both device kinds. -/
def speicherProfilZeuge : SpeicherProfil :=
  { mmioZugelassen := false, dmaZugelassen := false }

/-- RAM is admitted under the default profile. -/
theorem speicherProfilZeuge_ram :
    speicherArtZugelassen speicherProfilZeuge .ram = true := rfl

/-- MMIO is refused under the default profile. -/
theorem speicherProfilZeuge_mmio_verweigert :
    speicherArtZugelassen speicherProfilZeuge .mmio = false := rfl

/-- DMA is refused under the default profile. -/
theorem speicherProfilZeuge_dma_verweigert :
    speicherArtZugelassen speicherProfilZeuge .dma = false := rfl

/-- Joint memory-kind _zeuge: RAM admitted, MMIO and DMA refused. -/
theorem speicherArt_zeuge :
    speicherArtZugelassen speicherProfilZeuge .ram = true ∧
    speicherArtZugelassen speicherProfilZeuge .mmio = false ∧
    speicherArtZugelassen speicherProfilZeuge .dma = false :=
  ⟨speicherProfilZeuge_ram, speicherProfilZeuge_mmio_verweigert,
    speicherProfilZeuge_dma_verweigert⟩

/-! ## Generic hardware device-response interface.

   The device is GENERIC named behaviour: one data register plus an
   observation counter. The answer carries only that behaviour, never
   an OS or library contract. Every access advances the counter and
   appends its ordered event; device bytes never enter a RAM TSO
   store buffer (no `TSOZustand` appears here by construction). -/

/-- Generic device state: a data register plus an access counter. -/
structure GeraetZustand where
  daten : Nat
  zaehl : Nat
  deriving DecidableEq, Repr

/-- One observable ordered IO event: direction, width, port, value. -/
structure IoEreignis where
  dir : IoDir
  breite : IoBreite
  port : Nat
  wert : Nat
  deriving DecidableEq, Repr

/-- Value modulus of one port width. -/
def ioMaske : IoBreite → Nat
  | .p8 => 256 | .p16 => 65536 | .p32 => 4294967296

/-- The modulus is two to the width in bits. -/
theorem ioMaske_bits (b : IoBreite) : ioMaske b = 2 ^ ioBreiteBits b := by
  cases b <;> rfl

/-- Generic device answer: OUT stores the truncated value, IN returns
    the stored value truncated; every access advances the counter. -/
def geraetAntwort (g : GeraetZustand) (dir : IoDir) (b : IoBreite)
    (v : Nat) : GeraetZustand × Nat :=
  match dir with
  | .aus => (⟨v % ioMaske b, g.zaehl + 1⟩, 0)
  | .ein => (⟨g.daten, g.zaehl + 1⟩, g.daten % ioMaske b)

/-- OUT stores the truncated value in the device register. -/
theorem geraetAus_speichert (g : GeraetZustand) (b : IoBreite) (v : Nat) :
    (geraetAntwort g .aus b v).1.daten = v % ioMaske b := rfl

/-- OUT advances the observation counter. -/
theorem geraetAus_zaehlt (g : GeraetZustand) (b : IoBreite) (v : Nat) :
    (geraetAntwort g .aus b v).1.zaehl = g.zaehl + 1 := rfl

/-- IN answers the stored value truncated to the port width. -/
theorem geraetEin_antwortet (g : GeraetZustand) (b : IoBreite) (v : Nat) :
    (geraetAntwort g .ein b v).2 = g.daten % ioMaske b := rfl

/-- IN keeps the stored device register. -/
theorem geraetEin_behaelt (g : GeraetZustand) (b : IoBreite) (v : Nat) :
    (geraetAntwort g .ein b v).1.daten = g.daten := rfl

/-- IN advances the observation counter. -/
theorem geraetEin_zaehlt (g : GeraetZustand) (b : IoBreite) (v : Nat) :
    (geraetAntwort g .ein b v).1.zaehl = g.zaehl + 1 := rfl

/-- Joint device _zeuge: OUT stores 42 (counter 0 to 1), IN answers
    it back truncated (counter 1 to 2), register kept. -/
theorem geraetAntwort_zeuge :
    (geraetAntwort ⟨0, 0⟩ .aus .p8 42).1.daten = 42 ∧
    (geraetAntwort ⟨0, 0⟩ .aus .p8 42).1.zaehl = 1 ∧
    (geraetAntwort (geraetAntwort ⟨0, 0⟩ .aus .p8 42).1 .ein .p8 0).2 = 42 ∧
    (geraetAntwort (geraetAntwort ⟨0, 0⟩ .aus .p8 42).1 .ein .p8 0).1.zaehl = 2 := by
  decide

/-! ## Effective port and OUT payload over canonical registers. -/

/-- Effective port number: the immediate byte, or the low 16 bits of
    DX for DX-port forms. This keeps the two addressing forms apart. -/
def portVon (op : IoOp) (regs : Register → Wort) : Nat :=
  match op.quelle with
  | .imm p => p % 256
  | .dx => (regs .rdx).toNat % 65536

/-- An immediate port resolves to its byte value. -/
theorem portVon_imm (dir : IoDir) (b : IoBreite) (p : Nat)
    (regs : Register → Wort) :
    portVon ⟨dir, b, .imm p⟩ regs = p % 256 := rfl

/-- A DX port resolves to the low 16 bits of DX. -/
theorem portVon_dx (dir : IoDir) (b : IoBreite) (regs : Register → Wort) :
    portVon ⟨dir, b, .dx⟩ regs = (regs .rdx).toNat % 65536 := rfl

/-- OUT payload: the accumulator value within its port width. -/
def ausGabe (b : IoBreite) (rax : Wort) : Nat :=
  rax.toNat % ioMaske b

/-- The OUT payload fits its width: the device store keeps it whole. -/
theorem ausGabe_passt (b : IoBreite) (rax : Wort) :
    ausGabe b rax < ioMaske b := by
  unfold ausGabe
  cases b <;> exact Nat.mod_lt _ (by decide)

/-- The OUT payload IS the canonical truncation of the accumulator. -/
theorem ausGabe_ist_trunc (b : IoBreite) (rax : Wort) :
    ausGabe b rax =
      match b with
      | .p8 => (trunc .b8 rax).toNat
      | .p16 => (trunc .b16 rax).toNat
      | .p32 => (trunc .b32 rax).toNat := by
  cases b <;> simp only [ausGabe, ioMaske] <;> rw [narrowTruncMod] <;> congr 1

/-- IN accumulator merge with width discipline over the canonical
    narrow merge: 8/16-bit writes preserve the upper bits, 32-bit
    writes clear them (zero extension into 64 bits). -/
def einMische (b : IoBreite) (alt neu : Wort) : Wort :=
  match b with
  | .p8 => mergeRegNarrow .b8 alt neu
  | .p16 => mergeRegNarrow .b16 alt neu
  | .p32 => mergeRegNarrow .b32 alt neu

/-- A 32-bit IN clears the upper 32 bits (zero extension). -/
theorem einMische_p32_fits (alt neu : Wort) :
    (einMische .p32 alt neu).toNat < 2 ^ 32 :=
  mergeRegNarrow_b32_fits alt neu

/-- Pinned 8-bit IN: the low byte lands, the upper bits are kept. -/
theorem pin_einMische_p8 :
    einMische .p8 0xABCDEF1234567890 0x11 = 0xABCDEF1234567811 := by
  decide

/-- Pinned 16-bit IN: the low half lands, the upper bits are kept. -/
theorem pin_einMische_p16 :
    einMische .p16 0xABCDEF1234567890 0x1122 = 0xABCDEF1234561122 := by
  decide

/-- Pinned 32-bit IN: the low word lands, the upper half is cleared. -/
theorem pin_einMische_p32 :
    einMische .p32 0xFFFFFFFFFFFFFFFF 0x11223344 = 0x11223344 := by
  decide

/-! ## One port step over machine, device and ordered event log.

   Checks the decode length, then privilege at the effective port,
   then runs the generic device answer. Denial (bad length, denied
   privilege) is an explicit `none`, never a silent skip. Canonical
   `Speicher` is never touched: IN/OUT move bytes between the
   accumulator and the device only. -/

/-- Port machine state: the canonical core, the generic device, and
    the ordered IO event log. -/
structure IoZustand where
  kern : Zustand
  geraet : GeraetZustand
  spur : List IoEreignis

/-- One port step under a privilege profile. -/
def ioSchritt (dec : IoDec) (s : IoZustand) (p : IoProfil) :
    Option IoZustand :=
  match laengeOk dec.laenge with
  | false => none
  | true =>
    let port := portVon dec.op s.kern.register
    match ioZugelassen p port with
    | false => none
    | true =>
      let nach := ripNach s.kern.rip dec.laenge
      match dec.op.dir with
      | .aus =>
        let v := ausGabe dec.op.breite (s.kern.register .rax)
        let (g', _) := geraetAntwort s.geraet .aus dec.op.breite v
        some ⟨{ s.kern with rip := nach }, g',
          s.spur ++ [⟨.aus, dec.op.breite, port, v⟩]⟩
      | .ein =>
        let (g', ans) := geraetAntwort s.geraet .ein dec.op.breite 0
        let w := BitVec.ofNat 64 ans
        let rax' := einMische dec.op.breite (s.kern.register .rax) w
        some ⟨{ s.kern with register := regSet s.kern.register .rax rax', rip := nach }, g', s.spur ++ [⟨.ein, dec.op.breite, port, ans⟩]⟩

/-- A bad decode length refuses every port form, unconditionally. -/
theorem ioSchritt_laenge_verweigert (dec : IoDec) (s : IoZustand)
    (p : IoProfil) (h : laengeOk dec.laenge = false) :
    ioSchritt dec s p = none := by
  unfold ioSchritt
  simp [h]

/-- Denied privilege refuses: no device contact, no event, no move. -/
theorem ioSchritt_privileg_verweigert (dec : IoDec) (s : IoZustand)
    (p : IoProfil) (hok : laengeOk dec.laenge = true)
    (hpriv : ioZugelassen p (portVon dec.op s.kern.register) = false) :
    ioSchritt dec s p = none := by
  unfold ioSchritt
  simp [hok, hpriv]

/-- OUT success: RIP advances, the device stores the payload, the
    ordered event lands, registers and memory are kept. -/
theorem ioSchritt_aus_erfolg (dec : IoDec) (s : IoZustand)
    (p : IoProfil) (b : IoBreite) (q : PortQuelle)
    (hok : laengeOk dec.laenge = true)
    (h : dec.op = ⟨.aus, b, q⟩)
    (hpriv : ioZugelassen p (portVon dec.op s.kern.register) = true) :
    ioSchritt dec s p =
      some ⟨{ s.kern with rip := ripNach s.kern.rip dec.laenge },
        (geraetAntwort s.geraet .aus b
          (ausGabe b (s.kern.register .rax))).1,
        s.spur ++ [⟨.aus, b, portVon dec.op s.kern.register,
          ausGabe b (s.kern.register .rax)⟩]⟩ := by
  unfold ioSchritt
  simp only [hok, hpriv]
  rw [h]

/-- IN success: RIP advances, the accumulator merges the answer with
    width discipline, the ordered event lands, memory is kept. -/
theorem ioSchritt_ein_erfolg (dec : IoDec) (s : IoZustand)
    (p : IoProfil) (b : IoBreite) (q : PortQuelle)
    (hok : laengeOk dec.laenge = true)
    (h : dec.op = ⟨.ein, b, q⟩)
    (hpriv : ioZugelassen p (portVon dec.op s.kern.register) = true) :
    ioSchritt dec s p =
      some ⟨{ s.kern with rip := ripNach s.kern.rip dec.laenge, register := regSet s.kern.register .rax (einMische b (s.kern.register .rax) (BitVec.ofNat 64 (geraetAntwort s.geraet .ein b 0).2)) },
        (geraetAntwort s.geraet .ein b 0).1,
        s.spur ++ [⟨.ein, b, portVon dec.op s.kern.register,
          (geraetAntwort s.geraet .ein b 0).2⟩]⟩ := by
  unfold ioSchritt
  simp only [hok, hpriv]
  rw [h]

/-- A port step never touches canonical memory: device bytes bypass
    RAM (and its TSO ordering) by construction. -/
theorem ioSchritt_speicher (dec : IoDec) (s s' : IoZustand)
    (p : IoProfil) (hstep : ioSchritt dec s p = some s') :
    s'.kern.speicher = s.kern.speicher := by
  unfold ioSchritt at hstep
  cases hlen : laengeOk dec.laenge with
  | false => simp [hlen] at hstep
  | true =>
    simp only [hlen] at hstep
    cases hpriv : ioZugelassen p (portVon dec.op s.kern.register) with
    | false => simp [hpriv] at hstep
    | true =>
      simp only [hpriv] at hstep
      cases hdir : dec.op.dir with
      | aus =>
        simp only [hdir] at hstep
        cases hstep
        rfl
      | ein =>
        simp only [hdir] at hstep
        cases hstep
        rfl

/-- A port step preserves the flags (IN/OUT are flag-neutral). -/
theorem ioSchritt_flags (dec : IoDec) (s s' : IoZustand)
    (p : IoProfil) (hstep : ioSchritt dec s p = some s') :
    s'.kern.flags = s.kern.flags := by
  unfold ioSchritt at hstep
  cases hlen : laengeOk dec.laenge with
  | false => simp [hlen] at hstep
  | true =>
    simp only [hlen] at hstep
    cases hpriv : ioZugelassen p (portVon dec.op s.kern.register) with
    | false => simp [hpriv] at hstep
    | true =>
      simp only [hpriv] at hstep
      cases hdir : dec.op.dir with
      | aus =>
        simp only [hdir] at hstep
        cases hstep
        rfl
      | ein =>
        simp only [hdir] at hstep
        cases hstep
        rfl

/-- A port step advances RIP past the decoded length. -/
theorem ioSchritt_rip (dec : IoDec) (s s' : IoZustand)
    (p : IoProfil) (hstep : ioSchritt dec s p = some s') :
    s'.kern.rip = ripNach s.kern.rip dec.laenge := by
  unfold ioSchritt at hstep
  cases hlen : laengeOk dec.laenge with
  | false => simp [hlen] at hstep
  | true =>
    simp only [hlen] at hstep
    cases hpriv : ioZugelassen p (portVon dec.op s.kern.register) with
    | false => simp [hpriv] at hstep
    | true =>
      simp only [hpriv] at hstep
      cases hdir : dec.op.dir with
      | aus =>
        simp only [hdir] at hstep
        cases hstep
        rfl
      | ein =>
        simp only [hdir] at hstep
        cases hstep
        rfl

/-- A port step appends exactly one ordered event. -/
theorem ioSchritt_spur_waechst (dec : IoDec) (s s' : IoZustand)
    (p : IoProfil) (hstep : ioSchritt dec s p = some s') :
    s'.spur.length = s.spur.length + 1 := by
  unfold ioSchritt at hstep
  cases hlen : laengeOk dec.laenge with
  | false => simp [hlen] at hstep
  | true =>
    simp only [hlen] at hstep
    cases hpriv : ioZugelassen p (portVon dec.op s.kern.register) with
    | false => simp [hpriv] at hstep
    | true =>
      simp only [hpriv] at hstep
      cases hdir : dec.op.dir with
      | aus =>
        simp only [hdir] at hstep
        cases hstep
        simp
      | ein =>
        simp only [hdir] at hstep
        cases hstep
        simp

/-- OUT keeps every register (the accumulator is only read). -/
theorem ioSchritt_aus_register (dec : IoDec) (s s' : IoZustand)
    (p : IoProfil) (b : IoBreite) (q : PortQuelle)
    (h : dec.op = ⟨.aus, b, q⟩)
    (hstep : ioSchritt dec s p = some s') (r : Register) :
    s'.kern.register r = s.kern.register r := by
  unfold ioSchritt at hstep
  cases hlen : laengeOk dec.laenge with
  | false => simp [hlen] at hstep
  | true =>
    simp only [hlen] at hstep
    cases hpriv : ioZugelassen p (portVon dec.op s.kern.register) with
    | false => simp [hpriv] at hstep
    | true =>
      simp only [hpriv] at hstep
      cases hdir : dec.op.dir with
      | aus =>
        simp only [hdir] at hstep
        cases hstep
        rfl
      | ein =>
        rw [h] at hdir
        simp at hdir

/-! ## Fetch and byte-step from actual executable memory.

   The fetched window is the state's ACTUAL bytes at `rip`
   (`Byteschritt.geholt`: executable prefix only, capped at 15).
   Admission checks the consumed length against the fetched window,
   the decode-length guard, and execute permission of the consumed
   prefix -- exactly the `fetchDekodiert` discipline, lifted to the
   port decoder. No caller-supplied decoded value is ever trusted. -/

/-- Fetch and decode: the port decoder over the actual fetched
    window, gated by unified admission. -/
def fetchIo (s : Zustand) : Option (IoDec × List Byte) :=
  match decodeIo (geholt s) with
  | none => none
  | some q =>
    if q.1.laenge + q.2.length == (geholt s).length &&
        laengeOk q.1.laenge && ausfuehrbarN s.speicher s.rip q.1.laenge
    then some q else none

/-- A successful fetch decodes the actual fetched bytes and carries
    its checked facts: consumed length plus remaining suffix is the
    fetched window, the length is valid, and the consumed prefix is
    executable. -/
theorem fetchIo_erfolg (s : Zustand) (d : IoDec) (rest : List Byte)
    (h : fetchIo s = some (d, rest)) :
    decodeIo (geholt s) = some (d, rest) ∧
      d.laenge + rest.length = (geholt s).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN s.speicher s.rip d.laenge = true := by
  have e : fetchIo s =
      match decodeIo (geholt s) with
      | none => (none : Option (IoDec × List Byte))
      | some q =>
        if q.1.laenge + q.2.length == (geholt s).length &&
            laengeOk q.1.laenge && ausfuehrbarN s.speicher s.rip q.1.laenge
        then some q else none := rfl
  rw [e] at h
  generalize hg : decodeIo (geholt s) = g at h
  cases g with
  | none =>
    simp at h
  | some pr =>
    obtain ⟨d', rest'⟩ := pr
    dsimp only at h
    by_cases hz : (d'.laenge + rest'.length == (geholt s).length &&
        laengeOk d'.laenge && ausfuehrbarN s.speicher s.rip d'.laenge) = true
    · rw [if_pos hz] at h
      have hp : d' = d ∧ rest' = rest := by simpa using h
      obtain ⟨hd, hr⟩ := hp
      rw [hd, hr] at hg hz
      simp only [Bool.and_eq_true] at hz
      obtain ⟨⟨hlen, hok⟩, hexe⟩ := hz
      refine ⟨h, by simpa using beq_iff_eq.mp hlen, hok, hexe⟩
    · rw [if_neg hz] at h
      simp at h

/-- One port byte step from actual memory: fetch, decode, privilege,
    then the device step. Takes ONLY the machine state and the
    privilege profile: a forged `IoDec` cannot inject an access. Any
    fetch or step failure is `none`. -/
def ioByteschritt (s : IoZustand) (p : IoProfil) : Option IoZustand :=
  match fetchIo s.kern with
  | none => none
  | some (d, _) => ioSchritt d s p

/-- Selection: a fetched port instruction steps through `ioSchritt`. -/
theorem ioByteschritt_weiter (s : IoZustand) (p : IoProfil)
    (d : IoDec) (rest : List Byte) (o : IoZustand)
    (hf : fetchIo s.kern = some (d, rest))
    (hs : ioSchritt d s p = some o) :
    ioByteschritt s p = some o := by
  have e : ioByteschritt s p =
      match fetchIo s.kern with
      | none => (none : Option IoZustand)
      | some (j, _) => ioSchritt j s p := rfl
  rw [e, hf]
  exact hs

/-- Selection: fetch refusal is byte-step refusal. -/
theorem ioByteschritt_verweigert (s : IoZustand) (p : IoProfil)
    (hf : fetchIo s.kern = none) :
    ioByteschritt s p = none := by
  have e : ioByteschritt s p =
      match fetchIo s.kern with
      | none => (none : Option IoZustand)
      | some (j, _) => ioSchritt j s p := rfl
  rw [e, hf]

/-! ## Adapter for the common hardware execution (owner 660).

   The port step lifted to the extended state: it runs on `kern`,
   XMM and FP control are untouched (mirroring `laufAlt`).
   Syscall/interrupt scope stays with lane 672: no trap form exists
   here, and the adapter never decodes or steps one. -/

/-- Adapter step on the extended state under a privilege profile. -/
def hw660Schritt (d : IoDec) (t : FpZustand) (g : GeraetZustand)
    (spur : List IoEreignis) (p : IoProfil) :
    Option (FpZustand × GeraetZustand × List IoEreignis) :=
  match ioSchritt d ⟨t.kern, g, spur⟩ p with
  | none => none
  | some s' => some (⟨s'.kern, t.xmm, t.fp⟩, s'.geraet, s'.spur)

/-- The consumed length of a decoded port instruction. -/
def hw660Laenge (d : IoDec) : Nat := d.laenge

/-- The adapter runs the port step on `kern`. -/
theorem hw660Schritt_kern (d : IoDec) (t : FpZustand)
    (g : GeraetZustand) (spur : List IoEreignis) (p : IoProfil)
    (s' : IoZustand)
    (h : ioSchritt d ⟨t.kern, g, spur⟩ p = some s') :
    hw660Schritt d t g spur p =
      some (⟨s'.kern, t.xmm, t.fp⟩, s'.geraet, s'.spur) := by
  unfold hw660Schritt
  rw [h]

/-- The adapter keeps every XMM register. -/
theorem hw660Schritt_xmm (d : IoDec) (t : FpZustand)
    (g : GeraetZustand) (spur : List IoEreignis) (p : IoProfil)
    (s' : IoZustand)
    (h : ioSchritt d ⟨t.kern, g, spur⟩ p = some s') (q : XmmReg) :
    (hw660Schritt d t g spur p).map (fun u => u.1.xmm q) =
      some (t.xmm q) := by
  simp [hw660Schritt, h]

/-- The adapter keeps the FP control word. -/
theorem hw660Schritt_fp (d : IoDec) (t : FpZustand)
    (g : GeraetZustand) (spur : List IoEreignis) (p : IoProfil)
    (s' : IoZustand)
    (h : ioSchritt d ⟨t.kern, g, spur⟩ p = some s') :
    (hw660Schritt d t g spur p).map (fun u => u.1.fp) =
      some t.fp := by
  simp [hw660Schritt, h]

/-- Adapter refusal is port-step refusal. -/
theorem hw660Schritt_verweigert (d : IoDec) (t : FpZustand)
    (g : GeraetZustand) (spur : List IoEreignis) (p : IoProfil)
    (h : ioSchritt d ⟨t.kern, g, spur⟩ p = none) :
    hw660Schritt d t g spur p = none := by
  unfold hw660Schritt
  rw [h]

/-! ## Validator admission: privilege plus memory kind.

   One port operation is validator-admitted exactly when privilege
   holds at the effective port AND the surrounding memory kind is
   admitted. Port IO runs beside ordinary RAM; MMIO and DMA kinds
   refuse under the default profile until their memory-type and
   ordering rules are modelled. -/

/-- Validator admission for one port operation at one memory kind. -/
def ioValOk (prof : IoProfil) (mem : SpeicherProfil) (art : SpeicherArt)
    (op : IoOp) (regs : Register → Wort) : Bool :=
  ioZugelassen prof (portVon op regs) && speicherArtZugelassen mem art

/-- Admission means privilege and kind, jointly. -/
theorem ioValOk_heisst (prof : IoProfil) (mem : SpeicherProfil)
    (art : SpeicherArt) (op : IoOp) (regs : Register → Wort)
    (h : ioValOk prof mem art op regs = true) :
    ioZugelassen prof (portVon op regs) = true ∧
      speicherArtZugelassen mem art = true := by
  unfold ioValOk at h
  simp only [Bool.and_eq_true] at h
  exact h

/-- Joint validator _zeuge: port IO over RAM is admitted, while MMIO
    and DMA refuse under the default profile -- at the witnessed
    port, register file and profiles, jointly. -/
theorem ioValOk_zeuge :
    ioValOk ioProfilZeuge speicherProfilZeuge .ram
        ⟨.aus, .p8, .imm 96⟩ (fun _ => BitVec.ofNat 64 0) = true ∧
      ioValOk ioProfilZeuge speicherProfilZeuge .mmio
        ⟨.aus, .p8, .imm 96⟩ (fun _ => BitVec.ofNat 64 0) = false ∧
      ioValOk ioProfilZeuge speicherProfilZeuge .dma
        ⟨.aus, .p8, .imm 96⟩ (fun _ => BitVec.ofNat 64 0) = false ∧
      ioValOk { ioProfilZeuge with iopl := 0 } speicherProfilZeuge .ram
        ⟨.aus, .p8, .imm 96⟩ (fun _ => BitVec.ofNat 64 0) = false := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  have hpriv : ioZugelassen { ioProfilZeuge with iopl := 0 }
      (portVon ⟨.aus, .p8, .imm 96⟩
        (fun _ => BitVec.ofNat 64 0)) = false := by
    apply ioZugelassen_privileg_verweigert
    decide
  simp [ioValOk, hpriv]

/-! ## Reached witness: a fetched IN/OUT sequence into real memory.

   The image holds three instructions back to back: an 8-bit IN from
   port 0x60 (2 bytes), an 8-bit OUT to port 0x60 (2 bytes) and a
   pilot 64-bit store (7 bytes). The device is preset to `0x1234`, so
   the IN answers `0x34 = 52`: the accumulator observably moves
   42 to 52, the OUT stores 52 back into the device (observable
   device change `0x1234` to 52), and the pilot store moves the
   received 52 into real canonical memory (cell 8192, zero to 52).
   Every step is fetched from ACTUAL executable memory. -/

/-- Witness image: IN (port 0x60) then OUT (port 0x60) then the
    pilot store `[rbx + 0], rax`. -/
def ioWitBild : List Byte :=
  [natByte 228, natByte 96, natByte 230, natByte 96,
   natByte 72, natByte 137, natByte 131,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- Witness code bytes: the image at 4096, zeroes elsewhere. -/
def ioWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else ioWitBild.getD (a.toNat - 4096) (BitVec.ofNat 8 0)

/-- Witness execute permission: the whole fetch window. -/
def ioWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4128)

/-- Witness data permission: one eight-byte cell at 8192. Code is
    deliberately NOT data-readable: fetch needs execute only. -/
def ioWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness memory: the port program at 4096, the data cell at 8192. -/
def ioWitSpeicher : Speicher :=
  { bytes := ioWitBytes, lesbar := ioWitDaten,
    schreibbar := ioWitDaten, ausfuehrbar := ioWitCode }

/-- Witness registers: 42 in rax, the cell address in rbx. -/
def ioWitReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 42
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness core state: code at 4096. -/
def ioWitKern : Zustand :=
  { register := ioWitReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := ioWitSpeicher }

/-- Witness start: the accumulator holds 42, the device `0x1234`. -/
def ioWitStart : IoZustand := ⟨ioWitKern, ⟨0x1234, 0⟩, []⟩

/-- One fetched port step under the witness profile. -/
def ioWitSchritt1 : Option IoZustand :=
  ioByteschritt ioWitStart ioProfilZeuge

/-- Two fetched port steps under the witness profile. -/
def ioWitSchritt2 : Option IoZustand :=
  ioWitSchritt1.bind (fun s => ioByteschritt s ioProfilZeuge)

/-- The third step is the pilot byte step (the store) on the reached
    core: port and pilot execution compose on the same `Zustand`. -/
def ioWitSchritt3 : ByteAusgang :=
  match ioWitSchritt2 with
  | none => .verweigert
  | some s => byteschritt s.kern

/-- Observe the accumulator of a port-step outcome. -/
def ioBeobAkk (o : Option IoZustand) : Option Wort :=
  o.map (fun s => s.kern.register .rax)

/-- Observe RIP of a port-step outcome. -/
def ioBeobRip (o : Option IoZustand) : Option Wort :=
  o.map (fun s => s.kern.rip)

/-- Observe the device register and counter of an outcome. -/
def ioBeobGeraet (o : Option IoZustand) : Option (Nat × Nat) :=
  o.map (fun s => (s.geraet.daten, s.geraet.zaehl))

/-- Observe the ordered event log of an outcome. -/
def ioBeobSpur (o : Option IoZustand) : Option (List IoEreignis) :=
  o.map (fun s => s.spur)

/-- First step: the fetched IN answers `0x34 = 52` into AL. -/
theorem ioWit_erster_empfaengt :
    ioBeobAkk ioWitSchritt1 = some (BitVec.ofNat 64 52) := by
  decide

/-- Both port steps: the device moved `0x1234` to 52 with two
    observations, the accumulator holds the received 52, RIP is past
    both instructions, and the ordered log holds IN then OUT. -/
theorem ioWit_zweiter_sendet :
    ioBeobGeraet ioWitSchritt2 = some (52, 2) ∧
    ioBeobAkk ioWitSchritt2 = some (BitVec.ofNat 64 52) ∧
    ioBeobRip ioWitSchritt2 = some (BitVec.ofNat 64 4100) ∧
    ioBeobSpur ioWitSchritt2 =
      some [⟨.ein, .p8, 96, 52⟩, ⟨.aus, .p8, 96, 52⟩] := by
  decide

/-- Third step: the pilot store moves the received 52 into the real
    canonical cell and advances past the store. -/
theorem ioWit_dritter_speichert :
    ausgangByte (BitVec.ofNat 64 8192) ioWitSchritt3 =
      some (BitVec.ofNat 8 52) ∧
    ausgangRip ioWitSchritt3 = some (BitVec.ofNat 64 4107) := by
  decide

/-- The start cell reads zero: the run really changes memory. -/
theorem ioWit_anfang_null :
    ioWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 := by
  decide

/-- Past the port forms the stepper refuses pilot bytes: no silent
    execution of non-port forms. -/
theorem ioWit_pilot_wird_verweigert :
    ioWitSchritt2.bind (fun s => ioByteschritt s ioProfilZeuge) =
      none := by
  decide

/-- Denied privilege refuses the very first fetch: no device contact,
    no event, no move. -/
theorem ioWit_ohne_privileg_verweigert :
    ioByteschritt ioWitStart { ioProfilZeuge with iopl := 0 } =
      none := by
  decide

/-- A closed master switch refuses despite a fully named bitmap. -/
theorem ioWit_schalter_aus_verweigert :
    ioByteschritt ioWitStart { ioProfilZeuge with ioErlaubt := false } =
      none := by
  decide

/-- Witness memory with a forged first opcode byte. -/
def ioWitBytesFalsch (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 255 else ioWitBytes a

/-- Witness start standing on the forged opcode byte. -/
def ioWitStartFalsch : IoZustand :=
  ⟨{ ioWitKern with speicher := { ioWitSpeicher with
    bytes := ioWitBytesFalsch } }, ⟨0x1234, 0⟩, []⟩

/-- A forged first opcode byte refuses (unknown port form). -/
theorem ioWit_byte_geaendert_verweigert :
    ioByteschritt ioWitStartFalsch ioProfilZeuge = none := by
  decide

/-! ## Joint witnesses: reached memory/device change plus refusals. -/

/-- JOINT WITNESS: the fetched IN answers 52 into the accumulator,
    the fetched OUT stores 52 into the device (two observations), the
    pilot store moves the received 52 into real canonical memory from
    a zeroed cell -- and past the port forms plus under denied
    privilege the same stepper refuses. Non-degenerate: a
    device-changing and memory-changing reached run plus planted
    refusals, jointly instantiated. -/
theorem ioWit_lauf_zeuge :
    ioBeobAkk ioWitSchritt1 = some (BitVec.ofNat 64 52) ∧
    ioBeobGeraet ioWitSchritt2 = some (52, 2) ∧
    ioBeobSpur ioWitSchritt2 =
      some [⟨.ein, .p8, 96, 52⟩, ⟨.aus, .p8, 96, 52⟩] ∧
    ausgangByte (BitVec.ofNat 64 8192) ioWitSchritt3 =
      some (BitVec.ofNat 8 52) ∧
    ioWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 ∧
    ioWitSchritt2.bind (fun s => ioByteschritt s ioProfilZeuge) =
      none ∧
    ioByteschritt ioWitStart { ioProfilZeuge with iopl := 0 } =
      none := by
  refine ⟨ioWit_erster_empfaengt, ioWit_zweiter_sendet.1,
    ioWit_zweiter_sendet.2.2.2, ioWit_dritter_speichert.1,
    ioWit_anfang_null, ioWit_pilot_wird_verweigert,
    ioWit_ohne_privileg_verweigert⟩

/-- `decodeIo_consumes` at the witness: the IN row consumes 2 of 2. -/
theorem decodeIo_consumes_zeuge :
    (⟨⟨.ein, .p8, .imm 96⟩, 2⟩ : IoDec).laenge +
        ([] : List Byte).length =
      (encodeIo ⟨.ein, .p8, .imm 96⟩).length ∧
    1 ≤ (⟨⟨.ein, .p8, .imm 96⟩, 2⟩ : IoDec).laenge ∧
    (⟨⟨.ein, .p8, .imm 96⟩, 2⟩ : IoDec).laenge ≤ 15 := by
  have h : decodeIo (encodeIo ⟨.ein, .p8, .imm 96⟩ ++ []) =
      some (⟨⟨.ein, .p8, .imm 96⟩, 2⟩, []) := by
    simpa using roundtrip_io_ein_p8_imm 96 []
  exact decodeIo_consumes _ _ _ h

/-- `ioSchritt_aus_erfolg` at the witness: OUT stores the payload. -/
theorem ioSchritt_aus_erfolg_zeuge :
    ioSchritt ⟨⟨.aus, .p8, .imm 96⟩, 2⟩ ⟨ioWitKern, ⟨0, 0⟩, []⟩
        ioProfilZeuge =
      some ⟨{ ioWitKern with rip := ripNach ioWitKern.rip 2 },
        (geraetAntwort ⟨0, 0⟩ .aus .p8
          (ausGabe .p8 (ioWitReg .rax))).1,
        ([] : List IoEreignis) ++ [⟨.aus, .p8, 96,
          ausGabe .p8 (ioWitReg .rax)⟩]⟩ :=
  ioSchritt_aus_erfolg _ _ _ _ _ (by decide) rfl (by decide)

/-- `ioSchritt_ein_erfolg` at the witness: IN merges the answer. -/
theorem ioSchritt_ein_erfolg_zeuge :
    ioSchritt ⟨⟨.ein, .p8, .imm 96⟩, 2⟩ ⟨ioWitKern, ⟨0x1234, 0⟩, []⟩
        ioProfilZeuge =
      some ⟨{ ioWitKern with rip := ripNach ioWitKern.rip 2, register := regSet ioWitKern.register .rax (einMische .p8 (ioWitKern.register .rax) (BitVec.ofNat 64 (geraetAntwort ⟨0x1234, 0⟩ .ein .p8 0).2)) },
        (geraetAntwort ⟨0x1234, 0⟩ .ein .p8 0).1,
        ([] : List IoEreignis) ++ [⟨.ein, .p8, 96,
          (geraetAntwort ⟨0x1234, 0⟩ .ein .p8 0).2⟩]⟩ :=
  ioSchritt_ein_erfolg _ _ _ _ _ (by decide) rfl (by decide)

/-- `ioZugelassen_heisst_alle` at the witness profile and port. -/
theorem ioZugelassen_heisst_alle_zeuge :
    ioProfilZeuge.ioErlaubt = true ∧
      ioProfilZeuge.cpl ≤ ioProfilZeuge.iopl ∧
      ioProfilZeuge.erlaubt 96 = true :=
  ioZugelassen_heisst_alle _ _ ioProfilZeuge_laesst_60_zu

/-- `hw660Schritt_xmm` at the witness: the adapter keeps XMM0. -/
theorem hw660Schritt_xmm_zeuge :
    (hw660Schritt ⟨⟨.aus, .p8, .imm 96⟩, 2⟩
      ⟨ioWitKern, fun _ => BitVec.ofNat 128 0, kontextReset⟩
      ⟨0, 0⟩ [] ioProfilZeuge).map (fun u => u.1.xmm .xmm0) =
      some (BitVec.ofNat 128 0) :=
  hw660Schritt_xmm _ _ _ _ _ _ ioSchritt_aus_erfolg_zeuge .xmm0

/-- `hw660Schritt_fp` at the witness: the adapter keeps control. -/
theorem hw660Schritt_fp_zeuge :
    (hw660Schritt ⟨⟨.aus, .p8, .imm 96⟩, 2⟩
      ⟨ioWitKern, fun _ => BitVec.ofNat 128 0, kontextReset⟩
      ⟨0, 0⟩ [] ioProfilZeuge).map (fun u => u.1.fp) =
      some kontextReset :=
  hw660Schritt_fp _ _ _ _ _ _ ioSchritt_aus_erfolg_zeuge

/-- The adapter moves the device answer while keeping XMM/control:
    joint adapter witness over the generic lemmas. -/
theorem hw660Schritt_zeuge :
    ((hw660Schritt ⟨⟨.aus, .p8, .imm 96⟩, 2⟩
      ⟨ioWitKern, fun _ => BitVec.ofNat 128 0, kontextReset⟩
      ⟨0, 0⟩ [] ioProfilZeuge).map (fun u => u.2.1.daten) =
      some 42) ∧
    ((hw660Schritt ⟨⟨.aus, .p8, .imm 96⟩, 2⟩
      ⟨ioWitKern, fun _ => BitVec.ofNat 128 0, kontextReset⟩
      ⟨0, 0⟩ [] ioProfilZeuge).map (fun u => u.1.xmm .xmm0) =
      some (BitVec.ofNat 128 0)) := by
  refine ⟨by decide, hw660Schritt_xmm_zeuge⟩

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary (`Typen`,
   `Wort.trunc`, `Speicher.read64`/`write64`, `Ausfuehrung.laengeOk`/
   `ripNach`/`regSet`/`zeugeFlags`, `Codec.natByte`/`byteNat`,
   `Byteschritt.geholt`/`ausfuehrbarN`/`byteschritt`/`ausgangByte`/
   `ausgangRip`, `NarrowOps.mergeRegNarrow`/`narrowTruncMod`,
   `Gleitprofil.kontextReset`, `ScalarFloat.FpZustand`): exact
   selected port instructions (IN/OUT, widths 8/16/32,
   immediate-port versus DX-port forms) with canonical byte
   encode/decode, generic round trips, arbitrary-input length
   coverage and planted refusals; a finite privilege profile
   (CPL against IOPL, master switch, per-port bitmap) with
   denied-privilege refusal; a typed finite memory-kind interface
   admitting RAM and refusing MMIO/DMA; a GENERIC hardware
   device-response interface (data register plus observation
   counter, ordered IO events, no OS/library contract); the port
   step with accumulator width discipline (8/16-bit preserve,
   32-bit zero-extends, via the canonical narrow merge), exact
   frame facts (canonical memory never touched, flags kept, RIP
   advanced, one ordered event, OUT keeps registers), fetched
   execution under the `fetchDekodiert` discipline, the 660
   hardware-execution adapter (XMM/control untouched) and the
   port/validator admission; a joint fetched IN/OUT run that
   observably changes the device (`0x1234` to 52), the accumulator
   (42 to 52) and real canonical memory (cell 8192 zero to 52)
   with ordered events, plus planted malformed-byte, privilege,
   control-switch, pilot-byte and memory-kind refusals.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are a stated canonical
     subset with self-consistency only. `.tmp/HARDWARE-REFERENCES/
     REFERENCES.json` is absent on this machine, so no manual
     heading/page is cited; SDM IN/OUT, IOPL/TSS and memory-type
     correspondence stays OPEN.
   - No MMIO/DMA execution: both kinds refuse by admission; their
     memory-type and ordering rules are unmodelled, and no TSO
     store buffer ever carries a device byte by construction.
   - No 16-bit address-size or string-IO forms (INS/OUTS), no REP
     prefix, no per-port TSS-bit beyond the abstract bitmap, no
     timing: the bitmap's OS-side population is user logic.
   - No syscall/interrupt/trap scope (lane 672): no trap form is
     decoded or stepped here.
   - No source correspondence, no TSO/W/GX bridge, no ABI/image,
     entry, relocation, cost or termination claim; `none` is the
     absence of a transition, never a halt claim.
   - Full system/device scope remains OPEN wherever an essential
     emitted device form lacks covered architectural rules.
-/

#print axioms breiteAusNat_bits
#print axioms encodeIo_len
#print axioms roundtripIo
#print axioms decodeIo_consumes
#print axioms io_nichts_pilot_ret
#print axioms ioZugelassen_heisst_alle
#print axioms speicherArt_zeuge
#print axioms geraetAntwort_zeuge
#print axioms ausGabe_passt
#print axioms ausGabe_ist_trunc
#print axioms einMische_p32_fits
#print axioms ioSchritt_laenge_verweigert
#print axioms ioSchritt_privileg_verweigert
#print axioms ioSchritt_aus_erfolg
#print axioms ioSchritt_ein_erfolg
#print axioms ioSchritt_speicher
#print axioms ioSchritt_flags
#print axioms ioSchritt_rip
#print axioms ioSchritt_spur_waechst
#print axioms ioSchritt_aus_register
#print axioms fetchIo_erfolg
#print axioms ioByteschritt_weiter
#print axioms ioByteschritt_verweigert
#print axioms hw660Schritt_kern
#print axioms hw660Schritt_xmm
#print axioms hw660Schritt_fp
#print axioms ioValOk_heisst
#print axioms ioValOk_zeuge
#print axioms ioWit_lauf_zeuge
#print axioms decodeIo_consumes_zeuge
#print axioms ioSchritt_aus_erfolg_zeuge
#print axioms ioSchritt_ein_erfolg_zeuge
#print axioms hw660Schritt_zeuge

end Gabbro.Grammatik.X86
