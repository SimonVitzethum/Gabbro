/-
  File:      Grammatik/X86/NarrowCodec.lean
  Subject:   Byte-facing decoder/encoder and execution connection for
             accepted NarrowOps rows.

  Lane 562: covers exactly four narrow rows with a bounded independent
  extension decoder plus a canonical encoder: 32-bit register move
  (`mov32rr`, opcode 89 without REX.W), byte-to-32 zero/sign extension
  (`movzx8`/`movsx8`, opcodes 0F B6/BE without REX.W) and the 32-bit
  base-plus-displacement store (`store32`, opcode 89 mod=2 without
  REX.W). Every form always carries a canonical REX byte with W=0/X=0
  (values 40/41/44/45); REX.W=1 stays the pilot's domain and REX.X=1 is
  refused everywhere. The pilot `decode`/`schritt` are reused unchanged:
  dispatch tries the pilot first and consults the extension only where
  the pilot refuses (mirroring `decodeErw`); execution reuses the
  accepted `NarrowOps` evaluators on the same `Zustand`. No hardware
  correspondence is claimed: encodings are a stated canonical subset
  with self-consistency (round trip) only.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.DecodingCoverage
import Grammatik.X86.NarrowOps

namespace Gabbro.Grammatik.X86

/-- Covered narrow extension rows. Only these four rows are claimed;
    16-bit extension (0F B7/BF) and narrow loads stay open. -/
inductive NarrowOp where
  | mov32rr (dst src : Register)
  | movzx8 (dst src : Register)
  | movsx8 (dst src : Register)
  | store32 (base src : Register) (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- A decoded narrow instruction with its consumed length. -/
structure NarrowDec where
  op : NarrowOp
  laenge : Nat
  deriving DecidableEq, Repr

/-- Canonical REX byte with W=0/X=0: R=rh, B=bh extension bits. -/
def rexNarrow (rh bh : Nat) : Byte := natByte (64 + 4 * rh + bh)

/-- Accepted REX prefix bits: exactly 40/41/44/45 (W=0, X=0). -/
def rexNarrowBits : Byte → Option (Nat × Nat)
  | b =>
    match byteNat b with
    | 64 => some (0, 0)
    | 65 => some (0, 1)
    | 68 => some (1, 0)
    | 69 => some (1, 1)
    | _ => none

/-- Canonical byte encoding of one covered narrow row. Register moves
    and extensions are register-direct (mod=3); the store is
    base-plus-disp32 (mod=2) with the SIB byte exactly when the base
    needs it, mirroring the pilot store shape without REX.W. -/
def encodeNarrow : NarrowOp → List Byte
  | .mov32rr dst src =>
    [rexNarrow (regHigh src) (regHigh dst), natByte 137,
     modrmReg (regLow src) (regLow dst)]
  | .movzx8 dst src =>
    [rexNarrow (regHigh dst) (regHigh src), natByte 15, natByte 182,
     modrmReg (regLow dst) (regLow src)]
  | .movsx8 dst src =>
    [rexNarrow (regHigh dst) (regHigh src), natByte 15, natByte 190,
     modrmReg (regLow dst) (regLow src)]
  | .store32 base src d =>
    let head := [rexNarrow (regHigh src) (regHigh base), natByte 137,
      modrmMem (regLow src) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d

/-- Consumed length of one covered narrow row. -/
def narrowLen : NarrowOp → Nat
  | .mov32rr _ _ => 3
  | .movzx8 _ _ => 4
  | .movsx8 _ _ => 4
  | .store32 base _ _ => if regLow base == 4 then 8 else 7

/-- Every covered encoding fits the 15-byte instruction cap. -/
theorem encodeNarrow_len (op : NarrowOp) :
    1 ≤ (encodeNarrow op).length ∧ (encodeNarrow op).length ≤ 15 := by
  cases op with
  | mov32rr dst src => exact show 1 ≤ 3 ∧ 3 ≤ 15 from by decide
  | movzx8 dst src => exact show 1 ≤ 4 ∧ 4 ≤ 15 from by decide
  | movsx8 dst src => exact show 1 ≤ 4 ∧ 4 ≤ 15 from by decide
  | store32 base src d =>
    simp only [encodeNarrow]
    split
    · exact show 1 ≤ 8 ∧ 8 ≤ 15 from by decide
    · exact show 1 ≤ 7 ∧ 7 ≤ 15 from by decide

/-- The REX encoder lands in the accepted prefix set. -/
theorem rexNarrowBits_rexNarrow (rh bh : Nat)
    (hrh : rh < 2) (hbh : bh < 2) :
    rexNarrowBits (rexNarrow rh bh) = some (rh, bh) := by
  unfold rexNarrowBits rexNarrow
  have h1 : rh = 0 ∨ rh = 1 := by omega
  have h2 : bh = 0 ∨ bh = 1 := by omega
  cases h1 with
  | inl h0 =>
    cases h2 with
    | inl h3 => subst h0; subst h3; rfl
    | inr h3 => subst h0; subst h3; rfl
  | inr h0 =>
    cases h2 with
    | inl h3 => subst h0; subst h3; rfl
    | inr h3 => subst h0; subst h3; rfl

/-- Decode the store tail after REX and opcode 137: mod=2 with the SIB
    byte exactly when the base needs it, mirroring the pilot store
    shape. Length 8 with SIB, 7 without; anything else refuses. -/
def decodeNarrowStore (rh bh : Nat) (reg rm : Nat) :
    List Byte → Option (NarrowDec × List Byte)
  | [] => none
  | b :: rest =>
    if rm == 4 then
      if byteNat b == 36 then
        match parseLe32 rest with
        | some (d, rest') =>
          match codeReg (rh * 8 + reg), codeReg (bh * 8 + rm) with
          | some rs, some rb => some (⟨.store32 rb rs d, 8⟩, rest')
          | _, _ => none
        | none => none
      else none
    else
      match parseLe32 (b :: rest) with
      | some (d, rest') =>
        match codeReg (rh * 8 + reg), codeReg (bh * 8 + rm) with
        | some rs, some rb => some (⟨.store32 rb rs d, 7⟩, rest')
        | _, _ => none
      | none => none

/-- Decode after REX and opcode 137: mod=3 is the 32-bit register
    move, mod=2 the store tail; every other mode refuses. -/
def decodeNarrow89 (rh bh : Nat) (rest : List Byte) :
    Option (NarrowDec × List Byte) :=
  match rest with
  | [] => none
  | m :: rest' =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 3 =>
      match codeReg (rh * 8 + reg), codeReg (bh * 8 + rm) with
      | some rs, some rd => some (⟨.mov32rr rd rs, 3⟩, rest')
      | _, _ => none
    | 2 => decodeNarrowStore rh bh reg rm rest'
    | _ => none

/-- Decode after REX and the 0F prefix: only the covered byte-extension
    opcodes 182 (zero) and 190 (sign) in register-direct mode. The
    16-bit rows 183/191 and every memory mode refuse. -/
def decodeNarrow0F (rh bh : Nat) : List Byte → Option (NarrowDec × List Byte)
  | [] => none
  | op :: rest =>
    match byteNat op with
    | 182 =>
      match rest with
      | [] => none
      | m :: rest' =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        match byteNat m / 64 with
        | 3 =>
          match codeReg (rh * 8 + reg), codeReg (bh * 8 + rm) with
          | some rd, some rs => some (⟨.movzx8 rd rs, 4⟩, rest')
          | _, _ => none
        | _ => none
    | 190 =>
      match rest with
      | [] => none
      | m :: rest' =>
        let reg := byteNat m / 8 % 8
        let rm := byteNat m % 8
        match byteNat m / 64 with
        | 3 =>
          match codeReg (rh * 8 + reg), codeReg (bh * 8 + rm) with
          | some rd, some rs => some (⟨.movsx8 rd rs, 4⟩, rest')
          | _, _ => none
        | _ => none
    | _ => none

/-- Bounded independent extension decoder: a canonical REX prefix with
    W=0/X=0, then opcode 137 (move/store) or 15/182-190 (extension).
    Only canonical encodings are accepted; anything else refuses. -/
def decodeNarrowTail (rh bh : Nat) : List Byte → Option (NarrowDec × List Byte)
  | [] => none
  | b2 :: rest =>
    match byteNat b2 with
    | 137 => decodeNarrow89 rh bh rest
    | 15 => decodeNarrow0F rh bh rest
    | _ => none

/-- Top-level extension decode: the REX prefix selects the extension
    rows; anything without a canonical REX refuses. -/
def decodeNarrow : List Byte → Option (NarrowDec × List Byte)
  | [] => none
  | r :: tail =>
    match rexNarrowBits r with
    | none => none
    | some (rh, bh) => decodeNarrowTail rh bh tail

/-- Round trip for the 32-bit register move. -/
theorem roundtrip_mov32rr (dst src : Register) (suffix : List Byte) :
    decodeNarrow (encodeNarrow (.mov32rr dst src) ++ suffix) =
      some (⟨.mov32rr dst src, (encodeNarrow (.mov32rr dst src)).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for byte-to-32 zero extension. -/
theorem roundtrip_movzx8 (dst src : Register) (suffix : List Byte) :
    decodeNarrow (encodeNarrow (.movzx8 dst src) ++ suffix) =
      some (⟨.movzx8 dst src, (encodeNarrow (.movzx8 dst src)).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for byte-to-32 sign extension. -/
theorem roundtrip_movsx8 (dst src : Register) (suffix : List Byte) :
    decodeNarrow (encodeNarrow (.movsx8 dst src) ++ suffix) =
      some (⟨.movsx8 dst src, (encodeNarrow (.movsx8 dst src)).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

set_option maxHeartbeats 4000000 in
/-- Round trip for the 32-bit store, both SIB and non-SIB shapes. -/
theorem roundtrip_store32 (base src : Register) (d : BitVec 32)
    (suffix : List Byte) :
    decodeNarrow (encodeNarrow (.store32 base src d) ++ suffix) =
      some (⟨.store32 base src d, (encodeNarrow (.store32 base src d)).length⟩,
        suffix) := by
  cases base <;> cases src <;>
    simp [encodeNarrow, decodeNarrow, decodeNarrowTail, decodeNarrow89,
      decodeNarrowStore, codeReg, regCode, regHigh, regLow, rexNarrow,
      rexNarrowBits, modrmMem, leBytes32, parseLe32_cons]

/-- Decoding inverts encoding on every covered narrow row, over any
    suffix. The decoded length is the consumed prefix length. -/
theorem roundtripNarrow (op : NarrowOp) (suffix : List Byte) :
    decodeNarrow (encodeNarrow op ++ suffix) =
      some (⟨op, (encodeNarrow op).length⟩, suffix) := by
  cases op with
  | mov32rr dst src => exact roundtrip_mov32rr dst src suffix
  | movzx8 dst src => exact roundtrip_movzx8 dst src suffix
  | movsx8 dst src => exact roundtrip_movsx8 dst src suffix
  | store32 base src d => exact roundtrip_store32 base src d suffix

/-- A successful extension round trip consumes exactly its prefix. -/
theorem roundtripNarrow_len_ok (op : NarrowOp) (suffix : List Byte) :
    ∃ (n : Nat) (rest : List Byte),
      decodeNarrow (encodeNarrow op ++ suffix) = some (⟨op, n⟩, rest) ∧
        n + rest.length = (encodeNarrow op ++ suffix).length ∧
        1 ≤ n ∧ n ≤ 15 := by
  refine ⟨(encodeNarrow op).length, suffix, roundtripNarrow op suffix, ?_, ?_, ?_⟩
  · rw [List.length_append]
  · exact (encodeNarrow_len op).1
  · exact (encodeNarrow_len op).2

/-! ## Arbitrary-input coverage: every success consumes its stated length. -/

/-- Coverage shape: every covered narrow row with its exact length.
    The register move takes 3 bytes, each extension 4, the store 7 or 8. -/
def narrowDecktAb (d : NarrowDec) : Prop :=
  (∃ dst src, d.op = .mov32rr dst src ∧ d.laenge = 3) ∨
  (∃ dst src, d.op = .movzx8 dst src ∧ d.laenge = 4) ∨
  (∃ dst src, d.op = .movsx8 dst src ∧ d.laenge = 4) ∨
  (∃ base src disp, d.op = .store32 base src disp ∧
    (d.laenge = 7 ∨ d.laenge = 8))

/-- Store coverage: three outer bytes (REX, opcode, ModRM) plus the SIB
    byte with displacement (length 8) or the displacement alone
    (length 7). Truncated displacements and a wrong SIB byte refuse. -/
theorem decodeNarrowStore_abdeckung (rh bh reg rm : Nat) (bs : List Byte)
    (d : NarrowDec) (rest' : List Byte)
    (h : decodeNarrowStore rh bh reg rm bs = some (d, rest')) :
    (∃ pre, bs = pre ++ rest' ∧ pre.length + 3 = d.laenge) ∧
      laengeOk d.laenge = true ∧ narrowDecktAb d := by
  cases bs with
  | nil => simp [decodeNarrowStore] at h
  | cons b t =>
    simp only [decodeNarrowStore] at h
    split at h
    · split at h
      · cases hparse : parseLe32 t with
        | none => simp [hparse] at h
        | some pr =>
          obtain ⟨v, mid⟩ := pr
          simp only [hparse] at h
          cases hc1 : codeReg (rh * 8 + reg) with
          | none =>
            cases hc2 : codeReg (bh * 8 + rm) with
            | none => simp [hc1, hc2] at h
            | some rb => simp [hc1, hc2] at h
          | some rs =>
            cases hc2 : codeReg (bh * 8 + rm) with
            | none => simp [hc1, hc2] at h
            | some rb =>
              simp only [hc1, hc2] at h
              obtain ⟨b0, b1, b2, b3, h4⟩ :=
                parseLe32_suffix t v mid hparse
              cases h
              refine ⟨⟨[b, b0, b1, b2, b3], by simp [h4], rfl⟩, rfl, ?_⟩
              exact Or.inr (Or.inr (Or.inr
                ⟨_, _, _, rfl, Or.inr rfl⟩))
      · simp at h
    · cases hparse : parseLe32 (b :: t) with
      | none => simp [hparse] at h
      | some pr =>
        obtain ⟨v, mid⟩ := pr
        simp only [hparse] at h
        cases hc1 : codeReg (rh * 8 + reg) with
        | none =>
          cases hc2 : codeReg (bh * 8 + rm) with
          | none => simp [hc1, hc2] at h
          | some rb => simp [hc1, hc2] at h
        | some rs =>
          cases hc2 : codeReg (bh * 8 + rm) with
          | none => simp [hc1, hc2] at h
          | some rb =>
            simp only [hc1, hc2] at h
            obtain ⟨b0, b1, b2, b3, h4⟩ :=
              parseLe32_suffix (b :: t) v mid hparse
            cases h
            refine ⟨⟨[b0, b1, b2, b3], h4, rfl⟩, rfl, ?_⟩
            exact Or.inr (Or.inr (Or.inr
              ⟨_, _, _, rfl, Or.inl rfl⟩))

/-- Opcode-137 coverage: mod 3 reuses the register move at stated
    length 3, mod 2 the store level; every other mode refuses.
    Two outer bytes (REX, opcode) sit above this level. -/
theorem decodeNarrow89_abdeckung (rh bh : Nat) (bs : List Byte)
    (d : NarrowDec) (rest' : List Byte)
    (h : decodeNarrow89 rh bh bs = some (d, rest')) :
    (∃ pre, bs = pre ++ rest' ∧ pre.length + 2 = d.laenge) ∧
      laengeOk d.laenge = true ∧ narrowDecktAb d := by
  cases bs with
  | nil => simp [decodeNarrow89] at h
  | cons m t =>
    simp only [decodeNarrow89] at h
    split at h
    · cases hc1 : codeReg (rh * 8 + byteNat m / 8 % 8) with
      | none =>
        cases hc2 : codeReg (bh * 8 + byteNat m % 8) with
        | none => simp [hc1, hc2] at h
        | some rd => simp [hc1, hc2] at h
      | some rs =>
        cases hc2 : codeReg (bh * 8 + byteNat m % 8) with
        | none => simp [hc1, hc2] at h
        | some rd =>
          simp only [hc1, hc2] at h
          cases h
          exact ⟨⟨[m], rfl, rfl⟩, rfl,
            Or.inl ⟨_, _, rfl, rfl⟩⟩
    · have hsub := decodeNarrowStore_abdeckung rh bh (byteNat m / 8 % 8)
          (byteNat m % 8) t d rest' h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (m :: pre).length = pre.length + 1 := rfl
      exact ⟨⟨m :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
    · simp at h

/-- Extension-opcode coverage: only the covered byte-extension opcodes
    182 (zero) and 190 (sign) in register-direct mode; the 16-bit rows
    and every memory mode refuse. Two outer bytes (REX, 0F) sit above. -/
theorem decodeNarrow0F_abdeckung (rh bh : Nat) (bs : List Byte)
    (d : NarrowDec) (rest' : List Byte)
    (h : decodeNarrow0F rh bh bs = some (d, rest')) :
    (∃ pre, bs = pre ++ rest' ∧ pre.length + 2 = d.laenge) ∧
      laengeOk d.laenge = true ∧ narrowDecktAb d := by
  cases bs with
  | nil => simp [decodeNarrow0F] at h
  | cons op t =>
    simp only [decodeNarrow0F] at h
    split at h
    · cases t with
      | nil => simp at h
      | cons m t2 =>
        dsimp only at h
        split at h
        · cases hc1 : codeReg (rh * 8 + byteNat m / 8 % 8) with
          | none =>
            cases hc2 : codeReg (bh * 8 + byteNat m % 8) with
            | none => simp [hc1, hc2] at h
            | some rs => simp [hc1, hc2] at h
          | some rd =>
            cases hc2 : codeReg (bh * 8 + byteNat m % 8) with
            | none => simp [hc1, hc2] at h
            | some rs =>
              simp only [hc1, hc2] at h
              cases h
              exact ⟨⟨[op, m], rfl, rfl⟩, rfl,
                Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)⟩
        · simp at h
    · cases t with
      | nil => simp at h
      | cons m t2 =>
        dsimp only at h
        split at h
        · cases hc1 : codeReg (rh * 8 + byteNat m / 8 % 8) with
          | none =>
            cases hc2 : codeReg (bh * 8 + byteNat m % 8) with
            | none => simp [hc1, hc2] at h
            | some rs => simp [hc1, hc2] at h
          | some rd =>
            cases hc2 : codeReg (bh * 8 + byteNat m % 8) with
            | none => simp [hc1, hc2] at h
            | some rs =>
              simp only [hc1, hc2] at h
              cases h
              exact ⟨⟨[op, m], rfl, rfl⟩, rfl,
                Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl⟩))⟩
        · simp at h
    · simp at h

/-- NARROW DECODER COVERAGE: every successful `decodeNarrow` of an
    ARBITRARY byte list consumes exactly its stated length, the length
    is valid (1..15), the decoded row is one of the four covered rows
    at its exact length, and the input splits into consumed prefix and
    remaining suffix. Proved from the decoder side only. -/
theorem decodeNarrowTail_abdeckung (rh bh : Nat) (bs : List Byte)
    (d : NarrowDec) (rest : List Byte)
    (h : decodeNarrowTail rh bh bs = some (d, rest)) :
    (∃ pre, bs = pre ++ rest ∧ pre.length + 1 = d.laenge) ∧
      laengeOk d.laenge = true ∧ narrowDecktAb d := by
  cases bs with
  | nil => simp [decodeNarrowTail] at h
  | cons b2 t2 =>
    simp only [decodeNarrowTail] at h
    split at h
    · have hsub := decodeNarrow89_abdeckung rh bh t2 d rest h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (b2 :: pre).length = pre.length + 1 := rfl
      refine ⟨⟨b2 :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
    · have hsub := decodeNarrow0F_abdeckung rh bh t2 d rest h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (b2 :: pre).length = pre.length + 1 := rfl
      refine ⟨⟨b2 :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
    · simp at h

/-- Top-level narrow coverage: the REX prefix plus the tail rows. -/
theorem decodeNarrow_abdeckung (bs : List Byte) (d : NarrowDec)
    (rest : List Byte) (h : decodeNarrow bs = some (d, rest)) :
    (∃ pre, bs = pre ++ rest ∧ pre.length = d.laenge) ∧
      laengeOk d.laenge = true ∧ narrowDecktAb d := by
  cases bs with
  | nil => simp [decodeNarrow] at h
  | cons r t =>
    simp only [decodeNarrow] at h
    cases hrex : rexNarrowBits r with
    | none => simp [hrex] at h
    | some pr =>
      obtain ⟨rh, bh⟩ := pr
      simp only [hrex] at h
      have hsub := decodeNarrowTail_abdeckung rh bh t d rest h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (r :: pre).length = pre.length + 1 := rfl
      exact ⟨⟨r :: pre, by simp [hbs], by omega⟩, hok, hshape⟩

/-- Every successful extension decode of an arbitrary input consumes
    exactly its stated length within 1..15. -/
theorem decodeNarrow_consumes (bs : List Byte) (d : NarrowDec)
    (rest : List Byte) (h : decodeNarrow bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
  obtain ⟨⟨pre, hbs, hlen⟩, hok, _⟩ := decodeNarrow_abdeckung bs d rest h
  have hbl : bs.length = pre.length + rest.length := by
    rw [hbs, List.length_append]
  have hb : 1 ≤ d.laenge ∧ d.laenge ≤ 15 := by
    simp only [laengeOk, decide_eq_true_eq] at hok
    exact hok
  exact ⟨by omega, hb.1, hb.2⟩

/-! ## Pinned bytes and explicit refusals. -/

/-- Pinned bytes: 32-bit move of ecx into eax. -/
theorem pin_mov32_eax_ecx :
    encodeNarrow (.mov32rr .rax .rcx) =
      [natByte 64, natByte 137, natByte 200] := by
  decide

/-- Pinned decode: 32-bit move of ecx into eax. -/
theorem pin_mov32_eax_ecx_dekode :
    decodeNarrow [natByte 64, natByte 137, natByte 200] =
      some ((⟨.mov32rr .rax .rcx, 3⟩ : NarrowDec), []) := by
  decide

/-- Pinned bytes: zero extension of cl into eax. -/
theorem pin_movzx_eax_cl :
    encodeNarrow (.movzx8 .rax .rcx) =
      [natByte 64, natByte 15, natByte 182, natByte 193] := by
  decide

/-- Pinned decode: zero extension of cl into eax. -/
theorem pin_movzx_eax_cl_dekode :
    decodeNarrow [natByte 64, natByte 15, natByte 182, natByte 193] =
      some ((⟨.movzx8 .rax .rcx, 4⟩ : NarrowDec), []) := by
  decide

/-- Pinned bytes: sign extension of cl into eax. -/
theorem pin_movsx_eax_cl :
    encodeNarrow (.movsx8 .rax .rcx) =
      [natByte 64, natByte 15, natByte 190, natByte 193] := by
  decide

/-- Pinned bytes: 32-bit move between extended registers. -/
theorem pin_mov32_r9_r15 :
    encodeNarrow (.mov32rr .r9 .r15) =
      [natByte 69, natByte 137, natByte 249] := by
  decide

/-- Pinned decode: 32-bit move between extended registers. -/
theorem pin_mov32_r9_r15_dekode :
    decodeNarrow [natByte 69, natByte 137, natByte 249] =
      some ((⟨.mov32rr .r9 .r15, 3⟩ : NarrowDec), []) := by
  decide

/-- Pinned bytes: 32-bit store through rsp needs the SIB byte. -/
theorem pin_store32_rsp :
    encodeNarrow (.store32 .rsp .rax 16) =
      [natByte 64, natByte 137, natByte 132, natByte 36,
       natByte 16, natByte 0, natByte 0, natByte 0] := by
  decide

/-- Pinned decode: 32-bit store through rsp. -/
theorem pin_store32_rsp_dekode :
    decodeNarrow [natByte 64, natByte 137, natByte 132, natByte 36,
      natByte 16, natByte 0, natByte 0, natByte 0] =
      some ((⟨.store32 .rsp .rax 16, 8⟩ : NarrowDec), []) := by
  decide

/-- The empty input decodes to nothing. -/
theorem narrow_nichts_leer : decodeNarrow [] = none := rfl

/-- A lone REX prefix is truncated. -/
theorem narrow_nichts_rex_allein : decodeNarrow [natByte 64] = none := rfl

/-- A 32-bit move without its ModRM byte is truncated. -/
theorem narrow_nichts_bewegung_kurz :
    decodeNarrow [natByte 64, natByte 137] = none := rfl

/-- Opcode 1 (add) has no narrow row here. -/
theorem narrow_nichts_add_opcode :
    decodeNarrow [natByte 64, natByte 1, natByte 201] = none := rfl

/-- The 16-bit extension row 183 is not covered and refuses. -/
theorem narrow_nichts_sechzehn_erweiterung :
    decodeNarrow [natByte 64, natByte 15, natByte 183, natByte 193] =
      none := rfl

/-- A REX prefix with the W bit set stays the pilot's domain. -/
theorem narrow_nichts_rex_w :
    decodeNarrow [natByte 72, natByte 137, natByte 201] = none := rfl

/-- A REX prefix with the X bit set is not canonical. -/
theorem narrow_nichts_rex_x :
    decodeNarrow [natByte 66, natByte 137, natByte 201] = none := rfl

/-- A mod=0 memory form is not a covered narrow row. -/
theorem narrow_nichts_modus_null :
    decodeNarrow [natByte 64, natByte 137, natByte 8] = none := rfl

/-- A wrong SIB byte is refused. -/
theorem narrow_nichts_sib_falsch :
    decodeNarrow [natByte 64, natByte 137, natByte 132, natByte 0,
      natByte 0, natByte 0, natByte 0, natByte 0] = none := rfl

/-- A store with a short displacement is truncated. -/
theorem narrow_nichts_speicher_kurz :
    decodeNarrow [natByte 64, natByte 137, natByte 132, natByte 36,
      natByte 16] = none := rfl

/-- A register-direct extension opcode with a memory ModRM refuses:
    no narrow load row is covered. -/
theorem narrow_nichts_erweiterung_speicher :
    decodeNarrow [natByte 64, natByte 15, natByte 182, natByte 129] =
      none := rfl

/-! ## Pilot disjointness and the combined dispatcher. -/

/-- DISJOINTNESS: the pilot decoder refuses every covered narrow
    encoding, over any suffix. The extension never collides with an
    accepted pilot form; dispatch order stays canonical-first. -/
theorem narrow_pilot_verweigert (op : NarrowOp) (suffix : List Byte) :
    decode (encodeNarrow op ++ suffix) = none := by
  cases op with
  | mov32rr dst src => cases dst <;> cases src <;> rfl
  | movzx8 dst src => cases dst <;> cases src <;> rfl
  | movsx8 dst src => cases dst <;> cases src <;> rfl
  | store32 base src d => cases base <;> cases src <;> rfl

/-- Combined decode: the pilot first, the narrow extension only where
    the pilot refuses. Mirrors `decodeErw`: no pilot form is shadowed
    and no pilot byte string is re-decided. -/
def decodeCombo (bs : List Byte) :
    Option ((Decodiert ⊕ NarrowDec) × List Byte) :=
  match decode bs with
  | some (d, rest) => some (.inl d, rest)
  | none =>
    match decodeNarrow bs with
    | some (n, rest) => some (.inr n, rest)
    | none => none

/-- The combined decoder agrees with the pilot on every byte string
    the pilot accepts: no existing form is shadowed. -/
theorem decodeCombo_kanonisch (bs : List Byte) (d : Decodiert)
    (rest : List Byte) (h : decode bs = some (d, rest)) :
    decodeCombo bs = some (.inl d, rest) := by
  unfold decodeCombo
  rw [h]

/-- Where the pilot refuses, a covered narrow row is taken. -/
theorem decodeCombo_erweitert (bs : List Byte) (n : NarrowDec)
    (rest : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = some (n, rest)) :
    decodeCombo bs = some (.inr n, rest) := by
  unfold decodeCombo
  rw [h1, h2]

/-- Where both refuse, the combined decoder refuses. -/
theorem decodeCombo_nichts (bs : List Byte) (h1 : decode bs = none)
    (h2 : decodeNarrow bs = none) :
    decodeCombo bs = none := by
  unfold decodeCombo
  rw [h1, h2]

/-! ## Execution: the accepted narrow evaluator plus the length advance. -/

/-- Narrow step over the same `Zustand`: the accepted `NarrowOps`
    evaluator with RIP advanced past the decoded length. Register
    forms reuse `moveNarrow` and the extend-plus-merge composition of
    `loadNarrowExtend`; the store reuses `storeNarrow`. Flags follow
    the MOV discipline (preserved); a bad length or failed memory
    access is an explicit refusal. -/
def stepNarrow (d : NarrowDec) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.op with
    | .mov32rr dst src =>
      some ({ moveNarrow s .b32 dst src with rip := nach })
    | .movzx8 dst src =>
      some ({ s with register := regSet s.register dst (mergeRegNarrow .b32 (s.register dst) (extendNarrow .zero .b8 (s.register src))), rip := nach })
    | .movsx8 dst src =>
      some ({ s with register := regSet s.register dst (mergeRegNarrow .b32 (s.register dst) (extendNarrow .sign .b8 (s.register src))), rip := nach })
    | .store32 base src disp =>
      match storeNarrow s .b32 (effAddr s base disp) src with
      | some s' => some ({ s' with rip := nach })
      | none => none

/-- The 32-bit move steps through the accepted register evaluator. -/
theorem stepNarrow_mov32 (d : NarrowDec) (s : Zustand)
    (dst src : Register) (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32rr dst src) :
    stepNarrow d s =
      some ({ moveNarrow s .b32 dst src with
        rip := ripNach s.rip d.laenge }) := by
  unfold stepNarrow
  rw [hok, h]

/-- Zero extension steps through the accepted extend-plus-merge. -/
theorem stepNarrow_movzx8 (d : NarrowDec) (s : Zustand)
    (dst src : Register) (hok : laengeOk d.laenge = true)
    (h : d.op = .movzx8 dst src) :
    stepNarrow d s =
      some ({ s with register := regSet s.register dst (mergeRegNarrow .b32 (s.register dst) (extendNarrow .zero .b8 (s.register src))), rip := ripNach s.rip d.laenge }) := by
  unfold stepNarrow
  rw [hok, h]

/-- Sign extension steps through the accepted extend-plus-merge. -/
theorem stepNarrow_movsx8 (d : NarrowDec) (s : Zustand)
    (dst src : Register) (hok : laengeOk d.laenge = true)
    (h : d.op = .movsx8 dst src) :
    stepNarrow d s =
      some ({ s with register := regSet s.register dst (mergeRegNarrow .b32 (s.register dst) (extendNarrow .sign .b8 (s.register src))), rip := ripNach s.rip d.laenge }) := by
  unfold stepNarrow
  rw [hok, h]

/-- Store success carries the accepted narrow store plus the advance. -/
theorem stepNarrow_store_erfolg (d : NarrowDec) (s : Zustand)
    (base src : Register) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .store32 base src disp)
    (hwr : storeNarrow s .b32 (effAddr s base disp) src =
      some ({ s with speicher := m })) :
    stepNarrow d s =
      some ({ s with speicher := m, rip := ripNach s.rip d.laenge }) := by
  simp only [stepNarrow, hok, h, hwr]

/-- Store refusal: a failed narrow write is an explicit step failure. -/
theorem stepNarrow_store_verweigert (d : NarrowDec) (s : Zustand)
    (base src : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .store32 base src disp)
    (hwr : storeNarrow s .b32 (effAddr s base disp) src = none) :
    stepNarrow d s = none := by
  simp only [stepNarrow, hok, h, hwr]

/-- A bad decode length refuses every narrow form, unconditionally. -/
theorem stepNarrow_laenge_verweigert (d : NarrowDec) (s : Zustand)
    (h : laengeOk d.laenge = false) : stepNarrow d s = none := by
  unfold stepNarrow
  simp [h]

/-! ## Width-exact frame facts by reuse of the accepted evaluator. -/

/-- The 32-bit move lands the architectural merge, keeps flags and
    memory, and advances RIP past the decoded length. -/
theorem stepNarrow_mov32_rahmen (d : NarrowDec) (s s' : Zustand)
    (dst src : Register) (hok : laengeOk d.laenge = true)
    (h : d.op = .mov32rr dst src) (hstep : stepNarrow d s = some s') :
    s'.register dst = mergeRegNarrow .b32 (s.register dst) (s.register src) ∧
      s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip d.laenge := by
  rw [stepNarrow_mov32 d s dst src hok h] at hstep
  cases hstep
  refine ⟨?_, rfl, rfl, rfl⟩
  show (moveNarrow s .b32 dst src).register dst = _
  unfold moveNarrow
  exact regSet_gleich _ _ _

/-- Zero extension lands the source-extended merge, keeps flags and
    memory, and advances RIP past the decoded length. -/
theorem stepNarrow_movzx8_rahmen (d : NarrowDec) (s s' : Zustand)
    (dst src : Register) (hok : laengeOk d.laenge = true)
    (h : d.op = .movzx8 dst src) (hstep : stepNarrow d s = some s') :
    s'.register dst =
        mergeRegNarrow .b32 (s.register dst)
          (extendNarrow .zero .b8 (s.register src)) ∧
      s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip d.laenge := by
  rw [stepNarrow_movzx8 d s dst src hok h] at hstep
  cases hstep
  refine ⟨?_, rfl, rfl, rfl⟩
  show regSet s.register dst (mergeRegNarrow .b32 (s.register dst) (extendNarrow .zero .b8 (s.register src))) dst = _
  exact regSet_gleich _ _ _

/-- Sign extension lands the source-extended merge, keeps flags and
    memory, and advances RIP past the decoded length. -/
theorem stepNarrow_movsx8_rahmen (d : NarrowDec) (s s' : Zustand)
    (dst src : Register) (hok : laengeOk d.laenge = true)
    (h : d.op = .movsx8 dst src) (hstep : stepNarrow d s = some s') :
    s'.register dst =
        mergeRegNarrow .b32 (s.register dst)
          (extendNarrow .sign .b8 (s.register src)) ∧
      s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip d.laenge := by
  rw [stepNarrow_movsx8 d s dst src hok h] at hstep
  cases hstep
  refine ⟨?_, rfl, rfl, rfl⟩
  show regSet s.register dst (mergeRegNarrow .b32 (s.register dst) (extendNarrow .sign .b8 (s.register src))) dst = _
  exact regSet_gleich _ _ _

/-- A successful narrow store changes nothing outside its four bytes
    (reuses the canonical 32-bit frame). -/
theorem stepNarrow_store_rahmen (d : NarrowDec) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32) (m : Speicher) (x : Adresse)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .store32 base src disp)
    (hwr : writeBreite s.speicher .b32 (effAddr s base disp)
      (trunc .b32 (s.register src)) = some m)
    (hstep : stepNarrow d s = some s')
    (haussen : ∀ k : Nat, k < 4 → x ≠ addrOff (effAddr s base disp) k) :
    s'.speicher.bytes x = s.speicher.bytes x := by
  have hsn := storeNarrow_success s .b32 (effAddr s base disp) src m hwr
  rw [stepNarrow_store_erfolg d s base src disp m hok h hsn] at hstep
  cases hstep
  exact storeNarrow_frame_b32 s { s with speicher := m }
    (effAddr s base disp) x src m hwr hsn haussen

/-- A successful narrow store preserves the flags. -/
theorem stepNarrow_store_flags (d : NarrowDec) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true)
    (h : d.op = .store32 base src disp)
    (hwr : writeBreite s.speicher .b32 (effAddr s base disp)
      (trunc .b32 (s.register src)) = some m)
    (hstep : stepNarrow d s = some s') :
    s'.flags = s.flags := by
  have hsn := storeNarrow_success s .b32 (effAddr s base disp) src m hwr
  rw [stepNarrow_store_erfolg d s base src disp m hok h hsn] at hstep
  cases hstep
  rfl

/-! ## Reached witnesses: memory change, extension pins, step refusals. -/

/-- Witness registers: the data address in rbx, the spill word in rax. -/
def narrowWitReg : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rax then spillVal
  else BitVec.ofNat 64 0

/-- Witness start state: data cell at 8192, code at 4096. -/
def narrowWitState : Zustand :=
  { register := narrowWitReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugenSpeicher }

/-- MEMORY-CHANGING narrow witness: the decoded 32-bit store moves the
    spill word's low byte into the data cell (zero to 4) and advances
    RIP past its 7 bytes. -/
theorem narrow_store_witness :
    ((stepNarrow ⟨.store32 .rbx .rax (BitVec.ofNat 32 0), 7⟩
      narrowWitState).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 4)) ∧
    ((stepNarrow ⟨.store32 .rbx .rax (BitVec.ofNat 32 0), 7⟩
      narrowWitState).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4103)) ∧
    narrowWitState.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 := by
  decide

/-- Witness registers for extension: all-ones destination, 0x80 source. -/
def narrowWitExtReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF
  else if q = Register.rcx then BitVec.ofNat 64 0x80
  else BitVec.ofNat 64 0

/-- Witness start state for extension pins. -/
def narrowWitExtState : Zustand :=
  { register := narrowWitExtReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugenSpeicher }

/-- ZERO-EXTENSION pin through the step: 0x80 grows to 0x80 with the
    upper 32 bits cleared, RIP advances past 4 bytes. -/
theorem narrow_movzx_witness :
    ((stepNarrow ⟨.movzx8 .rax .rcx, 4⟩
      narrowWitExtState).map (fun s => s.register .rax) =
      some (BitVec.ofNat 64 0x80)) ∧
    ((stepNarrow ⟨.movzx8 .rax .rcx, 4⟩
      narrowWitExtState).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4100)) := by
  decide

/-- SIGN-EXTENSION pin through the step: 0x80 grows to 0xFFFFFF80
    with the upper 32 bits cleared, RIP advances past 4 bytes. -/
theorem narrow_movsx_witness :
    ((stepNarrow ⟨.movsx8 .rax .rcx, 4⟩
      narrowWitExtState).map (fun s => s.register .rax) =
      some (BitVec.ofNat 64 0xFFFFFF80)) ∧
    ((stepNarrow ⟨.movsx8 .rax .rcx, 4⟩
      narrowWitExtState).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4100)) := by
  decide

/-- 32-BIT MOVE pin through the step: the low 32 bits land, the upper
    half is cleared even over an all-ones destination. -/
theorem narrow_mov32_witness :
    ((stepNarrow ⟨.mov32rr .rax .rcx, 3⟩
      narrowWitExtState).map (fun s => s.register .rax) =
      some (BitVec.ofNat 64 0x80)) ∧
    ((stepNarrow ⟨.mov32rr .rax .rcx, 3⟩
      narrowWitExtState).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4099)) := by
  decide

/-- STEP LENGTH REFUSAL: a decoded row with length 0 has no transition. -/
theorem narrow_schritt_laenge_null :
    stepNarrow ⟨.mov32rr .rax .rcx, 0⟩ narrowWitExtState = none := by
  decide

/-- Witness memory without write permission anywhere. -/
def narrowOhneSchreib : Speicher :=
  { bytes := zeugeBytes, lesbar := zeugeWahr,
    schreibbar := fun _ => false, ausfuehrbar := zeugeFalsch }

/-- Witness state standing on write-denied memory. -/
def narrowWitKeinSchreib : Zustand :=
  { narrowWitState with speicher := narrowOhneSchreib }

/-- STEP STORE REFUSAL: without write permission the decoded store has
    no transition, while the address and length are unchanged data. -/
theorem narrow_schritt_speicher_verweigert :
    stepNarrow ⟨.store32 .rbx .rax (BitVec.ofNat 32 0), 7⟩
      narrowWitKeinSchreib = none := by
  decide

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary (`Typen`,
   `Wort.trunc`/`sext`, `Speicher.readBreite`/`writeBreite`,
   `Ausfuehrung.laengeOk`/`ripNach`/`effAddr`/`regSet`,
   `Codec.codeReg`/`regHigh`/`regLow`/`modrmReg`/`modrmMem`/`parseLe32`,
   `DecodingCoverage.parseLe32_suffix`, `NarrowOps.moveNarrow`/
   `extendNarrow`/`mergeRegNarrow`/`storeNarrow` and the UNCHANGED pilot
   `Codec.decode`): the four covered narrow rows (`NarrowOp`/`NarrowDec`)
   with a canonical encoder (`encodeNarrow`, 1..15 lengths), a bounded
   independent extension decoder (`decodeNarrow` via `decodeNarrowTail`,
   `decodeNarrow89`, `decodeNarrow0F`, `decodeNarrowStore`) with generic
   round trips (`roundtripNarrow`), decoder-side arbitrary-input
   coverage (`decodeNarrow_abdeckung` with per-level shape lemmas and
   the `decodeNarrow_consumes` corollary), pinned bytes for the move,
   both extensions and the SIB store, explicit refusals (empty,
   truncated, corrupt opcode, non-canonical REX.W/X, wrong mod/SIB,
   uncovered 16-bit extension rows 183/191), pilot disjointness
   (`narrow_pilot_verweigert`: the pilot refuses every covered
   encoding, so canonical-first dispatch never collides) with the
   combined dispatcher (`decodeCombo` and its three dispatch facts,
   mirroring `decodeErw`), and the execution connection (`stepNarrow`
   reusing the accepted narrow evaluator on the same `Zustand` with
   per-form step equations, width-exact frame facts and reached
   witnesses: a memory-changing store, zero/sign-extension pins, a
   32-bit clearing pin, plus step-level length and permission refusals).
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are a stated canonical
     subset with self-consistency only; silicon, caches, TLBs, store
     buffers and 16-bit rows are open.
   - No full narrow family: narrow loads, 16-bit extensions (opcodes
     183/191 refuse loudly here) and narrow ALU forms stay open; each
     new row needs its own encoding, coverage and execution proof.
   - No fetch wiring: `Byteschritt` still fetches with the pilot
     `decode` only; routing `fetchDekodiert` through `decodeCombo`
     waits on the `Typen`/`Bild` owners and is the next integration.
   - No source correspondence, no TSO bridge, no ABI/image, entry,
     relocation, cost or termination claim; `verweigert`/`none` is the
     absence of a transition, never a halt claim.
   - No new hardware or software assumptions: the only gates are the
     checked decode length and the canonical memory permissions.
-/

#print axioms encodeNarrow_len
#print axioms rexNarrowBits_rexNarrow
#print axioms roundtripNarrow
#print axioms roundtripNarrow_len_ok
#print axioms narrowDecktAb
#print axioms decodeNarrowStore_abdeckung
#print axioms decodeNarrow89_abdeckung
#print axioms decodeNarrow0F_abdeckung
#print axioms decodeNarrowTail_abdeckung
#print axioms decodeNarrow_abdeckung
#print axioms decodeNarrow_consumes
#print axioms pin_mov32_eax_ecx_dekode
#print axioms pin_movzx_eax_cl_dekode
#print axioms pin_store32_rsp_dekode
#print axioms narrow_pilot_verweigert
#print axioms decodeCombo_kanonisch
#print axioms decodeCombo_erweitert
#print axioms decodeCombo_nichts
#print axioms stepNarrow_mov32
#print axioms stepNarrow_movzx8
#print axioms stepNarrow_movsx8
#print axioms stepNarrow_store_erfolg
#print axioms stepNarrow_store_verweigert
#print axioms stepNarrow_laenge_verweigert
#print axioms stepNarrow_mov32_rahmen
#print axioms stepNarrow_movzx8_rahmen
#print axioms stepNarrow_movsx8_rahmen
#print axioms stepNarrow_store_rahmen
#print axioms stepNarrow_store_flags
#print axioms narrow_store_witness
#print axioms narrow_movzx_witness
#print axioms narrow_movsx_witness
#print axioms narrow_mov32_witness
#print axioms narrow_schritt_laenge_null
#print axioms narrow_schritt_speicher_verweigert

end Gabbro.Grammatik.X86
