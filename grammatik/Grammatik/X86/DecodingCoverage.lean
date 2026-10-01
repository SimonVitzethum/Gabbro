/-
  Decoder/fetch coverage from the actual decoder (lane 435).

  The byte pilot (`Codec`) proves round trips per instruction and the fetch
  layer (`Byteschritt`) checks consumed-length consistency at runtime, but the
  general fact -- every successful `decode` of an ARBITRARY byte list consumes
  exactly its stated length within 1..15 -- is open in both files. This module
  closes it from the decoder side only (never from encoder round trips), adds
  the per-form exact-length classification, the suffix/window congruence, and
  the executable entry-byte relation over loaded images. No hardware, source,
  TSO or whole-image claim is made here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.Bild

namespace Gabbro.Grammatik.X86

/-- Executable entry window: the first `n` bytes of a loaded image at entry
    `e` under `bias`, read through the checked section mapping. -/
def eintrittFenster (bild : Bild) (bias e n : Nat) : List Byte :=
  (List.range n).map (fun i => ladenByte bild bias (e + i))

/-- Entry decode: the actual decoder over the entry window, capped at the
    15-byte maximum. Length comes from decoding only, never an annotation. -/
def eintrittDekodiert (bild : Bild) (bias e : Nat) :
    Option (Decodiert × List Byte) :=
  decode (eintrittFenster bild bias e fetchCap)

/-! ## 1. Little-endian suffix facts: parsing exposes its bytes. -/

/-- A successful 32-bit parse exposes exactly four head bytes. -/
theorem parseLe32_suffix (bs : List Byte) (v : BitVec 32) (rest : List Byte)
    (h : parseLe32 bs = some (v, rest)) :
    ∃ b0 b1 b2 b3, bs = b0 :: b1 :: b2 :: b3 :: rest := by
  cases bs with
  | nil => simp [parseLe32] at h
  | cons b0 t =>
    cases t with
    | nil => simp [parseLe32] at h
    | cons b1 t2 =>
      cases t2 with
      | nil => simp [parseLe32] at h
      | cons b2 t3 =>
        cases t3 with
        | nil => simp [parseLe32] at h
        | cons b3 t4 =>
          simp only [parseLe32] at h
          cases Option.some_inj.mp h
          exact ⟨b0, b1, b2, b3, rfl⟩

/-- A successful 64-bit parse exposes exactly eight head bytes. -/
theorem parseLe64_suffix (bs : List Byte) (v : Wort) (rest : List Byte)
    (h : parseLe64 bs = some (v, rest)) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7,
      bs = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest := by
  cases bs with
  | nil => simp [parseLe64] at h
  | cons b0 t =>
    cases t with
    | nil => simp [parseLe64] at h
    | cons b1 t2 =>
      cases t2 with
      | nil => simp [parseLe64] at h
      | cons b2 t3 =>
        cases t3 with
        | nil => simp [parseLe64] at h
        | cons b3 t4 =>
          cases t4 with
          | nil => simp [parseLe64] at h
          | cons b4 t5 =>
            cases t5 with
            | nil => simp [parseLe64] at h
            | cons b5 t6 =>
              cases t6 with
              | nil => simp [parseLe64] at h
              | cons b6 t7 =>
                cases t7 with
                | nil => simp [parseLe64] at h
                | cons b7 t8 =>
                  simp only [parseLe64] at h
                  cases Option.some_inj.mp h
                  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩

/-- A successful 32-bit parse consumes four bytes. -/
theorem parseLe32_len (bs : List Byte) (v : BitVec 32) (rest : List Byte)
    (h : parseLe32 bs = some (v, rest)) :
    bs.length = 4 + rest.length := by
  obtain ⟨b0, b1, b2, b3, h4⟩ := parseLe32_suffix bs v rest h
  rw [h4]
  simp only [List.length_cons]
  omega

/-- A successful 64-bit parse consumes eight bytes. -/
theorem parseLe64_len (bs : List Byte) (v : Wort) (rest : List Byte)
    (h : parseLe64 bs = some (v, rest)) :
    bs.length = 8 + rest.length := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h8⟩ :=
    parseLe64_suffix bs v rest h
  rw [h8]
  simp only [List.length_cons]
  omega

/-! ## 2. Coverage shape: every accepted pilot form, exact length. -/

/-- Coverage shape: every accepted pilot form with its exact consumed length.
    All 14 `Befehl` constructors appear: `ret` at 1, `push`/`pop` at 1 or 2,
    the five register-direct operations at 3, `movImm64` at 10, `load`/`store`
    at 7 or 8, `jump`/`call` at 5 and the conditional jump at 6. -/
def decktAb (d : Decodiert) : Prop :=
  (d.befehl = .ret ∧ d.laenge = 1) ∨
  (∃ r, d.befehl = .push64 r ∧ (d.laenge = 1 ∨ d.laenge = 2)) ∨
  (∃ r, d.befehl = .pop64 r ∧ (d.laenge = 1 ∨ d.laenge = 2)) ∨
  (∃ dst src, (d.befehl = .movReg64 dst src ∨ d.befehl = .addReg64 dst src ∨
    d.befehl = .subReg64 dst src ∨ d.befehl = .xorReg64 dst src ∨
    d.befehl = .cmpReg64 dst src) ∧ d.laenge = 3) ∨
  (∃ dst v, d.befehl = .movImm64 dst v ∧ d.laenge = 10) ∨
  (∃ dst base disp, (d.befehl = .load64 dst base disp ∨
    d.befehl = .store64 base dst disp) ∧ (d.laenge = 7 ∨ d.laenge = 8)) ∨
  (∃ disp, (d.befehl = .jump32 disp ∨ d.befehl = .call32 disp) ∧
    d.laenge = 5) ∨
  (∃ c disp, d.befehl = .jumpIf32 c disp ∧ d.laenge = 6)

/-! ## 3. Register-direct level: no byte consumed, length 3 stated. -/

/-- Register-direct coverage: the tail passes through untouched while the
    stated length 3 accounts for the outer REX, opcode and ModRM bytes. -/
theorem decodeRegReg_abdeckung (op rBit bBit reg rm : Nat) (rest : List Byte)
    (d : Decodiert) (rest' : List Byte)
    (h : decodeRegReg op rBit bBit reg rm rest = some (d, rest')) :
    (∃ pre, rest = pre ++ rest' ∧ pre.length + 3 = d.laenge) ∧
      laengeOk d.laenge = true ∧ decktAb d := by
  unfold decodeRegReg at h
  cases h1 : codeReg (rBit * 8 + reg) with
  | none =>
    cases h2 : codeReg (bBit * 8 + rm) with
    | none => simp [h1, h2] at h
    | some rd => simp [h1, h2] at h
  | some rs =>
    cases h2 : codeReg (bBit * 8 + rm) with
    | none => simp [h1, h2] at h
    | some rd =>
      simp only [h1, h2] at h
      split at h
      · cases h
        exact ⟨⟨[], rfl, rfl⟩, rfl,
          Or.inr (Or.inr (Or.inr (Or.inl ⟨rd, rs, Or.inl rfl, rfl⟩)))⟩
      · cases h
        exact ⟨⟨[], rfl, rfl⟩, rfl,
          Or.inr (Or.inr (Or.inr (Or.inl
            ⟨rd, rs, Or.inr (Or.inl rfl), rfl⟩)))⟩
      · cases h
        exact ⟨⟨[], rfl, rfl⟩, rfl,
          Or.inr (Or.inr (Or.inr (Or.inl
            ⟨rd, rs, Or.inr (Or.inr (Or.inl rfl)), rfl⟩)))⟩
      · cases h
        exact ⟨⟨[], rfl, rfl⟩, rfl,
          Or.inr (Or.inr (Or.inr (Or.inl
            ⟨rd, rs, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩)))⟩
      · cases h
        exact ⟨⟨[], rfl, rfl⟩, rfl,
          Or.inr (Or.inr (Or.inr (Or.inl
            ⟨rd, rs, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩)))⟩
      · simp at h

/-! ## 4. Memory level: SIB byte plus displacement, or displacement. -/

/-- Memory coverage: three outer bytes (REX, opcode, ModRM) plus the SIB
    byte with displacement (length 8) or the displacement alone (length 7).
    Truncated displacements and a wrong SIB byte refuse. -/
theorem decodeMem_abdeckung (isLoad : Bool) (rBit bBit reg rm : Nat)
    (bs : List Byte) (d : Decodiert) (rest' : List Byte)
    (h : decodeMem isLoad rBit bBit reg rm bs = some (d, rest')) :
    (∃ pre, bs = pre ++ rest' ∧ pre.length + 3 = d.laenge) ∧
      laengeOk d.laenge = true ∧ decktAb d := by
  cases bs with
  | nil => simp [decodeMem] at h
  | cons b t =>
    simp only [decodeMem] at h
    split at h
    · split at h
      · cases hparse : parseLe32 t with
        | none => simp [hparse] at h
        | some pr =>
          obtain ⟨v, mid⟩ := pr
          simp only [hparse] at h
          cases hc1 : codeReg (rBit * 8 + reg) with
          | none =>
            cases hc2 : codeReg (bBit * 8 + rm) with
            | none => simp [hc1, hc2] at h
            | some rb => simp [hc1, hc2] at h
          | some rr =>
            cases hc2 : codeReg (bBit * 8 + rm) with
            | none => simp [hc1, hc2] at h
            | some rb =>
              simp only [hc1, hc2] at h
              obtain ⟨b0, b1, b2, b3, h4⟩ :=
                parseLe32_suffix t v mid hparse
              split at h
              · cases h
                refine ⟨⟨[b, b0, b1, b2, b3], by simp [h4], rfl⟩, rfl, ?_⟩
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨rr, rb, v, Or.inl rfl, Or.inr rfl⟩)))))
              · cases h
                refine ⟨⟨[b, b0, b1, b2, b3], by simp [h4], rfl⟩, rfl, ?_⟩
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨rr, rb, v, Or.inr rfl, Or.inr rfl⟩)))))
      · simp at h
    · cases hparse : parseLe32 (b :: t) with
      | none => simp [hparse] at h
      | some pr =>
        obtain ⟨v, mid⟩ := pr
        simp only [hparse] at h
        cases hc1 : codeReg (rBit * 8 + reg) with
        | none =>
          cases hc2 : codeReg (bBit * 8 + rm) with
          | none => simp [hc1, hc2] at h
          | some rb => simp [hc1, hc2] at h
        | some rr =>
          cases hc2 : codeReg (bBit * 8 + rm) with
          | none => simp [hc1, hc2] at h
          | some rb =>
            simp only [hc1, hc2] at h
            obtain ⟨b0, b1, b2, b3, h4⟩ :=
              parseLe32_suffix (b :: t) v mid hparse
            split at h
            · cases h
              refine ⟨⟨[b0, b1, b2, b3], h4, rfl⟩, rfl, ?_⟩
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨rr, rb, v, Or.inl rfl, Or.inl rfl⟩)))))
            · cases h
              refine ⟨⟨[b0, b1, b2, b3], h4, rfl⟩, rfl, ?_⟩
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨rr, rb, v, Or.inr rfl, Or.inl rfl⟩)))))

/-! ## 5. ModRM level: register-direct or disp32 memory, two outer bytes. -/

/-- ModRM coverage: mod 3 reuses the register-direct level, mod 2 the memory
    level; every other mode refuses. Two outer bytes (REX, opcode). -/
theorem decodeModrm_abdeckung (rBit bBit op : Nat) (bs : List Byte)
    (d : Decodiert) (rest' : List Byte)
    (h : decodeModrm rBit bBit op bs = some (d, rest')) :
    (∃ pre, bs = pre ++ rest' ∧ pre.length + 2 = d.laenge) ∧
      laengeOk d.laenge = true ∧ decktAb d := by
  cases bs with
  | nil => simp [decodeModrm] at h
  | cons m t =>
    simp only [decodeModrm] at h
    split at h
    · have hsub := decodeRegReg_abdeckung op rBit bBit (byteNat m / 8 % 8)
        (byteNat m % 8) t d rest' h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (m :: pre).length = pre.length + 1 := rfl
      refine ⟨⟨m :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
    · split at h
      · have hsub := decodeMem_abdeckung false rBit bBit (byteNat m / 8 % 8)
          (byteNat m % 8) t d rest' h
        obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
        have hcons : (m :: pre).length = pre.length + 1 := rfl
        refine ⟨⟨m :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
      · have hsub := decodeMem_abdeckung true rBit bBit (byteNat m / 8 % 8)
          (byteNat m % 8) t d rest' h
        obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
        have hcons : (m :: pre).length = pre.length + 1 := rfl
        refine ⟨⟨m :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
      · simp at h
    · simp at h

/-! ## 6. REX level: immediate-to-register or ModRM form, one outer byte. -/

/-- REX coverage: the `movImm64` range reuses the 64-bit parse, the five
    register and two memory opcodes reuse the ModRM level; anything else
    refuses. One outer byte (the REX prefix). -/
theorem decodeRex_abdeckung (rBit bBit : Nat) (bs : List Byte)
    (d : Decodiert) (rest' : List Byte)
    (h : decodeRex rBit bBit bs = some (d, rest')) :
    (∃ pre, bs = pre ++ rest' ∧ pre.length + 1 = d.laenge) ∧
      laengeOk d.laenge = true ∧ decktAb d := by
  cases bs with
  | nil => simp [decodeRex] at h
  | cons op t =>
    simp only [decodeRex] at h
    split at h
    · cases hc : codeReg (bBit * 8 + (byteNat op - 184)) with
      | none => simp [hc] at h
      | some dst =>
        simp only [hc] at h
        cases hparse : parseLe64 t with
        | none => simp [hparse] at h
        | some pr =>
          obtain ⟨v, mid⟩ := pr
          simp only [hparse] at h
          obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, h8⟩ :=
            parseLe64_suffix t v mid hparse
          cases h
          refine ⟨⟨[op, b0, b1, b2, b3, b4, b5, b6, b7], by simp [h8], rfl⟩,
            rfl, ?_⟩
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨dst, v, rfl, rfl⟩))))
    · split at h
      · have hsub := decodeModrm_abdeckung rBit bBit 137 t d rest' h
        obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
        have hcons : (op :: pre).length = pre.length + 1 := rfl
        refine ⟨⟨op :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
      · have hsub := decodeModrm_abdeckung rBit bBit 1 t d rest' h
        obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
        have hcons : (op :: pre).length = pre.length + 1 := rfl
        refine ⟨⟨op :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
      · have hsub := decodeModrm_abdeckung rBit bBit 41 t d rest' h
        obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
        have hcons : (op :: pre).length = pre.length + 1 := rfl
        refine ⟨⟨op :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
      · have hsub := decodeModrm_abdeckung rBit bBit 49 t d rest' h
        obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
        have hcons : (op :: pre).length = pre.length + 1 := rfl
        refine ⟨⟨op :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
      · have hsub := decodeModrm_abdeckung rBit bBit 57 t d rest' h
        obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
        have hcons : (op :: pre).length = pre.length + 1 := rfl
        refine ⟨⟨op :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
      · have hsub := decodeModrm_abdeckung rBit bBit 139 t d rest' h
        obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
        have hcons : (op :: pre).length = pre.length + 1 := rfl
        refine ⟨⟨op :: pre, by simp [hbs], by omega⟩, hok, hshape⟩
      · simp at h

/-! ## 7. Top level: every successful decode carries its own length. -/

/-- DECODER COVERAGE: every successful `decode` of an ARBITRARY byte list
    consumes exactly its stated length, the length is valid (1..15), the
    decoded form is one of the 14 pilot forms at its exact length, and the
    input splits into the consumed prefix and the remaining suffix. Proved
    from the decoder side only: no encoder round trip is used. -/
theorem decode_abdeckung (bs : List Byte) (d : Decodiert) (rest : List Byte)
    (h : decode bs = some (d, rest)) :
    d.laenge + rest.length = bs.length ∧ laengeOk d.laenge = true ∧ decktAb d ∧
      ∃ pre, bs = pre ++ rest ∧ pre.length = d.laenge := by
  cases bs with
  | nil => simp [decode] at h
  | cons b t =>
    simp only [decode] at h
    split at h
    · have hcons : (b :: t).length = t.length + 1 := rfl
      have heq : 1 + t.length = (b :: t).length := by omega
      have hpre : ([b] : List Byte).length = 1 := rfl
      cases h
      exact ⟨heq, rfl, Or.inl ⟨rfl, rfl⟩, [b], rfl, hpre⟩
    · cases hparse : parseLe32 t with
      | none => simp [hparse] at h
      | some pr =>
        obtain ⟨v, mid⟩ := pr
        simp only [hparse] at h
        obtain ⟨c0, c1, c2, c3, h4⟩ := parseLe32_suffix t v mid hparse
        have hlen := parseLe32_len t v mid hparse
        have hcons : (b :: t).length = t.length + 1 := rfl
        have heq : 5 + mid.length = (b :: t).length := by omega
        have hpre : ([b, c0, c1, c2, c3] : List Byte).length = 5 := rfl
        cases h
        refine ⟨heq, rfl, ?_, [b, c0, c1, c2, c3], by simp [h4], hpre⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨v, Or.inr rfl, rfl⟩))))))
    · cases hparse : parseLe32 t with
      | none => simp [hparse] at h
      | some pr =>
        obtain ⟨v, mid⟩ := pr
        simp only [hparse] at h
        obtain ⟨c0, c1, c2, c3, h4⟩ := parseLe32_suffix t v mid hparse
        have hlen := parseLe32_len t v mid hparse
        have hcons : (b :: t).length = t.length + 1 := rfl
        have heq : 5 + mid.length = (b :: t).length := by omega
        have hpre : ([b, c0, c1, c2, c3] : List Byte).length = 5 := rfl
        cases h
        refine ⟨heq, rfl, ?_, [b, c0, c1, c2, c3], by simp [h4], hpre⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨v, Or.inl rfl, rfl⟩))))))
    · cases t with
      | nil => simp at h
      | cons b2 t2 =>
        dsimp only at h
        by_cases hcc : 128 ≤ byteNat b2 ∧ byteNat b2 < 144
        · rw [if_pos hcc] at h
          cases hcond : codeCond (byteNat b2 - 128) with
          | none => simp [hcond] at h
          | some cond =>
            simp only [hcond] at h
            cases hparse : parseLe32 t2 with
            | none => simp [hparse] at h
            | some pr =>
              obtain ⟨v, mid⟩ := pr
              simp only [hparse] at h
              obtain ⟨c0, c1, c2, c3, h4⟩ :=
                parseLe32_suffix t2 v mid hparse
              have hlen := parseLe32_len t2 v mid hparse
              have hcons : (b :: b2 :: t2).length = t2.length + 2 := rfl
              have heq : 6 + mid.length = (b :: b2 :: t2).length := by omega
              have hpre :
                  ([b, b2, c0, c1, c2, c3] : List Byte).length = 6 := rfl
              cases h
              refine ⟨heq, rfl, ?_, [b, b2, c0, c1, c2, c3],
                by simp [h4], hpre⟩
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr ⟨cond, v, rfl, rfl⟩))))))
        · rw [if_neg hcc] at h
          simp at h
    · cases t with
      | nil => simp at h
      | cons b2 t2 =>
        dsimp only at h
        by_cases hpush : 80 ≤ byteNat b2 ∧ byteNat b2 < 88
        · rw [if_pos hpush] at h
          cases hreg : codeReg (byteNat b2 - 80 + 8) with
          | none => simp [hreg] at h
          | some r =>
            simp only [hreg] at h
            have hcons : (b :: b2 :: t2).length = t2.length + 2 := rfl
            have heq : 2 + t2.length = (b :: b2 :: t2).length := by omega
            have hpre : ([b, b2] : List Byte).length = 2 := rfl
            cases h
            refine ⟨heq, rfl, ?_, [b, b2], rfl, hpre⟩
            exact Or.inr (Or.inl ⟨r, rfl, Or.inr rfl⟩)
        · rw [if_neg hpush] at h
          by_cases hpop : 88 ≤ byteNat b2 ∧ byteNat b2 < 96
          · rw [if_pos hpop] at h
            cases hreg : codeReg (byteNat b2 - 88 + 8) with
            | none => simp [hreg] at h
            | some r =>
              simp only [hreg] at h
              have hcons : (b :: b2 :: t2).length = t2.length + 2 := rfl
              have heq : 2 + t2.length = (b :: b2 :: t2).length := by omega
              have hpre : ([b, b2] : List Byte).length = 2 := rfl
              cases h
              refine ⟨heq, rfl, ?_, [b, b2], rfl, hpre⟩
              exact Or.inr (Or.inr (Or.inl ⟨r, rfl, Or.inr rfl⟩))
          · rw [if_neg hpop] at h
            simp at h
    · have hsub := decodeRex_abdeckung 0 0 t d rest h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (b :: pre).length = pre.length + 1 := rfl
      have hcons2 : (b :: t).length = t.length + 1 := rfl
      have hblen : t.length = pre.length + rest.length := by
        rw [hbs, List.length_append]
      have heq : d.laenge + rest.length = (b :: t).length := by omega
      have hpre : (b :: pre).length = d.laenge := by omega
      exact ⟨heq, hok, hshape, b :: pre, by simp [hbs], hpre⟩
    · have hsub := decodeRex_abdeckung 0 1 t d rest h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (b :: pre).length = pre.length + 1 := rfl
      have hcons2 : (b :: t).length = t.length + 1 := rfl
      have hblen : t.length = pre.length + rest.length := by
        rw [hbs, List.length_append]
      have heq : d.laenge + rest.length = (b :: t).length := by omega
      have hpre : (b :: pre).length = d.laenge := by omega
      exact ⟨heq, hok, hshape, b :: pre, by simp [hbs], hpre⟩
    · have hsub := decodeRex_abdeckung 1 0 t d rest h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (b :: pre).length = pre.length + 1 := rfl
      have hcons2 : (b :: t).length = t.length + 1 := rfl
      have hblen : t.length = pre.length + rest.length := by
        rw [hbs, List.length_append]
      have heq : d.laenge + rest.length = (b :: t).length := by omega
      have hpre : (b :: pre).length = d.laenge := by omega
      exact ⟨heq, hok, hshape, b :: pre, by simp [hbs], hpre⟩
    · have hsub := decodeRex_abdeckung 1 1 t d rest h
      obtain ⟨⟨pre, hbs, hplen⟩, hok, hshape⟩ := hsub
      have hcons : (b :: pre).length = pre.length + 1 := rfl
      have hcons2 : (b :: t).length = t.length + 1 := rfl
      have hblen : t.length = pre.length + rest.length := by
        rw [hbs, List.length_append]
      have heq : d.laenge + rest.length = (b :: t).length := by omega
      have hpre : (b :: pre).length = d.laenge := by omega
      exact ⟨heq, hok, hshape, b :: pre, by simp [hbs], hpre⟩
    · by_cases hpush : 80 ≤ byteNat b ∧ byteNat b < 88
      · rw [if_pos hpush] at h
        cases hreg : codeReg (byteNat b - 80) with
        | none => simp [hreg] at h
        | some r =>
          simp only [hreg] at h
          have hcons : (b :: t).length = t.length + 1 := rfl
          have heq : 1 + t.length = (b :: t).length := by omega
          have hpre : ([b] : List Byte).length = 1 := rfl
          cases h
          refine ⟨heq, rfl, ?_, [b], rfl, hpre⟩
          exact Or.inr (Or.inl ⟨r, rfl, Or.inl rfl⟩)
      · rw [if_neg hpush] at h
        by_cases hpop : 88 ≤ byteNat b ∧ byteNat b < 96
        · rw [if_pos hpop] at h
          cases hreg : codeReg (byteNat b - 88) with
          | none => simp [hreg] at h
          | some r =>
            simp only [hreg] at h
            have hcons : (b :: t).length = t.length + 1 := rfl
            have heq : 1 + t.length = (b :: t).length := by omega
            have hpre : ([b] : List Byte).length = 1 := rfl
            cases h
            refine ⟨heq, rfl, ?_, [b], rfl, hpre⟩
            exact Or.inr (Or.inr (Or.inl ⟨r, rfl, Or.inl rfl⟩))
        · rw [if_neg hpop] at h
          simp at h


/-! ## 8. Window congruence: take/drop split at the decoded length. -/

/-- WINDOW CONGRUENCE: the remaining suffix is the drop at the decoded
    length, and the taken prefix with the suffix is the whole input. -/
theorem decode_fenster_kongruenz (bs : List Byte) (d : Decodiert)
    (rest : List Byte) (h : decode bs = some (d, rest)) :
    rest = bs.drop d.laenge ∧ bs.take d.laenge ++ rest = bs := by
  obtain ⟨heq, _, _, ⟨pre, hbs, hplen⟩⟩ := decode_abdeckung bs d rest h
  constructor
  · rw [hbs, ← hplen, List.drop_left]
  · rw [hbs, ← hplen, List.take_left]

/-! ## 9. Fetch corollaries: the executable window from the decoder. -/

/-- FETCH WINDOW CONGRUENCE: a successful fetch splits the fetched window
    at the decoded length. Derived from the decoder side only, through the
    existing fetch-to-decoder correspondence; no round trip is used. -/
theorem fetch_fenster_kongruenz (s : Zustand) (d : Decodiert)
    (rest : List Byte) (hf : fetchDekodiert s = some (d, rest)) :
    rest = (geholt s).drop d.laenge ∧
      (geholt s).take d.laenge ++ rest = geholt s := by
  obtain ⟨hdec, _, _, _⟩ := fetchDekodiert_entspricht s d rest hf
  exact decode_fenster_kongruenz (geholt s) d rest hdec

/-- BYTE-STEP-FROM-DECODER: a successful fetch runs `schritt` on the
    fetched instruction, the decoded form is covered at its exact length,
    and the length equation holds for the fetched window. The executable
    entry-byte relation derives from the actual decoder, not from placing
    canonical encodings. -/
theorem geholt_schritt_aus_decoder (s : Zustand) (d : Decodiert)
    (rest : List Byte) (hf : fetchDekodiert s = some (d, rest)) :
    (byteschritt s = match schritt d s with
      | none => .verweigert
      | some s' => .weiter s') ∧
      decktAb d ∧ d.laenge + rest.length = (geholt s).length := by
  obtain ⟨hdec, _, _, _⟩ := fetchDekodiert_entspricht s d rest hf
  obtain ⟨heq, _, hshape, _⟩ := decode_abdeckung (geholt s) d rest hdec
  refine ⟨?_, hshape, heq⟩
  cases hsch : schritt d s with
  | none =>
    have hbyte := byteschritt_verweigert_ohne_schritt s d rest hf hsch
    simp [hbyte]
  | some s' =>
    have hbyte := byteschritt_weiter s s' d rest hf hsch
    simp [hbyte]

/-! ## 10. Entry coverage: loaded-image entries from the decoder. -/

/-- ENTRY COVERAGE: decoding the executable entry window of a loaded image
    carries its own length (summing with the rest to the 15-byte cap), the
    length is valid, the form is covered, and the window splits. -/
theorem eintritt_abdeckung (bild : Bild) (bias e : Nat) (d : Decodiert)
    (rest : List Byte) (h : eintrittDekodiert bild bias e = some (d, rest)) :
    d.laenge + rest.length = fetchCap ∧ laengeOk d.laenge = true ∧ decktAb d ∧
      ∃ pre, eintrittFenster bild bias e fetchCap = pre ++ rest ∧
        pre.length = d.laenge := by
  have hwin : (eintrittFenster bild bias e fetchCap).length = fetchCap := by
    simp [eintrittFenster]
  unfold eintrittDekodiert at h
  obtain ⟨heq, hok, hshape, ⟨pre, hbs, hplen⟩⟩ :=
    decode_abdeckung _ d rest h
  exact ⟨by omega, hok, hshape, pre, hbs, hplen⟩

/- CUTS (skeleton):
    - The arbitrary-input length soundness, the per-form classification, the
      suffix/window congruence and the entry-byte bridge are not yet proved.
    - No hardware, source, TSO, concurrency or whole-image claim is made here.
-/

#print axioms eintrittFenster
#print axioms eintrittDekodiert

end Gabbro.Grammatik.X86
