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

/- CUTS (skeleton):
    - The arbitrary-input length soundness, the per-form classification, the
      suffix/window congruence and the entry-byte bridge are not yet proved.
    - No hardware, source, TSO, concurrency or whole-image claim is made here.
-/

#print axioms eintrittFenster
#print axioms eintrittDekodiert

end Gabbro.Grammatik.X86
