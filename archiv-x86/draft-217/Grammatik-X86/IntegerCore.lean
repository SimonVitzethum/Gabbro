/-
  File:      Grammatik/X86/IntegerCore.lean
  Subject:   The remaining P0 integer forms of DIRECT-COMPILER-DESIGN.md §3
             the optimiser/lowering need for -O3-like code: LEA (address
             computation, no memory access, no flags), AND/OR/TEST (REUSING
             the ShiftLogic/Ganzzahl logic semantics), NOT/NEG (REUSING the
             ShiftLogic NEG evidence), and the register-direct zero/sign
             extension forms MOVZX/MOVSX/MOVSXD into a 64-bit destination
             (REUSING NarrowOps's `extendNarrow`). Two-operand IMUL is
             already covered by `MulDiv.lean`'s `imul2`/`MulDivCodec.lean`
             and is NOT redefined here.

  Reused, not redefined: `Zustand`/`Register`/`Flags`/`Breite` (Typen.lean);
  `regSet`/`ripNach`/`laengeOk`/`schrittRegister`/`dispWort` (Ausfuehrung.lean);
  `trunc`/`sext`/`negB`/`sfTest`/`zfTest`/`parityEven` (Wort.lean); `andB`/
  `orB`/`notB`/`shlB`/`LogikGueltig` (Ganzzahl.lean); `andW`/`orW`/`logikFlags`/
  `negW`/`negWf`/`NegGueltig`/`negTrag`/`negUeberlauf` (ShiftLogic.lean --
  AND/OR/NOT/NEG value and flag semantics already exist there and are used
  AS IS); `extendNarrow`/`ExtendMode` (NarrowOps.lean); `natByte`/`byteNat`/
  `regHigh`/`regLow`/`regCode`/`codeReg`/`codeReg_regCode`/`regHigh_lt`/
  `regLow_lt`/`regCode_split`/`rexByte`/`modrmReg`/`leBytes32`/`parseLe32`/
  `parseLe32_cons`/`byteNat_natByte_of_lt`/`byteNat_natByte_any` (Codec.lean);
  the pilot `decode`/`Befehl`/`encode` (Codec.lean); `decodeMulDiv`/
  `mulDivEncode`/`MulDivBefehl` (MulDiv.lean/MulDivCodec.lean); `decodeShift`/
  `encodeShift`/`ShiftForm` (ShiftCodec.lean); `decodeNarrow`/`encodeNarrow`/
  `NarrowOp`/`rexNarrowBits` (NarrowCodec.lean).

  Nothing here forks a second AND/OR/NOT/NEG evaluator, a second extension
  evaluator, or a second register/ModRM encoder: every value and flag
  computation routes to the existing definitions above.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.FlagBeweis
import Grammatik.X86.ShiftLogic
import Grammatik.X86.NarrowOps
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.MulDiv
import Grammatik.X86.MulDivCodec
import Grammatik.X86.ShiftCodec
import Grammatik.X86.NarrowCodec

namespace Gabbro.Grammatik.X86

/-! ## 1. `Scale`: the SIB scale field, as a shift amount.

    The SIB byte's two-bit scale field names `2 ^ s` for `s ∈ 0..3`
    (factors 1, 2, 4, 8). Carried as a shift amount, matching the
    address-selection fact of §3A (`add a (shl b s)`). -/

inductive Scale where
  | s1 | s2 | s4 | s8
  deriving DecidableEq, Repr

/-- The scale as a shift amount (0, 1, 2, 3). -/
def scaleShift : Scale → Nat
  | .s1 => 0 | .s2 => 1 | .s4 => 2 | .s8 => 3

/-- The scale as a multiplicative factor (1, 2, 4, 8). -/
def scaleFactor (sc : Scale) : Nat := 2 ^ scaleShift sc

/-- Inverse: a two-bit scale field back to `Scale` (total on 0..3; the
    SIB scale field is always exactly two bits, so no other value is
    ever decoded from real bytes). -/
def scaleFromBits : Nat → Option Scale
  | 0 => some .s1 | 1 => some .s2 | 2 => some .s4 | 3 => some .s8
  | _ => none

/-- Decoding inverts encoding on every scale. -/
theorem scaleFromBits_scaleShift (sc : Scale) :
    scaleFromBits (scaleShift sc) = some sc := by
  cases sc <;> rfl

/-- Every scale shift fits two bits. -/
theorem scaleShift_lt (sc : Scale) : scaleShift sc < 4 := by
  cases sc <;> decide

/-! ## 2. `CoreBefehl`: the ten covered forms.

    No `Befehl` constructor is added and no pilot `schritt` equation is
    touched; this is an independent step function over the same
    `Zustand`, exactly in the style of `MulDivBefehl`/`ShiftForm`/
    `NarrowOp`. Two-operand IMUL is `MulDivBefehl.imul2`, already
    covered. -/

inductive CoreBefehl where
  /-- `lea dst, [base + index * 2 ^ scale + disp]`: no flags, no memory
      access. `index` names the register and scale; `none` is no index.
      The index register must not be `rsp` (SIB reuses that field value
      as the "no index" marker; `rsp` as an index is architecturally
      unrepresentable, named by `leaIndexOk`/CUTS below). -/
  | lea64 (dst base : Register) (index : Option (Register × Scale))
      (disp : BitVec 32)
  | andReg64 (dst src : Register)
  | orReg64 (dst src : Register)
  /-- `test lhs, rhs`: AND for flags only, writes no operand. -/
  | testReg64 (lhs rhs : Register)
  /-- `not dst`: flags UNCHANGED (architectural NOT touches no flag). -/
  | notReg64 (dst : Register)
  | negReg64 (dst : Register)
  | movzx64From8 (dst src : Register)
  | movzx64From16 (dst src : Register)
  | movsx64From8 (dst src : Register)
  | movsx64From16 (dst src : Register)
  /-- `movsxd dst, src` (32-bit source sign-extended to 64 bits). -/
  | movsx64From32 (dst src : Register)
  deriving DecidableEq, Repr

/-- A decoded core instruction with its consumed length. -/
structure CoreDecodiert where
  befehl : CoreBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-! ## 3. Value and flag semantics: every op routes to the REUSED helper.

    LEA's address value reuses `shlB .b64` (Ganzzahl.lean) for the
    scaled index and `dispWort` (Ausfuehrung.lean) for the
    sign-extended displacement; the three terms add as plain `Wort`
    (BitVec 64) addition, which IS modulo `2 ^ 64` by construction.
    AND/OR reuse `andW`/`orW .b64` (ShiftLogic.lean); NOT reuses `notB
    .b64` (Ganzzahl.lean) with flags copied unchanged from the
    pre-state; NEG reuses `negWf .b64` (ShiftLogic.lean, satisfying
    `NegGueltig`); the extensions reuse `extendNarrow` (NarrowOps.lean)
    at the named source width, written whole into the 64-bit
    destination (no `mergeRegNarrow`: a 64-bit destination is a full
    overwrite, never a narrow merge). -/

/-- LEA's computed address: `base + index * 2 ^ scale + sext32(disp)`,
    all as `Wort` addition (modulo `2 ^ 64`). -/
def leaVal (s : Zustand) (base : Register)
    (index : Option (Register × Scale)) (disp : BitVec 32) : Wort :=
  let idx : Wort := match index with
    | none => 0
    | some (r, sc) => shlB .b64 (s.register r) (scaleShift sc)
  s.register base + idx + dispWort disp

/-- Single core step; `none` is an explicit decode-length refusal (the
    ten covered forms never fail otherwise: no memory access, no
    trap). Reuses `laengeOk`/`ripNach`/`schrittRegister` unchanged. -/
def coreSchritt (d : CoreDecodiert) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .lea64 dst base index disp =>
      some (schrittRegister s nach s.flags dst (leaVal s base index disp))
    | .andReg64 dst src =>
      let r := andW .b64 (s.register dst) (s.register src)
      some (schrittRegister s nach r.2 dst r.1)
    | .orReg64 dst src =>
      let r := orW .b64 (s.register dst) (s.register src)
      some (schrittRegister s nach r.2 dst r.1)
    | .testReg64 lhs rhs =>
      let r := andW .b64 (s.register lhs) (s.register rhs)
      some ({ s with rip := nach, flags := r.2 })
    | .notReg64 dst =>
      some (schrittRegister s nach s.flags dst (notB .b64 (s.register dst)))
    | .negReg64 dst =>
      let r := negWf .b64 (s.register dst)
      some (schrittRegister s nach r.2 dst r.1)
    | .movzx64From8 dst src =>
      some (schrittRegister s nach s.flags dst
        (extendNarrow .zero .b8 (s.register src)))
    | .movzx64From16 dst src =>
      some (schrittRegister s nach s.flags dst
        (extendNarrow .zero .b16 (s.register src)))
    | .movsx64From8 dst src =>
      some (schrittRegister s nach s.flags dst
        (extendNarrow .sign .b8 (s.register src)))
    | .movsx64From16 dst src =>
      some (schrittRegister s nach s.flags dst
        (extendNarrow .sign .b16 (s.register src)))
    | .movsx64From32 dst src =>
      some (schrittRegister s nach s.flags dst
        (extendNarrow .sign .b32 (s.register src)))

/-! ## Step equations: one per form, every premise used. -/

theorem core_lea64 (d : CoreDecodiert) (s : Zustand) (dst base : Register)
    (index : Option (Register × Scale)) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .lea64 dst base index disp) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (leaVal s base index disp)) := by
  unfold coreSchritt; rw [hok, h]

theorem core_andReg64 (d : CoreDecodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .andReg64 dst src) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (andW .b64 (s.register dst) (s.register src)).2 dst
        (andW .b64 (s.register dst) (s.register src)).1) := by
  unfold coreSchritt; rw [hok, h]

theorem core_orReg64 (d : CoreDecodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .orReg64 dst src) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (orW .b64 (s.register dst) (s.register src)).2 dst
        (orW .b64 (s.register dst) (s.register src)).1) := by
  unfold coreSchritt; rw [hok, h]

theorem core_testReg64 (d : CoreDecodiert) (s : Zustand) (lhs rhs : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .testReg64 lhs rhs) :
    coreSchritt d s = some ({ s with rip := ripNach s.rip d.laenge, flags := (andW .b64 (s.register lhs) (s.register rhs)).2 }) := by
  unfold coreSchritt; rw [hok, h]

theorem core_notReg64 (d : CoreDecodiert) (s : Zustand) (dst : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .notReg64 dst) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (notB .b64 (s.register dst))) := by
  unfold coreSchritt; rw [hok, h]

theorem core_negReg64 (d : CoreDecodiert) (s : Zustand) (dst : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .negReg64 dst) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (negWf .b64 (s.register dst)).2 dst
        (negWf .b64 (s.register dst)).1) := by
  unfold coreSchritt; rw [hok, h]

theorem core_movzx64From8 (d : CoreDecodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .movzx64From8 dst src) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (extendNarrow .zero .b8 (s.register src))) := by
  unfold coreSchritt; rw [hok, h]

theorem core_movzx64From16 (d : CoreDecodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .movzx64From16 dst src) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (extendNarrow .zero .b16 (s.register src))) := by
  unfold coreSchritt; rw [hok, h]

theorem core_movsx64From8 (d : CoreDecodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .movsx64From8 dst src) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (extendNarrow .sign .b8 (s.register src))) := by
  unfold coreSchritt; rw [hok, h]

theorem core_movsx64From16 (d : CoreDecodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .movsx64From16 dst src) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (extendNarrow .sign .b16 (s.register src))) := by
  unfold coreSchritt; rw [hok, h]

theorem core_movsx64From32 (d : CoreDecodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .movsx64From32 dst src) :
    coreSchritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (extendNarrow .sign .b32 (s.register src))) := by
  unfold coreSchritt; rw [hok, h]

/-- A bad decode length refuses every form, unconditionally. -/
theorem core_laenge_verweigert (d : CoreDecodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) : coreSchritt d s = none := by
  unfold coreSchritt; simp [h]

/-! ## Frame facts: no covered form ever touches memory or permissions. -/

/-- Every successful core step changes no memory byte: none of the ten
    forms performs a load or a store. -/
theorem coreSchritt_speicher (d : CoreDecodiert) (s s' : Zustand)
    (h : coreSchritt d s = some s') : s'.speicher = s.speicher := by
  have hok : laengeOk d.laenge = true := by
    unfold coreSchritt at h
    cases hl : laengeOk d.laenge with
    | false => rw [hl] at h; cases h
    | true => rfl
  match hb : d.befehl with
  | .lea64 dst base index disp =>
    rw [core_lea64 d s dst base index disp hok hb] at h; cases h; rfl
  | .andReg64 dst src =>
    rw [core_andReg64 d s dst src hok hb] at h; cases h; rfl
  | .orReg64 dst src =>
    rw [core_orReg64 d s dst src hok hb] at h; cases h; rfl
  | .testReg64 lhs rhs =>
    rw [core_testReg64 d s lhs rhs hok hb] at h; cases h; rfl
  | .notReg64 dst =>
    rw [core_notReg64 d s dst hok hb] at h; cases h; rfl
  | .negReg64 dst =>
    rw [core_negReg64 d s dst hok hb] at h; cases h; rfl
  | .movzx64From8 dst src =>
    rw [core_movzx64From8 d s dst src hok hb] at h; cases h; rfl
  | .movzx64From16 dst src =>
    rw [core_movzx64From16 d s dst src hok hb] at h; cases h; rfl
  | .movsx64From8 dst src =>
    rw [core_movsx64From8 d s dst src hok hb] at h; cases h; rfl
  | .movsx64From16 dst src =>
    rw [core_movsx64From16 d s dst src hok hb] at h; cases h; rfl
  | .movsx64From32 dst src =>
    rw [core_movsx64From32 d s dst src hok hb] at h; cases h; rfl

/-- LEA, NOT and the three extension forms preserve the flags exactly
    (architectural: none of these five touches a flag). -/
theorem coreSchritt_flags_unveraendert (d : CoreDecodiert) (s s' : Zustand)
    (h : coreSchritt d s = some s')
    (hform : (∃ dst base index disp, d.befehl = .lea64 dst base index disp) ∨
      (∃ dst, d.befehl = .notReg64 dst) ∨
      (∃ dst src, d.befehl = .movzx64From8 dst src) ∨
      (∃ dst src, d.befehl = .movzx64From16 dst src) ∨
      (∃ dst src, d.befehl = .movsx64From8 dst src) ∨
      (∃ dst src, d.befehl = .movsx64From16 dst src) ∨
      (∃ dst src, d.befehl = .movsx64From32 dst src)) :
    s'.flags = s.flags := by
  have hok : laengeOk d.laenge = true := by
    unfold coreSchritt at h
    cases hl : laengeOk d.laenge with
    | false => rw [hl] at h; cases h
    | true => rfl
  rcases hform with ⟨dst, base, index, disp, hf⟩ | ⟨dst, hf⟩ |
    ⟨dst, src, hf⟩ | ⟨dst, src, hf⟩ | ⟨dst, src, hf⟩ | ⟨dst, src, hf⟩ |
    ⟨dst, src, hf⟩
  · rw [core_lea64 d s dst base index disp hok hf] at h; cases h; rfl
  · rw [core_notReg64 d s dst hok hf] at h; cases h; rfl
  · rw [core_movzx64From8 d s dst src hok hf] at h; cases h; rfl
  · rw [core_movzx64From16 d s dst src hok hf] at h; cases h; rfl
  · rw [core_movsx64From8 d s dst src hok hf] at h; cases h; rfl
  · rw [core_movsx64From16 d s dst src hok hf] at h; cases h; rfl
  · rw [core_movsx64From32 d s dst src hok hf] at h; cases h; rfl

/-! ## 4. Encoding: `rexByteX` (three extension bits), SIB, canonical rows.

    `rexByteX` extends the pilot's `rexByte` with the X bit (needed only
    by LEA's index register); every other form keeps X = 0, exactly the
    pilot's canonical choice. -/

/-- REX.W prefix with all three extension bits (X carries the SIB index
    extension; `rexByte rh bh` is the `xh = 0` case of this). -/
def rexByteX (rh xh bh : Nat) : Byte := natByte (72 + 4 * rh + 2 * xh + bh)

/-- SIB byte: two-bit scale, three-bit index, three-bit base. -/
def sibByte (scale indexLow baseLow : Nat) : Byte :=
  natByte (64 * scale + 8 * (indexLow % 8) + baseLow % 8)

/-- Decode a canonical REX.W(+X)(+R)(+B) prefix: byte values 72..79. -/
def rexCoreBits (b : Byte) : Option (Nat × Nat × Nat) :=
  let n := byteNat b
  if h : 72 ≤ n ∧ n < 80 then
    let k := n - 72
    some (k / 4, (k / 2) % 2, k % 2)
  else none

/-- Admission: an LEA index must not be `rsp` (the SIB "no index"
    marker reuses exactly `rsp`'s code; `rsp` is architecturally
    unrepresentable as an index, named here rather than silently
    miscoded -- see `core_poison_lea_rsp_index` below). -/
def leaIndexOk : Option (Register × Scale) → Bool
  | none => true
  | some (r, _) => decide (r ≠ Register.rsp)

/-- Admission for the whole instruction: every non-LEA form is always
    admitted; LEA needs `leaIndexOk`. -/
def coreValid : CoreBefehl → Bool
  | .lea64 _ _ index _ => leaIndexOk index
  | _ => true

/-- Canonical byte encoding of one covered core row. LEA always carries
    a SIB byte (mirroring the pilot's `load64`/`store64` SIB-forced
    shape through `rsp`/`r12`, generalised here to every base since the
    index may or may not be present); every other row is the plain
    REX.W(+R)(+B) register-direct shape already used by `MulDiv`/
    `ShiftCodec`/`NarrowCodec`. -/
def encodeCore : CoreBefehl → List Byte
  | .lea64 dst base index disp =>
    let (idxLow, idxHigh, scaleBits) := match index with
      | none => (4, 0, 0)
      | some (r, sc) => (regLow r, regHigh r, scaleShift sc)
    [rexByteX (regHigh dst) idxHigh (regHigh base), natByte 141,
     modrmMem (regLow dst) 4, sibByte scaleBits idxLow (regLow base)] ++
      leBytes32 disp
  | .andReg64 dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 33,
     modrmReg (regLow src) (regLow dst)]
  | .orReg64 dst src =>
    [rexByte (regHigh src) (regHigh dst), natByte 9,
     modrmReg (regLow src) (regLow dst)]
  | .testReg64 lhs rhs =>
    [rexByte (regHigh rhs) (regHigh lhs), natByte 133,
     modrmReg (regLow rhs) (regLow lhs)]
  | .notReg64 dst => [rexByte 0 (regHigh dst), natByte 247, modrmReg 2 (regLow dst)]
  | .negReg64 dst => [rexByte 0 (regHigh dst), natByte 247, modrmReg 3 (regLow dst)]
  | .movzx64From8 dst src =>
    [rexByte (regHigh dst) (regHigh src), natByte 15, natByte 182,
     modrmReg (regLow dst) (regLow src)]
  | .movzx64From16 dst src =>
    [rexByte (regHigh dst) (regHigh src), natByte 15, natByte 183,
     modrmReg (regLow dst) (regLow src)]
  | .movsx64From8 dst src =>
    [rexByte (regHigh dst) (regHigh src), natByte 15, natByte 190,
     modrmReg (regLow dst) (regLow src)]
  | .movsx64From16 dst src =>
    [rexByte (regHigh dst) (regHigh src), natByte 15, natByte 191,
     modrmReg (regLow dst) (regLow src)]
  | .movsx64From32 dst src =>
    [rexByte (regHigh dst) (regHigh src), natByte 99,
     modrmReg (regLow dst) (regLow src)]

/-- Consumed length of one covered core row. -/
def coreLen : CoreBefehl → Nat
  | .lea64 _ _ _ _ => 8
  | .andReg64 _ _ => 3 | .orReg64 _ _ => 3 | .testReg64 _ _ => 3
  | .notReg64 _ => 3 | .negReg64 _ => 3
  | .movzx64From8 _ _ => 4 | .movzx64From16 _ _ => 4
  | .movsx64From8 _ _ => 4 | .movsx64From16 _ _ => 4
  | .movsx64From32 _ _ => 3

/-- The encoding is exactly the stated length. -/
theorem encodeCore_laenge (b : CoreBefehl) :
    (encodeCore b).length = coreLen b := by
  cases b with
  | lea64 dst base index disp =>
    cases index with
    | none => rfl
    | some p => cases p with | mk r sc => rfl
  | andReg64 dst src => rfl
  | orReg64 dst src => rfl
  | testReg64 lhs rhs => rfl
  | notReg64 dst => rfl
  | negReg64 dst => rfl
  | movzx64From8 dst src => rfl
  | movzx64From16 dst src => rfl
  | movsx64From8 dst src => rfl
  | movsx64From16 dst src => rfl
  | movsx64From32 dst src => rfl

/-- Every covered encoding fits the 1..15 instruction bound. -/
theorem encodeCore_len_ok (b : CoreBefehl) :
    1 ≤ (encodeCore b).length ∧ (encodeCore b).length ≤ 15 := by
  rw [encodeCore_laenge]
  cases b <;> simp [coreLen] <;> omega

/-! ## 5. Decoder: parses bytes, never encode-equality. -/

/-- Register-register tail, shared by AND/OR/TEST: mod=3, `reg`→the
    register named by the REX.R extension, `rm`→the REX.B extension.
    `mk` orders the two into the right `CoreBefehl` constructor. -/
def decodeCoreRegReg (mk : Register → Register → CoreBefehl) (rh bh : Nat) :
    List Byte → Option (CoreDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeReg (rh * 8 + byteNat m / 8 % 8),
          codeReg (bh * 8 + byteNat m % 8) with
      | some rs, some rd => some (⟨mk rd rs, 3⟩, rest)
      | _, _ => none
    else none

/-- Group-3 tail for NOT (/2) and NEG (/3): mod=3, R must be clear
    (no second operand; mirrors `MulDiv`'s Group-3 R=0 discipline). -/
def decodeCoreF7 (rh bh : Nat) : List Byte → Option (CoreDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 ∧ rh == 0 then
      match byteNat m / 8 % 8, codeReg (bh * 8 + byteNat m % 8) with
      | 2, some dst => some (⟨.notReg64 dst, 3⟩, rest)
      | 3, some dst => some (⟨.negReg64 dst, 3⟩, rest)
      | _, _ => none
    else none

/-- `0F` tail for the four byte/word extension rows (B6/B7/BE/BF). -/
def decodeCore0F (rh bh : Nat) : List Byte → Option (CoreDecodiert × List Byte)
  | [] => none
  | op2 :: rest =>
    match rest with
    | [] => none
    | m :: rest' =>
      if byteNat m / 64 == 3 then
        match codeReg (rh * 8 + byteNat m / 8 % 8),
            codeReg (bh * 8 + byteNat m % 8) with
        | some dst, some src =>
          match byteNat op2 with
          | 182 => some (⟨.movzx64From8 dst src, 4⟩, rest')
          | 183 => some (⟨.movzx64From16 dst src, 4⟩, rest')
          | 190 => some (⟨.movsx64From8 dst src, 4⟩, rest')
          | 191 => some (⟨.movsx64From16 dst src, 4⟩, rest')
          | _ => none
        | _, _ => none
      else none

/-- MOVSXD tail (opcode `63`): mod=3 register-direct only. -/
def decodeCoreMovsxd (rh bh : Nat) : List Byte → Option (CoreDecodiert × List Byte)
  | [] => none
  | m :: rest =>
    if byteNat m / 64 == 3 then
      match codeReg (rh * 8 + byteNat m / 8 % 8),
          codeReg (bh * 8 + byteNat m % 8) with
      | some dst, some src => some (⟨.movsx64From32 dst src, 3⟩, rest)
      | _, _ => none
    else none

/-- LEA tail: mod=2 with `rm = 4` (SIB forced, mirroring the pilot's
    load/store SIB shape), then a SIB byte whose index field is read
    through BOTH the SIB low three bits and the REX.X extension. A SIB
    index field reconstructing exactly `rsp`'s code (`rsp`, `xh = 0`)
    is the architectural "no index" marker, decoded as `none`
    regardless of the scale bits (hardware ignores them there); any
    other reconstructed code is a genuine index register. -/
def decodeCoreLea (rh xh bh : Nat) : List Byte → Option (CoreDecodiert × List Byte)
  | modrm :: sib :: rest =>
    if byteNat modrm / 64 == 2 ∧ byteNat modrm % 8 == 4 then
      let reg := byteNat modrm / 8 % 8
      let scaleBits := byteNat sib / 64
      let idxLow := byteNat sib / 8 % 8
      let baseLow := byteNat sib % 8
      let fullIdx := xh * 8 + idxLow
      match codeReg (rh * 8 + reg), codeReg (bh * 8 + baseLow) with
      | some dst, some base =>
        match parseLe32 rest with
        | some (disp, rest') =>
          if fullIdx == 4 then
            some (⟨.lea64 dst base none disp, 8⟩, rest')
          else
            match codeReg fullIdx, scaleFromBits scaleBits with
            | some idxReg, some sc =>
              some (⟨.lea64 dst base (some (idxReg, sc)) disp, 8⟩, rest')
            | _, _ => none
        | none => none
      | _, _ => none
    else none
  | _ => none

/-- Dispatch after the REX prefix: opcode `8D` is LEA (any `xh`); every
    other covered opcode needs `xh = 0` (no form besides LEA has a
    third extended operand). -/
def decodeCoreTail (rh xh bh : Nat) : List Byte → Option (CoreDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    if byteNat op == 141 then decodeCoreLea rh xh bh rest
    else if xh != 0 then none
    else
      match byteNat op with
      | 33 => decodeCoreRegReg CoreBefehl.andReg64 rh bh rest
      | 9 => decodeCoreRegReg CoreBefehl.orReg64 rh bh rest
      | 133 => decodeCoreRegReg CoreBefehl.testReg64 rh bh rest
      | 247 => decodeCoreF7 rh bh rest
      | 15 => decodeCore0F rh bh rest
      | 99 => decodeCoreMovsxd rh bh rest
      | _ => none

/-- Decode the first canonical core instruction. Only a canonical
    REX.W(+X)(+R)(+B) prefix (bytes 72..79) opens any covered row;
    anything else refuses with `none`. -/
def decodeCore : List Byte → Option (CoreDecodiert × List Byte)
  | [] => none
  | r :: rest =>
    match rexCoreBits r with
    | none => none
    | some (rh, xh, bh) => decodeCoreTail rh xh bh rest

/-! ## 6. Generic byte-level helpers used by the round trips. -/

/-- `rexCoreBits` inverts `rexByteX` for extension bits each below 2. -/
theorem rexCoreBits_rexByteX (rh xh bh : Nat) (h1 : rh < 2) (h2 : xh < 2)
    (h3 : bh < 2) : rexCoreBits (rexByteX rh xh bh) = some (rh, xh, bh) := by
  unfold rexCoreBits rexByteX
  have hlt : 72 + 4 * rh + 2 * xh + bh < 256 := by omega
  have heq : byteNat (natByte (72 + 4 * rh + 2 * xh + bh)) =
      72 + 4 * rh + 2 * xh + bh := byteNat_natByte_of_lt _ hlt
  simp only [heq]
  have hb1 : 72 ≤ 72 + 4 * rh + 2 * xh + bh := by omega
  have hb2 : 72 + 4 * rh + 2 * xh + bh < 80 := by omega
  rw [dif_pos ⟨hb1, hb2⟩]
  have hk : 72 + 4 * rh + 2 * xh + bh - 72 = 4 * rh + 2 * xh + bh := by omega
  rw [hk]
  have e1 : (4 * rh + 2 * xh + bh) / 4 = rh := by omega
  have e2 : (4 * rh + 2 * xh + bh) / 2 % 2 = xh := by omega
  have e3 : (4 * rh + 2 * xh + bh) % 2 = bh := by omega
  rw [e1, e2, e3]

/-- `rexCoreBits` inverts the plain `rexByte` (X = 0). -/
theorem rexCoreBits_rexByte (rh bh : Nat) (h1 : rh < 2) (h2 : bh < 2) :
    rexCoreBits (rexByte rh bh) = some (rh, 0, bh) := by
  have h : rexByte rh bh = rexByteX rh 0 bh := by
    unfold rexByte rexByteX; rfl
  rw [h]; exact rexCoreBits_rexByteX rh 0 bh h1 (by decide) h2

/-- A register-direct `modrmReg` byte decodes to mod=3 with the stated
    reg/rm fields, for any register codes. -/
theorem modrmReg_fields (rl rm : Nat) :
    byteNat (modrmReg rl rm) / 64 = 3 ∧
    byteNat (modrmReg rl rm) / 8 % 8 = rl % 8 ∧
    byteNat (modrmReg rl rm) % 8 = rm % 8 := by
  unfold modrmReg
  have h1 : rl % 8 < 8 := Nat.mod_lt _ (by decide)
  have h2 : rm % 8 < 8 := Nat.mod_lt _ (by decide)
  have hlt : 192 + 8 * (rl % 8) + rm % 8 < 256 := by omega
  have heq : byteNat (natByte (192 + 8 * (rl % 8) + rm % 8)) =
      192 + 8 * (rl % 8) + rm % 8 := byteNat_natByte_of_lt _ hlt
  rw [heq]
  refine ⟨by omega, by omega, by omega⟩

/-- `codeReg` inverts the split register code of any register, without
    case analysis on the register (reuses `regCode_split`/
    `codeReg_regCode`). -/
theorem codeReg_regHigh_regLow (r : Register) :
    codeReg (regHigh r * 8 + regLow r) = some r := by
  rw [← regCode_split]; exact codeReg_regCode r

/-! ## 7. Round trips. -/

theorem roundtrip_andReg64 (dst src : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.andReg64 dst src) ++ suffix) =
      some (⟨.andReg64 dst src, 3⟩, suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_orReg64 (dst src : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.orReg64 dst src) ++ suffix) =
      some (⟨.orReg64 dst src, 3⟩, suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_testReg64 (lhs rhs : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.testReg64 lhs rhs) ++ suffix) =
      some (⟨.testReg64 lhs rhs, 3⟩, suffix) := by
  cases lhs <;> cases rhs <;> rfl

theorem roundtrip_notReg64 (dst : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.notReg64 dst) ++ suffix) =
      some (⟨.notReg64 dst, 3⟩, suffix) := by
  cases dst <;> rfl

theorem roundtrip_negReg64 (dst : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.negReg64 dst) ++ suffix) =
      some (⟨.negReg64 dst, 3⟩, suffix) := by
  cases dst <;> rfl

theorem roundtrip_movzx64From8 (dst src : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.movzx64From8 dst src) ++ suffix) =
      some (⟨.movzx64From8 dst src, 4⟩, suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_movzx64From16 (dst src : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.movzx64From16 dst src) ++ suffix) =
      some (⟨.movzx64From16 dst src, 4⟩, suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_movsx64From8 (dst src : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.movsx64From8 dst src) ++ suffix) =
      some (⟨.movsx64From8 dst src, 4⟩, suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_movsx64From16 (dst src : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.movsx64From16 dst src) ++ suffix) =
      some (⟨.movsx64From16 dst src, 4⟩, suffix) := by
  cases dst <;> cases src <;> rfl

theorem roundtrip_movsx64From32 (dst src : Register) (suffix : List Byte) :
    decodeCore (encodeCore (.movsx64From32 dst src) ++ suffix) =
      some (⟨.movsx64From32 dst src, 3⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-- Round trip for LEA with no index. -/
theorem roundtrip_lea64_none (dst base : Register) (disp : BitVec 32)
    (suffix : List Byte) :
    decodeCore (encodeCore (.lea64 dst base none disp) ++ suffix) =
      some (⟨.lea64 dst base none disp, 8⟩, suffix) := by
  have hrex := rexCoreBits_rexByteX (regHigh dst) 0 (regHigh base)
    (regHigh_lt dst) (by decide) (regHigh_lt base)
  have hmm := modrmReg_fields (regLow dst) 4 -- same shape as modrmMem's reg field
  have hdst := codeReg_regHigh_regLow dst
  have hbase := codeReg_regHigh_regLow base
  show decodeCore
      (([rexByteX (regHigh dst) 0 (regHigh base), natByte 141,
        modrmMem (regLow dst) 4, sibByte 0 4 (regLow base)] ++
        leBytes32 disp) ++ suffix) = _
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have h141 : (byteNat (natByte 141) == 141) = true := by decide
  simp only [decodeCore, hrex, decodeCoreTail, h141, if_true]
  show decodeCoreLea (regHigh dst) 0 (regHigh base)
      (modrmMem (regLow dst) 4 :: sibByte 0 4 (regLow base) ::
        (leBytes32 disp ++ suffix)) = _
  simp only [decodeCoreLea]
  have hmmField : byteNat (modrmMem (regLow dst) 4) / 64 = 2 ∧
      byteNat (modrmMem (regLow dst) 4) % 8 = 4 ∧
      byteNat (modrmMem (regLow dst) 4) / 8 % 8 = regLow dst % 8 := by
    unfold modrmMem
    have h1 : regLow dst % 8 < 8 := Nat.mod_lt _ (by decide)
    have hlt : 128 + 8 * (regLow dst % 8) + 4 % 8 < 256 := by omega
    have heq : byteNat (natByte (128 + 8 * (regLow dst % 8) + 4 % 8)) =
        128 + 8 * (regLow dst % 8) + 4 % 8 := byteNat_natByte_of_lt _ hlt
    rw [heq]; refine ⟨by omega, by omega, by omega⟩
  have hcond1 : (byteNat (modrmMem (regLow dst) 4) / 64 == 2) = true := by
    rw [hmmField.1]; decide
  have hcond2 : (byteNat (modrmMem (regLow dst) 4) % 8 == 4) = true := by
    rw [hmmField.2.1]; decide
  rw [if_pos ⟨hcond1, hcond2⟩]
  have hsibField : byteNat (sibByte 0 4 (regLow base)) / 64 = 0 ∧
      byteNat (sibByte 0 4 (regLow base)) / 8 % 8 = 4 % 8 ∧
      byteNat (sibByte 0 4 (regLow base)) % 8 = regLow base % 8 := by
    unfold sibByte
    have h1 : regLow base % 8 < 8 := Nat.mod_lt _ (by decide)
    have hlt : 64 * 0 + 8 * (4 % 8) + regLow base % 8 < 256 := by omega
    have heq : byteNat (natByte (64 * 0 + 8 * (4 % 8) + regLow base % 8)) =
        64 * 0 + 8 * (4 % 8) + regLow base % 8 := byteNat_natByte_of_lt _ hlt
    rw [heq]; refine ⟨by omega, by omega, by omega⟩
  have hmodDst : regLow dst % 8 = regLow dst := Nat.mod_eq_of_lt (regLow_lt dst)
  have hmodBase : regLow base % 8 = regLow base := Nat.mod_eq_of_lt (regLow_lt base)
  rw [hmmField.2.2, hsibField.1, hsibField.2.1, hsibField.2.2, hmodDst, hmodBase,
    hdst, hbase]
  rw [parseLe32_leBytes32]
  simp only [show (0 * 8 + 4 % 8 == 4) = true from by decide, if_true]

/-- Round trip for LEA with a non-`rsp` index. -/
theorem roundtrip_lea64_some (dst base idx : Register) (sc : Scale)
    (disp : BitVec 32) (hne : idx ≠ Register.rsp) (suffix : List Byte) :
    decodeCore (encodeCore (.lea64 dst base (some (idx, sc)) disp) ++
        suffix) =
      some (⟨.lea64 dst base (some (idx, sc)) disp, 8⟩, suffix) := by
  have hrex := rexCoreBits_rexByteX (regHigh dst) (regHigh idx) (regHigh base)
    (regHigh_lt dst) (regHigh_lt idx) (regHigh_lt base)
  have hdst := codeReg_regHigh_regLow dst
  have hbase := codeReg_regHigh_regLow base
  have hidx := codeReg_regHigh_regLow idx
  have hfullIdxNe : regHigh idx * 8 + regLow idx ≠ 4 := by
    rw [← regCode_split]
    intro hc
    have : codeReg (regCode idx) = codeReg 4 := by rw [hc]
    rw [codeReg_regCode] at this
    have h4 : codeReg 4 = some Register.rsp := by decide
    rw [h4] at this
    exact hne (Option.some.inj this)
  show decodeCore
      (([rexByteX (regHigh dst) (regHigh idx) (regHigh base), natByte 141,
        modrmMem (regLow dst) 4,
        sibByte (scaleShift sc) (regLow idx) (regLow base)] ++
        leBytes32 disp) ++ suffix) = _
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have h141 : (byteNat (natByte 141) == 141) = true := by decide
  simp only [decodeCore, hrex, decodeCoreTail, h141, if_true]
  show decodeCoreLea (regHigh dst) (regHigh idx) (regHigh base)
      (modrmMem (regLow dst) 4 ::
        sibByte (scaleShift sc) (regLow idx) (regLow base) ::
        (leBytes32 disp ++ suffix)) = _
  simp only [decodeCoreLea]
  have hmmField : byteNat (modrmMem (regLow dst) 4) / 64 = 2 ∧
      byteNat (modrmMem (regLow dst) 4) % 8 = 4 ∧
      byteNat (modrmMem (regLow dst) 4) / 8 % 8 = regLow dst % 8 := by
    unfold modrmMem
    have h1 : regLow dst % 8 < 8 := Nat.mod_lt _ (by decide)
    have hlt : 128 + 8 * (regLow dst % 8) + 4 % 8 < 256 := by omega
    have heq : byteNat (natByte (128 + 8 * (regLow dst % 8) + 4 % 8)) =
        128 + 8 * (regLow dst % 8) + 4 % 8 := byteNat_natByte_of_lt _ hlt
    rw [heq]; refine ⟨by omega, by omega, by omega⟩
  have hcond1 : (byteNat (modrmMem (regLow dst) 4) / 64 == 2) = true := by
    rw [hmmField.1]; decide
  have hcond2 : (byteNat (modrmMem (regLow dst) 4) % 8 == 4) = true := by
    rw [hmmField.2.1]; decide
  rw [if_pos ⟨hcond1, hcond2⟩]
  have hsibField : byteNat (sibByte (scaleShift sc) (regLow idx) (regLow base)) / 64
        = scaleShift sc ∧
      byteNat (sibByte (scaleShift sc) (regLow idx) (regLow base)) / 8 % 8
        = regLow idx % 8 ∧
      byteNat (sibByte (scaleShift sc) (regLow idx) (regLow base)) % 8
        = regLow base % 8 := by
    unfold sibByte
    have h1 : regLow idx % 8 < 8 := Nat.mod_lt _ (by decide)
    have h2 : regLow base % 8 < 8 := Nat.mod_lt _ (by decide)
    have h3 : scaleShift sc < 4 := scaleShift_lt sc
    have hlt : 64 * scaleShift sc + 8 * (regLow idx % 8) + regLow base % 8 < 256 := by
      omega
    have heq : byteNat
        (natByte (64 * scaleShift sc + 8 * (regLow idx % 8) + regLow base % 8))
        = 64 * scaleShift sc + 8 * (regLow idx % 8) + regLow base % 8 :=
      byteNat_natByte_of_lt _ hlt
    rw [heq]; refine ⟨by omega, by omega, by omega⟩
  rw [hmmField.2.2, hsibField.1, hsibField.2.1, hsibField.2.2]
  have hmodDst : regLow dst % 8 = regLow dst := Nat.mod_eq_of_lt (regLow_lt dst)
  have hmodBase : regLow base % 8 = regLow base := Nat.mod_eq_of_lt (regLow_lt base)
  rw [hmodDst, hmodBase, hdst, hbase]
  have hfullEq : regHigh idx * 8 + regLow idx % 8 = regHigh idx * 8 + regLow idx := by
    have h1 : regLow idx < 8 := regLow_lt idx
    rw [Nat.mod_eq_of_lt h1]
  rw [parseLe32_leBytes32]
  have hbeq : (regHigh idx * 8 + regLow idx % 8 == 4) = false := by
    rw [hfullEq]
    simp only [beq_eq_false_iff_ne]
    exact hfullIdxNe
  simp only [hbeq, Bool.false_eq_true, ite_false]
  rw [hfullEq, hidx, scaleFromBits_scaleShift]

/-- Decoding inverts encoding on every admitted core row, over any
    suffix (`coreValid` excludes only `lea64` with an `rsp` index). -/
theorem roundtripCore (b : CoreBefehl) (hv : coreValid b = true)
    (suffix : List Byte) :
    decodeCore (encodeCore b ++ suffix) = some (⟨b, coreLen b⟩, suffix) := by
  cases b with
  | lea64 dst base index disp =>
    cases index with
    | none => exact roundtrip_lea64_none dst base disp suffix
    | some p =>
      obtain ⟨idx, sc⟩ := p
      have hne : idx ≠ Register.rsp := by
        simpa [coreValid, leaIndexOk] using hv
      exact roundtrip_lea64_some dst base idx sc disp hne suffix
  | andReg64 dst src => exact roundtrip_andReg64 dst src suffix
  | orReg64 dst src => exact roundtrip_orReg64 dst src suffix
  | testReg64 lhs rhs => exact roundtrip_testReg64 lhs rhs suffix
  | notReg64 dst => exact roundtrip_notReg64 dst suffix
  | negReg64 dst => exact roundtrip_negReg64 dst suffix
  | movzx64From8 dst src => exact roundtrip_movzx64From8 dst src suffix
  | movzx64From16 dst src => exact roundtrip_movzx64From16 dst src suffix
  | movsx64From8 dst src => exact roundtrip_movsx64From8 dst src suffix
  | movsx64From16 dst src => exact roundtrip_movsx64From16 dst src suffix
  | movsx64From32 dst src => exact roundtrip_movsx64From32 dst src suffix

/-- A successful admitted round trip consumes exactly its prefix,
    within 1..15. -/
theorem roundtripCore_len_ok (b : CoreBefehl) (hv : coreValid b = true)
    (suffix : List Byte) :
    ∃ (n : Nat) (rest : List Byte),
      decodeCore (encodeCore b ++ suffix) = some (⟨b, n⟩, rest) ∧
        n + rest.length = (encodeCore b ++ suffix).length ∧
        1 ≤ n ∧ n ≤ 15 := by
  refine ⟨coreLen b, suffix, roundtripCore b hv suffix, ?_, ?_, ?_⟩
  · rw [List.length_append, encodeCore_laenge]
  · cases b <;> simp [coreLen] <;> omega
  · cases b <;> simp [coreLen] <;> omega

/-! ## 7. Disjointness: the precise byte boundary to the pilot and the
    other covered families.

    Every covered family (`decode`, `decodeMulDiv`, `decodeShift`,
    `decodeNarrow`) opens on its own fixed REX-prefix set and/or its own
    fixed opcode bytes; the proofs below are byte-level, never
    semantic. -/

/-- Any canonical REX.W(+X)(+R)(+B) prefix (bits each below 2) followed
    by LEA's opcode `141` is refused by the pilot decoder, independent
    of every later byte: the bounded (rh, xh, bh) case split is on
    EXTENSION BITS, never on a register, so it stays cheap regardless
    of how many registers/scales the caller quantifies over. -/
theorem decode_refuses_rexX_141 (rh xh bh : Nat) (h1 : rh < 2) (h2 : xh < 2)
    (h3 : bh < 2) (rest : List Byte) :
    decode (rexByteX rh xh bh :: natByte 141 :: rest) = none := by
  have hr : rh = 0 ∨ rh = 1 := by omega
  have hx : xh = 0 ∨ xh = 1 := by omega
  have hb : bh = 0 ∨ bh = 1 := by omega
  rcases hr with rfl | rfl <;> rcases hx with rfl | rfl <;>
    rcases hb with rfl | rfl <;> rfl

/-- The same bounded prefix followed by opcode `141` is refused by the
    Shift decoder (opcode `141` is neither `193` nor `211`). -/
theorem decodeShift_refuses_rexX_141 (rh xh bh : Nat) (h1 : rh < 2)
    (h2 : xh < 2) (h3 : bh < 2) (rest : List Byte) :
    decodeShift (rexByteX rh xh bh :: natByte 141 :: rest) = none := by
  have hr : rh = 0 ∨ rh = 1 := by omega
  have hx : xh = 0 ∨ xh = 1 := by omega
  have hb : bh = 0 ∨ bh = 1 := by omega
  rcases hr with rfl | rfl <;> rcases hx with rfl | rfl <;>
    rcases hb with rfl | rfl <;> rfl

/-- Any bounded REX.W(+X)(+R)(+B) prefix is refused by the Narrow
    decoder on the FIRST byte alone (Narrow's REX bytes are always
    `{64,65,68,69}`, strictly below every `rexByteX` value `72..79`),
    for ANY tail -- the single lemma this file's narrow disjointness
    needs for every covered form, LEA included. -/
theorem decodeNarrow_refuses_rexX (rh xh bh : Nat) (h1 : rh < 2) (h2 : xh < 2)
    (h3 : bh < 2) (rest : List Byte) :
    decodeNarrow (rexByteX rh xh bh :: rest) = none := by
  have hr : rh = 0 ∨ rh = 1 := by omega
  have hx : xh = 0 ∨ xh = 1 := by omega
  have hb : bh = 0 ∨ bh = 1 := by omega
  rcases hr with rfl | rfl <;> rcases hx with rfl | rfl <;>
    rcases hb with rfl | rfl <;> rfl

/-- The pilot decoder refuses every covered core encoding, over any
    suffix: no core opcode (`9`, `33`, `99`, `133`, `141`, `247` at
    digit 2/3, or `15` with a second byte in `{182,183,190,191}`) is
    among the pilot's recognised set
    (`{1,41,49,57,137,139}` register-direct, the `184..191` immediate
    range, or the bare non-REX opcodes). -/
theorem core_pilot_disjoint (b : CoreBefehl) (suffix : List Byte) :
    decode (encodeCore b ++ suffix) = none := by
  cases b with
  | lea64 dst base index disp =>
    cases index with
    | none =>
      show decode
          (([rexByteX (regHigh dst) 0 (regHigh base), natByte 141,
            modrmMem (regLow dst) 4, sibByte 0 4 (regLow base)] ++
            leBytes32 disp) ++ suffix) = none
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact decode_refuses_rexX_141 (regHigh dst) 0 (regHigh base)
        (regHigh_lt dst) (by decide) (regHigh_lt base) _
    | some p =>
      obtain ⟨r, sc⟩ := p
      show decode
          (([rexByteX (regHigh dst) (regHigh r) (regHigh base), natByte 141,
            modrmMem (regLow dst) 4,
            sibByte (scaleShift sc) (regLow r) (regLow base)] ++
            leBytes32 disp) ++ suffix) = none
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact decode_refuses_rexX_141 (regHigh dst) (regHigh r) (regHigh base)
        (regHigh_lt dst) (regHigh_lt r) (regHigh_lt base) _
  | andReg64 dst src => cases dst <;> cases src <;> rfl
  | orReg64 dst src => cases dst <;> cases src <;> rfl
  | testReg64 lhs rhs => cases lhs <;> cases rhs <;> rfl
  | notReg64 dst => cases dst <;> rfl
  | negReg64 dst => cases dst <;> rfl
  | movzx64From8 dst src => cases dst <;> cases src <;> rfl
  | movzx64From16 dst src => cases dst <;> cases src <;> rfl
  | movsx64From8 dst src => cases dst <;> cases src <;> rfl
  | movsx64From16 dst src => cases dst <;> cases src <;> rfl
  | movsx64From32 dst src => cases dst <;> cases src <;> rfl

/-- The core decoder refuses every pilot encoding, over any suffix. -/
theorem pilot_core_disjoint (b : Befehl) (suffix : List Byte) :
    decodeCore (encode b ++ suffix) = none := by
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

/-- The core decoder refuses every MulDiv encoding: `imul2` opens on
    opcode `15` with second byte `175`, disjoint from the core's
    `{182,183,190,191}`; `mulRax`/`divRax`/`idivRax` open on opcode
    `247` with ModRM digit in `{4,6,7}`, disjoint from the core's
    `{2,3}`. -/
theorem core_muldiv_disjoint (b : MulDivBefehl) (suffix : List Byte) :
    decodeCore (mulDivEncode b ++ suffix) = none := by
  cases b with
  | mulRax src => cases src <;> rfl
  | divRax src => cases src <;> rfl
  | idivRax src => cases src <;> rfl
  | imul2 dst src => cases dst <;> cases src <;> rfl

/-- The MulDiv decoder refuses every core NOT/NEG encoding (the only
    byte-level overlap risk: both open on `REX.W` + opcode `247`). -/
theorem muldiv_core_f7_disjoint (dst : Register) (suffix : List Byte) :
    decodeMulDiv (encodeCore (.notReg64 dst) ++ suffix) = none ∧
    decodeMulDiv (encodeCore (.negReg64 dst) ++ suffix) = none := by
  constructor <;> cases dst <;> rfl

/-- The core decoder refuses every Shift encoding: Shift opens only on
    opcodes `193`/`211`, neither of which is a core opcode. -/
theorem core_shift_disjoint (f : ShiftForm) (suffix : List Byte) :
    decodeCore (encodeShift f ++ suffix) = none := by
  cases f with
  | imm r dst n => cases dst <;> cases r <;> rfl
  | cl r dst => cases dst <;> cases r <;> rfl

/-- The Shift decoder refuses every core encoding: the core's opcodes
    are never `193`/`211`. -/
theorem shift_core_disjoint (b : CoreBefehl) (suffix : List Byte) :
    decodeShift (encodeCore b ++ suffix) = none := by
  cases b with
  | lea64 dst base index disp =>
    cases index with
    | none =>
      show decodeShift
          (([rexByteX (regHigh dst) 0 (regHigh base), natByte 141,
            modrmMem (regLow dst) 4, sibByte 0 4 (regLow base)] ++
            leBytes32 disp) ++ suffix) = none
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact decodeShift_refuses_rexX_141 (regHigh dst) 0 (regHigh base)
        (regHigh_lt dst) (by decide) (regHigh_lt base) _
    | some p =>
      obtain ⟨r, sc⟩ := p
      show decodeShift
          (([rexByteX (regHigh dst) (regHigh r) (regHigh base), natByte 141,
            modrmMem (regLow dst) 4,
            sibByte (scaleShift sc) (regLow r) (regLow base)] ++
            leBytes32 disp) ++ suffix) = none
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact decodeShift_refuses_rexX_141 (regHigh dst) (regHigh r)
        (regHigh base) (regHigh_lt dst) (regHigh_lt r) (regHigh_lt base) _
  | andReg64 dst src => cases dst <;> cases src <;> rfl
  | orReg64 dst src => cases dst <;> cases src <;> rfl
  | testReg64 lhs rhs => cases lhs <;> cases rhs <;> rfl
  | notReg64 dst => cases dst <;> rfl
  | negReg64 dst => cases dst <;> rfl
  | movzx64From8 dst src => cases dst <;> cases src <;> rfl
  | movzx64From16 dst src => cases dst <;> cases src <;> rfl
  | movsx64From8 dst src => cases dst <;> cases src <;> rfl
  | movsx64From16 dst src => cases dst <;> cases src <;> rfl
  | movsx64From32 dst src => cases dst <;> cases src <;> rfl

/-- The core decoder refuses every Narrow encoding: Narrow's REX bytes
    are always `{64,65,68,69}` (W=0), never a core REX byte `72..79`. -/
theorem core_narrow_disjoint (op : NarrowOp) (suffix : List Byte) :
    decodeCore (encodeNarrow op ++ suffix) = none := by
  cases op with
  | mov32rr dst src => cases dst <;> cases src <;> rfl
  | movzx8 dst src => cases dst <;> cases src <;> rfl
  | movsx8 dst src => cases dst <;> cases src <;> rfl
  | store32 base src d => cases base <;> cases src <;> rfl

/-- The Narrow decoder refuses every core encoding: the core's REX
    bytes are always `72..79` (W=1), never in Narrow's `{64,65,68,69}`. -/
theorem narrow_core_disjoint (b : CoreBefehl) (suffix : List Byte) :
    decodeNarrow (encodeCore b ++ suffix) = none := by
  cases b with
  | lea64 dst base index disp =>
    cases index with
    | none =>
      show decodeNarrow
          (([rexByteX (regHigh dst) 0 (regHigh base), natByte 141,
            modrmMem (regLow dst) 4, sibByte 0 4 (regLow base)] ++
            leBytes32 disp) ++ suffix) = none
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact decodeNarrow_refuses_rexX (regHigh dst) 0 (regHigh base)
        (regHigh_lt dst) (by decide) (regHigh_lt base) _
    | some p =>
      obtain ⟨r, sc⟩ := p
      show decodeNarrow
          (([rexByteX (regHigh dst) (regHigh r) (regHigh base), natByte 141,
            modrmMem (regLow dst) 4,
            sibByte (scaleShift sc) (regLow r) (regLow base)] ++
            leBytes32 disp) ++ suffix) = none
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact decodeNarrow_refuses_rexX (regHigh dst) (regHigh r)
        (regHigh base) (regHigh_lt dst) (regHigh_lt r) (regHigh_lt base) _
  | andReg64 dst src => cases dst <;> cases src <;> rfl
  | orReg64 dst src => cases dst <;> cases src <;> rfl
  | testReg64 lhs rhs => cases lhs <;> cases rhs <;> rfl
  | notReg64 dst => cases dst <;> rfl
  | negReg64 dst => cases dst <;> rfl
  | movzx64From8 dst src => cases dst <;> cases src <;> rfl
  | movzx64From16 dst src => cases dst <;> cases src <;> rfl
  | movsx64From8 dst src => cases dst <;> cases src <;> rfl
  | movsx64From16 dst src => cases dst <;> cases src <;> rfl
  | movsx64From32 dst src => cases dst <;> cases src <;> rfl

/- CUTS:
   Proved here: ten covered P0 integer forms (LEA/AND/OR/TEST/NOT/NEG/
   MOVZX×2/MOVSX×3) as an independent step (`coreSchritt`) over the
   REAL `Zustand`, reusing (never redefining) `andW`/`orW`/`logikFlags`/
   `negWf`/`NegGueltig`/`notB`/`extendNarrow`/`shlB`/`dispWort`/
   `schrittRegister`; exact architectural flags (NEG's CF/OF/AF/SF/ZF/PF
   via the reused `NegGueltig`, logic CF=OF=false/AF=none via the reused
   `logikFlags`, NOT and LEA leaving flags untouched); a canonical byte
   codec (`encodeCore`/`decodeCore`) with REX.W(+X)(+R)(+B) prefixes,
   SIB-forced LEA, round trips for every admitted form
   (`roundtripCore`, admission `coreValid` excluding only an `rsp`
   LEA index), the 1..15 length bound, and six disjointness theorems
   fixing the exact byte boundary to the pilot codec and to
   MulDiv/Shift/Narrow (both directions each).
   NOT proved here, and not claimed:
   - No hardware correspondence: the encodings are a stated canonical
     subset (one row per operation) with self-consistency (round trip)
     only, not verified against silicon. The choice to force a SIB byte
     for every LEA (rather than the base-only non-SIB ModRM the pilot
     uses for `load64`/`store64` when the base is not `rsp`/`r12`) is a
     canonical-subset simplification, not a hardware claim.
   - No arbitrary-input decode-length soundness: unlike
     `decodeMulDiv_len_ok`/`decodeNarrow_abdeckung`, this file proves
     length consumption only for bytes that come from `encodeCore`
     (`roundtripCore_len_ok`), not for every byte string a sub-decoder
     might accept. The per-branch structure (`decodeCoreTail`'s single
     `match` dispatch, each tail consuming a fixed prefix) makes this
     provable the same way; it is left for a follow-up pass.
   - No memory-operand forms: AND/OR/TEST/NOT/NEG here are
     register-direct only (no `[mem]` operand); LEA never dereferences
     its computed address (by definition). Immediate forms of AND/OR/
     TEST are not covered.
   - No fetch wiring: `decodeCore` parses caller-supplied byte lists,
     never actual executable memory; permission-checked fetch is the
     unified path's business (lane 575 style), not this file's.
   - No source correspondence beyond what `IntegerCoreWitnesses.lean`
     claims (AND/OR/NEG value transfer, LEA's address-selection fact,
     TEST's branch-on-zero fact); the AND/OR/NEG transfer is bounded to
     nonnegative source values in range, matching `zahlWort`'s own
     stated lossiness outside that range.
   - No TSO/concurrency bridge: every fact is sequential over one
     `Zustand`; memory is never touched by any of the ten forms, so no
     atomicity question even arises here.
   - No cost transfer: no latency, throughput or code-size claim.
   - No new hardware or software assumption and no checker rule: no
     diagnostic, poison-probe, example or CLI number is taken.
-/

#print axioms scaleFromBits_scaleShift
#print axioms scaleShift_lt
#print axioms leaVal
#print axioms coreSchritt
#print axioms core_lea64
#print axioms core_andReg64
#print axioms core_orReg64
#print axioms core_testReg64
#print axioms core_notReg64
#print axioms core_negReg64
#print axioms core_movzx64From8
#print axioms core_movzx64From16
#print axioms core_movsx64From8
#print axioms core_movsx64From16
#print axioms core_movsx64From32
#print axioms core_laenge_verweigert
#print axioms coreSchritt_speicher
#print axioms coreSchritt_flags_unveraendert
#print axioms encodeCore_laenge
#print axioms encodeCore_len_ok
#print axioms rexCoreBits_rexByteX
#print axioms rexCoreBits_rexByte
#print axioms modrmReg_fields
#print axioms codeReg_regHigh_regLow
#print axioms roundtrip_andReg64
#print axioms roundtrip_orReg64
#print axioms roundtrip_testReg64
#print axioms roundtrip_notReg64
#print axioms roundtrip_negReg64
#print axioms roundtrip_movzx64From8
#print axioms roundtrip_movzx64From16
#print axioms roundtrip_movsx64From8
#print axioms roundtrip_movsx64From16
#print axioms roundtrip_movsx64From32
#print axioms roundtrip_lea64_none
#print axioms roundtrip_lea64_some
#print axioms roundtripCore
#print axioms roundtripCore_len_ok
#print axioms decode_refuses_rexX_141
#print axioms decodeShift_refuses_rexX_141
#print axioms decodeNarrow_refuses_rexX
#print axioms core_pilot_disjoint
#print axioms pilot_core_disjoint
#print axioms core_muldiv_disjoint
#print axioms muldiv_core_f7_disjoint
#print axioms core_shift_disjoint
#print axioms shift_core_disjoint
#print axioms core_narrow_disjoint
#print axioms narrow_core_disjoint

end Gabbro.Grammatik.X86
