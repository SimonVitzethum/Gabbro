/-
  File:      Grammatik/Speichermodell/DarstellungTy.lean
  Subject:   The Lean side of the minimal-width / packed data layout,
             at the type level (agent 03, usability/efficiency team).

  `Darstellung.lean` proves the layout over bare `Int` ranges;
  `CSpeicher.lean` encodes Gabbro values as C integers (`encW`).
  This file joins them: `tyBits` (bits per `Ty`, with the `option`
  sentinel and the `grund` case count as values), `encN` (the offset
  encoding of a value), the fit (`encN_lt`), the round trip
  (`decN_encN`), the narrow cell (`narrowCell`, `narrow_fits`,
  `narrow_le_wide`), and packed arrays (`getCell`/`setCell` with
  non-interference, `packBytes_cells`). Over every type, no program
  named. Nothing here is an Arm instruction fact; Sail citations do
  not apply (rule 7 N/A, recorded in CUTS).
-/
import Grammatik.Speichermodell.Darstellung
import Grammatik.Kern.Syntax.Typen
import Grammatik.CBackend.Semantik.CSpeicher

namespace Grammatik.Speichermodell.DarstellungTy

/-! ## 1. Bits per type, and the offset encoding of a value. -/

/-- Bits of the offset encoding of a `Ty`: ranges via `Darstellung.bits`;
    `bool` is one bit; `option` counts the sentinel `n` as a value;
    `grund n` counts its `n` cases (`n ≥ 1`, else no cell). All other
    types have no minimal-width cell. -/
def tyBits : Gabbro.Grammatik.Ty → Option Nat
  | .int lo hi => some (Grammatik.Speichermodell.Darstellung.bits lo hi)
  | .bool => some 1
  | .opt n => some (Grammatik.Speichermodell.Darstellung.bits 0 n)
  | .grund n => if 1 ≤ n then
      some (Grammatik.Speichermodell.Darstellung.bits 0 ((n : Int) - 1))
      else none
  | _ => none

/-- The offset base of a type: `lo` for ranges, `0` for the rest. -/
def tyLo : Gabbro.Grammatik.Ty → Int
  | .int lo _ => lo
  | _ => 0

/-- The offset encoding of a value: `Darstellung.enc` of `encW`. -/
def encN {F : Type} {sig : F → Nat} (t : Gabbro.Grammatik.Ty)
    (v : Gabbro.Grammatik.Val F sig t) : Nat :=
  Grammatik.Speichermodell.Darstellung.enc (tyLo t)
    (Gabbro.Grammatik.encW t v)

/-! ## 2. Every value fits its bits. -/

/-- **The offset encoding of every value fits in `tyBits`.**
    Ranges via `Darstellung.enc_lt_two_pow` (with `Zahl.lo_le` /
    `le_hi`, as `encW_fits` does); `option` via `encOpt` (the sentinel
    `n` included); `grund` via `Fin`. -/
theorem encN_lt {F : Type} {sig : F → Nat} (t : Gabbro.Grammatik.Ty)
    (b : Nat) (hb : tyBits t = some b)
    (v : Gabbro.Grammatik.Val F sig t) : encN t v < 2 ^ b := by
  cases t with
  | int lo hi =>
      simp only [tyBits] at hb
      cases hb
      simp only [encN, tyLo, Gabbro.Grammatik.encW]
      exact Grammatik.Speichermodell.Darstellung.enc_lt_two_pow lo hi _
        (Gabbro.Grammatik.Zahl.lo_le v) (Gabbro.Grammatik.Zahl.le_hi v)
  | bool =>
      simp only [tyBits] at hb
      cases hb
      cases v <;> simp only [encN, tyLo, Gabbro.Grammatik.encW,
        Grammatik.Speichermodell.Darstellung.enc] <;> decide
  | opt n =>
      simp only [tyBits] at hb
      cases hb
      cases v with
      | none =>
          simp only [encN, tyLo, Gabbro.Grammatik.encW,
            Gabbro.Grammatik.encOpt,
            Grammatik.Speichermodell.Darstellung.enc]
          by_cases h : 0 ≤ n
          · exact Grammatik.Speichermodell.Darstellung.enc_lt_two_pow
              0 n n h (by omega)
          · have hpos : 0 < 2 ^ Grammatik.Speichermodell.Darstellung.bits 0 n :=
              Nat.two_pow_pos _
            omega
      | some z =>
          simp only [encN, tyLo, Gabbro.Grammatik.encW,
            Gabbro.Grammatik.encOpt]
          exact Grammatik.Speichermodell.Darstellung.enc_lt_two_pow 0 n _
            (by have h1 := Gabbro.Grammatik.Zahl.lo_le z; omega)
            (by have h2 := Gabbro.Grammatik.Zahl.le_hi z; omega)
  | grund n =>
      simp only [tyBits] at hb
      split at hb
      · cases hb
        simp only [encN, tyLo, Gabbro.Grammatik.encW]
        have h1 : (0 : Int) ≤ ((v.val : Nat) : Int) := by
          exact_mod_cast Nat.zero_le _
        have h2 : ((v.val : Nat) : Int) ≤ (n : Int) - 1 := by
          have := v.isLt
          omega
        exact Grammatik.Speichermodell.Darstellung.enc_lt_two_pow 0 _ _ h1 h2
      · simp at hb
  | sum _ => simp only [tyBits] at hb; simp at hb
  | never => simp only [tyBits] at hb; simp at hb
  | fl _ => simp only [tyBits] at hb; simp at hb
  | fnptr _ => simp only [tyBits] at hb; simp at hb
  | ptr _ _ => simp only [tyBits] at hb; simp at hb

/-! ## 3. The round trip (with the `option` side condition).

    `dec (tyLo t) (encN t v) = encW t v` needs, for `.opt n`, that the
    sentinel is non-negative: at `n < 0`, `encW` answers `n` while the
    offset encoding clamps to `0` (`dec 0 (enc 0 n) = 0 ≠ n`), so the
    unconditional form is false. Ranges need no condition
    (`dec_enc` takes its bounds as hypotheses, contradictory or not);
    `grund` cases come from `Fin`; the remaining types encode `0`. -/
theorem decN_encN {F : Type} {sig : F → Nat} (t : Gabbro.Grammatik.Ty)
    (v : Gabbro.Grammatik.Val F sig t)
    (hOpt : ∀ n : Int, t = .opt n → 0 ≤ n) :
    Grammatik.Speichermodell.Darstellung.dec (tyLo t) (encN t v) =
      Gabbro.Grammatik.encW t v := by
  cases t with
  | int lo hi =>
      simp only [tyLo, encN]
      exact Grammatik.Speichermodell.Darstellung.dec_enc lo hi _
        (Gabbro.Grammatik.Zahl.lo_le v) (Gabbro.Grammatik.Zahl.le_hi v)
  | bool =>
      cases v <;>
        simp only [tyLo, encN, Gabbro.Grammatik.encW,
          Grammatik.Speichermodell.Darstellung.enc,
          Grammatik.Speichermodell.Darstellung.dec] <;> decide
  | opt n =>
      cases v with
      | none =>
          have h0 := hOpt n rfl
          simp only [tyLo, encN]
          exact Grammatik.Speichermodell.Darstellung.dec_enc 0 n n h0
            (by omega)
      | some z =>
          simp only [tyLo, encN]
          exact Grammatik.Speichermodell.Darstellung.dec_enc 0
            (Gabbro.Grammatik.Zahl.n z) (Gabbro.Grammatik.Zahl.n z)
            (Gabbro.Grammatik.Zahl.lo_le z) (by omega)
  | grund n =>
      simp only [tyLo, encN]
      exact Grammatik.Speichermodell.Darstellung.dec_enc 0
        ((v.val : Nat) : Int) ((v.val : Nat) : Int)
        (by exact_mod_cast Nat.zero_le _) (by omega)
  | sum _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | never =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | fl _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | fnptr _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl
  | ptr _ _ =>
      simp only [tyLo, encN, Gabbro.Grammatik.encW]
      rfl

/-! ## 4. The narrow cell.

    `narrowCell` maps the bit count through `Darstellung.zellBytes`.
    `narrow_fits` needs the width premise: past 64 bits the C cell no
    longer covers the type (e.g. `.int 0 (2^100)` sits in `some 8`
    while its largest value needs 101 bits), so the unconditional form
    is false — recorded, with the counterexample, in REPORT-03.md. -/

/-- The narrow cell of a type, in bytes (`none` = no minimal cell). -/
def narrowCell (t : Gabbro.Grammatik.Ty) : Option Nat :=
  (tyBits t).map Grammatik.Speichermodell.Darstellung.zellBytes

/-- **A narrow cell within 64 bits holds the encoded value.** -/
theorem narrow_fits {F : Type} {sig : F → Nat}
    (t : Gabbro.Grammatik.Ty) (b c : Nat) (hb : tyBits t = some b)
    (h64 : b ≤ 64) (hc : narrowCell t = some c)
    (v : Gabbro.Grammatik.Val F sig t) :
    encN t v < 2 ^ (8 * c) := by
  have henc := encN_lt t b hb v
  simp only [narrowCell, hb, Option.map_some] at hc
  cases hc
  have hfit : b ≤ 8 * Grammatik.Speichermodell.Darstellung.zellBytes b :=
    Grammatik.Speichermodell.Darstellung.zellBytes_fits b h64
  have hpow : 2 ^ b ≤
      2 ^ (8 * Grammatik.Speichermodell.Darstellung.zellBytes b) :=
    Nat.pow_le_pow_right (by omega) hfit
  omega

/-- **The narrow cell never costs more than the declared C word it
    replaces** (for `0 ≤ lo` and `hi` inside the word): the type-level
    reading of `Darstellung.schmal_le_wort`. -/
theorem narrow_le_wide (lo hi : Int) (w : Nat)
    (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) (h0 : 0 ≤ lo)
    (hh : hi < 2 ^ (8 * w)) (c : Nat)
    (hc : narrowCell (.int lo hi) = some c) : c ≤ w := by
  simp only [narrowCell, tyBits, Option.map_some] at hc
  cases hc
  have h := Grammatik.Speichermodell.Darstellung.schmal_le_wort lo hi w hw
    h0 hh
  simp only [Grammatik.Speichermodell.Darstellung.schmalBytes,
    Grammatik.Speichermodell.Darstellung.wortBytes] at h
  omega

/-! ## 5. Witnesses: the audit numbers, decided. -/

/-- `u32 in 0 .. 3` needs 2 bits. -/
theorem tyBits_int03 : tyBits (.int 0 3) = some 2 := by decide

/-- `bool` needs 1 bit. -/
theorem tyBits_bool : tyBits .bool = some 1 := by decide

/-- `option` with sentinel 255 needs 8 bits. -/
theorem tyBits_opt255 : tyBits (.opt 255) = some 8 := by decide

/-- `option` with sentinel 256 needs 9 bits. -/
theorem tyBits_opt256 : tyBits (.opt 256) = some 9 := by decide

/-- 1000 `grund` cases need 10 bits. -/
theorem tyBits_grund1000 : tyBits (.grund 1000) = some 10 := by decide

/-- `u32 in 0 .. 100` fits one byte. -/
theorem narrowCell_int100 : narrowCell (.int 0 100) = some 1 := by decide

/-- `u32 in 0 .. 70000` fits four bytes. -/
theorem narrowCell_int70000 : narrowCell (.int 0 70000) = some 4 := by decide

/-- `encN_lt` fires on a concrete range value. -/
theorem encN_lt_int59 {F : Type} {sig : F → Nat} :
    @encN F sig (.int 5 9)
      (⟨7, by decide, by decide⟩ : Gabbro.Grammatik.Val F sig (.int 5 9)) <
      2 ^ 3 :=
  @encN_lt F sig (.int 5 9) 3 (by decide) _

/-- `encN_lt` fires on a concrete `option` value (`some`). -/
theorem encN_lt_opt3 {F : Type} {sig : F → Nat} :
    @encN F sig (.opt 3)
      (some (⟨2, by decide, by decide⟩ : Gabbro.Grammatik.Zahl 0 2)) < 2 ^ 2 :=
  @encN_lt F sig (.opt 3) 2 (by decide) _

/-! ## 6. Packed arrays: one word, many cells.

    A packed array of `n` cells of `b` bits is a single `Nat` word;
    cell `i` is bits `i*b .. i*b+b-1` (`Darstellung.feld` reads,
    `Darstellung.setze` writes). A write is read back exactly
    (`getCell_setCell`, from `Darstellung.feld_setze`); disjoint cells
    do not interfere (`getCell_setCell_ne`, via the two lemmas below:
    a field entirely below, resp. above, the written field keeps its
    value — the axiomatic form of `setze_niedrig`/`setze_hoch` for
    reads). -/

/-- Cell `i` of `b` bits in word `w`. -/
def getCell (w b i : Nat) : Nat :=
  Grammatik.Speichermodell.Darstellung.feld w (i * b) b

/-- Cell `i` of `b` bits in word `w` set to `v`. -/
def setCell (w b i v : Nat) : Nat :=
  Grammatik.Speichermodell.Darstellung.setze w (i * b) b v

/-- **A written cell reads back exactly** (for a value in the width). -/
theorem getCell_setCell (w b i v : Nat) (hv : v < 2 ^ b) :
    getCell (setCell w b i v) b i = v := by
  simp only [getCell, setCell]
  exact Grammatik.Speichermodell.Darstellung.feld_setze _ _ _ _ hv

/-- Reading below a written field sees only the low bits: split the
    word at `2^k` (generalised `Q`/`R`, so every rewrite below stays
    on the read side), push the high multiple of `2^b'` through the
    outer `%`, and identify the low part by `setze_niedrig`. -/
theorem div_mod_small_of_high (w k k' b' : Nat) (hle : k' + b' ≤ k) :
    (w / 2 ^ k') % 2 ^ b' = ((w % 2 ^ k) / 2 ^ k') % 2 ^ b' := by
  have hkk : k' ≤ k := by omega
  have e1 : 2 ^ k = 2 ^ k' * 2 ^ (k - k') := by
    rw [← Nat.pow_add]; congr 1; omega
  have e2 : 2 ^ (k - k') = 2 ^ b' * 2 ^ (k - k' - b') := by
    rw [← Nat.pow_add]; congr 1; omega
  have key : ∀ (Q R : Nat), w = 2 ^ k * Q + R → R < 2 ^ k →
      (w / 2 ^ k') % 2 ^ b' = (R / 2 ^ k') % 2 ^ b' := by
    intro Q R hQR hR
    rw [hQR, e1, Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), e2, Nat.mul_assoc,
      Nat.add_mul_mod_self_left]
  exact key _ _ (Nat.div_add_mod w (2 ^ k)).symm
    (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- **A field entirely below the written field is untouched.** -/
theorem feld_setze_disjoint_below (w k b v k' b' : Nat)
    (h : k' + b' ≤ k) :
    Grammatik.Speichermodell.Darstellung.feld
        (Grammatik.Speichermodell.Darstellung.setze w k b v) k' b' =
      Grammatik.Speichermodell.Darstellung.feld w k' b' := by
  simp only [Grammatik.Speichermodell.Darstellung.feld]
  rw [div_mod_small_of_high _ _ _ _ h,
    Grammatik.Speichermodell.Darstellung.setze_niedrig,
    ← div_mod_small_of_high _ _ _ _ h]

/-- Reading above a written field factors through the preserved
    high part: split the divisor, divide twice, and use `setze_hoch`. -/
theorem div_mod_high_of_low (w k b k' b' : Nat) (h : k + b ≤ k') :
    (w / 2 ^ k') % 2 ^ b' =
      ((w / 2 ^ (k + b)) / 2 ^ (k' - (k + b))) % 2 ^ b' := by
  have e : 2 ^ (k + b) * 2 ^ (k' - (k + b)) = 2 ^ k' := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.div_div_eq_div_mul, e]

/-- **A field entirely above the written field is untouched**: divide
    past the written field (which `setze_hoch` says is preserved),
    then read the remainder. -/
theorem feld_setze_disjoint_above (w k b v k' b' : Nat)
    (h : k + b ≤ k') :
    Grammatik.Speichermodell.Darstellung.feld
        (Grammatik.Speichermodell.Darstellung.setze w k b v) k' b' =
      Grammatik.Speichermodell.Darstellung.feld w k' b' := by
  have e : 2 ^ (k + b) * 2 ^ (k' - (k + b)) = 2 ^ k' := by
    rw [← Nat.pow_add]; congr 1; omega
  simp only [Grammatik.Speichermodell.Darstellung.feld]
  rw [div_mod_high_of_low _ _ _ _ _ h,
    Grammatik.Speichermodell.Darstellung.setze_hoch,
    Nat.div_div_eq_div_mul, e]

/-- **Disjoint cells do not interfere.** Note the statement carries no
    `v < 2 ^ b`: non-interference is structural (both cells read the
    same untouched bits); the width hypothesis belongs to
    `getCell_setCell` alone. -/
theorem getCell_setCell_ne (w b i j v : Nat) (hne : i ≠ j) :
    getCell (setCell w b i v) b j = getCell w b j := by
  simp only [getCell, setCell]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h1 : i + 1 ≤ j := by omega
    have hmul : (i + 1) * b ≤ j * b := Nat.mul_le_mul_right b h1
    have hle : i * b + b ≤ j * b := by
      have e : (i + 1) * b = i * b + b := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    exact feld_setze_disjoint_above w (i * b) b v (j * b) b hle
  · have h1 : j + 1 ≤ i := by omega
    have hmul : (j + 1) * b ≤ i * b := Nat.mul_le_mul_right b h1
    have hle : j * b + b ≤ i * b := by
      have e : (j + 1) * b = j * b + b := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    exact feld_setze_disjoint_below w (i * b) b v (j * b) b hle

/-- **A packed array costs at most the cell-per-element layout** (`n`
    cells of `b` bits with `b ≤ 8 * c` fit in `n * c` bytes). -/
theorem packBytes_cells (n b c : Nat) (h : b ≤ 8 * c) :
    Grammatik.Speichermodell.Darstellung.packBytes n b ≤ n * c := by
  have hle := Grammatik.Speichermodell.Darstellung.packBytes_le_zellen
    n b c h
  simp only [Grammatik.Speichermodell.Darstellung.zellenBytes] at hle
  exact hle

/-- A written 2-bit cell reads back. -/
theorem cells_zeuge : getCell (setCell 0 2 5 3) 2 5 = 3 := by decide

/-- A neighbouring write keeps the cell. -/
theorem cells_zeuge_ne :
    getCell (setCell (setCell 0 2 5 3) 2 6 1) 2 5 = 3 := by decide

end Grammatik.Speichermodell.DarstellungTy

/-
CUTS: what is not proved or not covered.
  - Proved: type-level bits and offset encoding (`tyBits`, `tyLo`,
    `encN`), fit (`encN_lt`), round trip (`decN_encN`, with the
    `0 ≤ n` side condition for `.opt` — the unconditional form is
    false at negative sentinels), the narrow cell (`narrowCell`,
    `narrow_fits` with the `b ≤ 64` premise, `narrow_le_wide`),
    packed arrays (`getCell`/`setCell`, write-readback,
    disjoint non-interference, `packBytes_cells`), and decide
    witnesses for the audit numbers.
  - `narrow_fits` is deliberately premised: past 64 bits the
    unconditional form is false (`.int 0 (2^100)` sits in `some 8`
    while its largest value needs 101 bits).
  - `getCell_setCell_ne` deliberately carries no `v < 2 ^ b`:
    non-interference is structural; the width hypothesis belongs to
    `getCell_setCell` alone (deviation from the hint, recorded).
  - NOT proved: lowering to actual AArch64 instructions (`ldrb`/
    `ubfx` selection is compiler work); `sum`/`never`/`fl`/`fnptr`/
    `ptr` cells (no minimal-width form, `tyBits` is `none`);
    heterogeneous per-element widths in one word.
  - Rule 7 (Sail citations) is N/A: representation metatheory over
    `Int`/`Nat`, no Arm instruction semantics (confidence: definitional,
    this file states no fact about any machine).
-/

#print axioms Grammatik.Speichermodell.DarstellungTy.encN_lt
#print axioms Grammatik.Speichermodell.DarstellungTy.decN_encN
#print axioms Grammatik.Speichermodell.DarstellungTy.narrow_fits
#print axioms Grammatik.Speichermodell.DarstellungTy.narrow_le_wide
#print axioms Grammatik.Speichermodell.DarstellungTy.getCell_setCell
#print axioms Grammatik.Speichermodell.DarstellungTy.feld_setze_disjoint_below
#print axioms Grammatik.Speichermodell.DarstellungTy.feld_setze_disjoint_above
#print axioms Grammatik.Speichermodell.DarstellungTy.getCell_setCell_ne
#print axioms Grammatik.Speichermodell.DarstellungTy.packBytes_cells
#print axioms Grammatik.Speichermodell.DarstellungTy.encN_lt_int59
#print axioms Grammatik.Speichermodell.DarstellungTy.encN_lt_opt3
#print axioms Grammatik.Speichermodell.DarstellungTy.cells_zeuge
#print axioms Grammatik.Speichermodell.DarstellungTy.cells_zeuge_ne
