module

public import Grammatik.Parser.Elab.UebersetzeAllg.Eingebaut

@[expose] public section

/-
  C13 fixtures (`_zeuge`) of the lowering of the closed integer builtins (`lowIb1`, `lowIb2`) on sided numbers at the
  storage width `W = 8`, generic in the unit, the context and the resources: the accepted forms with the range they
  carry, and the refusals the design names (unknown width, zero scan, shift or rotate amount `W`, a partial word, a
  saturating addition over crossing ranges, a byte swap off 16/32/64 bits, an operand outside the declared range).
  Every statement is checked by evaluation (`rfl`).
-/

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

namespace EingebautZeuge

variable {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}

/-- A sided literal `n`, widened to the range `lo .. hi`. -/
def sr (lo hi n : Int) (h0 : lo ≤ n := by decide) (h1 : n ≤ hi := by decide) : LowSide u Γ Λ :=
  { range := (lo, hi), term := Expr.widen h0 h1 (Expr.lit n) }

/-- The range of an accepted lowering. -/
def bereich (r : Except String (LowSide u Γ Λ)) : Option (Int × Int) := r.toOption.map (·.range)

/-! ## Accepted forms -/

/-- Wrapping addition of two bytes: the result is the whole byte range. -/
theorem addW_ok_zeuge :
    bereich (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .addW 8 (sr 0 255 200) (sr 0 255 100)) = some (0, 255) := by rfl

/-- A literal included in the byte range is widened to it. -/
theorem addW_literal_ok_zeuge :
    bereich (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .addW 8 (sr 0 255 200) (sr 7 7 7)) = some (0, 255) := by rfl

/-- Shift amount `W - 1 = 7`: accepted. -/
theorem shlW_ok_zeuge :
    bereich (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .shlW 8 (sr 0 255 1) (sr 0 7 7)) = some (0, 255) := by rfl

/-- A scan over an operand that excludes zero: the result is `0 .. W - 1`. -/
theorem clz_ok_zeuge :
    bereich (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .clz 8 (sr 1 255 5)) = some (0, 7) := by rfl

/-- The population count reaches `W`. -/
theorem popcount_ok_zeuge :
    bereich (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .popcount 8 (sr 0 255 5)) = some (0, 8) := by rfl

/-- A rotate of a whole byte by an amount below `W`. -/
theorem rotl_ok_zeuge :
    bereich (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .rotl 8 (sr 0 255 5) (sr 0 7 3)) = some (0, 255) := by rfl

/-- A saturating addition over nested ranges saturates at the larger one. -/
theorem addS_ok_zeuge :
    bereich (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .addS 0 (sr 0 255 5) (sr 5 20 6)) = some (0, 255) := by rfl

/-- A signed range saturates as well. -/
theorem addS_vz_ok_zeuge :
    bereich (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .addS 0 (sr (-128) 127 5) (sr (-128) 127 6)) = some (-128, 127) := by
  rfl

/-- A byte swap of a whole `u16`. -/
theorem bswap16_ok_zeuge :
    bereich (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .bswap 16 (sr 0 65535 5)) = some (0, 65535) := by rfl

/-! ## Refusals -/

/-- A width the declaration did not name (`0`) has no term. -/
theorem breite_unbekannt_abgelehnt_zeuge :
    (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .popcount 0 (sr 0 255 5)).toBool = false ∧
    (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .addW 0 (sr 0 255 5) (sr 0 255 5)).toBool = false := ⟨rfl, rfl⟩

/-- A scan over an operand that may be zero has no term (no CPU zero-case convention). -/
theorem nullscan_abgelehnt_zeuge :
    (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .clz 8 (sr 0 255 5)).toBool = false ∧
    (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .ctz 8 (sr 0 255 5)).toBool = false ∧
    (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .log2Floor 8 (sr 0 255 5)).toBool = false := ⟨rfl, rfl, rfl⟩

/-- A shift amount `W` (or a range reaching it) has no term. -/
theorem schiebebetrag_W_abgelehnt_zeuge :
    (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .shlW 8 (sr 0 255 1) (sr 0 8 3)).toBool = false := by rfl

/-- A rotate of a partial word, or by the amount `W`, has no term. -/
theorem drehung_abgelehnt_zeuge :
    (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .rotl 8 (sr 0 15 3) (sr 0 7 1)).toBool = false ∧
    (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .rotr 8 (sr 0 255 3) (sr 0 8 1)).toBool = false := ⟨rfl, rfl⟩

/-- A saturating addition over crossing ranges has no common declared range. -/
theorem saettigung_kreuzend_abgelehnt_zeuge :
    (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .addS 0 (sr 0 10 3) (sr 5 20 6)).toBool = false := by rfl

/-- A byte swap off 16, 32 and 64 bits, or of a partial word, has no term. -/
theorem bswap_abgelehnt_zeuge :
    (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .bswap 12 (sr 0 4095 5)).toBool = false ∧
    (lowIb1 (u := u) (Γ := Γ) (Λ := Λ) .bswap 16 (sr 0 255 5)).toBool = false := ⟨rfl, rfl⟩

/-- An operand outside the declared operand range has no term (a range wider than the byte). -/
theorem operand_ausserhalb_abgelehnt_zeuge :
    (lowIb2 (u := u) (Γ := Γ) (Λ := Λ) .addW 8 (sr 0 255 5) (sr 0 300 5)).toBool = false := by rfl

end EingebautZeuge

end Gabbro.Grammatik.Parser.UebersetzeAllg
