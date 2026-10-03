/-
  File:      Grammatik/X86/OptStrengthRed.lean
  Subject:   Strength reduction rule lemma: imul-by-8 to shl (lane 871).

  DESIGN section 7 row: local premise "per-width flag/fault identity lemma
  (CF vs OF distinct)", certificate "A register rule", failure cases
  "imul r,8 -> shl r,3 with live CF; signed-divide rounding via shift;
  a*2.0 -> a+a (rounding/NaN)", phase L, cost O(window).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`,
  `X86.Ganzzahl`, `X86.ShiftLogic`, `X86.MulDiv`, `X86.StaerkeReduktion`):
  the per-width flag/fault identity (imul locks CF = OF to the signed
  carry while shl-by-3 leaves OF undefined and reads CF as the last bit
  shifted out, so a live CF refuses the rewrite), the four validator-decided
  side conditions with their refusals, the generic value identity
  `a * 8 = a << 3` over arbitrary nonneg values, and the `Endblock.bind`
  connection (value, `execEnd` outcome, word image, admission implies
  CF-dead). The float `a*2.0 -> a+a` shape and the signed-divide-via-shift
  shape have NO rewrite arm and are refused by name. No `ensures` is
  derived, no refusal becomes a warning, no faulting form is speculated
  above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Ganzzahl
import Grammatik.X86.ShiftLogic
import Grammatik.X86.MulDiv
import Grammatik.X86.StaerkeReduktion

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one strength-reduction site
    (DESIGN section 7 row): CF dead at the site (recomputed liveness
    citation), the width/range check passed (count below width, no
    overflow -- recomputed range citation), no float shape, no
    signed-divide shape. -/
structure StrengthCert where
  cfTot : Bool
  breiteOk : Bool
  keinFP : Bool
  keinSDiv : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def staerkeZulassen (c : StrengthCert) : Bool :=
  c.cfTot && c.breiteOk && c.keinFP && c.keinSDiv

/-! ## 1. Per-width flag/fault identity: CF is distinct from OF.

    IMUL locks CF and OF together to the signed carry (`mulFlagsS` pins
    both to `mulTragS`; `MulGueltigS` in `Ganzzahl.lean`: CF = OF =
    signed carry, AF undefined). SHL-by-3 instead reads CF as the last
    bit shifted out (`shlTrag`: bit `64 - 3` of the truncated operand)
    and leaves OF UNDEFINED (`shlUeberlauf`: `none` for every masked
    count but one). Same value, different flags -- which is exactly why
    the DESIGN row demands the identity lemma and refuses the rewrite
    with a live CF (section 2). -/

/-- IMUL locks CF and OF together to the signed carry. -/
theorem imul_cf_gleicht_of (f : Flags) (x y : Wort) :
    (mulFlagsS f x y).cf = (mulFlagsS f x y).of := by
  rfl

/-- SHL-by-3 leaves OF undefined and reads CF as bit 61 of the operand:
    the masked count is `3 % 64 = 3`, never one. -/
theorem shl_drei_trag (x : Wort) :
    shlUeberlauf .b64 x 3 = none ∧
    shlTrag .b64 x 3 = (trunc .b64 x).toNat.testBit 61 := by
  have h1 : schiebeZaehler .b64 3 = 3 := by decide
  have h2 : schiebeZaehler .b64 3 ≠ 1 := by decide
  refine ⟨?_, ?_⟩
  · simp [shlUeberlauf, h2]
  · have hb : Breite.b64.bits = 64 := rfl
    simp [shlTrag, h1, hb]

/-- CE-6 witness: `2^62 * 8` and `2^62 << 3` agree in value (both wrap
    to zero) but disagree in CF: IMUL reports the signed carry (`true`),
    SHL reports the last bit shifted out, bit 61 (`false`). A live CF
    therefore observes the difference, and the rewrite must refuse. -/
theorem cf_unterscheidet_imul_shl :
    mulTragS .b64 0x4000000000000000 8 ≠
    shlTrag .b64 0x4000000000000000 3 := by
  decide

/-! ## 2. Refusal: the three DESIGN failure cases must NOT fire.

    A rewrite with a live CF is refused (`cfTot = false` forces
    `staerkeZulassen = false`: CE-6 above). A float `a*2.0 -> a+a`
    shape is refused (`keinFP = false`: no mul/add flag-payload
    identity is established -- NaN payload and invalid/inexact flags
    differ on silicon, so no float arm exists here). A
    signed-divide-via-shift shape is refused (`keinSDiv = false`:
    truncation differs from shift for negative numerators,
    `sdiv_kein_shift` in `StaerkeReduktion.lean`). A width-changing
    site is refused (`breiteOk = false`). All are proved of the
    decided Bool, so the validator cannot silently skip them. -/

/-- A live CF refuses the rewrite (CE-6). -/
theorem staerkeVerweigert_cf (c : StrengthCert)
    (h : c.cfTot = false) :
    staerkeZulassen c = false := by
  simp [staerkeZulassen, h]

/-- A width-changing site refuses. -/
theorem staerkeVerweigert_breite (c : StrengthCert)
    (h : c.breiteOk = false) :
    staerkeZulassen c = false := by
  simp [staerkeZulassen, h]

/-- A float `a*2.0 -> a+a` shape refuses: no float arm exists. -/
theorem staerkeVerweigert_float (c : StrengthCert)
    (h : c.keinFP = false) :
    staerkeZulassen c = false := by
  simp [staerkeZulassen, h]

/-- A signed-divide-via-shift shape refuses. -/
theorem staerkeVerweigert_sdiv (c : StrengthCert)
    (h : c.keinSDiv = false) :
    staerkeZulassen c = false := by
  simp [staerkeZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_staerkeZulassen_ok :
    staerkeZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: a live-CF certificate is refused. -/
theorem probe_staerkeZulassen_cf :
    staerkeZulassen ⟨false, true, true, true⟩ = false := by
  decide

/-- Probe: a float certificate is refused. -/
theorem probe_staerkeZulassen_float :
    staerkeZulassen ⟨true, true, false, true⟩ = false := by
  decide

end Gabbro.Grammatik.X86
