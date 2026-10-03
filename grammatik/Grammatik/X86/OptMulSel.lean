/-
  File:      Grammatik/X86/OptMulSel.lean
  Subject:   Multiply selection rule: 3-operand IMUL for constant multiplies.

  Lane 888: the DESIGN §3A tile "3-operand `IMUL r, r/m, imm8/imm32` for
  constant multiplies with a proved range (strength reduction cites the §3
  row, never a bare pattern)" as a generic rule lemma over arbitrary values
  with validator-decided side conditions (DESIGN §7 strength-reduction row:
  local premise "per-width flag/fault identity lemma (CF vs OF distinct)",
  certificate "A register rule", failure "imul r,8 -> shl r,3 with live CF").
  Reuses the canonical vocabulary (`Typen`, `Syntax`, `Semantik`,
  `ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.Ganzzahl`, `StaerkeReduktion`,
  `MulDiv`); the single accepted IR is not available, so the connection is
  stated over the real `Syntax`/`Semantik` `execEnd` fragment it covers.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Ganzzahl
import Grammatik.X86.StaerkeReduktion
import Grammatik.X86.MulDiv

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one constant-multiply site
    (DESIGN §7 row): the proved range is present at the site (`breiteOk`),
    the constant fits the imm8/imm32 encoding (`immPasst`), the
    per-width flag/fault identity is discharged (`flagsOk`: dead flags or
    the CF-vs-OF row cited), and the site is an integer multiply, never a
    float one (`keinGleit`: `a*2.0 -> a+a` is refused). -/
structure MulSelCert where
  breiteOk : Bool
  immPasst : Bool
  flagsOk : Bool
  keinGleit : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL selection
    keeps another certified translation, never a warning. -/
def mulSelZulassen (c : MulSelCert) : Bool :=
  c.breiteOk && c.immPasst && c.flagsOk && c.keinGleit

/-! ## 1. Refusal: the DESIGN failure cases must NOT select.

    Each refusal is proved of the decided Bool, so the validator cannot
    silently skip it: an unproved range (`breiteOk = false`: never a
    "range hope"), a constant outside the imm8/imm32 encoding
    (`immPasst = false`), an undischarged flag/fault identity
    (`flagsOk = false`: the CE-6 `imul r,8 -> shl r,3` with live CF shape
    keeps IMUL, never the shift), and a float multiply (`keinGleit =
    false`: `a*2.0 -> a+a` rounding/NaN). -/

/-- A missing proved range refuses the selection. -/
theorem mulSelVerweigert_bereich (c : MulSelCert)
    (h : c.breiteOk = false) :
    mulSelZulassen c = false := by
  simp [mulSelZulassen, h]

/-- A constant outside imm8/imm32 refuses the selection. -/
theorem mulSelVerweigert_imm (c : MulSelCert)
    (h : c.immPasst = false) :
    mulSelZulassen c = false := by
  simp [mulSelZulassen, h]

/-- An undischarged flag/fault identity refuses the selection. -/
theorem mulSelVerweigert_flags (c : MulSelCert)
    (h : c.flagsOk = false) :
    mulSelZulassen c = false := by
  simp [mulSelZulassen, h]

/-- A float multiply refuses the selection (IEEE: rounding/NaN). -/
theorem mulSelVerweigert_gleit (c : MulSelCert)
    (h : c.keinGleit = false) :
    mulSelZulassen c = false := by
  simp [mulSelZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_mulSelZulassen_ok :
    mulSelZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: a range-hope certificate is refused. -/
theorem probe_mulSelZulassen_bereich :
    mulSelZulassen ⟨false, true, true, true⟩ = false := by
  decide

/-- Probe: an imm-misfit certificate is refused. -/
theorem probe_mulSelZulassen_imm :
    mulSelZulassen ⟨true, false, true, true⟩ = false := by
  decide

/-- Probe: a float-tainted certificate is refused. -/
theorem probe_mulSelZulassen_gleit :
    mulSelZulassen ⟨true, true, true, false⟩ = false := by
  decide

/-! ## 2. The selected target form and its per-width overflow row.

    The pilot `Befehl` has no multiply form, so like `MulDivBefehl` this
    structure exposes exactly how the selection grows the target: a
    3-operand `IMUL r, r/m, imm` (`dst := src * imm`, register-direct).
    Encoding and wiring stay with the codec lane; value and flags here
    reuse the accepted `Ganzzahl`/`MulDiv` vocabulary (DESIGN §3 row:
    "overflow (CF/OF) + signedness per width"). -/

/-- The selected 3-operand IMUL: `dst := src * imm`. -/
structure Imul3 where
  dst : Register
  src : Register
  imm : Int
  deriving DecidableEq, Repr

/-- The value the selected form computes: the truncated word product. -/
def imul3Wert (a k : Wort) : Wort := mulLow .b64 a k

/-- Full width: the selected value is the plain machine product. -/
theorem imul3Wert_b64 (a k : Wort) : imul3Wert a k = a * k := by
  simp [imul3Wert, mulLow_b64]

/-- The selected signed flag snapshot satisfies the signed validity row. -/
theorem imul3Flags_gueltig (f : Flags) (a k : Wort) :
    MulGueltigS .b64 a k (mulFlagsS f a k) :=
  mulFlagsS_gueltig f a k

/-- The per-width overflow row, cited not restated: where the unsigned
    high half vanishes, the unsigned carry is clear. -/
theorem imul3Traegerfrei (a k : Wort)
    (h : mulHighU .b64 a k = 0) :
    mulTragU .b64 a k = false := by
  simp [mulTragU, h]

/-- Probe: `6 * 7` selects value `42` with a zero high half. -/
theorem probe_imul3Wert : imul3Wert 6 7 = 42 ∧ mulHighU .b64 6 7 = 0 := by
  decide

/-- Probe: no carry on `6 * 7`. -/
theorem probe_imul3Traeger : mulTragU .b64 6 7 = false := by
  decide

/-- Probe: signedness per width (`-1 * -1 = +1` at 8 bits: unsigned
    carry set, signed carry clear -- the reason CF and OF need distinct
    rows in the §7 premise). -/
theorem probe_mulTragVorzeichen :
    mulTragU .b8 0xFF 0xFF = true ∧ mulTragS .b8 0xFF 0xFF = false := by
  decide

/-! ## 3. Source value, width-exact read-back, shift agreement.

    Over ARBITRARY values (`x k : Int`): the constant multiply computes
    the product (the "operands literal" premise is carried by the
    rewrite, which fires only on `.lit` operands); under the proved
    range `hW` the product reads back whole through the canonical word
    (no truncation, no wrap -- the later lowering writes the selected
    constant form, not a wrapped one); where the constant is a power of
    two the shift agrees under checked nonoverflow (citing the accepted
    `shlW_keinUeberlauf`, never a bare pattern). -/

/-- `x * k` folds to `x * k`: the value is preserved. -/
theorem mulKonst_wert (x k : Int) :
    (Zahl.mul (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨k, Int.le_refl k, Int.le_refl k⟩ : Zahl k k)).n = x * k := by
  rfl

/-- The proved-range product reads back whole through the canonical word. -/
theorem mulWort_liest (x k : Int) (hW : 0 ≤ x * k ∧ x * k < 2 ^ 64) :
    ((BitVec.ofNat 64 (x * k).toNat : Wort)).toNat = (x * k).toNat := by
  have h : (x * k).toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Where the constant is a power of two, the shift agrees with the
    product under checked nonoverflow (the §3 row cited via the accepted
    strength-reduction lemma). -/
theorem mulShift_stimmt (w : Wort) (n : Nat)
    (h : w.toNat * 2 ^ n < 2 ^ 64) :
    (shlW w n).toNat = w.toNat * 2 ^ n :=
  shlW_keinUeberlauf w n h

/-- Probe: `6 * 7` is `42`. -/
theorem probe_mulKonst : (Zahl.mul (⟨6, by decide, by decide⟩ : Zahl 6 6)
    (⟨7, by decide, by decide⟩ : Zahl 7 7)).n = 42 := by
  decide

/-- Probe: `42` reads back as `42` through the word. -/
theorem probe_mulWort :
    ((BitVec.ofNat 64 ((6 : Int) * 7).toNat : Wort)).toNat = 42 := by
  decide

/-- Probe: `6 << 3` is `48` on real words. -/
theorem probe_mulShift : (shlW 6 3).toNat = 48 := by
  decide

/-! ## 4. Proved range: the four-corner range collapses on literals.

    The source `mul` carries the four-corner `imin`/`imax` range. For
    literal operands both corners ARE the product (each `if` has the
    same value on both branches), so the validator's range proof at the
    site is this collapse -- never a "range hope". The collapse feeds
    the `weiter` widening in the connection below. -/

/-- One collapsed corner: `imin a a = a`. -/
theorem imin_selbst (a : Int) : imin a a = a := by
  unfold imin
  split <;> rfl

/-- One collapsed corner: `imax a a = a`. -/
theorem imax_selbst (a : Int) : imax a a = a := by
  unfold imax
  split <;> rfl

/-- The lower four-corner range of `x * k` collapses to the product. -/
theorem vierEcken_unten (x k : Int) :
    imin (imin (x * k) (x * k)) (imin (x * k) (x * k)) = x * k := by
  rw [imin_selbst, imin_selbst]

/-- The upper four-corner range of `x * k` collapses to the product. -/
theorem vierEcken_oben (x k : Int) :
    imax (imax (x * k) (x * k)) (imax (x * k) (x * k)) = x * k := by
  rw [imax_selbst, imax_selbst]

/-- Range evidence below: the product fits under its collapsed corner. -/
theorem vierEcken_weiter_unten (x k : Int) :
    x * k ≤ imin (imin (x * k) (x * k)) (imin (x * k) (x * k)) := by
  simp [vierEcken_unten x k]

/-- Range evidence above: the collapsed corner fits under the product. -/
theorem vierEcken_weiter_oben (x k : Int) :
    imax (imax (x * k) (x * k)) (imax (x * k) (x * k)) ≤ x * k := by
  simp [vierEcken_oben x k]

/-! ## 5. Connection: the selected multiply behaves like the source one.

    The rewrite fires only on `.lit` operands with a proved range
    (`hW`, section 3, via the §4 collapse as the `weiter` evidence); it
    is stated at an `Endblock.bind` window with an ARBITRARY
    continuation `rest`, so the conclusion covers every downstream
    observation at once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved (`x * k` on both sides);
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (multiply is total: divisor-zero and quotient-overflow
    traps do not exist here, and none is speculated above a guard),
    every downstream observation agrees (contracts at their place read
    the same values from the same environments, call logs gain no
    event, no shared access is added or removed for concurrency --
    both sides read `orte = []`), and the step-budget accounting is
    unchanged (same block shape, the selected form is pure and
    unbudgeted);
    (3) the proved-range product reads back whole through the canonical
    word (the 3-operand IMUL writes the value, not a wrapped one;
    CF/OF follow the §2 per-width row at the selected site).
    IEEE is preserved by refusal: no float multiply is ever selected
    (§1 `keinGleit`), so `a*2.0 -> a+a` rounding/NaN is untouched.
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard. -/

/-- CONNECTION: selecting 3-operand IMUL for `x * k` preserves value,
    outcome and the width-exact word image. -/
theorem OptMulSel_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (x k : Int)
    (rest : Endblock D V l ((.int (x * k) (x * k)) :: Γ) Λ)
    (hW : 0 ≤ x * k ∧ x * k < 2 ^ 64)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (.lit (x * k) : Expr D Γ Λ (.int (x * k) (x * k))) σ ρ).n
      = (eval σ₀ (.mul (.lit x) (.lit k) : Expr D Γ Λ
          (.int (imin (imin (x * k) (x * k)) (imin (x * k) (x * k)))
            (imax (imax (x * k) (x * k)) (imax (x * k) (x * k))))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (.lit (x * k) : Expr D Γ Λ (.int (x * k) (x * k))) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.weiter (vierEcken_weiter_unten x k)
          (vierEcken_weiter_oben x k) (.mul (.lit x) (.lit k))) rest) σ ρ
    ∧ ((BitVec.ofNat 64 (x * k).toNat : Wort)).toNat = (x * k).toNat := by
  exact ⟨rfl, rfl, mulWort_liest x k hW⟩

/-! ## 6. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptMulSel_verbindung` instantiated JOINTLY:
    `6 * 7` selects to `42` under a `bind` with a `leave` continuation,
    in the NON-DEGENERATE reference program `refD` (whose `einzahlen`
    writes its table, `refEin_schreibt`), beside the reached F-machine
    run `MB` that changes memory (`refB_erreicht`, `refB_schreibt`:
    slot `0 -> 100`). All conjunct groups are used. -/

/-- JOINT WITNESS for `OptMulSel_verbindung`: `6 * 7` selects to `42`
    on `refD`, beside the memory-changing reached run. -/
theorem OptMulSel_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (x k : Int)
      (rest : Endblock refD V l ((.int (x * k) (x * k)) :: Γ) Λ)
      (_hW : 0 ≤ x * k ∧ x * k < 2 ^ 64)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (.lit (x * k) : Expr refD Γ Λ (.int (x * k) (x * k))) σ ρ).n
        = (eval σ₀ (.mul (.lit x) (.lit k) : Expr refD Γ Λ
            (.int (imin (imin (x * k) (x * k)) (imin (x * k) (x * k)))
              (imax (imax (x * k) (x * k)) (imax (x * k) (x * k))))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (.lit (x * k) : Expr refD Γ Λ (.int (x * k) (x * k))) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (.weiter (vierEcken_weiter_unten x k)
            (vierEcken_weiter_oben x k) (.mul (.lit x) (.lit k))) rest) σ ρ
      ∧ ((BitVec.ofNat 64 (x * k).toNat : Wort)).toNat = (x * k).toNat
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptMulSel_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (x := 6) (k := 7) (rest := Endblock.leave rfl) (hW := by decide)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true, 6, 7,
    Endblock.leave rfl, by decide,
    refSp0.welt [], refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/-! ## 7. Selector and certificate shape.

    Late selection (phase L, DESIGN §7): the admitted site takes the
    3-operand IMUL; the shift alternative fires only with dead flags --
    the CE-6 refusal (`imul r,8 -> shl r,3` with live CF keeps IMUL,
    never the shift, since the value agrees but the flags diverge).
    The certificate is the local rewrite record (source site to selected
    `Imul3`) plus the recomputed analysis citations (the admitted
    `MulSelCert`; the per-width overflow row of §2 and the flag-liveness
    evidence it cites are re-decided by the validator, never trusted). -/

/-- Late selection at one admitted site: 3-operand IMUL. -/
def waehleImul3 (dst src : Register) (k : Int) (c : MulSelCert) : Option Imul3 :=
  if mulSelZulassen c then some ⟨dst, src, k⟩ else none

/-- The shift alternative: only with dead flags, else refused. -/
def waehleShift (dst : Register) (n : Nat) (flagsLive : Bool)
    (c : MulSelCert) : Option (Register × Nat) :=
  if mulSelZulassen c && !flagsLive then some (dst, n) else none

/-- The admitted site selects the 3-operand IMUL. -/
theorem waehleImul3_zugelassen (dst src : Register) (k : Int)
    (c : MulSelCert) (h : mulSelZulassen c = true) :
    waehleImul3 dst src k c = some ⟨dst, src, k⟩ := by
  simp [waehleImul3, h]

/-- The refused site selects nothing. -/
theorem waehleImul3_verweigert (dst src : Register) (k : Int)
    (c : MulSelCert) (h : mulSelZulassen c = false) :
    waehleImul3 dst src k c = none := by
  simp [waehleImul3, h]

/-- CE-6: with live flags the shift is refused -- the site keeps IMUL. -/
theorem waehleShift_verweigert_live (dst : Register) (n : Nat)
    (c : MulSelCert) (h : flagsLive = true) :
    waehleShift dst n flagsLive c = none := by
  simp [waehleShift, h]

/-- With dead flags at an admitted site the shift is available. -/
theorem waehleShift_erlaubt_tot (dst : Register) (n : Nat)
    (c : MulSelCert) (h : mulSelZulassen c = true) :
    waehleShift dst n false c = some (dst, n) := by
  simp [waehleShift, h]

/-- A refused certificate refuses the shift at any liveness. -/
theorem waehleShift_verweigert_zert (dst : Register) (n : Nat)
    (flagsLive : Bool) (c : MulSelCert)
    (h : mulSelZulassen c = false) :
    waehleShift dst n flagsLive c = none := by
  simp [waehleShift, h]

/-- The exact certificate shape: local rewrite record plus recomputed
    analysis citations. -/
structure MulSelZert where
  ziel : Imul3
  freigabe : MulSelCert
  deriving DecidableEq, Repr

/-- Certificate check: the cited admission re-decided. -/
def mulSelZertOk (z : MulSelZert) : Bool :=
  mulSelZulassen z.freigabe

/-- The check reads the cited admission. -/
theorem mulSelZertOk_heisst (z : MulSelZert) :
    mulSelZertOk z = mulSelZulassen z.freigabe := by
  rfl

/-- A refused citation refuses the certificate. -/
theorem mulSelZertOk_verweigert (z : MulSelZert)
    (h : mulSelZulassen z.freigabe = false) :
    mulSelZertOk z = false := by
  simp [mulSelZertOk, h]

/- CUTS:
    - No byte encoding or decoding: nothing here claims which bytes
      encode the 3-operand IMUL; Codec owns that, and wiring `Imul3`
      into `Befehl`/`schritt`/decoder/image stays OPEN. `Imul3.imm` is
      checked input data (the imm8/imm32 fit is the validator-decided
      `immPasst`, re-decided, never trusted).
    - No TSO/concurrency bridge beyond non-interference: all facts are
      sequential over one `eval`/`execEnd` window; both sides read
      `orte = []`, so no shared access exists to transfer. Aligned
      multi-byte atomicity, tearing and the GX refinement stay with the
      TSO lane.
    - No cost/budget transfer beyond shape preservation: the selected
      window is the same block shape with a pure computation, so
      step-budget accounting is unchanged; the formal level-(c)
      machine-work bound is OPEN per IR-VALIDIERUNG.
    - No `div`/`sdiv`/`srem` selection anywhere: only total `mul` is
      selected. Trapping operations are never pure and never selected
      above their guard.
    - No float selection anywhere: `keinGleit = false` refuses, so
      `a*2.0 -> a+a` rounding/NaN is untouched, not lowered.
    - No contract inference: the result RANGE of the selected form is
      the checker's `M104` business; only VALUES are proved equal, and
      no `ensures` is derived.
    - No silicon correspondence: the CF/OF rows, the truncation
      direction and the flag-validity relations are STATED executable
      semantics over the canonical vocabulary, not verified against
      hardware.
    - This file adds no new source-language construct or checker rule:
      no diagnostic, poison-probe, example or CLI numbers are taken.
-/

#print axioms mulSelZulassen
#print axioms mulSelVerweigert_bereich
#print axioms mulSelVerweigert_imm
#print axioms mulSelVerweigert_flags
#print axioms mulSelVerweigert_gleit
#print axioms imul3Wert_b64
#print axioms imul3Flags_gueltig
#print axioms imul3Traegerfrei
#print axioms probe_mulTragVorzeichen
#print axioms mulKonst_wert
#print axioms mulWort_liest
#print axioms mulShift_stimmt
#print axioms imin_selbst
#print axioms imax_selbst
#print axioms vierEcken_unten
#print axioms vierEcken_oben
#print axioms vierEcken_weiter_unten
#print axioms vierEcken_weiter_oben
#print axioms OptMulSel_verbindung
#print axioms OptMulSel_verbindung_zeuge
#print axioms waehleImul3_zugelassen
#print axioms waehleImul3_verweigert
#print axioms waehleShift_verweigert_live
#print axioms waehleShift_erlaubt_tot
#print axioms waehleShift_verweigert_zert
#print axioms mulSelZertOk_heisst
#print axioms mulSelZertOk_verweigert

end Gabbro.Grammatik.X86
