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

/-! ## 3. Value identity: `a * 8` is `a << 3`, over arbitrary values.

    The generic rule lemma reuses `mul_pow2_shl` (`StaerkeReduktion.lean`)
    at `k = 3`. Every premise is a source side condition, forwarded
    unchanged, so no check is weakened and no fault is added or removed
    (the factor `2^3` is never zero). The folded window below reads back
    whole through the canonical word under the checked nonoverflow `hW`
    (the machine-width check `shlW_keinUeberlauf` shape). -/

/-- `8` is `2^3`: the readable name of the rule's factor. -/
theorem acht_ist_zwei_hoch_drei : ((2 : Int) ^ 3) = 8 := by
  decide

/-- `a * 2^3` is `a << 3`: the generic value identity. -/
theorem mul_acht_shl_drei (w : Nat) (l1 h1 : Int)
    (hw1 : h1 < 2 ^ w) (hw2 : ((3 : Nat) : Int) < ((w : Nat) : Int))
    (h0 : 0 ≤ l1)
    (a : Zahl l1 h1) :
    (Zahl.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (⟨((3 : Nat) : Int), Int.le_refl _, Int.le_refl _⟩ : Zahl ((3 : Nat) : Int) ((3 : Nat) : Int))).n
      = (Zahl.mul a (⟨((2 : Int) ^ 3), Int.le_refl _, Int.le_refl _⟩ : Zahl ((2 : Int) ^ 3) ((2 : Int) ^ 3))).n := by
  exact mul_pow2_shl w 3 l1 h1 hw1 hw2 h0 a

/-- Probe: `5 * 8` is `40` through the source product. -/
theorem probe_mul_acht : (Zahl.mul (⟨5, by decide, by decide⟩ : Zahl 5 5)
    (⟨((2 : Int) ^ 3), by decide, by decide⟩ : Zahl ((2 : Int) ^ 3) ((2 : Int) ^ 3))).n = 40 := by
  decide

/-- The rewritten value reads back whole through the canonical word. -/
theorem staerkeWort_acht (n : Int) (hW : 0 ≤ n * 8 ∧ n * 8 < 2 ^ 64) :
    ((BitVec.ofNat 64 (n * 8).toNat : Wort)).toNat = (n * 8).toNat := by
  have h : (n * 8).toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Probe: `5 * 8` reads back as `40` through the word. -/
theorem probe_staerkeWort :
    ((BitVec.ofNat 64 (((5 : Int)) * 8).toNat : Wort)).toNat = 40 := by
  decide

/-! ## 4. Connection: `a * 8` under a bind behaves like `a << 3`.

    The rewrite fires only on the admitted integer shape (the DESIGN
    "operands literal, width exact" premise by construction: the factor
    is the literal `2^3`, the count the literal `3`, the width proofs
    `hw1`/`hw2`/`h0` are validator-decided premises forwarded unchanged,
    and the range evidence `pMulLo`/`pMulHi` widens the product window to
    the shift window's exact type), with an ARBITRARY continuation
    `rest`, so the conclusion covers every downstream observation at
    once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved (generic over arbitrary
    operand values via `mul_acht_shl_drei`);
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or removed
    (`logik`/`hardware` agree), every downstream observation agrees
    (contracts at their place read the same values from the same
    environments, call logs gain no event, no shared access is added or
    removed for concurrency -- both sides read `a.orte`, and the IEEE
    `gleitPasst` outcomes downstream agree since no `Block.gleit` is
    rewritten), and the step-budget accounting is unchanged (same block
    shape, the removed multiplication is pure and unbudgeted);
    (3) the rewritten value reads back whole through the canonical word
    under the checked nonoverflow `hW`;
    (4) admission implies the CF side condition held -- the rule CANNOT
    fire with a live CF (CE-6, section 1).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard (the factor `2^3` is
    never zero; `sdiv` and float shapes have no arm here). -/

/-- CONNECTION: `a * 8` under a bind preserves value, outcome, the
    width-exact word image, and fires only with a dead CF. -/
theorem OptStrengthRed_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (cert : StrengthCert) (hz : staerkeZulassen cert = true)
    (w : Nat) (l1 h1 : Int)
    (hw1 : h1 < 2 ^ w) (hw2 : ((3 : Nat) : Int) < ((w : Nat) : Int))
    (h0 : 0 ≤ l1)
    (a : Expr D Γ Λ (.int l1 h1))
    (pMulLo : 0 ≤ imin (imin (l1 * (2 : Int) ^ 3) (l1 * (2 : Int) ^ 3))
      (imin (h1 * (2 : Int) ^ 3) (h1 * (2 : Int) ^ 3)))
    (pMulHi : imax (imax (l1 * (2 : Int) ^ 3) (l1 * (2 : Int) ^ 3))
      (imax (h1 * (2 : Int) ^ 3) (h1 * (2 : Int) ^ 3)) ≤ h1 * 2 ^ (3 : Int).toNat)
    (rest : Endblock D V l ((.int 0 (h1 * 2 ^ (3 : Int).toNat)) :: Γ) Λ)
    (σ₀ σ : World D) (ρ : Env D Γ)
    (hW : 0 ≤ (eval σ₀ a σ ρ).n * 8 ∧ (eval σ₀ a σ ρ).n * 8 < 2 ^ 64) :
    (eval σ₀ (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))) σ ρ).n
      = (eval σ₀ (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))) rest) σ ρ
    ∧ ((BitVec.ofNat 64 ((eval σ₀ a σ ρ).n * 8).toNat : Wort)).toNat
        = ((eval σ₀ a σ ρ).n * 8).toNat
    ∧ cert.cfTot = true ∧ cert.breiteOk = true := by
  have hVal : ∀ (L1 L2 : World D),
      (eval L1 (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))) L2 ρ).n
        = (eval L1 (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))) L2 ρ).n :=
    fun L1 L2 => mul_acht_shl_drei w l1 h1 hw1 hw2 h0 (eval L1 a L2 ρ)
  have hort : (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))).orte
      = (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))).orte := rfl
  have hEq : ∀ (L : World D),
      eval L (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))) L ρ
        = eval L (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))) L ρ := by
    intro L
    have hn := hVal L L
    cases e1 : eval L (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))) L ρ with
    | mk n1 lo1 hi1 =>
      cases e2 : eval L (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))) L ρ with
      | mk n2 lo2 hi2 =>
        have hn2 : n1 = n2 := by rw [e1, e2] at hn; exact hn
        subst hn2
        rfl
  have hOut : execEnd O passes R
      (Endblock.bind (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))) rest) σ ρ
      = execEnd O passes R
      (Endblock.bind (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))) rest) σ ρ := by
    simp only [execEnd, hort, hEq]
  have hAdm : cert.cfTot = true ∧ cert.breiteOk = true := by
    simp only [staerkeZulassen, Bool.and_eq_true] at hz
    exact ⟨hz.1.1.1, hz.1.1.2⟩
  exact ⟨hVal σ₀ σ, hOut, staerkeWort_acht _ hW, hAdm.1, hAdm.2⟩

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptStrengthRed_verbindung` instantiated JOINTLY:
    `5 * 8` becomes `5 << 3` under a `bind` with a `leave`
    continuation, in the NON-DEGENERATE reference program `refD` (whose
    `einzahlen` writes its table, `refEin_schreibt`), beside the reached
    F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). Every conjunct is used. -/

/-- JOINT WITNESS for `OptStrengthRed_verbindung`: `5 * 8` becomes
    `5 << 3` on `refD`, beside the memory-changing reached run. -/
theorem OptStrengthRed_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (cert : StrengthCert) (_hz : staerkeZulassen cert = true)
      (w : Nat) (l1 h1 : Int)
      (hw1 : h1 < 2 ^ w) (hw2 : ((3 : Nat) : Int) < ((w : Nat) : Int))
      (h0 : 0 ≤ l1)
      (a : Expr refD Γ Λ (.int l1 h1))
      (pMulLo : 0 ≤ imin (imin (l1 * (2 : Int) ^ 3) (l1 * (2 : Int) ^ 3))
        (imin (h1 * (2 : Int) ^ 3) (h1 * (2 : Int) ^ 3)))
      (pMulHi : imax (imax (l1 * (2 : Int) ^ 3) (l1 * (2 : Int) ^ 3))
        (imax (h1 * (2 : Int) ^ 3) (h1 * (2 : Int) ^ 3)) ≤ h1 * 2 ^ (3 : Int).toNat)
      (rest : Endblock refD V l ((.int 0 (h1 * 2 ^ (3 : Int).toNat)) :: Γ) Λ)
      (σ₀ σ : World refD) (ρ : Env refD Γ)
      (_hW : 0 ≤ (eval σ₀ a σ ρ).n * 8 ∧ (eval σ₀ a σ ρ).n * 8 < 2 ^ 64),
      (eval σ₀ (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))) σ ρ).n
        = (eval σ₀ (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (Expr.weiter pMulLo pMulHi (Expr.mul a (Expr.lit ((2 : Int) ^ 3)))) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (Expr.shl w hw1 hw2 h0 (Int.natCast_nonneg 3) a (Expr.lit ((3 : Nat) : Int))) rest) σ ρ
      ∧ ((BitVec.ofNat 64 ((eval σ₀ a σ ρ).n * 8).toNat : Wort)).toNat
        = ((eval σ₀ a σ ρ).n * 8).toNat
      ∧ cert.cfTot = true ∧ cert.breiteOk = true
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptStrengthRed_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (cert := ⟨true, true, true, true⟩) (hz := by decide)
    (w := 6) (l1 := 5) (h1 := 5) (hw1 := by decide) (hw2 := by decide) (h0 := by decide)
    (a := (Expr.lit 5 : Expr refD [] [] (.int 5 5)))
    (pMulLo := by decide) (pMulHi := by decide)
    (rest := Endblock.leave rfl)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
    (hW := by decide)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true,
    ⟨true, true, true, true⟩, by decide,
    6, 5, 5, by decide, by decide, by decide,
    (Expr.lit 5 : Expr refD [] [] (.int 5 5)), by decide, by decide,
    Endblock.leave rfl,
    refSp0.welt [], refSp0.welt [], Env.nil, by decide,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2.1
  · exact hV.2.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No machine-byte claim: correspondence stops at source `eval` values,
      `execEnd` outcomes and canonical words. Encoding, decoding, RIP
      stepping, ELF loading and execution of emitted bytes stay with the
      validation lanes; `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` owns
      that transfer.
    - No `sdiv` and no float rewrite arm: both shapes are refused by name
      (`keinSDiv`/`keinFP`; truncation-vs-shift by `sdiv_kein_shift` in
      `StaerkeReduktion.lean`). The float `a*2.0 -> a+a` shape has no arm
      because no mul/add flag-payload identity is established here (NaN
      payload and invalid/inexact flags differ on silicon); IEEE
      preservation for the integer rule is downstream agreement through
      the `execEnd` equality, since no `Block.gleit` is rewritten.
    - No new target forms: the imul/shl flag evidence (`mulFlagsS`,
      `shlTrag`, `shlUeberlauf`, `SchiebeGueltig`) is REUSED from
      `Ganzzahl`/`ShiftLogic`/`MulDiv`; wiring new forms into `Befehl`,
      `schritt`, the decoder and the image stays with the Typen owner.
    - No per-access TSO/GX bridge, no ABI/loader claim, no contract
      inference: contracts hold at their place with the actual values,
      read from the same environments on both sides.
    - No machine-work inequality: both windows share one block shape, so
      step-budget accounting is unchanged at the source level; the formal
      machine-work transfer is phase work elsewhere, never re-summed here.
    - Never derives `ensures`; never turns a refusal into a warning; never
      speculates a faulting form above its guard (the factor `2^3` is
      proved nonzero by construction: the divisor can never be zero).
-/

#print axioms staerkeZulassen
#print axioms imul_cf_gleicht_of
#print axioms shl_drei_trag
#print axioms cf_unterscheidet_imul_shl
#print axioms staerkeVerweigert_cf
#print axioms staerkeVerweigert_breite
#print axioms staerkeVerweigert_float
#print axioms staerkeVerweigert_sdiv
#print axioms probe_staerkeZulassen_ok
#print axioms probe_staerkeZulassen_cf
#print axioms probe_staerkeZulassen_float
#print axioms acht_ist_zwei_hoch_drei
#print axioms mul_acht_shl_drei
#print axioms probe_mul_acht
#print axioms staerkeWort_acht
#print axioms probe_staerkeWort
#print axioms OptStrengthRed_verbindung
#print axioms OptStrengthRed_verbindung_zeuge

end Gabbro.Grammatik.X86
