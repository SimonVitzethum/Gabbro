/-
  File:      Grammatik/X86/OptShiftSel.lean
  Subject:   Shift selection rule: imm/CL forms with per-width count masking (lane 887).

  DESIGN section 7 row (strength reduction / flags-aware peepholes, phase L):
  local premise "per-width flag/fault identity (CF vs OF distinct), count below
  width, masked-count agreement", certificate "A register rule + recomputed
  avail/liveness", failure "select with live CF/OF; count at/above width;
  disagreeing masked counts". Checked-arithmetic stop points are preserved
  exactly: the checked premises (hw1 hw2 h0 h0') are forwarded unchanged and
  the outcome (including stop classes) is equal. No ensures derived, no
  refusal weakened, no faulting form speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Ganzzahl

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Validator-decided side conditions for one shift-selection site
    (DESIGN section 7 row): the width matches the lowered form
    (`breiteOk`, recomputed from the lowering map), the masked counts
    agree (`zaehlerGleich`, recomputed from `schiebeZaehler`, never
    trusted), no flag survivor crosses the site (`flaggenTot`,
    recomputed liveness: CF/OF identity or dead), and no checked stop
    is widened or hoisted (`keinePruefung`: count below width, divisor
    checks untouched, IDIV/DIV never speculated). -/
structure ShiftSelCert where
  breiteOk : Bool
  zaehlerGleich : Bool
  flaggenTot : Bool
  keinePruefung : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def shiftSelZulassen (c : ShiftSelCert) : Bool :=
  c.breiteOk && c.zaehlerGleich && c.flaggenTot && c.keinePruefung

/-! ## 1. Refusal: the DESIGN failure cases must NOT select.

    A selection whose masked counts disagree (imm byte vs CL value with
    different `schiebeZaehler` images) is refused; a selection with a live
    flag survivor (CF/OF read downstream: the `imul r,8 -> shl r,3` shape
    with live CF, DESIGN CE-4) is refused; a width-mismatched selection
    (a 32-bit value into a 64-bit shift without extension) is refused; a
    selection that widens or hoists a checked stop (count at/above the
    width, a shift above its count-range guard, any IDIV/DIV motion) is
    refused. All are proved of the decided Bool, so the validator cannot
    silently skip them. -/

/-- Disagreeing masked counts refuse the selection. -/
theorem shiftSelVerweigert_zaehler (c : ShiftSelCert)
    (h : c.zaehlerGleich = false) :
    shiftSelZulassen c = false := by
  simp [shiftSelZulassen, h]

/-- A live flag survivor refuses the selection. -/
theorem shiftSelVerweigert_flaggen (c : ShiftSelCert)
    (h : c.flaggenTot = false) :
    shiftSelZulassen c = false := by
  simp [shiftSelZulassen, h]

/-- A width mismatch refuses the selection. -/
theorem shiftSelVerweigert_breite (c : ShiftSelCert)
    (h : c.breiteOk = false) :
    shiftSelZulassen c = false := by
  simp [shiftSelZulassen, h]

/-- A widened or hoisted checked stop refuses the selection. -/
theorem shiftSelVerweigert_pruefung (c : ShiftSelCert)
    (h : c.keinePruefung = false) :
    shiftSelZulassen c = false := by
  simp [shiftSelZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_shiftSelZulassen_ok :
    shiftSelZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: a count-disagreeing certificate is refused. -/
theorem probe_shiftSelZulassen_zaehler :
    shiftSelZulassen ⟨true, false, true, true⟩ = false := by
  decide

/-- Probe: a flag-live certificate is refused. -/
theorem probe_shiftSelZulassen_flaggen :
    shiftSelZulassen ⟨true, true, false, true⟩ = false := by
  decide

/-! ## 2. Per-width count masking: the generic selection rule.

    Hardware masks the count (five bits below 64 bits, six bits at
    64 bits: the reused `schiebeZaehler` of `Ganzzahl.lean`). The rule is
    generic over ARBITRARY words and counts: where the validator
    recomputed masked-count agreement (`h`, the decided form of
    `zaehlerGleich`), the imm form and the CL form compute the same value
    for `shl`/`shr`/`sar`. No new implementation: the values are the
    reused canonical operations, so midpoint disagreement is impossible. -/

/-- Same masked count, same left-shift value (imm vs CL). -/
theorem shiftSel_shl (b : Breite) (x : Wort) (cImm cCl : Nat)
    (h : schiebeZaehler b cImm = schiebeZaehler b cCl) :
    shlB b x cImm = shlB b x cCl := by
  unfold shlB
  rw [h]

/-- Same masked count, same logical right-shift value. -/
theorem shiftSel_shr (b : Breite) (x : Wort) (cImm cCl : Nat)
    (h : schiebeZaehler b cImm = schiebeZaehler b cCl) :
    shrB b x cImm = shrB b x cCl := by
  unfold shrB
  rw [h]

/-- Same masked count, same arithmetic right-shift value. -/
theorem shiftSel_sar (b : Breite) (x : Wort) (cImm cCl : Nat)
    (h : schiebeZaehler b cImm = schiebeZaehler b cCl) :
    sarB b x cImm = sarB b x cCl := by
  unfold sarB
  rw [h]

/-- Pin: imm 65 masks to 1 at 64 bits, and the value follows. -/
theorem probe_shiftSel_65 :
    schiebeZaehler .b64 65 = schiebeZaehler .b64 1 ∧ shlB .b64 1 65 = 2 := by
  decide

/-- Pin: imm 33 masks to 1 at 32 bits, and the value follows. -/
theorem probe_shiftSel_33_schmal :
    schiebeZaehler .b32 33 = schiebeZaehler .b32 1 ∧ shrB .b32 8 33 = 4 := by
  decide

/-- Pin: a zero count keeps the value. -/
theorem probe_shiftSel_null :
    shlB .b64 7 0 = 7 ∧ shrB .b64 7 0 = 7 ∧ sarB .b64 7 0 = 7 := by
  decide

/-! ## 3. Source values: the checked premises travel unchanged.

    Source `shl`/`shr` carry their checked-arithmetic side conditions in
    the syntax itself (`hw1`: the operand fits the width, `hw2`: the count
    range lies below the width so `0 << 40` is inexpressible, `h0 h0'`:
    nonnegativity `M137`). The selection forwards every one of them
    unchanged to both spellings, so no checked stop is added, removed or
    widened, and no `div`/`rem`/`sdiv` stop (`M102`) is touched: the value
    on each side is `Zahl.shl`/`Zahl.shr` on the same checked foundations,
    depending only on the two numbers. -/

/-- Source `shl` value depends only on the two numbers. -/
theorem shiftQuelle_shl_wert (w : Nat) (l1 h1 l2 h2 : Int)
    (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (a : Zahl l1 h1) (b : Zahl l2 h2) :
    (Zahl.shl w hw1 hw2 h0 h0' a b).n = a.n * 2 ^ b.n.toNat := by
  rfl

/-- Source `shr` value depends only on the two numbers. -/
theorem shiftQuelle_shr_wert (w : Nat) (l1 h1 l2 h2 : Int)
    (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (a : Zahl l1 h1) (b : Zahl l2 h2) :
    (Zahl.shr w hw1 hw2 h0 h0' a b).n = a.n / 2 ^ b.n.toNat := by
  rfl

/-! ## 4. Connection: the selected shift behaves like the written one.

    The rewrite replaces the count spelling `e1` by `e2` under a `bind`
    with an ARBITRARY continuation `rest`, so the conclusion covers every
    downstream observation at once. Premises, all validator-decided and
    all used:
    - `hz`: the site is admitted (`shiftSelZulassen`);
    - `hEq`: the count-equality obligation, conditional on admission (the
      recomputed analysis citation: avail/dominance plus the masked-count
      agreement of section 2 at the lowered site);
    - `hOrte`: both spellings read the same carriers, so the `lese`
      worlds agree and no observation (trace event, concurrent footprint)
      differs.
    Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved;
    (2) the `execEnd` OUTCOME is equal -- same constructor, same successor
    worlds and environments -- so no fault is added or removed (`logik` /
    `hardware` stop classes agree: checked-arithmetic stops preserved
    exactly), every downstream observation agrees (contracts at their
    place read the same values from the same environments, call logs gain
    no event -- `Expr` carries no calls and `rest` is shared, no shared
    access is added or removed for concurrency), the bound type is an
    `int` so no float value is folded (IEEE untouched), and the
    step-budget accounting is unchanged (same block shape, the replaced
    count is pure and unbudgeted).
    Nothing here derives an `ensures`, turns a refusal into a warning, or
    speculates a faulting form above its guard. -/

/-- Count congruence for source `shl`: equal count values give equal
    shifts. Proved by cases on the three numbers (never a rewrite into
    the dependent range proofs), so the checked premises visibly travel
    unchanged into both spellings. -/
theorem zahlShl_kongr (w : Nat) (l1 h1 l2 h2 : Int)
    (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (x : Zahl l1 h1) (y1 y2 : Zahl l2 h2)
    (h : y1.n = y2.n) :
    Zahl.shl w hw1 hw2 h0 h0' x y1
    = Zahl.shl w hw1 hw2 h0 h0' x y2 := by
  obtain ⟨xn, _, _⟩ := x
  obtain ⟨yn1, _, _⟩ := y1
  obtain ⟨yn2, _, _⟩ := y2
  change yn1 = yn2 at h
  subst h
  rfl

/-- CONNECTION: selecting the count spelling under a bind preserves
    value and outcome. -/
theorem OptShiftSel_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool} {l1 h1 l2 h2 : Int}
    (w : Nat)
    (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (a : Expr D Γ Λ (.int l1 h1))
    (e1 e2 : Expr D Γ Λ (.int l2 h2))
    (rest : Endblock D V l ((.int 0 (h1 * 2 ^ h2.toNat)) :: Γ) Λ)
    (cert : ShiftSelCert)
    (hz : shiftSelZulassen cert = true)
    (hEq : shiftSelZulassen cert = true →
      ∀ (σ₀ σ : World D) (ρ : Env D Γ),
        (eval σ₀ e1 σ ρ).n = (eval σ₀ e2 σ ρ).n)
    (hOrte : e1.orte = e2.orte)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (.shl w hw1 hw2 h0 h0' a e1) σ ρ).n
      = (eval σ₀ (.shl w hw1 hw2 h0 h0' a e2) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (.shl w hw1 hw2 h0 h0' a e1) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.shl w hw1 hw2 h0 h0' a e2) rest) σ ρ := by
  have heq := hEq hz
  have hzahl : ∀ (s₀ s : World D) (r : Env D Γ),
      Zahl.shl w hw1 hw2 h0 h0' (eval s₀ a s r) (eval s₀ e1 s r)
      = Zahl.shl w hw1 hw2 h0 h0' (eval s₀ a s r) (eval s₀ e2 s r) := by
    intro s₀ s r
    exact zahlShl_kongr w l1 h1 l2 h2 hw1 hw2 h0 h0' _ _ _ (heq s₀ s r)
  refine ⟨?_, ?_⟩
  · show (Zahl.shl w hw1 hw2 h0 h0' (eval σ₀ a σ ρ) (eval σ₀ e1 σ ρ)).n
       = (Zahl.shl w hw1 hw2 h0 h0' (eval σ₀ a σ ρ) (eval σ₀ e2 σ ρ)).n
    exact congrArg Zahl.n (hzahl σ₀ σ ρ)
  · have horte : (Expr.shl w hw1 hw2 h0 h0' a e1).orte
        = (Expr.shl w hw1 hw2 h0 h0' a e2).orte := by
      show a.orte ++ e1.orte = a.orte ++ e2.orte
      rw [hOrte]
    have hval : ∀ (s : World D),
        eval s (Expr.shl w hw1 hw2 h0 h0' a e1) s ρ
        = eval s (Expr.shl w hw1 hw2 h0 h0' a e2) s ρ := by
      intro s
      show Zahl.shl w hw1 hw2 h0 h0' (eval s a s ρ) (eval s e1 s ρ)
         = Zahl.shl w hw1 hw2 h0 h0' (eval s a s ρ) (eval s e2 s ρ)
      exact hzahl s s ρ
    simp only [execEnd, horte]
    have hv := hval (σ.lese Λ (Expr.shl w hw1 hw2 h0 h0' a e2).orte)
    rw [hv]

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptShiftSel_verbindung` instantiated JOINTLY:
    `3 << (1 + 1)` selects the `3 << 2` spelling (the imm/CL choice at
    the lowered site: both counts evaluate to `2` with no read footprint)
    under a `bind` with a `leave` continuation, in the NON-DEGENERATE
    reference program `refD` (whose `einzahlen` writes its table,
    `refEin_schreibt`), beside the reached F-machine run `MB` that changes
    memory (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`). -/

/-- JOINT WITNESS for `OptShiftSel_verbindung`: `3 << (1 + 1)` selects
    `3 << 2` on `refD`, beside the memory-changing reached run. -/
theorem OptShiftSel_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool) (l1 h1 l2 h2 : Int)
      (w : Nat)
      (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
      (a : Expr refD Γ Λ (.int l1 h1))
      (e1 e2 : Expr refD Γ Λ (.int l2 h2))
      (rest : Endblock refD V l ((.int 0 (h1 * 2 ^ h2.toNat)) :: Γ) Λ)
      (cert : ShiftSelCert)
      (_hz : shiftSelZulassen cert = true)
      (_hEq : shiftSelZulassen cert = true →
        ∀ (σ₀ σ : World refD) (ρ : Env refD Γ),
          (eval σ₀ e1 σ ρ).n = (eval σ₀ e2 σ ρ).n)
      (_hOrte : e1.orte = e2.orte)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (Expr.shl w hw1 hw2 h0 h0' a e1) σ ρ).n
        = (eval σ₀ (Expr.shl w hw1 hw2 h0 h0' a e2) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (Expr.shl w hw1 hw2 h0 h0' a e1) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (Expr.shl w hw1 hw2 h0 h0' a e2) rest) σ ρ
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptShiftSel_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (l1 := 3) (h1 := 3) (l2 := 2) (h2 := 2) (w := 8)
    (hw1 := by decide) (hw2 := by decide) (h0 := by decide) (h0' := by decide)
    (a := Expr.lit 3) (e1 := Expr.lit 2)
    (e2 := Expr.add (Expr.lit 1) (Expr.lit 1))
    (rest := Endblock.leave rfl)
    (cert := ⟨true, true, true, true⟩) (hz := by decide)
    (hEq := fun _ _ _ _ => rfl) (hOrte := rfl)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true,
    3, 3, 2, 2, 8,
    by decide, by decide, by decide, by decide,
    Expr.lit 3, Expr.lit 2, Expr.add (Expr.lit 1) (Expr.lit 1),
    Endblock.leave rfl, ⟨true, true, true, true⟩, by decide,
    (fun _ _ _ _ => rfl), rfl,
    refSp0.welt [], refSp0.welt [], Env.nil,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    Proved here: the validator-decided admission Bool (`shiftSelZulassen`)
    with its four DESIGN refusals (disagreeing masked counts, live flag
    survivor, width mismatch, widened/hoisted checked stop); the generic
    per-width selection rule over arbitrary words and counts
    (`shiftSel_shl/shr/sar`: masked-count agreement gives equal values
    through the reused canonical operations, with 64/32-bit pins and a
    zero-count pin); the source value shape (`shiftQuelle_shl/shr_wert`:
    checked premises forwarded unchanged); the count congruence
    (`zahlShl_kongr`); and the `bind`-window CONNECTION
    (`OptShiftSel_verbindung`: value plus full `execEnd` outcome equality,
    hence identical stop classes, contracts at their place, call logs,
    footprints, IEEE non-interference and budget accounting) with its
    JOINT witness on `refD` beside the memory-changing reached run.
    NOT proved here, and not claimed:
    - No byte codec or decoder claim: which bytes encode imm/CL shifts is
      `ShiftCodec.lean` business; this file selects between count
      spellings with agreed masked counts and never decodes a byte.
    - No lowering-side flag-identity proof: `flaggenTot` is
      validator-recomputed admission; the evidence it cites is the reused
      `SchiebeGueltig` of `ShiftLogic.lean`, not re-proved here.
    - No layer-B/C certificate binding: `hEq`/`hOrte` name the recomputed
      analysis obligations per site; the block map and duty binding stay
      with the lowering lane.
    - No `shr`/`sar` syntax connection: their VALUES select
      (section 2); only `shl` gets the `Endblock` connection here.
    - No cost transfer beyond shape equality: the same block shape keeps
      source-budget accounting unchanged; the formal level-(c)
      machine-work bound is OPEN per IR-VALIDIERUNG (lane 278).
    - No TSO/GX bridge beyond footprint equality: same `orte` gives the
      same read events; per-access refinement stays OPEN.
    - No silicon correspondence: masking is stated executable semantics
      from `Ganzzahl.lean`, not verified against hardware.
-/

#print axioms shiftSelZulassen
#print axioms shiftSelVerweigert_zaehler
#print axioms shiftSelVerweigert_flaggen
#print axioms shiftSelVerweigert_breite
#print axioms shiftSelVerweigert_pruefung
#print axioms shiftSel_shl
#print axioms shiftSel_shr
#print axioms shiftSel_sar
#print axioms shiftQuelle_shl_wert
#print axioms shiftQuelle_shr_wert
#print axioms zahlShl_kongr
#print axioms OptShiftSel_verbindung
#print axioms OptShiftSel_verbindung_zeuge

end Gabbro.Grammatik.X86
