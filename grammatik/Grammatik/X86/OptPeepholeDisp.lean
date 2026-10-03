/-
  File:      Grammatik/X86/OptPeepholeDisp.lean
  Subject:   Displacement peephole rule lemma (lane 877).

  DESIGN section 7 row "Flags-aware peepholes": local premise "rule in
  register, flag-liveness, disp-fits-i32, no token op in pure window",
  certificate "A", failure case "x-x drops invalid flag; FMA fusion of
  mul+add; UCOMI-to-ordered-compare NaN swap", phase L, cost O(windows).

  The rewrite narrows a displacement spelling (disp32 to disp8/disp0)
  where the validator recomputed that the displacement fits signed 32
  bits and the pure window holds no token op; flag liveness is
  re-decided at the site, and any UCOMI-to-ordered-compare NaN swap is
  refused. Work here is over the REUSED canonical vocabulary
  (`Typen`, `Syntax`, `Semantik`, `Gleitkomma`, `ReferenzB`,
  `X86.ScalarFloat` for the NaN row): no new semantics, no `ensures`
  derived, no refusal turned into a warning, no faulting form
  speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.Gleitkomma
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.ScalarFloat

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one displacement peephole
    site (DESIGN section 7 row): the recomputed displacement fits
    signed 32 bits, the pure window holds no token op, flag liveness is
    re-decided at the site, and no UCOMI-to-ordered-compare NaN swap
    is proposed. -/
structure DispCert where
  disp : Int
  passt : Bool
  keinToken : Bool
  flagOk : Bool
  keinNaNTausch : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation (the
    valid wider displacement spelling), never to a warning. -/
def dispPeepholeZulassen (c : DispCert) : Bool :=
  c.passt && c.keinToken && c.flagOk && c.keinNaNTausch

/-! ## 1. Refusal: the DESIGN failure cases must NOT narrow.

    A displacement that does not fit signed 32 bits refuses
    (`passt = false`); a token op inside the pure window refuses
    (`keinToken = false`: the window is pure address math only, so a
    memory, call, check, atomic or faulting-FP op inside it is never
    narrowed around); a live flag across the window refuses
    (`flagOk = false`: narrowing must not drop or re-decide a flag a
    later branch reads); and any UCOMI-to-ordered-compare NaN swap
    refuses (`keinNaNTausch = false`: section 4 shows the unordered
    row collapses both ordered directions to `false`). All four are
    proved of the decided Bool, so the validator cannot silently skip
    them; the fallback is the valid wider spelling, never a warning. -/

/-- A displacement that misses i32 refuses the narrowing. -/
theorem dispVerweigert_passt (c : DispCert)
    (h : c.passt = false) :
    dispPeepholeZulassen c = false := by
  simp [dispPeepholeZulassen, h]

/-- A token op in the pure window refuses the narrowing. -/
theorem dispVerweigert_token (c : DispCert)
    (h : c.keinToken = false) :
    dispPeepholeZulassen c = false := by
  simp [dispPeepholeZulassen, h]

/-- A live flag across the window refuses the narrowing. -/
theorem dispVerweigert_flag (c : DispCert)
    (h : c.flagOk = false) :
    dispPeepholeZulassen c = false := by
  simp [dispPeepholeZulassen, h]

/-- A UCOMI-to-ordered-compare NaN swap refuses the narrowing. -/
theorem dispVerweigert_nan (c : DispCert)
    (h : c.keinNaNTausch = false) :
    dispPeepholeZulassen c = false := by
  simp [dispPeepholeZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_dispZulassen_ok :
    dispPeepholeZulassen ⟨4, true, true, true, true⟩ = true := by
  decide

/-- Probe: a NaN-swap certificate is refused. -/
theorem probe_dispZulassen_nan :
    dispPeepholeZulassen ⟨4, true, true, true, false⟩ = false := by
  decide

/-! ## 2. disp-fits-i32: the validator-recomputed bound.

    The canonical displacement is a 32-bit sign-extended value
    (`dispWort` of `Ausfuehrung.lean`, reused through
    `EffectiveAddress.lean`): the narrow spelling reaches exactly the
    same address wherever the displacement lies in
    `-2147483648 .. 2147483647`. The validator recomputes the bound
    into `passt`; the three pins below fix the edges, and the generic
    lemma carries every disp8 displacement into i32, so a
    disp8-narrowed window is always admitted on the bound. -/

/-- The validator-recomputed bound: the displacement fits signed
    32 bits. -/
def dispPasstI32 (d : Int) : Bool :=
  decide (-2147483648 ≤ d ∧ d ≤ 2147483647)

/-- Pin: the largest forward displacement fits. -/
theorem dispPasst_maxPos : dispPasstI32 2147483647 = true := by
  decide

/-- Pin: the largest backward displacement fits. -/
theorem dispPasst_minNeg : dispPasstI32 (-2147483648) = true := by
  decide

/-- Pin: one past the largest forward displacement misses. -/
theorem dispPasst_drueber : dispPasstI32 2147483648 = false := by
  decide

/-- Every disp8 displacement fits i32 (both premises feed the bound:
    neither bound alone implies the conjunction). -/
theorem disp8_passt_i32 (d : Int) (h1 : -128 ≤ d) (h2 : d ≤ 127) :
    dispPasstI32 d = true := by
  unfold dispPasstI32
  simp only [decide_eq_true_eq]
  omega

/-- Admission carries the recomputed bound field: the validator cannot
    admit the site while recording a miss. -/
theorem dispZulassen_passt (c : DispCert)
    (hz : dispPeepholeZulassen c = true) :
    c.passt = true := by
  simp [dispPeepholeZulassen] at hz
  exact hz.1.1.1

/-! ## 3. Pure-window value preservation over arbitrary values.

    The narrowing rewrites only the displacement SPELLING: the
    effective address is `base + disp` before and after, over
    ARBITRARY integers (`base`, `d`). The "no token op" premise is
    carried by the certificate (`keinToken`, refused in section 1):
    the window is pure address math, so no memory event, no fault,
    no flag and no observation can differ between the spellings.
    The disp0 escape (`[base]` for `[base + 0]`) adds zero. -/

/-- The narrowed displacement names the recorded value: rewriting
    through the admitted record is the identity on arbitrary bases. -/
theorem dispAdresse_durchRecord (base : Int) (c : DispCert) (d : Int)
    (hDisp : c.disp = d) :
    base + c.disp = base + d := by
  rw [hDisp]

/-- The disp0 escape adds zero: `[base]` and `[base + 0]` agree on
    arbitrary bases. -/
theorem disp0_addiert_null (base : Int) :
    base + (0 : Int) = base := by
  omega

/-! ## 4. IEEE: the unordered row collapses both ordered directions.

    The DESIGN failure case "UCOMI-to-ordered-compare NaN swap":
    `ucomiFlags` on a NaN answers the unordered row (ZF, PF and CF
    set: `ucomiFlags_ungeordnet_links/rechts` of the accepted
    `X86.ScalarFloat`), while the ordered model comparisons answer
    `false` in BOTH directions (`flt_nan_links`, `flt_nan_rechts`).
    So a rewrite that replaces the unordered branch by an ordered
    compare, or swaps the operands and flips the condition, takes the
    wrong edge on NaN: it is refused by `keinNaNTausch`
    (`dispVerweigert_nan`). The admitted peephole itself touches no
    FP bit: its window is pure address math with no token op, and a
    faulting float op is token-threaded, hence excluded by `keinToken`. -/

/-- On a left NaN both ordered directions answer `false`: no ordered
    swap can reproduce the unordered row, so the swap must refuse. -/
theorem ucomiTausch_kollabiert (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    Gleitkomma.flt Gleitkomma.f64 a b = false ∧
      Gleitkomma.flt Gleitkomma.f64 b a = false :=
  ⟨flt_nan_links a b h, flt_nan_rechts b a h⟩

/-! ## 5. Connection: the narrowed window behaves like the wide one.

    Stated at an `Endblock.bind` window with an ARBITRARY
    continuation `rest`, so the conclusion covers every downstream
    observation at once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved (the narrow spelling
    names the same `base + disp` sum: section 3);
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree), every downstream observation
    agrees (contracts at their place read the same values from the
    same environments, call logs gain no event, no shared access is
    added or removed for concurrency -- both sides read `orte = []`),
    and the step-budget accounting is unchanged (same block shape;
    the removed encoding bytes are unbudgeted pure address math);
    (3) the validator admission carries the recomputed i32 bound
    (`dispZulassen_passt`: the site was admitted only with the bound
    re-decided);
    (4) the narrowed address reads back whole through the canonical
    word (no truncation, no wrap).
    The checker's range at the site (`weiter`/`narrow`) is untouched
    and still enforced there. Nothing here derives an `ensures`,
    turns a refusal into a warning, or speculates a faulting form
    above its guard: float ops are token-threaded, hence outside the
    pure window by `keinToken`, and the NaN swap is refused by
    `keinNaNTausch` (section 4). -/

/-- The narrowed address reads back whole through the canonical word. -/
theorem dispWort_ganz (x : Int) (c : DispCert)
    (hW : 0 ≤ x + c.disp ∧ x + c.disp < 2 ^ 64) :
    ((BitVec.ofNat 64 (x + c.disp).toNat : Wort)).toNat
      = (x + c.disp).toNat := by
  have h : (x + c.disp).toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- CONNECTION: narrowing `x + disp` under a bind preserves value and
    outcome, carries the recomputed i32 bound, and keeps the
    width-exact word image. -/
theorem OptPeepholeDisp_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (x : Int) (c : DispCert)
    (rest : Endblock D V l ((.int (x + c.disp) (x + c.disp)) :: Γ) Λ)
    (hz : dispPeepholeZulassen c = true)
    (hW : 0 ≤ x + c.disp ∧ x + c.disp < 2 ^ 64)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (.lit (x + c.disp) : Expr D Γ Λ (.int (x + c.disp) (x + c.disp))) σ ρ).n
      = (eval σ₀ (.add (.lit x) (.lit c.disp) : Expr D Γ Λ (.int (x + c.disp) (x + c.disp))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (.lit (x + c.disp) : Expr D Γ Λ (.int (x + c.disp) (x + c.disp))) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.add (.lit x) (.lit c.disp) : Expr D Γ Λ (.int (x + c.disp) (x + c.disp))) rest) σ ρ
    ∧ c.passt = true
    ∧ ((BitVec.ofNat 64 (x + c.disp).toNat : Wort)).toNat = (x + c.disp).toNat := by
  exact ⟨rfl, rfl, dispZulassen_passt c hz, dispWort_ganz x c hW⟩

/-! ## 6. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptPeepholeDisp_verbindung` instantiated JOINTLY:
    `3 + 4` narrows to `7` under a `bind` with a `leave`
    continuation, admitted by the record `⟨4, true, true, true, true⟩`,
    in the NON-DEGENERATE reference program `refD` (whose `einzahlen`
    writes its table, `refEin_schreibt`), beside the reached F-machine
    run `MB` that changes memory (`refB_erreicht`, `refB_schreibt`).
    Every conjunct is used. -/

/-- JOINT WITNESS for `OptPeepholeDisp_verbindung`: `3 + 4` narrows
    to `7` on `refD`, beside the memory-changing reached run. -/
theorem OptPeepholeDisp_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (x : Int) (c : DispCert)
      (rest : Endblock refD V l ((.int (x + c.disp) (x + c.disp)) :: Γ) Λ)
      (_hz : dispPeepholeZulassen c = true)
      (_hW : 0 ≤ x + c.disp ∧ x + c.disp < 2 ^ 64)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (.lit (x + c.disp) : Expr refD Γ Λ (.int (x + c.disp) (x + c.disp))) σ ρ).n
        = (eval σ₀ (.add (.lit x) (.lit c.disp) : Expr refD Γ Λ (.int (x + c.disp) (x + c.disp))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (.lit (x + c.disp) : Expr refD Γ Λ (.int (x + c.disp) (x + c.disp))) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (.add (.lit x) (.lit c.disp) : Expr refD Γ Λ (.int (x + c.disp) (x + c.disp))) rest) σ ρ
      ∧ c.passt = true
      ∧ ((BitVec.ofNat 64 (x + c.disp).toNat : Wort)).toNat = (x + c.disp).toNat
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptPeepholeDisp_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (x := 3) (c := ⟨4, true, true, true, true⟩)
    (rest := Endblock.leave rfl) (hz := by decide) (hW := by decide)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true, 3,
    ⟨4, true, true, true, true⟩,
    Endblock.leave rfl, by decide, by decide,
    refSp0.welt [], refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    Proved here (all over the REUSED canonical vocabulary -- source
    `Typen`/`Syntax`/`Semantik` values and `execEnd` outcomes, the
    kernel float model through the accepted `X86.ScalarFloat` NaN row,
    the reference program `refD` with its reached memory-changing
    run -- no new semantics, register, memory, decoder or source
    model):
    - the peephole certificate with its admission pin (local rewrite
      record: recorded displacement plus the four validator-decided
      side conditions of the DESIGN section 7 row) and all four
      DESIGN refusals as decided Bools (i32 miss, token op in the
      pure window, live flag, UCOMI-to-ordered-compare NaN swap),
      with admitted/refused probes;
    - disp-fits-i32 edge pins, every-disp8-fits-i32, and admission
      carrying the bound field;
    - pure-window value preservation over arbitrary integers plus the
      disp0 escape;
    - the IEEE NaN collapse (both ordered directions answer `false`
      on NaN), which is why the swap must refuse;
    - the `OptPeepholeDisp_verbindung` connection (value, `execEnd`
      outcome, bound field, word image) with the joint
      `OptPeepholeDisp_verbindung_zeuge` witness on the
      non-degenerate writer program beside the memory-changing run.
    NOT proved here, and not claimed:
    - No encoder-row/codec claim: the disp8/disp0 byte spellings, the
      length function and the layout `layoutOk` revalidation after
      any byte shortening stay with the codec/layout lanes (DESIGN
      section 2B: a layout change without re-decoding revalidation
      is refused).
    - No cost claim: `targetWork`/`expandBound` accounting of the
      shortened window stays with the cost lane; the window keeps the
      same block shape, and machine-work bounds are never re-summed
      here.
    - No silicon correspondence: address math reuses `dispWort`;
      faults are the existing permission-checked outcomes, and the
      flag model is the accepted `Flags` with `af : Option Bool`,
      not silicon.
    - No TSO/GX bridge: footprints are unchanged sequential sets;
      tearing, visibility and grouping stay open.
    - No `x - x` to `0` and no FMA fusion: those DESIGN failure cases
      belong to their own rule rows and are refused here by
      construction (this window is address addition only).
    - No source-to-byte validation claim.
-/

#print axioms dispPeepholeZulassen
#print axioms dispVerweigert_passt
#print axioms dispVerweigert_token
#print axioms dispVerweigert_flag
#print axioms dispVerweigert_nan
#print axioms probe_dispZulassen_ok
#print axioms probe_dispZulassen_nan
#print axioms dispPasstI32
#print axioms dispPasst_maxPos
#print axioms dispPasst_minNeg
#print axioms dispPasst_drueber
#print axioms disp8_passt_i32
#print axioms dispZulassen_passt
#print axioms dispAdresse_durchRecord
#print axioms disp0_addiert_null
#print axioms ucomiTausch_kollabiert
#print axioms dispWort_ganz
#print axioms OptPeepholeDisp_verbindung
#print axioms OptPeepholeDisp_verbindung_zeuge

end Gabbro.Grammatik.X86
