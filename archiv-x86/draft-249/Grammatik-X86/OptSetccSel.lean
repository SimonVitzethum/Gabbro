/-
  File:      Grammatik/X86/OptSetccSel.lean
  Subject:   SETcc selection rule lemma (lane 890).

  DESIGN rows: §3 SETcc row (byte result 0/1 exact; no flag leak),
  §3A (SETcc where MEASURED suitable, never by default; register-only
  first), §4 float row (UCOMISD + SETcc/Jcc with JP row; NaN unordered
  is false), §7 flags-aware peepholes (rule in register, flag-liveness,
  no token op in pure window), certificate A (local rewrite record plus
  recomputed analysis citations).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`,
  `X86.ControlFlow`, `X86.ControlCodec`): the validator-decided side
  conditions, their refusals, the 0/1 byte value over arbitrary
  conditions, the byte-step window frame, the admitted float-compare
  equation, and the source/target connection. No `ensures` is derived,
  no refusal becomes a warning, no faulting form is speculated above
  its guard. No accepted IR exists yet, so the source fragment is the
  real `Syntax`/`Semantik` `Endblock.bind` window.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.ControlFlow
import Grammatik.X86.ControlCodec

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one SETcc-selection site:
    measured-suitable (never by default), no live flag consumer across
    the compare+SETcc window, no token op in the pure window,
    register destination only, and float sites carry their unordered
    (JP) row under one MXCSR scope. -/
structure SetccSelCert where
  massGeeignet : Bool
  keinFlagLeck : Bool
  reinesFenster : Bool
  nurRegister : Bool
  fpBereinigt : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation
    (the branched spelling), never to a warning. -/
def setccZulassen (c : SetccSelCert) : Bool :=
  c.massGeeignet && c.keinFlagLeck && c.reinesFenster && c.nurRegister
    && c.fpBereinigt

/-! ## 1. Refusals: each DESIGN failure case must NOT select SETcc.

    A branchless selection whose branch is predictable (or has no
    measured evidence: `massGeeignet = false`, §3A "never by default")
    is refused and falls back to the branched spelling. A site where a
    live flag consumer reads across the compare+SETcc window
    (`keinFlagLeck = false`, §3 row "no flag leak") is refused: the
    compare clobbers flags the later site still needs. A window with a
    token op (`reinesFenster = false`, §7 peephole row) is refused. A
    memory destination (`nurRegister = false`: r/m8 refused, the
    register-only-first precedent of §3A for CMOV) is refused: a memory
    SETcc is a memory event with tearing/visibility obligations this
    rule does not discharge. A float-derived condition without its
    unordered (JP) row or outside one MXCSR scope (`fpBereinigt =
    false`, §4 row and §7 "UCOMI→ordered-compare NaN swap") is refused:
    NaN is unordered and must read `false`, never the ordered bit. -/

/-- A predictable (or unmeasured) branch keeps its branch. -/
theorem setccVerweigert_messung (c : SetccSelCert)
    (h : c.massGeeignet = false) :
    setccZulassen c = false := by
  simp [setccZulassen, h]

/-- A flag leak across the window refuses. -/
theorem setccVerweigert_flagleck (c : SetccSelCert)
    (h : c.keinFlagLeck = false) :
    setccZulassen c = false := by
  simp [setccZulassen, h]

/-- A token op in the pure window refuses. -/
theorem setccVerweigert_fenster (c : SetccSelCert)
    (h : c.reinesFenster = false) :
    setccZulassen c = false := by
  simp [setccZulassen, h]

/-- A memory destination refuses: register-only first. -/
theorem setccVerweigert_speicher (c : SetccSelCert)
    (h : c.nurRegister = false) :
    setccZulassen c = false := by
  simp [setccZulassen, h]

/-- An unordered float condition without its JP row refuses. -/
theorem setccVerweigert_fp (c : SetccSelCert)
    (h : c.fpBereinigt = false) :
    setccZulassen c = false := by
  simp [setccZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_setccZulassen_ok :
    setccZulassen ⟨true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a flag-leaking certificate is refused. -/
theorem probe_setccZulassen_flagleck :
    setccZulassen ⟨true, false, true, true, true⟩ = false := by
  decide

/-- Probe: the default (unmeasured) selection is refused. -/
theorem probe_setccZulassen_messung :
    setccZulassen ⟨false, true, true, true, true⟩ = false := by
  decide

/-- Probe: a float site without its unordered row is refused. -/
theorem probe_setccZulassen_fp :
    setccZulassen ⟨true, true, true, true, false⟩ = false := by
  decide

/-! ## 2. Value level: the byte result is exactly 0/1 of the condition.

    Each lemma is over ARBITRARY conditions and flag snapshots
    (`c : Bedingung`, `f : Flags`): the flag-production premise (which
    compare established these flags from which values) is carried by
    the certificate's recomputed analysis citations and forwarded as
    `hb` at the use sites below, so no flag fact is invented here. -/

/-- The SETcc byte IS the 0/1 selection over the flag snapshot. -/
theorem setccByte_wahl (c : Bedingung) (f : Flags) :
    setCCByte c f =
      (if bedingung c f then BitVec.ofNat 8 1 else BitVec.ofNat 8 0) := by
  simp [setCCByte]

/-- The SETcc byte reads back as the 0/1 natural of the condition. -/
theorem setccByte_nat (c : Bedingung) (f : Flags) :
    (setCCByte c f).toNat = (if bedingung c f then 1 else 0) := by
  rw [setccByte_wahl]
  cases (bedingung c f) <;> decide

/-- The SETcc application writes that byte into the low byte,
    upper bits preserved. -/
theorem setccAnwenden_tief (s : Zustand) (dst : Register) (c : Bedingung) :
    ((setCCAnwenden s dst c).register dst).toNat % 256
      = (setCCByte c s.flags).toNat := by
  have h := setLowByte_tief (s.register dst) (setCCByte c s.flags)
  have e : (setCCAnwenden s dst c).register dst =
      setLowByte (s.register dst) (setCCByte c s.flags) := by
    simp [setCCAnwenden, regSet]
  rw [e]
  exact h

/-- Complementary condition-code selection with swapped constants
    materialises the same byte: choosing `ne` with `0/1` swapped is
    the same 0/1 as `e`. The generic form over an arbitrary `b`. -/
theorem setccKomplement_wahl (b : Bool) :
    (if b then (1 : Byte) else 0) = (if !b then (0 : Byte) else 1) := by
  cases b <;> rfl

/-- Probe: zero-flag set materialises `1`. -/
theorem probe_setccByte_true :
    (setCCByte .e witTrue.flags).toNat = 1 := by
  decide

/-- Probe: zero-flag clear materialises `0`. -/
theorem probe_setccByte_false :
    (setCCByte .e witFalse.flags).toNat = 0 := by
  decide

/-! ## 3. Byte-step window: value, flags, memory, upper bits, RIP.

    Over the ACCEPTED byte step (`setccSchrittBytes` over the actual
    decoded length): the destination low byte is the 0/1 of the
    arbitrary condition value, flags and memory are kept (no flag leak
    AT the SETcc itself — the compare's clobber is the `keinFlagLeck`
    citation), every other byte of the destination word is kept, and
    RIP advances past exactly the decoded bytes. The length guard is
    checked data (`hok`), never an emitter note. -/

/-- CONNECTION (target window): the admitted byte step materialises
    the condition's 0/1 and keeps flags, memory, upper bits and RIP. -/
theorem setccByteSchritt_verbindung (len : Nat) (s s' : Zustand)
    (dst : Register) (c : Bedingung) (b : Bool)
    (hok : laengeOk len = true)
    (hstep : setccSchrittBytes len s dst c = some s')
    (hb : bedingung c s.flags = b) :
    (s'.register dst).toNat % 256 = (if b then 1 else 0)
      ∧ s'.flags = s.flags ∧ s'.speicher = s.speicher
      ∧ s'.rip = ripNach s.rip len
      ∧ (s'.register dst).toNat / 256
        = (s.register dst).toNat / 256 := by
  have hval := setccSchrittBytes_wert len s s' dst c hok hstep
  have hrahmen := setccSchrittBytes_rahmen len s s' dst c hok hstep
  have hbyte : (setCCByte c s.flags).toNat = (if b then 1 else 0) := by
    rw [setccByte_nat c s.flags, hb]
  have htief := setLowByte_tief (s.register dst) (setCCByte c s.flags)
  have hhoch := setLowByte_hoch (s.register dst) (setCCByte c s.flags)
  refine ⟨?_, hrahmen.1, hrahmen.2.1, hrahmen.2.2.1, ?_⟩
  · rw [hval, htief, hbyte]
  · rw [hval]
    exact hhoch

/-! ## 4. Float compare: single rounding, one scope, same outcome.

    The validator precomputes the float equation IN THE KERNEL under
    one MXCSR scope and supplies the unordered (JP) row
    (`fpBereinigt`); the recomputation obligation is conditional on
    admission (`hEq` takes `hz`), exactly as for integer folds. NaN
    stays unordered-`false`: no ordered-compare swap without its JP
    row ever reaches this equation (it is refused in §1). The
    UCOMISD byte correspondence itself belongs to the lowering lane. -/

/-- The admitted float-compare materialisation preserves value and
    `gleitPasst` outcome. -/
theorem setccGleit_behält (cert : SetccSelCert) (op : GleitOp)
    (qa qb qf lo hi : Int × Int)
    (hz : setccZulassen cert = true)
    (hEq : setccZulassen cert = true →
      bruch qf = gleitRechne op (bruch qa) (bruch qb)) :
    gleitPasst lo hi (bruch qf) =
      gleitPasst lo hi (gleitRechne op (bruch qa) (bruch qb)) := by
  have e := hEq hz
  rw [e]

/-! ## 5. Connection: complementary selections agree at source and target.

    The rule selects a branchless boolean materialisation for one
    admitted site; choosing the complementary condition code with
    swapped constants (the generic form over an arbitrary `b`: `b`
    with `1/0` vs `!b` with `0/1`-swapped) is the same value. Stated
    at an `Endblock.bind` window with an ARBITRARY continuation
    `rest`, so the conclusion covers every downstream observation at
    once. Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved across the complement
    choice (both sides widen to the common `.int 0 1` through
    `weiter`, whose range evidence is carried as premises);
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree), every downstream observation
    agrees (contracts at their place read the same values from the
    same environments, call logs gain no event, no shared access is
    added or removed for concurrency -- both materialisations are
    literals with `orte = []`), and the step-budget accounting is
    unchanged (same block shape; the removed branch is covered by the
    validator's measured-suitability citation, never by hope);
    (3) the admitted target byte is exactly that 0/1, through the
    validator's flag-production premise (`hSel` takes `hz`: the
    equation is claimed only where the validator admitted the site
    AND recomputed which compare established these flags).
    Nothing here derives an `ensures`, turns a refusal into a
    warning, or speculates a faulting form above its guard. The
    checker's range at the site is untouched and still enforced
    there -- never weakened, never re-derived. -/

/-- CONNECTION: complementary SETcc selections preserve value,
    outcome and the admitted target byte. -/
theorem OptSetccSel_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (b : Bool) (cert : SetccSelCert)
    (hz : setccZulassen cert = true)
    (c : Bedingung) (f : Flags)
    (hSel : setccZulassen cert = true → bedingung c f = b)
    (hw1 : 0 ≤ (if b then 1 else 0))
    (hw2 : (if b then 1 else 0) ≤ 1)
    (hk1 : 0 ≤ (if !b then 0 else 1))
    (hk2 : (if !b then 0 else 1) ≤ 1)
    (rest : Endblock D V l ((.int 0 1) :: Γ) Λ)
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (Expr.weiter hw1 hw2
      (.lit (if b then 1 else 0) : Expr D Γ Λ
        (.int (if b then 1 else 0) (if b then 1 else 0)))) σ ρ).n
      = (eval σ₀ (Expr.weiter hk1 hk2
        (.lit (if !b then 0 else 1) : Expr D Γ Λ
          (.int (if !b then 0 else 1) (if !b then 0 else 1)))) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (Expr.weiter hw1 hw2
          (.lit (if b then 1 else 0) : Expr D Γ Λ
            (.int (if b then 1 else 0) (if b then 1 else 0)))) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (Expr.weiter hk1 hk2
          (.lit (if !b then 0 else 1) : Expr D Γ Λ
            (.int (if !b then 0 else 1) (if !b then 0 else 1)))) rest) σ ρ
    ∧ (setCCByte c f).toNat = (if b then 1 else 0) := by
  have e := hSel hz
  refine ⟨?_, ?_, ?_⟩
  · cases b <;> rfl
  · cases b <;> rfl
  · rw [setccByte_nat c f, e]

/-! ## 6. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptSetccSel_verbindung` instantiated JOINTLY:
    `true` materialised as `1` (complement: `!true` with swapped
    constants) under a `bind` with a `leave` continuation, on the
    admitted certificate, with the flag-production fact `e` over the
    zero flag, in the NON-DEGENERATE reference program `refD` (whose
    `einzahlen` writes its table, `refEin_schreibt`), beside the
    reached F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). All conjunct groups are used. -/

/-- JOINT WITNESS for `OptSetccSel_verbindung`: `true` as `1`
    on `refD`, beside the memory-changing reached run. -/
theorem OptSetccSel_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (b : Bool) (cert : SetccSelCert)
      (_hz : setccZulassen cert = true)
      (c : Bedingung) (f : Flags)
      (_hSel : setccZulassen cert = true → bedingung c f = b)
      (_hw1 : 0 ≤ (if b then 1 else 0))
      (_hw2 : (if b then 1 else 0) ≤ 1)
      (_hk1 : 0 ≤ (if !b then 0 else 1))
      (_hk2 : (if !b then 0 else 1) ≤ 1)
      (rest : Endblock refD V l ((.int 0 1) :: Γ) Λ)
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (Expr.weiter _hw1 _hw2
        (.lit (if b then 1 else 0) : Expr refD Γ Λ
          (.int (if b then 1 else 0) (if b then 1 else 0)))) σ ρ).n
        = (eval σ₀ (Expr.weiter _hk1 _hk2
          (.lit (if !b then 0 else 1) : Expr refD Γ Λ
            (.int (if !b then 0 else 1) (if !b then 0 else 1)))) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (Expr.weiter _hw1 _hw2
            (.lit (if b then 1 else 0) : Expr refD Γ Λ
              (.int (if b then 1 else 0) (if b then 1 else 0)))) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (Expr.weiter _hk1 _hk2
            (.lit (if !b then 0 else 1) : Expr refD Γ Λ
              (.int (if !b then 0 else 1) (if !b then 0 else 1)))) rest) σ ρ
      ∧ (setCCByte c f).toNat = (if b then 1 else 0)
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptSetccSel_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (b := true) (cert := ⟨true, true, true, true, true⟩)
    (hz := by decide) (c := .e) (f := witTrue.flags)
    (hSel := fun _ => by decide)
    (hw1 := by decide) (hw2 := by decide)
    (hk1 := by decide) (hk2 := by decide)
    (rest := Endblock.leave rfl)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true, true,
    ⟨true, true, true, true, true⟩, by decide, .e, witTrue.flags,
    (fun _ => by decide),
    by decide, by decide, by decide, by decide,
    Endblock.leave rfl,
    refSp0.welt [], refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No lowering correspondence: source `Stmt.ite` to lowered
      CMP+SETcc bytes is the lowering lane's theorem (594/638
      decision); per-access refinement into W/GX is OPEN (TSO bridge
      lane). Correspondence here stops at the 0/1 value, the
      `execEnd` outcome and the accepted byte-step equations.
    - No totalCost inequality: the selected window keeps the same
      block shape with one pure value moved, so step-budget
      accounting is unchanged; the formal level-(c) machine-work
      transfer is OPEN per IR-VALIDIERUNG (lane 278). The
      `CostSummary` schema is reused untouched, never re-summed.
    - No memory-destination SETcc: r/m8 with a memory operand is
      refused (`nurRegister`); the single-copy atomicity,
      tearing and visibility obligations of a memory SETcc belong to
      the concurrency lane.
    - No UCOMISD byte correspondence: the float equation is gated by
      the validator's recomputed kernel equation plus the unordered
      (JP) row; the scalar-SSE2 byte proof is the lowering lane's.
    - No new `Befehl` evaluation, no checker change, no silicon,
      ABI or loader claim: the one target semantics
      (`setccSchrittBytes` over the actual decoded length) is reused
      untouched, and no source admission is tightened to ease proof.
-/

#print axioms setccZulassen
#print axioms setccVerweigert_messung
#print axioms setccVerweigert_flagleck
#print axioms setccVerweigert_fenster
#print axioms setccVerweigert_speicher
#print axioms setccVerweigert_fp
#print axioms setccByte_wahl
#print axioms setccByte_nat
#print axioms setccAnwenden_tief
#print axioms setccKomplement_wahl
#print axioms probe_setccByte_true
#print axioms probe_setccByte_false
#print axioms setccByteSchritt_verbindung
#print axioms setccGleit_behält
#print axioms OptSetccSel_verbindung
#print axioms OptSetccSel_verbindung_zeuge

end Gabbro.Grammatik.X86
