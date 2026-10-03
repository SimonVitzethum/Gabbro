/-
  File:      Grammatik/X86/OptLayoutAlign.lean
  Subject:   Loop-alignment rule lemma (lane 883).

  DESIGN section 7 row (layout/allocation, phase L) with the section 7A
  alignment/code-size tuning row: align loop heads and vector loads per the
  measured traits of the selected profile; padding feeds layout, relaxation
  rounds and padding byte cost, and is NEVER a timing promise. Local premise
  (validator-decided): loop-head trait, vector-load trait, measured profile
  flag, alignment class in {16, 32}, pad below the class. Certificate: the
  local rewrite record `AlignBeleg` (final start, body length, class, pad,
  final head) plus recomputed trait citations carried in `AlignCert`.
  Failure case (refuse): unmeasured traits, pad at or above the class, a
  class outside {16, 32} -- and never a fixed timing promise.

  What is proved here, over the REUSED canonical vocabulary (`Syntax`,
  `Semantik`, `ReferenzB`): padding is layout-only -- the executed body is
  byte-identical, so `execBlock` agrees exactly (same constructor, same
  successor worlds and environments: values incl. IEEE, faults, contracts at
  their place, call logs, shared accesses and step-budget accounting all
  transfer together), while the layout facts (final-head equation, head
  alignment, pad bound, positive body length) are recomputed by the
  `alignOk` Bool. No `ensures` is derived, no refusal becomes a warning, no
  faulting form is speculated above its guard, no cycle claim is made.
-/
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.RufMaschineF

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one loop-alignment site
    (DESIGN section 7 / 7A row): the loop-head trait and the vector-load
    trait of the measured profile both hold, the profile measurement is
    cited (`gemessen`), the class is 16 or 32, and the pad is below it. -/
structure AlignCert where
  kopfOk : Bool
  lastOk : Bool
  gemessen : Bool
  ausr : Nat
  pad : Nat
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def alignZulassen (c : AlignCert) : Bool :=
  c.kopfOk && c.lastOk && c.gemessen &&
    decide (c.ausr = 16 ∨ c.ausr = 32) && decide (c.pad < c.ausr)

/-- An unmeasured site refuses: without the cited profile measurement the
    rule must NOT fire, even if the traits read true. -/
theorem alignVerweigert_unvermesssen (c : AlignCert)
    (h : c.gemessen = false) :
    alignZulassen c = false := by
  simp [alignZulassen, h]

/-- A pad at or above the class refuses: the inserted bytes would reach the
    next head and the layout equation stops pinning one head. -/
theorem alignVerweigert_pad (c : AlignCert)
    (h : c.ausr ≤ c.pad) :
    alignZulassen c = false := by
  have hlt : decide (c.pad < c.ausr) = false :=
    decide_eq_false (Nat.not_lt.mpr h)
  simp [alignZulassen, hlt]

/-- A class outside {16, 32} refuses: only the two measured classes have a
    trait citation; anything else is an unmeasured layout. -/
theorem alignVerweigert_ausr (c : AlignCert)
    (h16 : c.ausr ≠ 16) (h32 : c.ausr ≠ 32) :
    alignZulassen c = false := by
  have hcls : decide (c.ausr = 16 ∨ c.ausr = 32) = false :=
    decide_eq_false (fun h => h.elim h16 h32)
  simp [alignZulassen, hcls]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_alignZulassen_ok :
    alignZulassen ⟨true, true, true, 16, 0⟩ = true := by
  decide

/-- Probe: an unmeasured certificate is refused. -/
theorem probe_alignZulassen_unvermesssen :
    alignZulassen ⟨true, true, false, 16, 0⟩ = false := by
  decide

/-- Probe: an overflowing pad is refused. -/
theorem probe_alignZulassen_pad :
    alignZulassen ⟨true, true, true, 16, 16⟩ = false := by
  decide

/-- Probe: an unmeasured class is refused. -/
theorem probe_alignZulassen_klasse :
    alignZulassen ⟨true, true, true, 8, 0⟩ = false := by
  decide

/-! ## 1. What admission gives: the pad bound, recomputed. -/

/-- An admitted certificate carries a pad below its class. -/
theorem alignZulassen_pad (c : AlignCert)
    (h : alignZulassen c = true) : c.pad < c.ausr := by
  simp only [alignZulassen, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hpad⟩ := h
  exact of_decide_eq_true hpad

/-! ## 2. The layout certificate: final head, recomputed, never trusted.

    The local rewrite record carries the FINAL loop-head start, the body
    length in bytes, the class, the inserted pad and the FINAL head. The
    checker recomputes the head equation, the head alignment and the pad
    bound from carried data and never iterates a relaxation round: length
    stability of the body (it is byte-identical) is why one pass suffices.
    The executed body itself is untouched -- padding lives only in these
    layout facts. -/

/-- Layout certificate for one aligned loop-head site. -/
structure AlignBeleg where
  start : Nat
  len : Nat
  ausr : Nat
  pad : Nat
  ziel : Nat
  deriving DecidableEq, Repr

/-- Checked certificate: the pad is below the class, the class is measured,
    the final head is start plus pad, the final head is aligned, and the
    body is nonempty. -/
def alignOk (b : AlignBeleg) : Bool :=
  decide (b.pad < b.ausr) && decide (b.ausr = 16 ∨ b.ausr = 32) &&
    decide (b.ziel = b.start + b.pad) && decide (b.ziel % b.ausr = 0) &&
    decide (0 < b.len)

/-- ACCEPTANCE: a certificate with a bounded pad, a measured class, the
    head equation, head alignment and a nonempty body is accepted. Every
    premise is used. -/
theorem alignOk_akzeptiert (b : AlignBeleg)
    (hpad : b.pad < b.ausr)
    (hcls : b.ausr = 16 ∨ b.ausr = 32)
    (hgleich : b.ziel = b.start + b.pad)
    (hmod : b.ziel % b.ausr = 0)
    (hlen : 0 < b.len) :
    alignOk b = true := by
  unfold alignOk
  rw [decide_eq_true hpad, decide_eq_true hcls, decide_eq_true hgleich,
    decide_eq_true hmod, decide_eq_true hlen]
  rfl

/-- ADDRESS EQUATION: an accepted certificate pins the final head at
    start plus pad. Every premise is used. -/
theorem alignBeleg_adresse (b : AlignBeleg)
    (h : alignOk b = true) :
    b.ziel = b.start + b.pad := by
  simp only [alignOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, _⟩, hgleich⟩, _⟩, _⟩ := h
  exact of_decide_eq_true hgleich

/-- HEAD ALIGNMENT: an accepted certificate has its final head on the
    class boundary. Every premise is used. -/
theorem alignBeleg_ausgerichtet (b : AlignBeleg)
    (h : alignOk b = true) :
    b.ziel % b.ausr = 0 := by
  simp only [alignOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, hmod⟩, _⟩ := h
  exact of_decide_eq_true hmod

/-- PAD BOUND: an accepted certificate carries a pad below its class.
    Every premise is used. -/
theorem alignBeleg_pad (b : AlignBeleg)
    (h : alignOk b = true) :
    b.pad < b.ausr := by
  simp only [alignOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hpad, _⟩, _⟩, _⟩, _⟩ := h
  exact of_decide_eq_true hpad

/-- CONCRETE ACCEPT: start 4096, 5-byte body, class 16, no pad needed,
    head already on the boundary. -/
theorem align_zeuge_akzeptiert :
    alignOk ⟨4096, 5, 16, 0, 4096⟩ = true := by
  decide

/-- CONCRETE REFUSALS: overflowing pad, misaligned final head and a
    padded head that misses the boundary are each refused. -/
theorem align_zeuge_verweigert :
    alignOk ⟨4096, 5, 16, 16, 4112⟩ = false ∧
    alignOk ⟨4096, 5, 16, 0, 4100⟩ = false ∧
    alignOk ⟨4096, 5, 16, 4, 4100⟩ = false := by
  decide

/-! ## 3. Connection: padding moves the head, never the execution.

    The rewrite is layout-only: `layoutPad` is the identity on executed
    syntax -- the body bytes are unchanged, only the carried head moves by
    the checked pad. Conclusion, jointly:
    (1) the `execBlock` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no value is changed (integer
    and IEEE alike: the same expressions evaluate in the same worlds, and
    `gleitPasst`/`logik bereich` outcomes agree), no fault is added or
    removed (`logik`/`hardware` agree, guards still fire at their place),
    every downstream observation agrees (contracts at their place read the
    same values from the same environments, call logs gain no event, no
    shared access is added or removed for concurrency -- both sides run
    the same body), and the step-budget accounting is unchanged (same
    block shape, padding is unbudgeted layout);
    (2) the final head equation, recomputed from the certificate;
    (3) the final-head alignment, recomputed from the certificate;
    (4) the pad bound, recomputed from the admission.
    Nothing here derives an `ensures`, turns a refusal into a warning,
    speculates a faulting form above its guard, or promises timing: the
    measured traits only select among valid layouts. -/

/-- Layout-only rewrite: padding never touches executed syntax. -/
def layoutPad {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    Block D V l Γ Λ Λ' := b

/-- CONNECTION: an admitted, certified alignment preserves the `execBlock`
    outcome and pins the final head facts. Every premise is used: the
    admission for the pad bound (via the bound record), the certificate
    check for the head facts, the binding for joining the two records, and
    the body, worlds, oracle, budget and handler for the outcome. -/
theorem OptLayoutAlign_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (cert : AlignCert) (bg : AlignBeleg)
    (hz : alignZulassen cert = true)
    (hok : alignOk bg = true)
    (hbind : bg.ausr = cert.ausr ∧ bg.pad = cert.pad)
    (body : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (layoutPad body) σ ρ = execBlock O passes R body σ ρ ∧
    bg.ziel = bg.start + bg.pad ∧
    bg.ziel % bg.ausr = 0 ∧
    cert.pad < cert.ausr := by
  obtain ⟨hba, hbp⟩ := hbind
  refine ⟨rfl, alignBeleg_adresse bg hok, alignBeleg_ausgerichtet bg hok, ?_⟩
  have hcert := alignZulassen_pad cert hz
  omega

/-! ## 4. Joint witness: the rule fires beside a real memory move.

    ALL premises of `OptLayoutAlign_verbindung` instantiated JOINTLY: the
    admitted certificate `⟨true, true, true, 16, 0⟩`, the accepted head
    record `⟨4096, 5, 16, 0, 4096⟩` bound to it, and the layout-identical
    empty body under the NON-DEGENERATE reference program `refD` (whose
    `einzahlen` writes its table, `refEin_schreibt`), beside the reached
    F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). Every conjunct is used. -/

/-- JOINT WITNESS for `OptLayoutAlign_verbindung`: admitted alignment
    with an accepted head record on `refD`, beside the memory-changing
    reached run. -/
theorem OptLayoutAlign_verbindung_zeuge :
    ∃ (cert : AlignCert) (bg : AlignBeleg)
      (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
      (body : Block refD V l Γ Λ Λ') (σ : World refD) (ρ : Env refD Γ),
      alignZulassen cert = true ∧
      alignOk bg = true ∧
      (bg.ausr = cert.ausr ∧ bg.pad = cert.pad) ∧
      (execBlock O passes R (layoutPad body) σ ρ =
        execBlock O passes R body σ ρ) ∧
      bg.ziel = bg.start + bg.pad ∧
      bg.ziel % bg.ausr = 0 ∧
      cert.pad < cert.ausr ∧
      (vertragVon refD refEin).schreibt () = true ∧
      RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
      MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptLayoutAlign_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (l := true) (Γ := [])
    (Λ := [Res.held (D := refD) ()]) (Λ' := [Res.held (D := refD) ()])
    (cert := ⟨true, true, true, 16, 0⟩)
    (bg := ⟨4096, 5, 16, 0, 4096⟩)
    (hz := by decide) (hok := by decide) (hbind := ⟨rfl, rfl⟩)
    (body := Block.nil) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨⟨true, true, true, 16, 0⟩, ⟨4096, 5, 16, 0, 4096⟩,
    vertragVon refD refEin, refO, 0, keinRuf, true, [],
    [Res.held (D := refD) ()], [Res.held (D := refD) ()], Block.nil,
    refSp0.welt [], Env.nil,
    by decide, by decide, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No relaxation-round convergence: one certified site carries its
      final head; whole-function narrowing stability across sites
      (DESIGN section 2B) stays future work.
    - No totalCost / machine-work inequality: the aligned window is the
      same block shape with unbudgeted layout bytes beside it, so
      step-budget accounting is unchanged; the formal level-(c)
      machine-work bound is OPEN per IR-VALIDIERUNG (same reading as
      lane 860).
    - No timing claim: the measured traits select among valid layouts
      only; cycle bounds need named assumptions plus the proved work
      transfer (FLOAT-ZEIT section 8.2), DEFERRED here, exactly as the
      DESIGN section 7A row requires ("no fixed timing promise").
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at recomputed head arithmetic over `Nat`.
    - No checker change: no source admission is tightened to ease proof;
      everything is over the real `Block`/`execBlock` and recomputed
      `Bool` checks.
-/

#print axioms alignZulassen
#print axioms alignVerweigert_unvermesssen
#print axioms alignVerweigert_pad
#print axioms alignVerweigert_ausr
#print axioms alignZulassen_pad
#print axioms alignOk
#print axioms alignOk_akzeptiert
#print axioms alignBeleg_adresse
#print axioms alignBeleg_ausgerichtet
#print axioms alignBeleg_pad
#print axioms layoutPad
#print axioms OptLayoutAlign_verbindung
#print axioms OptLayoutAlign_verbindung_zeuge

end Gabbro.Grammatik.X86
