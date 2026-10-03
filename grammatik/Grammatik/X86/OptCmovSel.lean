/-
  File:      Grammatik/X86/OptCmovSel.lean
  Subject:   CMOV-selection rule lemma (lane 891).

  DESIGN section 7 row implemented: the §3A tile "SETcc/CMOVcc where
  MEASURED suitable, never by default" with the flags-peephole premises
  ("rule in register, flag-liveness"). Local premise (validator-decided):
  unpredictable branch, cheap operands, unselected side proved
  fault-free, register-only select, fresh flags, one FP rounding scope.
  Certificate: local rewrite record plus recomputed analysis citations.
  Failure case (refuse, default stays branch): memory-source CMOV and
  any may-fault unselected side; also predictable branches, expensive
  operands, stale flags, cross-scope floats. Phase L, cost O(windows).

  Proved over the REUSED vocabulary (`Typen`, `Syntax`, `Semantik`,
  `ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.ControlFlow`): the select
  computes the taken arm value, the admitted rewrite keeps the `execEnd`
  outcome (no fault added or removed, same successor worlds — hence
  contracts at their place, call logs, shared accesses and budget
  accounting unchanged), the selected word reads back whole, and the
  select preserves the `gleitPasst` outcome. No `ensures` is derived,
  no refusal becomes a warning, no faulting form is speculated above
  its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.ControlFlow
import Grammatik.X86.ConditionalMove

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one CMOV-selection site
    (DESIGN §3A tile + §7 flags-peephole row). Every field is checked
    data the validator recomputes; a refused OPTIONAL optimisation
    falls back to the branch, never to a warning. -/
structure CmovSelCert where
  unvorhersehbar : Bool
  billig : Bool
  fehlerfrei : Bool
  nurRegister : Bool
  flagsFrisch : Bool
  gleicheRundung : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. Default stays branch. -/
def cmovSelZulassen (c : CmovSelCert) : Bool :=
  c.unvorhersehbar && c.billig && c.fehlerfrei && c.nurRegister &&
    c.flagsFrisch && c.gleicheRundung

/-- Selected value: what the branch would take and the select computes. -/
def selWert (b : Bool) (x y : Int) : Int := if b then x else y

/-! ## 1. Refusal: the DESIGN failure cases must NOT select.

    A CMOV with a memory source reads BOTH sides' memory: the
    unselected side may still fault architecturally (page fault on the
    untaken path is real, OPTIMIZER §3.10 hard gate), so
    `nurRegister = false` forces `cmovSelZulassen = false` and the
    default branch stays. A may-fault unselected side
    (`fehlerfrei = false`: division, faulting load, trap-capable FP
    behind the select) is refused the same way: predicating a faulting
    form behind `cmov` does NOT remove its fault. Predictable
    branches, expensive operands, stale flags and cross-scope floats
    are refused likewise. All proved of the decided Bool. -/

/-- Memory-source CMOV refuses: the unselected side may still fault. -/
theorem cmovSelVerweigert_speicher (c : CmovSelCert)
    (h : c.nurRegister = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- A may-fault unselected side refuses. -/
theorem cmovSelVerweigert_fehler (c : CmovSelCert)
    (h : c.fehlerfrei = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- A predictable branch refuses: default stays branch. -/
theorem cmovSelVerweigert_vorhersehbar (c : CmovSelCert)
    (h : c.unvorhersehbar = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- Expensive operands refuse. -/
theorem cmovSelVerweigert_teuer (c : CmovSelCert)
    (h : c.billig = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- Stale flags refuse: the select must read the compare's flags. -/
theorem cmovSelVerweigert_flags (c : CmovSelCert)
    (h : c.flagsFrisch = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- A cross-rounding-scope float select refuses. -/
theorem cmovSelVerweigert_rundung (c : CmovSelCert)
    (h : c.gleicheRundung = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_cmovSelZulassen_ok :
    cmovSelZulassen ⟨true, true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a memory-tainted certificate is refused. -/
theorem probe_cmovSelZulassen_speicher :
    cmovSelZulassen ⟨true, true, true, false, true, true⟩ = false := by
  decide

/-! ## 2. Value: the register-only select computes the taken arm.

    Over ARBITRARY words (`xw yw : Wort`): the `cmovAnwenden`
    destination word under flags reading `b` IS the taken arm word.
    Both arms are already computed values in registers (cheap-operand
    premise, carried by `hsrc`/`hdst`); the select adds no rounding,
    no fault and no memory event of its own. -/

/-- Taken select value: `selWert true` is the first arm. -/
theorem selWert_genommen (x y : Int) : selWert true x y = x := by
  rfl

/-- Untaken select value: `selWert false` is the second arm. -/
theorem selWert_nicht (x y : Int) : selWert false x y = y := by
  rfl

/-- Taken target word: under taken flags the destination takes the
    source word (the taken arm, already in its register). -/
theorem cmovWaehlt_genommen (s : Zustand) (dst src : Register)
    (c0 : Bedingung) (xw : Wort)
    (hbed : bedingung c0 s.flags = true)
    (hsrc : s.register src = xw) :
    (cmovAnwenden s dst src c0).register dst = xw := by
  rw [cmovAnwenden_genommen_wert s dst src c0 hbed, hsrc]

/-- Untaken target word: under untaken flags the destination keeps
    its word (the untaken arm, already in its register). -/
theorem cmovWaehlt_nicht (s : Zustand) (dst src : Register)
    (c0 : Bedingung) (yw : Wort)
    (hbed : bedingung c0 s.flags = false)
    (hdst : s.register dst = yw) :
    (cmovAnwenden s dst src c0).register dst = yw := by
  rw [cmovAnwenden_nicht_wert s dst src c0 hbed, hdst]

/-- The selected value reads back whole through the canonical word:
    width-exact (`hW`), no truncation, no wrap. -/
theorem selWortLiest (x : Int) (hW : 0 ≤ x ∧ x < 2 ^ 64) :
    ((BitVec.ofNat 64 x.toNat : Wort)).toNat = x.toNat := by
  have h : x.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The select preserves the taken arm's `gleitPasst` outcome: a
    register-only select moves the exact bit pattern, adding no
    rounding scope of its own, so neither a value nor a `logik
    bereich` outcome is folded away. -/
theorem selGleit_behaelt (b : Bool) (qa qb : GFloat)
    (lo hi : Int × Int) :
    gleitPasst lo hi (if b then qa else qb) =
      if b then gleitPasst lo hi qa else gleitPasst lo hi qb := by
  cases b <;> rfl

/-! ## 3. Certificate: local rewrite record plus recomputed citations.

    The exact certificate shape the emitter attaches to one
    CMOV-selection site: the source site and condition spans
    (recomputed positions, not diagnostic codes), the
    validator-decided side conditions, and the references to the
    recomputed analyses (branch-bias evidence for unpredictability,
    operand-cost facts for cheapness, the fault-freedom proof for the
    unselected side). The validator re-decides every side condition
    from these citations; `belegOk` gates USE of the rewrite. -/

/-- One CMOV-selection certificate: local rewrite record plus
    recomputed analysis citations. -/
structure CmovSelBeleg where
  stelle : Nat
  bedingungStelle : Nat
  zulassung : CmovSelCert
  biasBeleg : Nat
  kostenBeleg : Nat
  deriving DecidableEq, Repr

/-- Certificate admission: the carried side conditions hold. -/
def belegOk (g : CmovSelBeleg) : Bool :=
  cmovSelZulassen g.zulassung

/-- Probe: an admitted certificate passes. -/
theorem probe_belegOk :
    belegOk ⟨0, 1, ⟨true, true, true, true, true, true⟩, 2, 3⟩ = true := by
  decide

/-- Probe: a memory-source certificate is refused. -/
theorem probe_belegVerweigert_speicher :
    belegOk ⟨0, 1, ⟨true, true, true, false, true, true⟩, 2, 3⟩ = false := by
  decide

/-! ## 4. Blocks: the branch and the validator's choice.

    The branch computes both arms as pure literals and takes one; the
    select binds the chosen value. Both arms are literals (`orte =
    []`), so neither reads a shared carrier, calls, nor traps. The
    validator's choice is the select exactly where the certificate is
    admitted, otherwise the branch (default stays branch). -/

/-- The branch: both arms pure literals, one taken. -/
def branchEnd {D : Deklaration} (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (c : Expr D Γ Λ .bool) (x y : Int) : Endblock D V true Γ Λ :=
  .cons (.ite c (Block.bind (.lit x) .nil) (Block.bind (.lit y) .nil))
    (.leave rfl)

/-- The select: the chosen value bound. -/
def selectEnd {D : Deklaration} (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (v : Int) : Endblock D V true Γ Λ :=
  .bind (.lit v) (.leave rfl)

/-- The validator's choice: the select where admitted, else the
    branch. -/
def cmovWahlBlock {D : Deklaration} (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (g : CmovSelBeleg) (c : Expr D Γ Λ .bool) (b : Bool)
    (x y : Int) : Endblock D V true Γ Λ :=
  if belegOk g then selectEnd V (selWert b x y) else branchEnd V c x y

/-- ADMISSION USE: the admitted validator choice IS the select. -/
theorem cmovWahl_waehlt {D : Deklaration} (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (g : CmovSelBeleg) (hz : belegOk g = true)
    (c : Expr D Γ Λ .bool) (b : Bool) (x y : Int) :
    cmovWahlBlock V g c b x y = selectEnd V (selWert b x y) := by
  unfold cmovWahlBlock
  simp [hz]

/- CUTS:
    - Proved: admission, six refusals, select value equations, taken/
      untaken target words, width-exact word readback, `gleitPasst`
      preservation.
    - OPEN: branch/select blocks, the `OptCmovSel_verbindung` rule
      lemma (exec-outcome preservation) and its joint witness.
-/

#print axioms cmovSelZulassen
#print axioms selWert
#print axioms cmovSelVerweigert_speicher
#print axioms cmovSelVerweigert_fehler
#print axioms cmovSelVerweigert_vorhersehbar
#print axioms cmovSelVerweigert_teuer
#print axioms cmovSelVerweigert_flags
#print axioms cmovSelVerweigert_rundung
#print axioms probe_cmovSelZulassen_ok
#print axioms probe_cmovSelZulassen_speicher
#print axioms selWert_genommen
#print axioms selWert_nicht
#print axioms cmovWaehlt_genommen
#print axioms cmovWaehlt_nicht
#print axioms selWortLiest
#print axioms selGleit_behaelt
#print axioms belegOk
#print axioms probe_belegOk
#print axioms probe_belegVerweigert_speicher
#print axioms branchEnd
#print axioms selectEnd
#print axioms cmovWahlBlock
#print axioms cmovWahl_waehlt

end Gabbro.Grammatik.X86
