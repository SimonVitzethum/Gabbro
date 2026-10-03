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

/- CUTS:
    - Skeleton only: admission Bool, selected value. The refusal
      theorems, value/word/float lemmas, branch/select blocks, the
      `OptCmovSel_verbindung` rule lemma and its joint witness follow
      in small steps.
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

end Gabbro.Grammatik.X86
