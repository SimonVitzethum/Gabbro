module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Logik.Ruf.FremdRuf.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- The read-back count `0` as an answer. -/
def fdW0 : ErgVal fdD (fdD.aerg fdRead) := ⟨0, by decide, by decide⟩

/-- The read call environment, carrying descriptor `3`. -/
def fdRho3 : Env fdD (fdD.aparams fdRead) :=
  Env.cons (⟨3, by decide, by decide⟩ : Wert fdD (.int 0 7)) Env.nil

/-- The open fit at the witness call site. -/
theorem fdFitO : einpassenErg fdO.zeiger (fdD.aerg fdOpen)
    (fdO.wirkt fdOpen fdWelt0 Env.nil).2 = some fdV3 := by
  have hred : einpassenErg fdO.zeiger (fdD.aerg fdOpen)
        (fdO.wirkt fdOpen fdWelt0 Env.nil).2
        = einpassen (D := fdD) fdO.zeiger (.int 0 7) 3 := rfl
  rw [hred]
  simp only [einpassen]
  split
  next hcond => rfl
  next hcond =>
    have hpos : (0 : Int) ≤ (3 : Int) ∧ (3 : Int) ≤ (7 : Int) := by decide
    exact absurd hpos hcond

/-- The read fit at the witness call site: after the open call the
    slot still reads `0`. -/
theorem fdFitR : einpassenErg fdO.zeiger (fdD.aerg fdRead)
    (fdO.wirkt fdRead (fdO.wirkt fdOpen fdWelt0 Env.nil).1 fdRho3).2
    = some fdW0 := by
  have hred : einpassenErg fdO.zeiger (fdD.aerg fdRead)
        (fdO.wirkt fdRead (fdO.wirkt fdOpen fdWelt0 Env.nil).1 fdRho3).2
        = einpassen (D := fdD) fdO.zeiger (.int 0 100) 0 := rfl
  rw [hred]
  simp only [einpassen]
  split
  next hcond => rfl
  next hcond =>
    have hpos : (0 : Int) ≤ (0 : Int) ∧ (0 : Int) ≤ (100 : Int) := by decide
    exact absurd hpos hcond

/-! ## 7. The reached run: one writing leaf -/

/-- Thread program: thread 1 fires the writing leaf, thread 0 rests. -/
def fdProg : PCProg fdD
  | 1 => [.leaf [] [Sum.inl ()]]
  | _ => []

/-- The start machine for the run. -/
def fdPC0 : GenMaschine fdD := GenStart fdSp0

/-- The evaluated index: `0`. -/
def fdK0 : Int := 0

/-- The evaluated value: `5` in range. -/
def fdV5 : Wert fdD (.int 0 100) := ⟨5, by decide, by decide⟩


end Gabbro.Grammatik
