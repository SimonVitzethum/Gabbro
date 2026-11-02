module
public import Grammatik.Korpus.Zeugnis.Zeugnis.T2.Teil1Basis
import all Grammatik.Korpus.Zeugnis.Zeugnis.T2.Teil1Basis

public import Grammatik.Korpus.Zeugnis.Zeugnis.T1

@[expose] public section



namespace Gabbro.Grammatik
/-! ## The test world: one concrete declaration for the decide probes

    `decide` needs closed terms: it evaluates the table, and evaluation
    cannot look through an abstract `D`. So the probes below pin ONE world --
    one guarded global of `0 .. 7`, one guarded table with one int field of
    `0 .. 10` over eleven rows, one lock that guards both, one nullary
    procedure and one unary one. Every probe names this world explicitly;
    nothing about the soundness theorems depends on it. -/

/-- Nullary test signature: no params, no result, no reasons, no rights,
    no marks, no held locks. -/
def TestSig0 : Signatur Unit Unit Unit Empty :=
  ⟨[], none, 0, [], fun _ => false, fun _ => false, [], [], none, {}⟩

/-- Unary test signature: one int param -- for the negative call probe. -/
def TestSig1 : Signatur Unit Unit Unit Empty :=
  ⟨[.int 0 5], none, 0, [], fun _ => false, fun _ => false, [], [], none, {}⟩

/-- A one-glob, one-table, one-lock test world: every access is guarded. -/
def TestD : Deklaration where
  Tab := Unit
  count := fun _ => 11
  Feld := fun _ => Unit
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => true
  tabNr := fun _ => some ()
  Glob := Unit
  gtyp := fun _ => .int 0 7
  nutzlast := fun _ => []
  atomar := fun _ => true
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Unit
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  stufen := fun e => e.elim
  braucht := fun _ => [.inl ()]
  gbraucht := fun _ => [.inl ()]
  eigner := fun _ => []
  Fn := Bool
  sig := fun | false => 0 | true => 1
  sigNr := fun | 0 => TestSig0 | 1 => TestSig1 | _ => TestSig0
  eigner_nie_erzeugt := fun _ _ m _ _ => m.elim
  Inv := Empty
  traeger := fun e => e.elim
  invs := []
  Ax := Empty
  aparams := fun e => e.elim
  aerg := fun e => e.elim
  aschreibt := fun e => e.elim
  agschreibt := fun e => e.elim
  Reg := Empty
  rtyp := fun e => e.elim
  rklasse := fun e => e.elim
  spiegel := fun e => e.elim
  rzusage := fun e => e.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g h => by simp only [Bool.false_eq_true] at h

/-- Procedure contract: no result, holds nothing, produces nothing. -/
def TestV : Vertrag TestD :=
  ⟨fun _ => true, fun _ => true, none, 0, [], [], none, {}⟩

/-- Value contract: returns an int in `1 .. 1`. -/
def TestVw : Vertrag TestD :=
  ⟨fun _ => true, fun _ => true, some (.int 1 1), 0, [], [], none, {}⟩

/-- The nullary call fits the procedure contract at empty resources: no
    rights to check (both write maps are `false`), nothing consumed, and the
    held-lock check is vacuous in both directions over the empty lists. -/
theorem TestHp : RufPasst TestD TestV (TestD.signatur false) [] where
  hw := fun t h => by simp only [TestD, TestSig0, TestSig1, Deklaration.signatur, Bool.false_eq_true] at h
  hg := fun g h => by simp only [TestD, TestSig0, TestSig1, Deklaration.signatur, Bool.false_eq_true] at h
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := RufPasst.hh_von fun L => iff_of_false List.not_mem_nil List.not_mem_nil
  hx := RufPasst.hx_von fun L => iff_of_false List.not_mem_nil List.not_mem_nil
  ownerReady := OwnerFlow.empty_of_empty _

/-- Same fit for the unary callee: `RufPasst` never constrained the params,
    so the same vacuous proofs go through -- and the table still rejects the
    call, on `params = []`. -/
theorem TestHp1 : RufPasst TestD TestV (TestD.signatur true) [] where
  hw := fun t h => by simp only [TestD, TestSig0, TestSig1, Deklaration.signatur, Bool.false_eq_true] at h
  hg := fun g h => by simp only [TestD, TestSig0, TestSig1, Deklaration.signatur, Bool.false_eq_true] at h
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := RufPasst.hh_von fun L => iff_of_false List.not_mem_nil List.not_mem_nil
  hx := RufPasst.hx_von fun L => iff_of_false List.not_mem_nil List.not_mem_nil
  ownerReady := OwnerFlow.empty_of_empty _

/-! ## Witness pairs: acceptance and rejection, both by `decide` -/

/-- `1 + 2` printed as `(3, 3)`: Lean accepts the print. -/
example : GueltigAbleitung TestD [] [] (.add (.lit 1) (.lit 2)) 3 3 := by decide

/-- `5 / 2` printed as `(0, 5)`: nonneg dividend, positive divisor (M102). -/
example : GueltigAbleitung TestD [] [] (.div (.lit 5) (.lit 2)) 0 5 := by decide

/-- `5` widened to `0 .. 10`: a checked `weiter` in the safe direction. -/
example : GueltigAbleitung TestD [] [] (.wide 0 10 (.lit 5)) 0 10 := by decide

/-- MISMATCHED print: `1 + 2` claimed as `(0, 0)` -- provably not valid.
    This is the loud failure: no acceptance proof can be built from it. -/
example : ¬ GueltigAbleitung TestD [] [] (.add (.lit 1) (.lit 2)) 0 0 := by decide

/-- FORGED proof: `5 / 0` -- the divisor range admits zero, so the table
    yields no range at all. -/
example : ¬ GueltigAbleitung TestD [] [] (.div (.lit 5) (.lit 0)) 0 5 := by decide

/-- FORGED widening: `20` claimed in `0 .. 10` -- outside, no certificate. -/
example : ¬ GueltigAbleitung TestD [] [] (.wide 0 10 (.lit 20)) 0 10 := by decide

/-! ### CUT-1 and CUT-2 probes: signed division, bitwise, shifts -/

/-- `7 sdiv 2` printed as `(-7, 7)`: the divisor excludes zero (SG-3, second sentence). -/
example : GueltigAbleitung TestD [] [] (.sdiv (.lit 7) (.lit 2)) (-7) 7 := by decide

/-- FORGED proof: `7 sdiv 0` -- same claim as above, but the divisor admits zero. -/
example : ¬ GueltigAbleitung TestD [] [] (.sdiv (.lit 7) (.lit 0)) (-7) 7 := by decide

/-- `7 srem 2` printed as `(-1, 1)`: the remainder range comes from the DIVISOR. -/
example : GueltigAbleitung TestD [] [] (.srem (.lit 7) (.lit 2)) (-1) 1 := by decide

/-- FORGED proof: `7 srem 0` -- same claim as above, but the divisor admits zero. -/
example : ¬ GueltigAbleitung TestD [] [] (.srem (.lit 7) (.lit 0)) (-1) 1 := by decide

end Gabbro.Grammatik
