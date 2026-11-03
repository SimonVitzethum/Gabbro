module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T2.Teil2
@[expose] public section

namespace Gabbro.Grammatik.RequiredRangeWitness

/-- Reuse the existing nonempty declaration and its actual function parameter environment. -/
abbrev Context := rufDF.params rufCallerF

def rest : Block rufDF (vertragVon rufDF rufCallerF) false (.int 0 0 :: Context) [] [] := .nil

def literal (number : Int) : Expr rufDF Context [] (.int number number) := Expr.lit number

def body (number : Int) : Block rufDF (vertragVon rufDF rufCallerF) false Context [] [] :=
  .narrowRequired (literal number) 0 0 rest

/-- The exact block-head counterexample, with a real typed entry environment and memory. -/
def machine (number : Int) : RufMaschineG rufDF :=
  { speicher := spF,
    faeden := fun _ =>
      ⟨[], ⟨rufCallerF, rhoCallerF, spF.welt [],
        ⟨false, Context, [], rhoCallerF, .dann (body number) .leer⟩⟩, [], []⟩,
    lauf := [], start := spF.welt [] }

def read (number : Int) : World rufDF := ((machine number).weltVon 0).lese [] (literal number).orte

def zero : Wert rufDF (.int 0 0) := ⟨0, by decide, by decide⟩

/-- All premises hold together: the actual source value passes 0..0, the new G constructor
    fires, and its actual successor contains the narrowed value in the typed environment. -/
theorem required_zero_steps :
    (0 ≤ (eval (read 0) (literal 0) (read 0) rhoCallerF).n ∧
      (eval (read 0) (literal 0) (read 0) rhoCallerF).n ≤ 0) ∧
    ∃ next, RufSchrittG rufPF rufOF 0 (machine 0) 0 next ∧
      (next.faeden 0).kopf.rest =
        ⟨false, .int 0 0 :: Context, [], Env.cons zero rhoCallerF,
          .dann rest (.schrumpf .leer)⟩ := by
  have bounds : 0 ≤ (eval (read 0) (literal 0) (read 0) rhoCallerF).n ∧
      (eval (read 0) (literal 0) (read 0) rhoCallerF).n ≤ 0 := ⟨by decide, by decide⟩
  refine ⟨bounds, _, RufSchrittG.dannNarrowRequired (machine 0) 0 false Context [] [] 0 0 0 0
    (literal 0) rest .leer rhoCallerF rfl (read 0) rfl bounds [] rfl (by
      intro lock member
      cases member), ?_⟩
  rfl

/-- Out of range stays logical capacity failure. The new guard and hence PrueftG both fail;
    it is not a hardware, flag or budget stop. -/
theorem outside_capacity_and_guard :
    execBlock (V := vertragVon rufDF rufCallerF) rufOF 0 keinRuf (body 1)
      ((machine 1).weltVon 0) rhoCallerF = .logik .kapazitaet ∧
    ¬ RequiredRangePrueftG (machine 1) 0 ∧ ¬ PrueftG rufOF 0 (machine 1) 0 := by
  have rejected : ¬ RequiredRangePrueftG (machine 1) 0 := by
    intro guard
    have impossible := guard false Context [] [] rhoCallerF 1 1 0 0 (literal 1) rest .leer rfl
    exact (by decide : ¬ (1 : Int) ≤ 0) impossible.2
  exact ⟨rfl, rejected, fun checked => rejected checked.requiredRange⟩

end Gabbro.Grammatik.RequiredRangeWitness
