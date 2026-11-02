module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Duties
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures.Fixtures
open Uebersetze UebersetzeAllg UebersetzeAllg2 Zielsatz

def withMeasure (measure : UMeasure) : UProg :=
  { countdown with fns := [{function "countdown" "countdown" with decreases := some measure}] }

theorem duplicate_clause_zeuge :
    uMeasureClause [] [.drops (.variable "n"), .drops (.lit 0)] =
      .error "duplicate or ambiguous decreases clause" := by decide +kernel

theorem hidden_old_zeuge : uMeasureClause [] [.drops (.bin "+" (.lit 1) (.old (.variable "GLOBAL")))] =
    .error "old-state read in decreases" := by decide +kernel

theorem unsupported_call_zeuge : uMeasureClause [] [.drops (.bin "+" (.lit 1) (.call "helper" [.variable "n"]))] =
    .error "unsupported call in decreases" := by decide +kernel

theorem hidden_global_zeuge :
    (lowerMeasures (withMeasure (.bin "+" (.lit 1) (.variable "GLOBAL")))).toOption.isSome = false := by
  decide +kernel

theorem negative_measure_zeuge :
    (lowerMeasures (withMeasure (.un "-" (.lit 1)))).toOption.isSome = false := by decide +kernel

def unequalCycle : UProg :=
  { mutual with fns := [function "left" "right", {function "right" "left" with decreases := none}] }

/-- A missing clause in one member of an actual mutual cycle is not guessed from its parameters. -/
theorem differing_cycle_lengths_zeuge : (lowerAllg unequalCycle).toOption.isSome = false := by decide +kernel

theorem absence_zeuge :
    let unit := {acyclic with fns := [{function "leaf" "leaf" with body := [], decreases := none}]}
    (match lowerMeasures unit with | .ok measures => (measures.mass 0).isEmpty | .error _ => false) = true := by
  decide +kernel

def unchanged : UProg :=
  { tabs := [], locks := [], fns := [{function "stay" "stay" with body := [.call "stay" [.val (.param "n")]]}] }
def increasing : UProg :=
  { tabs := [], locks := [], fns := [{function "grow" "grow" with
      needs := [.cmp "==" (.param "n") (.lit 0)], body := [.call "grow" [.val (.lit 1)]]}] }

theorem unchanged_lowered : (lowerAllg unchanged).toOption.isSome = true := by decide +kernel
theorem increasing_lowered : (lowerAllg increasing).toOption.isSome = true := by decide +kernel

def unchangedP := program unchanged unchanged_lowered
def unchangedM := (exported unchanged unchanged_lowered).val
def increasingP := program increasing increasing_lowered
def increasingM := (exported increasing increasing_lowered).val

/-- Structural measure export does not pretend to prove descent: the gate rejects unchanged arguments. -/
theorem unchanged_argument_zeuge
    (R : ∀ f : (declOf unchanged).Fn, World (declOf unchanged) →
      Env (declOf unchanged) ((declOf unchanged).params f) → RufAusgang f)
    (state : World (declOf unchanged)) :
    massTor unchangedM.mass (zykS unchangedP [0] 0)
      (unchangedM.mass.wert 0 state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil)) R
      0 state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) = .logik (.abstieg 0) := by rfl

/-- Increasing the actual argument also fails the existing gate, despite successful structural export. -/
theorem increasing_argument_zeuge
    (R : ∀ f : (declOf increasing).Fn, World (declOf increasing) →
      Env (declOf increasing) ((declOf increasing).params f) → RufAusgang f)
    (state : World (declOf increasing)) :
    massTor increasingM.mass (zykS increasingP [0] 0)
      (increasingM.mass.wert 0 state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil)) R
      0 state (.cons (⟨1, by decide, by decide⟩ : Zahl 0 1) .nil) = .logik (.abstieg 0) := by rfl

/-- The unchanged-call program cannot discharge the semantic duty, irrespective of its contracts' oracle. -/
theorem unchanged_no_duty_zeuge (passes : Nat) (Q : AxEns (declOf unchanged))
    (S : SperrInv (declOf unchanged))
    (T : (declOf unchanged).Tab ⊕ (declOf unchanged).Glob → Prop)
    (state : World (declOf unchanged)) :
    ¬ MassPflicht unchangedP passes Q S T unchangedM.mass (zykS unchangedP [0]) 0 := by
  intro duty
  let O : Orakel (declOf unchanged) :=
    ⟨fun a => Fin.elim0 a, fun r => Fin.elim0 r, fun r => Fin.elim0 r,
      fun g => Fin.elim0 g, fun _ => none⟩
  let R : ∀ f : (declOf unchanged).Fn, World (declOf unchanged) →
      Env (declOf unchanged) ((declOf unchanged).params f) → RufAusgang f := fun _ _ _ => .logik .schleife
  have frame : RespektiertRahmen unchangedP R := by
    constructor
    · intro f σ ρ _ σ' v h; cases h
    · intro f σ ρ σ' v h; cases h
  have noDescent : OhneAbstieg R := by intro g σ ρ h bad; cases bad
  have noPre : OhneVorbedingung R := by intro g σ ρ e h g' bad; cases h; cases bad
  have bad := duty O (fun a => Fin.elim0 a)
    ⟨fun r => Fin.elim0 r, fun g => Fin.elim0 g⟩ (fun a => Fin.elim0 a)
    (fun L => Fin.elim0 L) (fun L => Fin.elim0 L) idA (havocA_id T)
    R frame noDescent noPre state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil)
    (by rfl) 0 (by decide +kernel)
  exact bad (by rfl)

/-- The increasing-call program also fails the actual duty from a legal entry argument. -/
theorem increasing_no_duty_zeuge (passes : Nat) (Q : AxEns (declOf increasing))
    (S : SperrInv (declOf increasing))
    (T : (declOf increasing).Tab ⊕ (declOf increasing).Glob → Prop)
    (state : World (declOf increasing)) :
    ¬ MassPflicht increasingP passes Q S T increasingM.mass (zykS increasingP [0]) 0 := by
  intro duty
  let O : Orakel (declOf increasing) :=
    ⟨fun a => Fin.elim0 a, fun r => Fin.elim0 r, fun r => Fin.elim0 r,
      fun g => Fin.elim0 g, fun _ => none⟩
  let R : ∀ f : (declOf increasing).Fn, World (declOf increasing) →
      Env (declOf increasing) ((declOf increasing).params f) → RufAusgang f := fun _ _ _ => .logik .schleife
  have frame : RespektiertRahmen increasingP R := by
    constructor
    · intro f σ ρ _ σ' v h; cases h
    · intro f σ ρ σ' v h; cases h
  have noDescent : OhneAbstieg R := by intro g σ ρ h bad; cases bad
  have noPre : OhneVorbedingung R := by intro g σ ρ e h g' bad; cases h; cases bad
  have bad := duty O (fun a => Fin.elim0 a)
    ⟨fun r => Fin.elim0 r, fun g => Fin.elim0 g⟩ (fun a => Fin.elim0 a)
    (fun L => Fin.elim0 L) (fun L => Fin.elim0 L) idA (havocA_id T)
    R frame noDescent noPre state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil)
    (by rfl) 0 (by decide +kernel)
  exact bad (by rfl)

/-- Source provenance, ordinary structural admission and the actual duty hold jointly. -/
theorem lowerExpression_denotes_zeuge (state : World (declOf countdown)) (n : Zahl 0 1) :
    elabU countdownItems = .ok countdown ∧
    AkzeptiertX countP (Cover.Differenz.sperrFamilie countdown) [0] [] [] [] = true ∧
    SourceTuple countdown 0 (countM.mass 0) ∧
    countM.mass.wert 0 state (.cons n .nil) = [n.n.toNat] ∧
    ∀ passes Q S T, MassPflicht countP passes Q S T countM.mass (zykS countP [0]) 0 :=
  ⟨countdown_origin_zeuge, countdown_accepted_zeuge, countM.source 0,
    countdown_value_zeuge state n, countdown_duty_zeuge⟩

/-- The source-tree encoding preserves a nontrivial arithmetic expression exactly. -/
theorem uMeasureSource_exact_zeuge :
    let source := SExpr.bin "+" (.variable "n") (.lit 1)
    let measure := UMeasure.bin "+" (.variable "n") (.lit 1)
    uMeasureSource source = .ok measure ∧ measure.source = source := ⟨rfl, rfl⟩

theorem lowerAllg_measures_zeuge :
    lowerMeasures countdown = .ok countM ∧
    cycleLengths countdown countP countM.mass = true ∧
    AkzeptiertX countP (Cover.Differenz.sperrFamilie countdown) [0] [] [] [] = true ∧
    ∀ passes Q S T, MassPflicht countP passes Q S T countM.mass (zykS countP [0]) 0 :=
  ⟨(exported countdown countdown_lowered).property, by decide +kernel,
    countdown_accepted_zeuge, countdown_duty_zeuge⟩

theorem lowerMeasures_denotes_zeuge :
    (∃ c : Component countdown 0, countM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf countdown)) (env : Env (declOf countdown) ((declOf countdown).params 0)),
        SourceValue (fnAt countdown 0) (fnAt countdown 0).measureConstants env (.variable "n")
          (eval initial c.2.1 state env).n) ∧
    AkzeptiertX countP (Cover.Differenz.sperrFamilie countdown) [0] [] [] [] = true ∧
    ∀ passes Q S T, MassPflicht countP passes Q S T countM.mass (zykS countP [0]) 0 :=
  ⟨lowerMeasures_denotes countdown countM 0 [] [.drops (.variable "n")] (.variable "n")
      (.variable "n") rfl rfl rfl,
    countdown_accepted_zeuge, countdown_duty_zeuge⟩

/-- Division over a positive denominator lowers with an empty footprint. -/
def divU : UProg := withMeasure (.bin "/" (.variable "n") (.lit 1))
theorem divLowered : (lowerAllg divU).toOption.isSome = true := by decide +kernel
def divM := (exported divU divLowered).val
theorem divSource : SourceTuple divU 0 (divM.mass 0) := divM.source 0
theorem divDenotes :
    ∃ c : Component divU 0, divM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf divU)) (env : Env (declOf divU) ((declOf divU).params 0)),
        SourceValue (fnAt divU 0) (fnAt divU 0).measureConstants env
          (.bin "/" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes divU divM 0 [] [.drops (.bin "/" (.variable "n") (.lit 1))]
    (.bin "/" (.variable "n") (.lit 1)) (.bin "/" (.variable "n") (.lit 1)) rfl rfl rfl

/-- A denominator that may be zero is refused, never guessed. -/
theorem div_zero_zeuge :
    (lowerMeasures (withMeasure (.bin "/" (.variable "n") (.lit 0)))).toOption.isSome = false := by
  decide +kernel

/-- A nonzero signed denominator still fails the entry nonnegativity gate when its
    quotient may go negative: the gate is not weakened for the signed branch. -/
theorem div_negative_gate_zeuge :
    (lowerMeasures (withMeasure (.bin "/" (.variable "n")
      (.bin "-" (.variable "n") (.lit 2))))).toOption.isSome = false := by
  decide +kernel

/-- Remainder over a positive denominator lowers with an empty footprint. -/
def remU : UProg := withMeasure (.bin "%" (.variable "n") (.lit 2))
theorem remLowered : (lowerAllg remU).toOption.isSome = true := by decide +kernel
def remM := (exported remU remLowered).val
theorem remSource : SourceTuple remU 0 (remM.mass 0) := remM.source 0
theorem remDenotes :
    ∃ c : Component remU 0, remM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf remU)) (env : Env (declOf remU) ((declOf remU).params 0)),
        SourceValue (fnAt remU 0) (fnAt remU 0).measureConstants env
          (.bin "%" (.variable "n") (.lit 2)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes remU remM 0 [] [.drops (.bin "%" (.variable "n") (.lit 2))]
    (.bin "%" (.variable "n") (.lit 2)) (.bin "%" (.variable "n") (.lit 2)) rfl rfl rfl

/-- A remainder over a denominator that may be zero is refused, never guessed. -/
theorem rem_zero_zeuge :
    (lowerMeasures (withMeasure (.bin "%" (.variable "n") (.lit 0)))).toOption.isSome = false := by
  decide +kernel

/-- Bitwise and over non-negative ranges lowers with an empty footprint. -/
def andU : UProg := withMeasure (.bin "&" (.variable "n") (.lit 1))
theorem andLowered : (lowerAllg andU).toOption.isSome = true := by decide +kernel
def andM := (exported andU andLowered).val
theorem andSource : SourceTuple andU 0 (andM.mass 0) := andM.source 0
theorem andDenotes :
    ∃ c : Component andU 0, andM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf andU)) (env : Env (declOf andU) ((declOf andU).params 0)),
        SourceValue (fnAt andU 0) (fnAt andU 0).measureConstants env
          (.bin "&" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes andU andM 0 [] [.drops (.bin "&" (.variable "n") (.lit 1))]
    (.bin "&" (.variable "n") (.lit 1)) (.bin "&" (.variable "n") (.lit 1)) rfl rfl rfl

/-- A bit operation over a negative range is refused, never guessed. -/
theorem and_negative_zeuge :
    (lowerMeasures (withMeasure (.bin "&" (.bin "-" (.lit 0) (.variable "n"))
      (.variable "n")))).toOption.isSome = false := by
  decide +kernel

/-- Bitwise or over non-negative ranges lowers with an empty footprint. -/
def orU : UProg := withMeasure (.bin "|" (.variable "n") (.lit 1))
theorem orLowered : (lowerAllg orU).toOption.isSome = true := by decide +kernel
def orM := (exported orU orLowered).val
theorem orSource : SourceTuple orU 0 (orM.mass 0) := orM.source 0
theorem orDenotes :
    ∃ c : Component orU 0, orM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf orU)) (env : Env (declOf orU) ((declOf orU).params 0)),
        SourceValue (fnAt orU 0) (fnAt orU 0).measureConstants env
          (.bin "|" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes orU orM 0 [] [.drops (.bin "|" (.variable "n") (.lit 1))]
    (.bin "|" (.variable "n") (.lit 1)) (.bin "|" (.variable "n") (.lit 1)) rfl rfl rfl

/-- A bitwise or over a negative range is refused, never guessed. -/
theorem or_negative_zeuge :
    (lowerMeasures (withMeasure (.bin "|" (.bin "-" (.lit 0) (.variable "n"))
      (.lit 1)))).toOption.isSome = false := by
  decide +kernel

/-- Bitwise xor over non-negative ranges lowers with an empty footprint. -/
def xorU : UProg := withMeasure (.bin "^" (.variable "n") (.lit 1))
theorem xorLowered : (lowerAllg xorU).toOption.isSome = true := by decide +kernel
def xorM := (exported xorU xorLowered).val
theorem xorSource : SourceTuple xorU 0 (xorM.mass 0) := xorM.source 0
theorem xorDenotes :
    ∃ c : Component xorU 0, xorM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf xorU)) (env : Env (declOf xorU) ((declOf xorU).params 0)),
        SourceValue (fnAt xorU 0) (fnAt xorU 0).measureConstants env
          (.bin "^" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes xorU xorM 0 [] [.drops (.bin "^" (.variable "n") (.lit 1))]
    (.bin "^" (.variable "n") (.lit 1)) (.bin "^" (.variable "n") (.lit 1)) rfl rfl rfl

/-- A bitwise xor over a negative range is refused, never guessed. -/
theorem xor_negative_zeuge :
    (lowerMeasures (withMeasure (.bin "^" (.bin "-" (.lit 0) (.variable "n"))
      (.lit 1)))).toOption.isSome = false := by
  decide +kernel

/-- Shift left over non-negative ranges lowers with an empty footprint. -/
def shlU : UProg := withMeasure (.bin "<<" (.variable "n") (.lit 1))
theorem shlLowered : (lowerAllg shlU).toOption.isSome = true := by decide +kernel
def shlM := (exported shlU shlLowered).val
theorem shlSource : SourceTuple shlU 0 (shlM.mass 0) := shlM.source 0
theorem shlDenotes :
    ∃ c : Component shlU 0, shlM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf shlU)) (env : Env (declOf shlU) ((declOf shlU).params 0)),
        SourceValue (fnAt shlU 0) (fnAt shlU 0).measureConstants env
          (.bin "<<" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes shlU shlM 0 [] [.drops (.bin "<<" (.variable "n") (.lit 1))]
    (.bin "<<" (.variable "n") (.lit 1)) (.bin "<<" (.variable "n") (.lit 1)) rfl rfl rfl

/-- A shift amount no type holds is refused, never guessed. -/
theorem shl_range_zeuge :
    (lowerMeasures (withMeasure (.bin "<<" (.variable "n") (.lit 4097)))).toOption.isSome = false := by
  decide +kernel

/-- Shift right over non-negative ranges lowers with an empty footprint. -/
def shrU : UProg := withMeasure (.bin ">>" (.variable "n") (.lit 1))
theorem shrLowered : (lowerAllg shrU).toOption.isSome = true := by decide +kernel
def shrM := (exported shrU shrLowered).val
theorem shrSource : SourceTuple shrU 0 (shrM.mass 0) := shrM.source 0
theorem shrDenotes :
    ∃ c : Component shrU 0, shrM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf shrU)) (env : Env (declOf shrU) ((declOf shrU).params 0)),
        SourceValue (fnAt shrU 0) (fnAt shrU 0).measureConstants env
          (.bin ">>" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes shrU shrM 0 [] [.drops (.bin ">>" (.variable "n") (.lit 1))]
    (.bin ">>" (.variable "n") (.lit 1)) (.bin ">>" (.variable "n") (.lit 1)) rfl rfl rfl

/-- A shift amount no type holds is refused, never guessed. -/
theorem shr_range_zeuge :
    (lowerMeasures (withMeasure (.bin ">>" (.variable "n") (.lit 4097)))).toOption.isSome = false := by
  decide +kernel

end Gabbro.Grammatik.Parser.Measures.Fixtures
