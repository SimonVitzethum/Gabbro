module

public import Grammatik.Logik.Ruf.FremdRuf.T2.Teil1Basis
import all Grammatik.Logik.Ruf.FremdRuf.T2.Teil1Basis

public import Grammatik.Logik.Ruf.FremdRuf.T1

@[expose] public section



namespace Gabbro.Grammatik
/-! ## 9. Argument preconditions: the caller's half of a gate contract

  Fix lane F5 (review G10 F5, G04 F2). `AxVertragO` quantifies over EVERY
  argument environment: the declared ensures must hold whatever the caller
  passes. A real gate's behaviour depends on well-formed arguments (a
  NUL-terminated path for `open`, a descriptor that is open for `read`), so
  under `AxVertragO` alone a CALLER bug is booked as a failed hardware
  assumption. This section splits the premise:

  * `AxPre` -- the gate's declared argument precondition (its `requires`),
    over the call-time world and the passed arguments;
  * `AxVertragOP Pre Q O` -- the hardware premise restricted to calls that
    meet it (weaker than `AxVertragO`: `axVertragOP_of_O`);
  * `AufruferPflicht Pre a σ ρ` -- the caller's obligation at one call site,
    user logic (the `V` obligation `gabbro obligations` counts at every call
    of a gate with `requires`).

  At a call that meets the caller's obligation the restricted premise
  delivers exactly what the full one did (`fremdruf_gate_gilt_pre`). And
  the goal theorem is not touched: from the restricted premise the machine's
  oracle is re-dressed as one that meets the FULL premise (c) of
  `gabbro_ziel` (`hardware_aus_vertragP`: ill-formed calls answer a raw
  word outside the declared result type) and that agrees with the machine's
  oracle on every well-formed call (`mitVorbedingung_gleich`).
  `Spec.lean` is unchanged. -/

/-- A per-gate argument precondition: the declared `requires`, over the
    world at the call and the passed arguments. -/
abbrev AxPre (D : Deklaration) := ∀ a : D.Ax, World D → Env D (D.aparams a) → Bool

/-- The hardware premise restricted to well-formed calls: whenever the
    caller met the gate's precondition and the raw answer fits the declared
    result type, the declared ensures holds. -/
def AxVertragOP {D : Deklaration} (Pre : AxPre D) (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
    Pre a σ ρ = true →
    einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ ρ).2 = some v → Q a (O.wirkt a σ ρ).1 v = true

/-- The caller's obligation at one call site: its arguments meet the gate's
    precondition. User logic, not hardware. -/
def AufruferPflicht {D : Deklaration} (Pre : AxPre D) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) : Prop :=
  Pre a σ ρ = true

/-- The restricted premise is weaker: every oracle meeting the full premise
    meets it, for every precondition. -/
theorem axVertragOP_of_O {D : Deklaration} (Pre : AxPre D) {Q : AxEns D} {O : Orakel D}
    (h : AxVertragO Q O) : AxVertragOP Pre Q O :=
  fun a σ ρ v _ hfit => h a σ ρ v hfit

/-- One gate call under the split premise: the caller's obligation plus the
    restricted hardware premise give the fitting answer's ensures, and the
    frame premise gives the gate-declared frame. Every premise is used:
    `hPflicht` and `hQ` give the ensures, `hO` the frame, `hEff`/`hEffG`
    restate it in the gate's own effect terms. -/
theorem fremdruf_gate_gilt_pre (g : GateData fdD) (a : fdD.Ax) (O : Orakel fdD)
    (Pre : AxPre fdD) (Q : AxEns fdD)
    (hO : GutO O) (hQ : AxVertragOP Pre Q O)
    (hEff : g.eff = fdD.aschreibt a) (hEffG : g.effG = fdD.agschreibt a)
    (σ : World fdD) (ρ : Env fdD (fdD.aparams a))
    (hPflicht : AufruferPflicht Pre a σ ρ)
    (v : ErgVal fdD (fdD.aerg a))
    (hfit : einpassenErg O.zeiger (fdD.aerg a) (O.wirkt a σ ρ).2 = some v) :
    Q a (O.wirkt a σ ρ).1 v = true ∧
    Rahmen g.eff g.effG σ (O.wirkt a σ ρ).1 := by
  refine ⟨hQ a σ ρ v hPflicht hfit, ?_⟩
  have hfr := (hO a σ ρ).1
  rw [hEff, hEffG]
  exact hfr

/-- The machine's oracle, re-dressed: the same answer world everywhere, the
    same raw answer on every well-formed call, and on an ill-formed call the
    raw word `raus a` (chosen outside the declared result type). -/
def mitVorbedingung {D : Deklaration} (Pre : AxPre D) (O : Orakel D) (raus : D.Ax → Int) :
    Orakel D :=
  { O with wirkt := fun a σ ρ =>
      ((O.wirkt a σ ρ).1, if Pre a σ ρ = true then (O.wirkt a σ ρ).2 else raus a) }

/-- On a well-formed call the re-dressed oracle IS the machine's oracle. -/
theorem mitVorbedingung_gleich {D : Deklaration} (Pre : AxPre D) (O : Orakel D)
    (raus : D.Ax → Int) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
    (h : AufruferPflicht Pre a σ ρ) :
    (mitVorbedingung Pre O raus).wirkt a σ ρ = O.wirkt a σ ρ := by
  have h' : Pre a σ ρ = true := h
  show ((O.wirkt a σ ρ).1, if Pre a σ ρ = true then (O.wirkt a σ ρ).2 else raus a) =
    O.wirkt a σ ρ
  rw [if_pos h']

/-- **The bridge to premise (c) of `gabbro_ziel`.** Frame, register
    locality and the restricted ensures of the machine's oracle, plus raw
    words outside every declared result type, give the FULL hardware
    premise `HardwareAnnahmen` for the re-dressed oracle. The ill-formed
    calls are exactly the ones whose answers no longer fit. -/
theorem hardware_aus_vertragP [RootNativeFloat.Hardware] {D : Deklaration} (Pre : AxPre D) (Q : AxEns D) (O : Orakel D)
    (raus : D.Ax → Int)
    (hO : GutO O) (hR : RegLokal O) (hQ : AxVertragOP Pre Q O)
    (hraus : ∀ a, einpassenErg O.zeiger (D.aerg a) (raus a) = none) :
    Zielsatz.HardwareAnnahmen (mitVorbedingung Pre O raus) Q := by
  refine ⟨fun a σ ρ => hO a σ ρ, hR, ?_, inferInstance⟩
  intro a σ ρ v hfit
  by_cases hp : Pre a σ ρ = true
  · have e := mitVorbedingung_gleich Pre O raus a σ ρ hp
    rw [e] at hfit ⊢
    exact hQ a σ ρ v hp hfit
  · have hn : ((mitVorbedingung Pre O raus).wirkt a σ ρ).2 = raus a := by
      show (if Pre a σ ρ = true then (O.wirkt a σ ρ).2 else raus a) = raus a
      rw [if_neg hp]
    have hz : (mitVorbedingung Pre O raus).zeiger = O.zeiger := rfl
    rw [hn, hz, hraus a] at hfit
    exact absurd hfit (by simp only [reduceCtorEq, not_false_eq_true])

/-! ### The fixture's preconditions, and an oracle only the split premise admits -/

/-- The descriptor a read call passes. -/
def fdKopf : Env fdD (fdD.aparams fdRead) → Int
  | .cons w _ => (w : Zahl 0 7).n

/-- The fixture's gate preconditions. `open`: the terminator of the path
    frame stands -- slot `1` reads `0` (the analog of example 149's
    `path_nul_terminated`; the open gate itself overwrites it with its
    marker `5`, so a second open without a fresh terminator is ill-formed).
    `read`: the descriptor passed is the one the open gate hands out (`3`). -/
def fdPre : AxPre fdD
  | true, σ, _ => decide ((σ.slots () 1 ()).n = 0)
  | false, _, ρ => decide (fdKopf ρ = 3)

/-- An oracle that keeps its contract on well-formed calls only: an open or
    a read with the handed-out descriptor answers as `fdO`; a read with any
    OTHER descriptor answers the slot value plus one -- the kernel's
    garbage for a caller's bug. -/
def fdObad : Orakel fdD where
  wirkt
    | true, σ, ρ => fdO.wirkt true σ ρ
    | false, σ, ρ => ((fdO.wirkt false σ ρ).1,
        if fdKopf ρ = 3 then (fdO.wirkt false σ ρ).2 else (σ.slots () 0 ()).n + 1)
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- The bad oracle keeps the frames: its answer worlds are `fdO`'s. -/
theorem fdObad_gut : GutO fdObad := by
  intro a σ ρ
  cases a with
  | true => exact fdO_gut true σ ρ
  | false => exact fdO_gut false σ ρ

/-- The bad oracle meets the RESTRICTED premise: on every well-formed call
    it answers as `fdO`, which meets the full one. -/
theorem fdObad_vertragP : AxVertragOP fdPre fdQ fdObad := by
  intro a σ ρ v hp hfit
  cases a with
  | true => exact fdQ_vertrag true σ ρ v hfit
  | false =>
    have h3 : fdKopf ρ = 3 := of_decide_eq_true hp
    have e : fdObad.wirkt false σ ρ = fdO.wirkt false σ ρ := by
      show ((fdO.wirkt false σ ρ).1,
          if fdKopf ρ = 3 then (fdO.wirkt false σ ρ).2 else (σ.slots () 0 ()).n + 1) =
        fdO.wirkt false σ ρ
      rw [if_pos h3]
    rw [e] at hfit ⊢
    exact fdQ_vertrag false σ ρ v hfit

/-- A read call with descriptor `5`: not the handed-out one. -/
def fdRho5 : Env fdD (fdD.aparams fdRead) :=
  Env.cons (⟨5, by decide, by decide⟩ : Wert fdD (.int 0 7)) Env.nil

/-- The ill-formed read breaks the caller's obligation. -/
theorem fdPflicht_verletzt : ¬ AufruferPflicht fdPre fdRead fdWelt0 fdRho5 := by
  intro h
  have h' : decide (fdKopf fdRho5 = 3) = true := h
  have h5 : fdKopf fdRho5 = 3 := of_decide_eq_true h'
  have e : fdKopf fdRho5 = 5 := rfl
  omega

/-- **The split is load-bearing.** The bad oracle does NOT meet the full
    premise: its answer to the ill-formed read (`1`, while slot `0` reads
    `0`) fits and breaks the ensures. Under `AxVertragO` alone this caller
    bug would be the hardware's; under the split it is the caller's
    (`fdPflicht_verletzt`), and the hardware premise holds
    (`fdObad_vertragP`). -/
theorem fdObad_nicht_voll : ¬ AxVertragO fdQ fdObad := by
  intro h
  have hred : einpassenErg fdObad.zeiger (fdD.aerg fdRead)
      (fdObad.wirkt fdRead fdWelt0 fdRho5).2
      = einpassen (D := fdD) fdObad.zeiger (.int 0 100) 1 := rfl
  have hfit : einpassenErg fdObad.zeiger (fdD.aerg fdRead)
      (fdObad.wirkt fdRead fdWelt0 fdRho5).2
      = some (⟨1, by decide, by decide⟩ : Wert fdD (.int 0 100)) := by
    rw [hred]
    simp only [einpassen]
    split
    next hcond => rfl
    next hcond =>
      have hpos : (0 : Int) ≤ (1 : Int) ∧ (1 : Int) ≤ (100 : Int) := by decide
      exact absurd hpos hcond
  have hq := h fdRead fdWelt0 fdRho5 _ hfit
  have hq' : decide ((1 : Int) = (fdSp0.slots () 0 ()).n) = true := hq
  have h1 : (1 : Int) = (fdSp0.slots () 0 ()).n := of_decide_eq_true hq'
  have h0 : (fdSp0.slots () 0 ()).n = 0 := rfl
  omega

/-- The raw word the re-dressed oracle answers on an ill-formed call:
    `101`, outside both declared result types. -/
def fdRaus : fdD.Ax → Int := fun _ => 101

/-- `101` fits neither declared result type. -/
theorem fdRaus_passt_nicht (a : fdD.Ax) :
    einpassenErg fdObad.zeiger (fdD.aerg a) (fdRaus a) = none := by
  cases a with
  | true =>
    show einpassen (D := fdD) fdObad.zeiger (.int 0 7) 101 = none
    simp only [einpassen]
    split
    next hcond => exact absurd hcond.2 (by decide)
    next => rfl
  | false =>
    show einpassen (D := fdD) fdObad.zeiger (.int 0 100) 101 = none
    simp only [einpassen]
    split
    next hcond => exact absurd hcond.2 (by decide)
    next => rfl

/-- The fixture has no registers and no globals: register locality holds
    vacuously for every oracle over it. -/
theorem fdObad_regLokal : RegLokal fdObad :=
  ⟨fun r => (nomatch r), fun g => (nomatch g)⟩

/-- The world after the open call at the witness site. -/
def fdWelt1 : World fdD := (fdObad.wirkt fdOpen fdWelt0 Env.nil).1

/-- The read fit of the bad oracle at the well-formed witness call: the
    slot still reads `0`. -/
theorem fdObadFitR : einpassenErg fdObad.zeiger (fdD.aerg fdRead)
    (fdObad.wirkt fdRead fdWelt1 fdRho3).2 = some fdW0 := by
  have hred : einpassenErg fdObad.zeiger (fdD.aerg fdRead)
        (fdObad.wirkt fdRead fdWelt1 fdRho3).2
        = einpassen (D := fdD) fdObad.zeiger (.int 0 100) 0 := rfl
  rw [hred]
  simp only [einpassen]
  split
  next hcond => rfl
  next hcond =>
    have hpos : (0 : Int) ≤ (0 : Int) ∧ (0 : Int) ≤ (100 : Int) := by decide
    exact absurd hpos hcond

end Gabbro.Grammatik
