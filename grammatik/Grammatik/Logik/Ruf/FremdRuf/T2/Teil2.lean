module

public import Grammatik.Logik.Ruf.FremdRuf.T1
public import Grammatik.Logik.Ruf.FremdRuf.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- ZEUGE: every premise of `fremdruf_gate_gilt_pre` holds jointly on the
    fixture with the BAD oracle -- frame, restricted premise, the read gate's
    declared effects, the caller's obligation at a well-formed read after
    the open (descriptor `3`), a fitting answer -- and the witness is
    non-degenerate: the same oracle breaks the full premise
    (`fdObad_nicht_voll`), the precondition is false at another call
    (`fdPflicht_verletzt`), and the open gate's own precondition held
    at the start world (the terminator stood) and fails after it (the
    marker overwrote it). -/
theorem fremdruf_gate_gilt_pre_zeuge :
    ∃ (g : GateData fdD) (σ : World fdD) (ρ : Env fdD (fdD.aparams fdRead))
      (v : ErgVal fdD (fdD.aerg fdRead)),
      GutO fdObad ∧ AxVertragOP fdPre fdQ fdObad ∧
      g.eff = fdD.aschreibt fdRead ∧ g.effG = fdD.agschreibt fdRead ∧
      AufruferPflicht fdPre fdRead σ ρ ∧
      einpassenErg fdObad.zeiger (fdD.aerg fdRead) (fdObad.wirkt fdRead σ ρ).2 = some v ∧
      ¬ AxVertragO fdQ fdObad ∧
      ¬ AufruferPflicht fdPre fdRead fdWelt0 fdRho5 ∧
      AufruferPflicht fdPre fdOpen fdWelt0 Env.nil ∧
      ¬ AufruferPflicht fdPre fdOpen fdWelt1 Env.nil := by
  refine ⟨fdGateRead, fdWelt1, fdRho3, fdW0, fdObad_gut, fdObad_vertragP,
    fdGateRead_eff, fdGateRead_effG, ?_, fdObadFitR, fdObad_nicht_voll,
    fdPflicht_verletzt, ?_, ?_⟩
  · show decide (fdKopf fdRho3 = 3) = true
    exact decide_eq_true rfl
  · show decide ((fdWelt0.slots () 1 ()).n = 0) = true
    exact decide_eq_true rfl
  · intro h
    have h' : decide ((fdWelt1.slots () 1 ()).n = 0) = true := h
    have h0 : (fdWelt1.slots () 1 ()).n = 0 := of_decide_eq_true h'
    have h5 : (fdWelt1.slots () 1 ()).n = 5 := fdO_open_marke fdWelt0 Env.nil
    omega

/-- ZEUGE for the bridge: its premises hold jointly on the bad oracle (the
    one the full premise refuses), so the re-dressed oracle meets premise
    (c) of `gabbro_ziel` in full, and on the well-formed witness read it
    answers exactly as the machine's oracle does. -/
theorem hardware_aus_vertragP_zeuge [RootNativeFloat.Hardware] :
    GutO fdObad ∧ RegLokal fdObad ∧ AxVertragOP fdPre fdQ fdObad ∧
      (∀ a, einpassenErg fdObad.zeiger (fdD.aerg a) (fdRaus a) = none) ∧
      ¬ AxVertragO fdQ fdObad ∧
      Zielsatz.HardwareAnnahmen (mitVorbedingung fdPre fdObad fdRaus) fdQ ∧
      (mitVorbedingung fdPre fdObad fdRaus).wirkt fdRead fdWelt1 fdRho3 =
        fdObad.wirkt fdRead fdWelt1 fdRho3 :=
  ⟨fdObad_gut, fdObad_regLokal, fdObad_vertragP, fdRaus_passt_nicht, fdObad_nicht_voll,
    hardware_aus_vertragP fdPre fdQ fdObad fdRaus fdObad_gut fdObad_regLokal
      fdObad_vertragP fdRaus_passt_nicht,
    mitVorbedingung_gleich fdPre fdObad fdRaus fdRead fdWelt1 fdRho3
      (show decide (fdKopf fdRho3 = 3) = true from decide_eq_true rfl)⟩

/-! ## 10. From single calls to call sequences (lane 262, OFFEN O23)

  `hardware_aus_vertragP` (§9) bridges one call: on a well-formed call the
  re-dressed oracle IS the machine's oracle (`mitVorbedingung_gleich`). What a
  gate client runs is a SEQUENCE of calls threading worlds -- open, then read
  in the world the open answered. This section lifts the coincidence to such
  sequences, at the oracle layer: if every call of the sequence meets the
  gate's precondition, folding the re-dressed oracle over the sequence gives
  the same worlds and raw answers as folding the machine's oracle.

  This is deliberately NOT a program run: no `Stmt`, no `execStmt`, no
  `bindAxiom` is involved, and nothing here is called a semantics. A machine
  run stepping through gate calls would need the F-machine residue shape
  (see CUTS). What is proved is the oracle-layer coincidence a run-level
  bridge stands on: under the caller's obligations at every call site, the two
  oracles agree on every call of the sequence. -/

/-- A sequence of oracle calls: each call names its gate and carries its own
    argument environment. The world is threaded, not stored: each call runs in
    the world the previous call answered. -/
def rufFolgeWirkt {D : Deklaration} (O : Orakel D) : World D →
    List (Σ a : D.Ax, Env D (D.aparams a)) → World D × List Int
  | σ, [] => (σ, [])
  | σ, ⟨a, ρ⟩ :: rest =>
    let (σ', w) := O.wirkt a σ ρ
    let (σ'', ws) := rufFolgeWirkt O σ' rest
    (σ'', w :: ws)


end Gabbro.Grammatik
