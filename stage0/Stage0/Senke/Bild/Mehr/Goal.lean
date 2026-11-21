module

public import Stage0.Senke.Bild.ImageGoal
public import Stage0.Senke.Bild.Mehr.PrivatePath
public import Stage0.Senke.Welt.Spans.IdleValue

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Mach Runner.Beweis

variable {src : String} {K : Nat} {options : Profil.Options}

/-- Inside a related private segment, every prefix of the emitted IR's
    TSO execution retains the full goal at the same committed GX state.
    This composes the standard goal theorem with buffered-store projection
    and the concrete relation to the machine state and its local frames. -/
theorem irBild_private_tso_zielsatz [Kern] {output : Emitted src K options}
    {bytes : List Runner.B} (built : emit src K options = .ok output)
    (payload : irBild src K options = .ok bytes)
    (Q : AxEns (declOf output.compiled.unit))
    (certifiable : OldSource.zertifizierbar output.compiled.unit = true)
    (dispatch : output.startPlan.dispatch = []) (runtime : output.compiled.unit.gestartet = [])
    (checked : unitStartGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true)
    (callSites : CallSitePflicht (output.goalUnit Q)) (posts : PostDeckt (output.goalUnit Q))
    (O : Orakel (declOf output.compiled.unit)) (binding : ForeignVertrag (output.goalUnit Q) O)
    (hardware : HardwareAnnahmenHw O Q)
    {live : Faden → Bool} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (sourceReached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q live) state)
    {runnerLayout : Runner.Beweis.Lay} {initial final : Cfg (TSO runnerLayout) (Res T)}
    (loaded : BytesAt initial.ms.1.m Runner.Prog.IMG bytes)
    {snapshots : Nat → Option Solo} {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe}
    {committed : Mem} {footprint : Nat → W → Prop}
    (rel : MTRel (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint initial.ms).1, initial.ths⟩ state snapshots positions committed)
    (blind : AlleBlind initial.ths)
    (access : ∀ {before after i},
      SCErreichbar runnerLayout ⟨projectSCState footprint initial.ms, initial.ths⟩ before →
      SCSchritt runnerLayout i before after → ∀ {s op k},
      snapshots i = some s → before.ths[i]? = some (some (.ask op k)) →
      (∀ addr, fussOp op addr → s.F addr) ∧
      (schreibtOp op = true → ∀ addr, fussOp op addr → s.Wr addr))
    (buffers : PrivateBuffers footprint initial.ms.1)
    (machineReached : TSOPrivateReachable runnerLayout footprint initial final) :
    let E := output.goalUnit Q
    WeltAt initial.ms.1.m output.image.Y.withIdle ((speicherR E.sp0).welt []) ∧
    ∃ updated, MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
        ⟨(projectSCState footprint final.ms).1, final.ths⟩ state updated positions committed ∧
      AlleBlind final.ths ∧
      ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe output.image.passes
        (GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
        (RufStartG E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts))
        (E.arenen.map (·.mitRuhe)) state := by
  obtain ⟨updated, rel', blind', _⟩ :=
    tso_private_runs_refine rel blind access buffers machineReached
  have imageLoaded : BytesAt initial.ms.1.m Runner.Prog.IMG output.bytes :=
    (irBild_eq_output built payload).symm ▸ loaded
  exact ⟨(output.loaded_initial_world imageLoaded).withIdle, updated, rel', blind',
    output.zielsatz Q certifiable dispatch runtime checked callSites posts O binding hardware sourceReached⟩

end Gabbro.Stage0
