module

public import Stage0.Senke.Bild.EmittedZiel
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Fremd

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke

variable {src : String} {K : Nat} {options : Profil.Options}

/-- The unit judged for an image with explicit concurrent roots. Its
    initial world, entry arguments and ordered root arguments are the
    ones serialized by the production emitter. -/
def Emitted.goalUnit (output : Emitted src K options) (Q : AxEns (declOf output.compiled.unit)) :
    Einheit (declOf output.compiled.unit) :=
  OldSource.einheitDer output.compiled.unit output.compiled.program Q output.sp0
    output.compiled.main output.args output.starts [] output.compiled.checkedDeclarations.val

theorem Emitted.goalUnit_starts (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) :
    (output.goalUnit Q).starts = ⟨output.compiled.main, output.args⟩ :: output.starts := rfl

/-- The invariant branch of the model's unit verdict follows from the
    compiler's writer check and the emitter's check on the serialized memory. -/
theorem Emitted.goal_invariants (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) :
    invariantenGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true := by
  have checked : CheckedInitialInvariants (output.goalUnit Q) output.lsA.1 := by
    have initial := output.initialInvariants
    unfold CheckedInitialInvariants at initial ⊢
    refine ⟨initial.1, ?_⟩
    have locks := initial.2
    unfold checkLockInitial at locks ⊢
    simpa only [initialUnit, Emitted.goalUnit, OldSource.einheitDer, OldSource.einheitVon,
      Emitted.lsA, Emitted.sp0, (Senke.initialWorld_memory _ output.initialValid).1] using locks
  apply checked.goal_verdict
  have accepted := OldSource.accepts_program _ _ _ output.compiled.accepted
    output.compiled.checkedDeclarations.property
  simp only [AkzeptiertX, Invarianten.Pruefer.invariantVCB, Bool.and_eq_true] at accepted
  exact accepted.2.1

/-- With an empty axiom family, the compiler supplies both branches of the
    goal checker's verdict on the declared initial state. -/
theorem Emitted.goal_axiomFree (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (empty : output.compiled.unit.axs.length = 0) :
    unitStartGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true := by
  refine Bool.and_eq_true_iff.mpr ⟨output.goal_invariants Q, ?_⟩
  have only : Q = axWahr (declOf output.compiled.unit) := by
    funext a
    exact False.elim ((Nat.not_lt_zero a.val) (empty ▸ a.isLt))
  subst Q
  exact output.axiomFreeLogic empty

/-- The precise logical start associated with the image. Missing thread
    positions are filled by the model's canonical idle thread. -/
abbrev Emitted.goalStart (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (live : Faden → Bool) :
    FadenMaschine (declOf output.compiled.unit).mitRuhe :=
  FadenStart (output.goalUnit Q).P.mitRuhe (speicherR (output.goalUnit Q).sp0)
    (initRuhe (output.goalUnit Q).starts) live

/-- Specialize the original goal theorem to the canonical program, start
    memory, arguments and pass limit of the emitted image. The compiler's
    success supplies structural acceptance. The checked unit verdict
    supplies the user duty, and A4 follows from canonical initialization. -/
theorem Emitted.zielsatz (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit))
    (_certifiable : OldSource.zertifizierbar output.compiled.unit = true)
    (dispatch : output.startPlan.dispatch = []) (runtime : output.compiled.unit.gestartet = [])
    (checked : nutzerPflichtGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true)
    (callSites : CallSitePflicht (output.goalUnit Q)) (posts : PostDeckt (output.goalUnit Q))
    (O : Orakel (declOf output.compiled.unit)) (binding : ForeignVertrag (output.goalUnit Q) O)
    (hardware : HardwareAnnahmenHw O Q)
    {live : Faden → Bool} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (reached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q live) state) :
    let E := output.goalUnit Q
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      (RufStartG E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts)) (E.arenen.map (·.mitRuhe)) state := by
  have start : unitStartGeprueftB (output.goalUnit Q) output.fsA.1 output.lsA.1 = true :=
    Bool.and_eq_true_iff.mpr ⟨output.goal_invariants Q, checked⟩
  have verdict := output.goal_checker_concurrent Q dispatch runtime start
  have duties : NutzerPflichtA (output.goalUnit Q) :=
    nutzerPflicht_of_geprueft output.fsA.2 output.lsA.2 checked
  exact gabbro_ziel akzeptiertX_pruefer _ (output.goalUnit Q) output.fsA output.lsA output.csA
    verdict duties callSites posts O binding hardware output.image.passes _ _
    (laufzeit_initRuhe (output.goalUnit Q)) live state reached

/-- Axiom-free production images carry the program-logic and start verdict
    into the goal theorem. All foreign obligations have an empty domain. -/
theorem Emitted.zielsatz_axiomFree (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (empty : output.compiled.unit.axs.length = 0)
    (certifiable : OldSource.zertifizierbar output.compiled.unit = true)
    (dispatch : output.startPlan.dispatch = []) (runtime : output.compiled.unit.gestartet = [])
    (O : Orakel (declOf output.compiled.unit)) (hardware : HardwareAnnahmenHw O Q)
    {live : Faden → Bool} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (reached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q live) state) :
    let E := output.goalUnit Q
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      (RufStartG E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts)) (E.arenen.map (·.mitRuhe)) state := by
  have absent (a : (declOf output.compiled.unit).Ax) :
      (declOf output.compiled.unit).axHerkunft a ≠ some AxOrigin.software :=
    False.elim ((Nat.not_lt_zero a.val) (empty ▸ a.isLt))
  exact output.zielsatz Q certifiable dispatch runtime
    (Bool.and_eq_true_iff.mp (output.goal_axiomFree Q empty)).2
    (callSitePflicht_ohne _ absent) (postDeckt_ohne _ absent) O (foreignVertrag_ohne _ O absent) hardware reached

/-- Successful CLI payload production identifies the exact certified
    output, also under the automatic stack-reserve policy. -/
theorem irBild_eq_output {output : Emitted src K options} {bytes : List Runner.B}
    (built : emit src K options = .ok output) (payload : irBild src K options = .ok bytes) :
    output.bytes = bytes := by
  rw [irBild, built] at payload
  exact Except.ok.inj payload

/-- The image's entry and every serialized root occupy the same ordered
    positions in the canonical logical start, even for duplicate functions. -/
theorem Emitted.goalStart_argument (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (i : Faden)
    (start : Σ f : (declOf output.compiled.unit).Fn,
      Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params f))
    (atPosition : (⟨output.compiled.main, output.args⟩ :: output.starts)[i]? = some start) :
    initRuhe (output.goalUnit Q).starts i = ⟨some start.1, envR start.2⟩ := by
  simp only [initRuhe, output.goalUnit_starts, atPosition]

end Gabbro.Stage0
