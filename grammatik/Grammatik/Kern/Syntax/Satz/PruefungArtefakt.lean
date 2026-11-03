module

public import Grammatik.Kern.Syntax.Satz.PruefungGegenprobe

@[expose] public section

namespace Gabbro.Grammatik

/-- Measured acceptance binds the unique external probe and the exact selected
    image. `Gemessen` alone records a result, but does not compare image names. -/
def SondenNachweis (checks : List (CheckDecl D)) (c : CheckDecl D)
    (selectedImage : String) (artifact : SondenArtefakt)
    (status : ProbenStand) (report : CheckReport) : Prop :=
  (∃ text, SondenBindung checks c artifact.name text) ∧
    artifact.bild = selectedImage ∧ Gemessen c artifact status report

/-- The finite binding check includes membership, exact text/name and the
    absence of another check owning the external name. -/
def sondenBindungB (checks : List (CheckDecl D)) (c : CheckDecl D)
    (externalName : String) : Bool :=
  c.sonde.any (fun pair => decide (pair.1 = externalName)) &&
    checks.any (fun d => decide (d.name = c.name ∧ d.sonde = c.sonde)) &&
    checks.all (fun d => decide (d.name = c.name) ||
      decide (d.sonde.map Prod.fst ≠ some externalName))

/-- Image, mode, status and verdict are checked as data. Structural admission
    remains separate from whether an external test was actually run. -/
def sondenArtefaktB (c : CheckDecl D) (selectedImage : String)
    (artifact : SondenArtefakt) (status : ProbenStand) (report : CheckReport) : Bool :=
  decide (artifact.bild = selectedImage) &&
    decide (c.testbau = artifact.testbau) &&
    c.sonde.any (fun pair => decide (pair.1 = artifact.name)) &&
    decide (status = .durchgefallen) && !report.urteil

/-- Measured acceptance over a descriptor selected from the derived checks.
    The caller supplies membership to the soundness theorem below. -/
def sondenNachweisB (checks : List (CheckDecl D)) (c : CheckDecl D)
    (selectedImage : String) (artifact : SondenArtefakt)
    (status : ProbenStand) (report : CheckReport) : Bool :=
  sondenBindungB checks c artifact.name &&
    sondenArtefaktB c selectedImage artifact status report

/-- The executable evidence gate requires the actual unique binding, exact
    selected image, matching mode and an observed negative verdict. -/
theorem sondenNachweisB_sound (checks : List (CheckDecl D)) (c : CheckDecl D)
    (selectedImage : String) (artifact : SondenArtefakt)
    (status : ProbenStand) (report : CheckReport) (member : c ∈ checks)
    (accepted : sondenNachweisB checks c selectedImage artifact status report = true) :
    SondenNachweis checks c selectedImage artifact status report := by
  obtain ⟨bound, measured⟩ := Bool.and_eq_true.mp accepted
  cases identity : c.sonde with
  | none => simp [sondenBindungB, identity] at bound
  | some pair =>
    obtain ⟨externalName, text⟩ := pair
    have nameEq : externalName = artifact.name := by
      have first := (Bool.and_eq_true.mp (Bool.and_eq_true.mp bound).1).1
      simpa [sondenBindungB, identity] using first
    have others : checks.all (fun d => decide (d.name = c.name) ||
        decide (d.sonde.map Prod.fst ≠ some artifact.name)) = true :=
      (Bool.and_eq_true.mp bound).2
    have binding : SondenBindung checks c artifact.name text := by
      refine ⟨?_, member, ?_⟩
      · simpa [nameEq] using identity
      · intro d hd different
        have other := List.all_eq_true.mp others d hd
        simpa [different] using other
    have facts : artifact.bild = selectedImage ∧
        c.testbau = artifact.testbau ∧ status = .durchgefallen ∧
        report.urteil = false := by
      simpa [sondenArtefaktB, identity, nameEq, Bool.and_eq_true] using measured
    exact ⟨⟨text, binding⟩, facts.1, facts.2.2.1, facts.2.2.2,
      by simp [identity], facts.2.1, text, by simpa [nameEq] using identity⟩

/-- A changed image is stale even if name, source label and mode still match. -/
theorem sondenArtefaktB_stale (c : CheckDecl D) (selectedImage : String)
    (artifact : SondenArtefakt) (status : ProbenStand) (report : CheckReport)
    (stale : artifact.bild ≠ selectedImage) :
    sondenArtefaktB c selectedImage artifact status report = false := by
  simp [sondenArtefaktB, stale]

/-- The Prop rejects the same stale image, independent of the claimed result. -/
theorem sondenNachweis_stale (checks : List (CheckDecl D)) (c : CheckDecl D)
    (selectedImage : String) (artifact : SondenArtefakt)
    (status : ProbenStand) (report : CheckReport)
    (stale : artifact.bild ≠ selectedImage) :
    ¬ SondenNachweis checks c selectedImage artifact status report :=
  fun evidence => stale evidence.2.1

/-- A result with no bound check can never become measured acceptance. -/
theorem sondenNachweis_unbound (checks : List (CheckDecl D)) (c : CheckDecl D)
    (selectedImage : String) (artifact : SondenArtefakt)
    (status : ProbenStand) (report : CheckReport) (unbound : c.sonde = none) :
    ¬ SondenNachweis checks c selectedImage artifact status report := by
  rintro ⟨⟨text, binding⟩, _, _⟩
  have mismatch := binding.1
  rw [unbound] at mismatch
  cases mismatch

end Gabbro.Grammatik
