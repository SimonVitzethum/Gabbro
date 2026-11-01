module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T1
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- The leaf writes: the outcome is `.ok` with a changed world and the same
    environment. The world changes because `assignSlot` stores the parameter
    value 2 at slot 0 (was 0); the trace gains the write event. -/
theorem leafSF_mem (σ' : World rufDF) (ρ' : Env rufDF (rufDF.params rufIncF))
    (h : (execStmt (V := vertragVon rufDF rufIncF) rufOF 0 keinRuf leafSF
      rufWeltF rufRhoF) = Ausgang.ok σ' ρ') :
    σ'.slots () 0 () = (⟨2, by decide, by decide⟩ : Wert rufDF (.int 0 5)) ∧
      ρ' = rufRhoF := by
  have hrfl : (execStmt (V := vertragVon rufDF rufIncF) rufOF 0 keinRuf leafSF
      rufWeltF rufRhoF) =
      Ausgang.ok (D := rufDF) (V := vertragVon rufDF rufIncF) _ rufRhoF := rfl
  rw [hrfl] at h
  cases h
  refine ⟨rfl, rfl⟩

/-- Start memory: slot 0 holds 0 (the leaf will write 2). -/
def spF : Speicher rufDF :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => Empty.elim g⟩

/-- The caller-side rho: the entry value 2, transported to the caller
    params (same shape, `rufDF_params`). -/
def rhoCallerF : Env rufDF (rufDF.params rufCallerF) :=
  (rufDF_params rufCallerF).symm ▸ rufRhoF

def initF : Faden → Σ f : rufDF.Fn, Env rufDF (rufDF.params f) :=
  fun _ => ⟨rufCallerF, rhoCallerF⟩

theorem initF_rho : initF 0 =
    (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := by rfl

def M0F : RufMaschineF rufDF := RufStartF rufPF spF initF

/-- The start head is the caller body with the entry environment.
    Proved by unfolding the start definition and the init function
    (`rfl` fails: the `match` on `initF 0` needs the equation). -/
theorem M0F_kopf :
    (M0F.faeden 0).kopf.rest =
    ⟨false, rufDF.params rufCallerF,
     Signatur.anfang rufDF (rufDF.signatur rufCallerF),
     rhoCallerF, rufCallerRumpfF⟩ := by
  have hstart : (RufStartF (D := rufDF) rufPF spF initF).faeden 0 =
      (match initF 0 with
      | ⟨g', rho'⟩ =>
        (⟨[], (⟨g', rho', spF.welt [],
          ⟨false, rufDF.params g', Signatur.anfang rufDF (rufDF.signatur g'),
           rho', rufPF.rumpf g'⟩⟩ : RufRahmenF rufDF),
         [], [RufEreignisF.eintritt g' rho' (spF.welt [])]⟩ :
          RufFadenF rufDF)) := rfl
  have hif : initF 0 = (⟨rufCallerF, rhoCallerF⟩ :
      Σ f : rufDF.Fn, Env rufDF (rufDF.params f)) := by
    simp only [initF]
  have hM : M0F.faeden 0 =
      (⟨[], (⟨rufCallerF, rhoCallerF, spF.welt [],
        ⟨false, rufDF.params rufCallerF,
         Signatur.anfang rufDF (rufDF.signatur rufCallerF),
         rhoCallerF, rufPF.rumpf rufCallerF⟩⟩ : RufRahmenF rufDF),
       [], [RufEreignisF.eintritt rufCallerF rhoCallerF (spF.welt [])]⟩ :
        RufFadenF rufDF) := by
    simp only [M0F]
    rw [hstart, hif]
  have hrumpf : rufPF.rumpf rufCallerF = rufCallerRumpfF := rfl
  rw [hM, hrumpf]

/-- The start head function is the caller. -/
theorem M0F_fun : (M0F.faeden 0).kopf.f = rufCallerF := by rfl

/-- Caller params unfold to the single int (needed to align `rufArgsF`). -/
theorem callerParamsF : rufDF.params rufCallerF = [.int 0 5] :=
  rufDF_params rufCallerF


end Gabbro.Grammatik
