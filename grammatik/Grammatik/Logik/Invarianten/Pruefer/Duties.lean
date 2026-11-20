module

public import Grammatik.Logik.Invarianten.Pruefer.Unit
public import Grammatik.Zielsatz.Atomar.AtomarPflicht

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Invarianten.Pruefer

variable {D : Deklaration} [DecidableEq D.Fn]

/-- The remaining user logic. Table/group/global invariant proofs are absent.
    Semantic locks without optional expression evidence retain their initial
    invariant duty. Lock locality and absence of logic stops remain user logic;
    the checker never silently proves a semantic predicate it cannot reify. -/
structure NutzerLogikA (E : Einheit D) : Prop where
  bodies : ∀ passes f, KoerperGutSA E.P passes E.Q E.S (GeteiltA E.P E.ws) f
  lockLocal : SperrInvLokal E.S
  axiomLocal : AxEnsLokal E.Q
  startRequires : ∀ a ∈ E.starts ++ E.gestartet, ReqAmEintritt E.P a.1 (E.sp0.welt []) a.2
  opaqueLockInitial : ∀ lock, E.lockFormulas lock = none → E.S.inv lock E.sp0 = true

/-- Reconstruct the old premise (b) from checker facts and precisely the
    remaining logic duties. The statement of gabbro_ziel remains unchanged. -/
theorem nutzerPflichtA_of_geprueft {E : Einheit D} {functions : List D.Fn} {locks : List D.Lock}
    {budget : Invarianten.VC.VCBudget} (complete : ∀ f, f ∈ functions)
    (lockComplete : ∀ lock, lock ∈ locks)
    (checked : InvariantenGeprueft E functions locks budget) (logic : NutzerLogikA E) :
    NutzerPflichtA E := by
  refine ⟨⟨fun passes f => ⟨logic.bodies passes f,
    invGut_of_geprueft complete checked passes f⟩,
    logic.lockLocal, logic.axiomLocal⟩, ⟨?_, logic.startRequires⟩⟩
  obtain ⟨certificate, result⟩ := checked
  intro lock
  cases source : E.lockFormulas lock with
  | none => exact logic.opaqueLockInitial lock source
  | some formula =>
      exact certificate.lockInitial lock (lockComplete lock) (by simp only [source, Option.isSome_some])

/-- Start-memory truth of every declared invariant is a checker consequence,
    including invariants no function happens to owe. -/
theorem invariantenStart_of_geprueft {E : Einheit D} {functions : List D.Fn} {locks : List D.Lock}
    {budget : Invarianten.VC.VCBudget} (checked : InvariantenGeprueft E functions locks budget) :
    ∀ item ∈ D.invs, InvHaelt E.P item (E.sp0.welt []) := by
  obtain ⟨certificate, result⟩ := checked
  exact certificate.initial

end Gabbro.Grammatik.Zielsatz

namespace Gabbro.Grammatik.Invarianten.Pruefer

open Zielsatz

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}
  {functions : List D.Fn} {sources : LockSources S} {budget : VC.VCBudget}
  {hints : Vertraege.Pruefer.LoopHints D} {locks : List D.Lock}

theorem invariantVCB_invGut (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget hints locks = true)
    (passes : Nat) (Q : AxEns D) (f : D.Fn) :
    InvGutS program passes Q S f ∧ InvGutGrund program passes Q S f := by
  have facts := invariantVCB_invGutA complete accepted passes Q (fun _ => False)
    (fun _ impossible => False.elim impossible) f
  exact ⟨invGutS_of_A facts.1, invGutGrund_of_A facts.2⟩

/-- Reconstruct the existing SC duty from the checker certificate. Only the
    locality premises remain inputs; Spec itself is unchanged. -/
theorem logikPflicht_of_invariantVCB (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget hints locks = true)
    (Q : AxEns D)
    (locality : SperrInvLokal S ∧ AxEnsLokal Q) :
    LogikPflicht program S Q :=
  ⟨fun passes f => ⟨koerperGutS_of_A
      ((invariantVCB_sound complete accepted f passes Q (fun _ => False)
        (fun _ impossible => False.elim impossible)).1),
      invariantVCB_invGut complete accepted passes Q f⟩,
    locality⟩

/-- The same adapter preserves the atomic rely rather than replacing shared
    reads with sequential reads. Unsupported atomic-reading bodies refuse. -/
theorem logikPflichtA_of_invariantVCB (complete : ∀ f, f ∈ functions)
    (accepted : invariantVCB program S functions sources budget hints locks = true)
    (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier)
    (locality : SperrInvLokal S ∧ AxEnsLokal Q) :
    LogikPflichtA program S Q shared :=
  ⟨fun passes f => ⟨(invariantVCB_sound complete accepted f passes Q shared subset).1,
    invariantVCB_invGutA complete accepted passes Q shared subset f⟩, locality⟩

end Gabbro.Grammatik.Invarianten.Pruefer
