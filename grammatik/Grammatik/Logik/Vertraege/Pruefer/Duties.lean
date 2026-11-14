module

public import Grammatik.Logik.Vertraege.Pruefer.Decision

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC Invarianten.Pruefer

variable {D : Deklaration} {program : Programm D} {S : SperrInv D}

/-- Generic handler filtering preserves all existing return/frame guarantees.
    A filtered call may stop but cannot manufacture a normal answer. -/
theorem respectsGate
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (respects : RespektiertRahmen program calls)
    (gate : ∀ f : D.Fn, World D → Env D (D.params f) → Bool)
    (error : D.Fn → Logik D) :
    RespektiertRahmen program
      (fun f world locals => if gate f world locals then calls f world locals else .logik (error f)) := by
  constructor
  · intro f world locals requires next value returned
    split at returned
    · exact respects.1 f world locals requires next value returned
    · cases returned
  · intro f world locals next value returned
    split at returned
    · exact respects.2 f world locals next value returned
    · cases returned

/-- P20's atomic-freedom gate transports the stronger WP to the rely
    semantics. No atomic read is silently treated as a sequential read. -/
theorem checkedEnvironment_atomic (policy : CallPolicy program) (f : D.Fn)
    (locals : Env D (D.params f)) (checked : CheckedEnvironment (S := S) policy f locals) (free : atomicFreeB program f = true)
    (shared : D.Tab ⊕ D.Glob → Prop) (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier)
    (O : Orakel D) (local : RegLokal O) (passes : Nat)
    (U : Umwelt D) (havoc : HavocOk S U) (A : AUmwelt D) (atomic : HavocA shared A)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (respects : RespektiertRahmen program calls) (allowed : Logik D → Prop)
    (errors : ∀ g world locals, policy.holds g world locals → ∀ error,
      calls g world locals = .logik error → allowed error)
    (world : World D) (requires : ReqAmEintritt program f world locals) :
    EndPost program f world locals allowed
      (execEndHA S O U A passes calls (program.rumpf f) world locals) := by
  let runtime : Runtime program (fun _ => []) S :=
    { oracle := O, passes := passes, calls := calls
      evidence := frameOnlyEvidence program calls respects
      environment := U, havoc := havoc }
  have valid := checked runtime world allowed ⟨respects, errors⟩ requires
  have noShared : ∀ carrier ∈ endblockOrteP program (program.rumpf f), ¬ shared carrier :=
    fun carrier member present => atomicFreeB_sound program f free carrier member (subset carrier present)
  rw [Endblock.execHA_frei program S O U A passes calls atomic local.2 _ noShared]
  exact valid

theorem checkedExecution_atomic (policy : CallPolicy program) (f : D.Fn)
    (checked : CheckedExecution (S := S) policy f) (free : atomicFreeB program f = true)
    (shared : D.Tab ⊕ D.Glob → Prop) (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier)
    (O : Orakel D) (local : RegLokal O) (passes : Nat)
    (U : Umwelt D) (havoc : HavocOk S U) (A : AUmwelt D) (atomic : HavocA shared A)
    (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (respects : RespektiertRahmen program calls) (allowed : Logik D → Prop)
    (errors : ∀ g world locals, policy.holds g world locals → ∀ error,
      calls g world locals = .logik error → allowed error)
    (world : World D) (locals : Env D (D.params f)) (requires : ReqAmEintritt program f world locals) :
    EndPost program f world locals allowed
      (execEndHA S O U A passes calls (program.rumpf f) world locals) := by
  exact checkedEnvironment_atomic policy f locals (checked locals) free shared subset
    O local passes U havoc A atomic calls respects allowed errors world requires

/-- The contract part of (b), including call-site requires, value returns,
    owed invariant returns and absence of local logic stops, for every rely. -/
def ContractDuties (program : Programm D) (S : SperrInv D) (f : D.Fn) : Prop :=
  ∀ (passes : Nat) (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop),
    (∀ carrier, shared carrier → AtomarAusgenommen carrier) →
    KoerperGutSA program passes Q S shared f ∧
      InvGutSA program passes Q S shared f ∧ InvGutGrundA program passes Q S shared f

theorem contractDuties_of_execution (f : D.Fn)
    (checked : CheckedExecution (S := S) (requiresPolicy program) f)
    (free : atomicFreeB program f = true) : ContractDuties program S f := by
  intro passes Q shared subset
  have run := checkedExecution_atomic (requiresPolicy program) f checked free shared subset
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro O frame local hardware U havoc A atomic R respects noPre world locals requires
    constructor
    · intro next value returned
      have valid := run O local passes U havoc A atomic R respects (fun _ => True)
        (fun _ _ _ _ _ _ => trivial) world locals requires
      rw [returned] at valid
      exact valid.1
    · intro g returned
      have gated : RespektiertRahmen program (torRuf program R) :=
        respectsGate R respects (fun g world locals => wahr? (eval world (program.requires g) world locals))
          Logik.vorbedingung
      have valid := run O local passes U havoc A atomic (torRuf program R) gated
        (fun error => ∀ g, error ≠ Logik.vorbedingung g)
        (fun f world locals entry error reply => by
          have same : torRuf program R f world locals = R f world locals := if_pos entry
          rw [same] at reply
          exact noPre f world locals error reply)
        world locals requires
      rw [returned] at valid
      exact valid g rfl
  · intro O frame local hardware U havoc A atomic R respects noLogic world locals requires error returned
    have valid := run O local passes U havoc A atomic R respects (fun _ => False)
      (fun f world locals _ error reply => noLogic f world locals error reply) world locals requires
    rw [returned] at valid
    exact valid
  · intro O frame local hardware U havoc A atomic R respects noPre world locals requires next value returned
    have valid := run O local passes U havoc A atomic R respects (fun _ => True)
      (fun _ _ _ _ _ _ => trivial) world locals requires
    rw [returned] at valid
    exact valid.2
  · intro O frame local hardware U havoc A atomic R respects noPre world locals requires next reason returned
    have valid := run O local passes U havoc A atomic R respects (fun _ => True)
      (fun _ _ _ _ _ _ => trivial) world locals requires
    rw [returned] at valid
    exact valid

/-- The Bool-facing function check constructs every proof internally. -/
def checkFunction (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (hint : Option (QF (Observation D))) (f : D.Fn) :
    Except Refusal (PLift (ContractDuties program S f)) := do
  if free : atomicFreeB program f = true then
    let execution ← checkExecution program S (requiresPolicy program) sources budget hint f
    return ⟨contractDuties_of_execution f execution.down free⟩
  else .error (.unsupported "contract body reads atomic memory outside the checked VC fragment")

end Gabbro.Grammatik.Vertraege.Pruefer
