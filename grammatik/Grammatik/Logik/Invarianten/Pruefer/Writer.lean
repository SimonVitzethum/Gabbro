module

public import Grammatik.Logik.Invarianten.Pruefer.Locks
public import Grammatik.Speichermodell.Atomar.Invariants.AtomarRec

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer

open Frag Elim Elim.Korrekt VC Modell

variable {D : Deklaration}

/-- The invariant duties needed by the goal, uniformly in the hardware
    contract, execution budget and choice of shared atomic carriers. This is
    semantic evidence obtained from checked VCs, never a checker input. -/
def InvariantDuties (program : Programm D) (S : SperrInv D) (f : D.Fn) : Prop :=
  ∀ (passes : Nat) (Q : AxEns D) (shared : D.Tab ⊕ D.Glob → Prop),
    (∀ carrier, shared carrier → AtomarAusgenommen carrier) →
    InvGutSA program passes Q S shared f ∧ InvGutGrundA program passes Q S shared f

def atomicFreeB (program : Programm D) (f : D.Fn) : Bool :=
  (endblockOrteP program (program.rumpf f)).all fun carrier =>
    match carrier with
    | .inl _ => true
    | .inr name => !D.atomar name

theorem atomicFreeB_sound (program : Programm D) (f : D.Fn)
    (accepted : atomicFreeB program f = true) :
    ∀ carrier ∈ endblockOrteP program (program.rumpf f), ¬ AtomarAusgenommen carrier := by
  intro carrier member atomic
  obtain ⟨name, same, atom⟩ := atomic
  subst carrier
  have fact := List.all_eq_true.mp accepted (.inr name) member
  simp only [atom, Bool.not_true, Bool.false_eq_true] at fact

/-- Exact replay of the actual body, uniformly in handlers and atomic rely.
    This certificate says nothing about truth of requires or ensures. -/
def AtomicReplay (program : Programm D) (f : D.Fn) : Prop :=
  ∀ (S : SperrInv D) (O : Orakel D), RegLokal O → ∀ (U : Umwelt D)
    (A : AUmwelt D) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g)
    (shared : D.Tab ⊕ D.Glob → Prop), HavocA shared A →
    (∀ carrier, shared carrier → AtomarAusgenommen carrier) → ∀ world locals,
    execEndHA S O U A passes R (program.rumpf f) world locals =
      execEndH S O U passes R (program.rumpf f) world locals

/-- Keep the existing conservative gate, then admit the additional fragment
    only with the same exact model replay theorem. Direct atomic reads remain
    refused; a callee's logical contract is still checked independently.
    `endblockOrteP` includes callee metadata, while execution reads only call
    arguments. Empty metadata computes executable reads solely for the generic
    replay theorem; all checking and handlers retain the original program. -/
def atomicReplay? (program : Programm D) (f : D.Fn) : Option (PLift (AtomicReplay program f)) :=
  let replay (footprint : Programm D)
      (free : ∀ carrier ∈ endblockOrteP footprint (program.rumpf f),
        ¬ AtomarAusgenommen carrier) : AtomicReplay program f := by
    intro S O locality U A passes R shared atomic subset world locals
    exact Endblock.execHA_frei footprint S O U A passes R atomic locality.2 _
      (fun carrier member present => free carrier member (subset carrier present)) world locals
  if free : atomicFreeB program f = true then
    some ⟨replay program (atomicFreeB_sound program f free)⟩
  else
    let footprint : Programm D :=
      { program with
        requires := fun _ => .tru
        ensures := fun _ => .tru
        ptrVertrag := fun _ => { pre := .tru, post := .tru } }
    if free : (endblockOrteP footprint (program.rumpf f)).all
        (fun carrier => match carrier with
          | .inl _ => true
          | .inr name => !D.atomar name) = true then
      some ⟨replay footprint (by
        intro carrier member atomic
        obtain ⟨name, same, atom⟩ := atomic
        subst carrier
        have fact := List.all_eq_true.mp free (.inr name) member
        simp only [atom, Bool.not_true, Bool.false_eq_true] at fact)⟩
    else none

/-- If requires cannot be translated here, check the invariant writer under
    true. The separate contract gate still refuses unsupported requires;
    forgetting its information never assumes an unproved fact. -/
def writerEntry (program : Programm D) (f : D.Fn) (locals : Env D (D.params f)) :
    { formula : LProp (Observation D) // ∀ world,
      ReqAmEintritt program f world locals → formula.denote (assignment world) } :=
  match translate (program.requires f) locals with
  | .ok encoded => ⟨encoded.payload, fun world requires => (encoded.bool_iff world).mp requires⟩
  | .error _ => ⟨.tru, fun _ _ => trivial⟩

/-- A local condition records the actual extended compiler result and decides
    its universally closed VC. Requires is translated, never assumed as an
    unproved ensures or as an invariant about arbitrary entry states. -/
def checkEnvironment (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (f : D.Fn)
    (post : InvariantFormula program (D.invs.filter (fun item => schuldet f item)))
    (locals : Env D (D.params f)) :
    Except Frag.Refusal (PLift (∀ (runtime : Runtime program (fun _ => []) S) world,
      ReqAmEintritt program f world locals →
      runtime.wpE (program.rumpf f) (EndFlow post.formula) world locals)) := do
  let entry := writerEntry program f locals
  let compiled ← Extended.compileWriter program (fun _ => []) (lockFormula S sources) budget
    none (program.rumpf f) locals post.formula
  if accepted : decideB (Extended.writerVC compiled entry.val .tru) (Extended.writerVC_closed compiled entry.val .tru) = true then
    return ⟨fun runtime world requires =>
      Extended.writerVC_wp_sound compiled entry.val .tru accepted runtime world
        (entry.property world requires) trivial⟩
  else .error (.unsupported "writer invariant VC is false; inspect writerCounterexample")

/-- An empty owed family needs no body analysis. Otherwise every parameter
    environment is checked. Atomic-reading writers are currently refused;
    this conservative restriction does not weaken the atomic rely. -/
def checkWriter (program : Programm D) (S : SperrInv D) (sources : LockSources S)
    (budget : VCBudget) (f : D.Fn) (checkLocks : Bool := false) :
    Except Frag.Refusal (PLift (InvariantDuties program S f)) := do
  if empty : (D.invs.filter (fun item => schuldet f item)).isEmpty = true ∧ checkLocks = false then
    return ⟨fun _ _ _ _ => by
      constructor <;>
        intro O frame locality contract U havoc A atomic R respects noPre world locals requires next value returned <;>
        intro item member owed
      all_goals
        have inside := List.mem_filter.mpr ⟨member, owed⟩
        rw [List.isEmpty_iff.mp empty.1] at inside
        exact False.elim (List.not_mem_nil inside)⟩
  else
    if let some replay := atomicReplay? program f then
      let post ← invariantFormula program (D.invs.filter (fun item => schuldet f item))
      let domain ← environments (D := D) budget.expansion (D.params f)
      let checked ← collect domain.values
        (fun locals => ∀ (runtime : Runtime program (fun _ => []) S) world,
          ReqAmEintritt program f world locals →
          runtime.wpE (program.rumpf f) (EndFlow post.formula) world locals)
        (checkEnvironment program S sources budget f post)
      return ⟨fun passes Q shared subset => by
        constructor <;>
          intro O frame locality contract U havoc A atomic R respects noPre world locals requires next value returned
        all_goals
          let runtime : Runtime program (fun _ => []) S :=
            { oracle := O, passes := passes, calls := R
              evidence := frameOnlyEvidence program R respects
              environment := U, havoc := havoc }
          have valid := checked.down locals (domain.complete locals) runtime world requires
          rw [replay.down S O locality U A passes R shared atomic subset] at returned
          change EndFlow post.formula (execEndH S O U passes R (program.rumpf f) world locals) at valid
          rw [returned] at valid
          intro item member owed
          exact (post.correct next).mp valid item (List.mem_filter.mpr ⟨member, owed⟩)⟩
    else .error (.unsupported "invariant writer reads atomic memory outside the checked VC fragment")

end Gabbro.Grammatik.Invarianten.Pruefer
