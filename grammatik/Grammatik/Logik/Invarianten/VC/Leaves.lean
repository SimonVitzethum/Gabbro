module

public import Grammatik.Logik.Invarianten.VC.Locks

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D}
variable {program : Programm D} {checked : D.Fn → List D.Inv}

structure CleanupFormula (S : SperrInv D) (locks : List D.Lock) where
  formula : QF (Observation D)
  correct : ∀ world, formula.denote (assignment world) ↔ scopesInvH S locks world = true

def cleanupFormula (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock)) :
    (locks : List D.Lock) → Except Frag.Refusal (CleanupFormula S locks)
  | [] => .ok
      { formula := .tru
        correct := fun _ => by simp [QF.denote, scopesInvH] }
  | lock :: locks => do
      let head ← facts lock
      let tail ← cleanupFormula facts locks
      return {
          formula := conj head.formula tail.formula
          correct := fun world => by
            rw [conj_denote, head.correct world, tail.correct world]
            simp only [scopesInvH, List.all_cons, Bool.and_eq_true] }

theorem assignment_cleanup (world : World D) (locks : List D.Lock) :
    assignment (locks.foldl World.gibt world) = assignment world := by
  induction locks generalizing world with
  | nil => rfl
  | cons lock locks ih =>
      exact (ih (world.gibt lock)).trans (assignment_gibt world lock)

/-- The straight-line rules use the same scalar substitution and call havoc
    as P18; the normal continuation may now depend on updated local values. -/
def leafCondition {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (budget : Nat) (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock))
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D Γ) :
    Except Frag.Refusal (StatementCondition program checked S code locals goals) :=
  match code with
  | .assignGlob name expression _ _ => do
      match h : goals.normal locals with
      | .error cause => .error cause
      | .ok normal => do
          let pre ← scalarWP expression locals (.glob name) normal
          return {
              formula := pre.formula
              sound := fun runtime world valid => by
                unfold Runtime.wpS
                simp only [execStmtH, Goals.holds, h, denotes]
                rw [assignment_schreibGlob]
                apply pre.sound
                rw [assignment_lese]
                exact valid }
  | .assignSlot table field index expression _ _ => do
      match h : goals.normal locals with
      | .error cause => .error cause
      | .ok normal => do
          let encodedIndex ← translate index locals
          let offset ← encodedIndex.constantIndex
          let pre ← scalarWP expression locals (.slot table field offset.val) normal
          return {
              formula := pre.formula
              sound := fun runtime world valid => by
                unfold Runtime.wpS
                simp only [execStmtH, Goals.holds, h, denotes]
                rw [assignment_schreibSlot, offset.property]
                apply pre.sound
                rw [assignment_lese]
                exact valid }
  | .assignVar name expression => mutableCondition budget name expression locals goals
  | .call f args hp hr => do
      match h : goals.normal locals with
      | .error cause => .error cause
      | .ok normal => do
          let known ← invariantFormula program (checked f)
          return {
              formula := callWP f known.formula normal
              sound := fun runtime world valid => by
                let read := world.lese Λ args.orte
                let actual := evalArgs read args read locals
                have validRead : (callWP f known.formula normal).denote (assignment read) := by
                  rw [assignment_lese]
                  exact valid
                unfold Runtime.wpS
                dsimp only [execStmtH]
                cases reply : runtime.calls f read actual with
                | ok next value =>
                    have frame := runtime.evidence.frame f read actual next value reply
                    have inv := (known.correct next).mpr
                      (runtime.evidence.invariants f read actual next value reply)
                    have result := callWP_sound f known.formula normal read next validRead frame inv
                    simpa only [Goals.holds, h, denotes] using result
                | why next reason => exact (Fin.cast hr reason).elim0
                | logik error => trivial
                | hardware error => trivial }
  | .ret expression _ => .ok
      { formula := goals.terminal
        sound := fun _ world valid => by
          change goals.terminal.denote (assignment (world.lese Λ expression.orte))
          rw [assignment_lese]
          exact valid }
  | .retWhy _ _ => .ok
      { formula := goals.terminal
        sound := fun _ _ valid => valid }
  | .leave h => do
      let pre ← requireCondition (program := program) (checked := checked) (S := S) (goals.escape locals)
      return pre.map (fun _ _ valid => valid)
  | .next h => do
      let pre ← requireCondition (program := program) (checked := checked) (S := S) (goals.again locals)
      return pre.map (fun _ _ valid => valid)
  | .retScoped expression cleanup => do
      let releases ← cleanupFormula facts cleanup.scopes
      return {
          formula := conj releases.formula goals.terminal
          sound := fun runtime world valid => by
            have parts := (conj_denote _ _ _).mp valid
            let read := world.lese Λ expression.orte
            have same : assignment read = assignment world := assignment_lese _ _ _
            have releaseReady := (releases.correct read).mp (by rw [same]; exact parts.1)
            unfold Runtime.wpS
            simp only [execStmtH, releaseReady, ↓reduceIte, Goals.holds]
            rw [assignment_cleanup, assignment_lese]
            exact parts.2 }
  | .retWhyScoped reason cleanup => do
      let releases ← cleanupFormula facts cleanup.scopes
      return {
          formula := conj releases.formula goals.terminal
          sound := fun runtime world valid => by
            have parts := (conj_denote _ _ _).mp valid
            have releaseReady := (releases.correct world).mp parts.1
            unfold Runtime.wpS
            simp only [execStmtH, releaseReady, ↓reduceIte, Goals.holds]
            rw [assignment_cleanup]
            exact parts.2 }
  | _ => .error (.unsupported "writer statement is outside the checked scalar/control fragment")

end Gabbro.Grammatik.Invarianten.VC
