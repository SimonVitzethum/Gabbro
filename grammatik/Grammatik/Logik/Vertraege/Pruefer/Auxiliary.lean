module

public import Grammatik.Logik.Vertraege.Pruefer.Sources
public import Grammatik.Zielsatz.Kern.Spec.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Pruefer Zielsatz

variable {D : Deklaration}

/-- A reified lock predicate is local exactly as checked from its reads. -/
def checkLockLocal (S : SperrInv D) (sources : LockSources S) (lock : D.Lock) :
    Except Frag.Refusal (PLift (∀ s s', (∀ c ∈ S.orte lock, TraegerGleich s s' c) →
      S.inv lock s = S.inv lock s')) := do
  let some source := sources lock
    | .error (.unsupported "lock invariant is missing its elaborated source expression")
  match checked : checkCarriers (S.orte lock) source.expression with
  | .error cause => .error cause
  | .ok _ =>
      return ⟨fun s s' same => by
        have sourceAt (memory : Speicher D) :
            eval (memory.welt []) source.expression (memory.welt []) .nil = S.inv lock memory := by
          simpa only [speicher_welt_speicher] using source.correct (memory.welt [])
        rw [← sourceAt s, ← sourceAt s']
        exact eval_gleichAuf source.expression (checkCarriers_sound _ _ checked)
          (σ := s.welt []) (σ' := s'.welt [])
          ⟨fun t member => same (.inl t) member, fun g member => same (.inr g) member⟩ .nil⟩

/-- Oracle truth is an environment assumption. Locality of its SOURCE is a
    structural checker matter, and is independent of the oracle's truth. -/
def checkAxiomLocal (Q : AxEns D) (sources : AxiomSources Q) (a : D.Ax) :
    Except Frag.Refusal (PLift (∀ world next value,
      (∀ t, D.aschreibt a t = true → world.slots t = next.slots t) →
      (∀ g, D.agschreibt a g = true → world.globs g = next.globs g) →
      Q a world value = Q a next value)) :=
  if checked : (sources.expression a).orte.all (Sum.elim (D.aschreibt a) (D.agschreibt a)) = true then
    .ok ⟨fun world next value tables globals => by
      rw [← sources.correct a world value, ← sources.correct a next value]
      apply eval_gleichAuf (sources.expression a) (fun _ h => h)
      exact ⟨fun t member => tables t (List.all_eq_true.mp checked (.inl t) member),
        fun g member => globals g (List.all_eq_true.mp checked (.inr g) member)⟩⟩
  else .error (.unsupported "oracle contract reads outside its declared answer footprint")

/-- Decide a universally closed implication using the same decoded type facts
    as function and invariant WPs. Refusals contain a counterexample assignment. -/
def checkImplication (label : String) (pre : LProp (Observation D)) (post : QF (Observation D)) :
    Except Frag.Refusal (PLift (∀ world, pre.denote (assignment world) → post.denote (assignment world))) :=
  if accepted : decideB (close (writerMatrix pre .tru post)) (close_closed (writerMatrix pre .tru post)) = true then
    .ok ⟨fun world requires => by
      have closed := (lower_denote _ (assignment world)).mp (close_sound _ accepted (assignment world))
      have implication := (lower_denote _ (assignment world)).mp
        ((quoteQF_denote _ _).mp (closed (typeFacts_sound _ world)))
      exact (quoteQF_denote _ _).mp (implication ⟨requires, trivial⟩)⟩
  else .error (.invalid (invalidMessage label pre post))

/-- One target's interface entry condition is checked contravariantly. The
    normal return implication is checked for every decoded result. Post
    implications are conservatively required without the interface precondition;
    no entry-memory predicate is incorrectly reused in the return world. -/
def checkPointerEnvironment (program : Programm D) (budget : VCBudget)
    (f : D.Fn) (n : Nat) (target : D.passt f n = true) (locals : Env D (D.sigNr n).params) :
    Except Frag.Refusal (PLift (
      (∀ old, (program.ptrVertrag n).preHolds old locals → ReqAmEintritt program f old (umsig target locals)) ∧
      (∀ old next value, (program.ptrVertrag n).preHolds old locals →
        EnsAmRueck program f old next (umsig target locals) value →
        (program.ptrVertrag n).postHolds old next locals (ptrResult target value)))) := do
  let interfacePre ← translate (program.ptrVertrag n).pre locals
  let targetPre ← translate (program.requires f) (umsig target locals)
  let entry ← checkImplication "pointer target requires" interfacePre.payload (lower targetPre.payload)
  let independent ← currentOnly (program.ptrVertrag n).post
  let domain ← results (D := D) budget.expansion (D.erg f)
  let returned ← collect domain.values
    (fun value => ∀ old next,
      EnsAmRueck program f old next (umsig target locals) value →
      (program.ptrVertrag n).postHolds old next locals (ptrResult target value))
    (fun value => do
      let concrete ← postFormula program f (umsig target locals) value
      let abstract ← translate (program.ptrVertrag n).post
        (ergEnv (D.sigNr n).erg (ptrResult target value) locals)
      let proved ← checkImplication "pointer target ensures" (quoteQF concrete.val) (lower abstract.payload)
      return ⟨fun old next ensures => by
        have valid := proved.down next ((quoteQF_denote _ _).mpr ((concrete.property old next).mpr ensures))
        have evaluated := (abstract.bool_iff next).mpr ((lower_denote _ _).mp valid)
        unfold CallContract.postHolds
        rw [independent.down old next]
        exact evaluated⟩)
  return ⟨⟨fun old requires =>
    (targetPre.bool_iff old).mpr ((lower_denote _ _).mp
      (entry.down old ((interfacePre.bool_iff old).mp requires))),
    fun old next value _ ensures => returned.down value (domain.complete value) old next ensures⟩⟩

def checkPointerTarget (program : Programm D) (budget : VCBudget) (f : D.Fn) (n : Nat) :
    Except Frag.Refusal (PLift (∀ target : D.passt f n = true, PtrZielVerfeinert program f n target)) :=
  if target : D.passt f n = true then
    match required : program.requires f, program.ensures f,
        (program.ptrVertrag n).pre, returned : (program.ptrVertrag n).post with
    | .tru, .tru, .tru, .tru =>
        .ok ⟨fun _ => by
          constructor
          · intro old locals _
            simp only [ReqAmEintritt, required, eval, wahr?]
          · intro old next locals value _ _
            simp only [CallContract.postHolds, returned, eval, wahr?]⟩
    | _, _, _, _ => do
        let domain ← environments (D := D) budget.expansion (D.sigNr n).params
        let checked ← collect domain.values _ (checkPointerEnvironment program budget f n target)
        return ⟨fun _ => ⟨fun old locals requires => (checked.down locals (domain.complete locals)).1 old requires,
          fun old next locals value requires ensures =>
            (checked.down locals (domain.complete locals)).2 old next value requires ensures⟩⟩
  else .ok ⟨fun impossible => False.elim (target impossible)⟩

/-- The finite interface table, not a finite observed run, covers all possible
    function-pointer targets, including targets never called by this image. -/
def checkPointers (program : Programm D) (functions : List D.Fn)
    (layout : PointerSignatures D) (budget : VCBudget := {}) :
    Except Frag.Refusal (PLift (∀ f ∈ functions, ∀ n (target : D.passt f n = true),
      PtrZielVerfeinert program f n target)) := do
  let checked ← collect functions _ (fun f =>
    collect (List.range layout.count) _ (checkPointerTarget program budget f))
  return ⟨fun f member n target => by
    by_cases inside : n < layout.count
    · exact checked.down f member n (List.mem_range.mpr inside) target
    · have absent := layout.outside f n (Nat.le_of_not_gt inside)
      rw [absent] at target
      cases target⟩

end Gabbro.Grammatik.Vertraege.Pruefer
