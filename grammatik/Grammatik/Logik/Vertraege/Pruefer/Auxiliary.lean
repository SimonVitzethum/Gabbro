module

public import Grammatik.Logik.Vertraege.Pruefer.Sources
public import Grammatik.Logik.Vertraege.Pruefer.Control.Refinement
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

/-- Interface refinement quantifies typed scalar arguments and returns. -/
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
        let checked ← Symbolic.checkContractRefinement budget.specializations (D.passt_sig target).params (D.passt_sig target).erg
          (program.ptrVertrag n).pre (program.requires f) (program.ensures f) (program.ptrVertrag n).post
        return ⟨fun _ => ⟨checked.down.1, fun old world actual value _ valid =>
          checked.down.2 old world actual value valid⟩⟩
  else .ok ⟨fun impossible => False.elim (target impossible)⟩

/-- No conforming target of any interface lies in `cycle`: a call through a pointer
    then never needs a descent. Decided over the table's complete target lists. -/
def acyclicTargets (layout : PointerSignatures D) (cycle : D.Fn → Bool) :
    Option (PLift (∀ g n, D.passt g n = true → cycle g = false)) :=
  if checked : (List.range layout.count).all (fun n => (layout.targets n).all (fun g => !cycle g)) = true then
    some ⟨fun g n target => by
      by_cases inside : n < layout.count
      · have row := List.all_eq_true.mp checked n (List.mem_range.mpr inside)
        have entry := List.all_eq_true.mp row g (layout.covers g n target)
        revert entry
        cases cycle g <;> decide
      · have absent := layout.outside g n (Nat.le_of_not_gt inside)
        rw [absent] at target
        cases target⟩
  else none

/-- The finite interface table, not a finite observed run, covers all possible
    function-pointer targets, including targets never called by this image:
    every conforming target of every interface refines it (`PtrVerfeinert`). -/
def checkPointers (program : Programm D) (layout : PointerSignatures D) (budget : VCBudget := {}) :
    Except Frag.Refusal (PLift (PtrVerfeinert program)) := do
  let checked ← collect (List.range layout.count) _ (fun n =>
    collect (layout.targets n) _ (fun f => checkPointerTarget program budget f n))
  return ⟨fun f n target => by
    by_cases inside : n < layout.count
    · exact checked.down n (List.mem_range.mpr inside) f (layout.covers f n target) target
    · have absent := layout.outside f n (Nat.le_of_not_gt inside)
      rw [absent] at target
      cases target⟩

/-- The refinement decided over an optional table; `none` when the table is missing or a
    target does not refine its interface. -/
def refinementOf (program : Programm D) (table : Option (PointerSignatures D)) :
    Option (PLift (PtrVerfeinert program)) :=
  table.bind (fun layout => (checkPointers program layout).toOption)

end Gabbro.Grammatik.Vertraege.Pruefer
