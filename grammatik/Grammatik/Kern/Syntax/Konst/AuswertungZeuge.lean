module

public import Grammatik.Kern.Syntax.Konst.Zeuge
public import Grammatik.Kern.Syntax.Konst.Auswertung

@[expose] public section
namespace Gabbro.Grammatik

/-! ## Evaluation witness: local binding, condition and nested call.

  Stage 4 of the C17 const-block design, G-level witness: a two-function
  closed program over the shared witness declaration. The caller binds a
  local, branches on it and calls the callee in the taken branch; the
  callee returns arithmetic. The witness evaluates through `evalConstCall`,
  plus one refused case per failure kind constructible here: a real
  contract violation, real resource exhaustion, and the range and
  dependency constructors (unreachable for admissible programs, kept for
  the exporter mapping). -/

/-- Caller/callee fitting at the empty resource context. -/
@[expose] def passt2 (f g : ConstWitness.witnessD.Fn) : RufPasst ConstWitness.witnessD (vertragVon ConstWitness.witnessD f) (ConstWitness.witnessD.signatur g) [] := { hw := fun t => t.elim, hg := fun g => g.elim, hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩, hh := fun l => l.elim }

/-- Shared bodies: caller with binding, condition and nested call; callee
    with arithmetic return. -/
@[expose] def rumpfBeide (f : ConstWitness.witnessD.Fn) : Endblock ConstWitness.witnessD (vertragVon ConstWitness.witnessD f) false (ConstWitness.witnessD.params f) (Signatur.anfang ConstWitness.witnessD (ConstWitness.witnessD.signatur f)) := if f.val = 0 then .bind (.lit 5) (.ite (.lt (.var .here) (.lit 10)) (.bindCall 1 .nil rfl (passt2 f 1) rfl (.ret (.val (.var .here)) (List.Perm.refl _))) (.ret (.val (.lit 3)) (List.Perm.refl _))) else .ret (.val (.add (.lit 1) (.lit 2))) (List.Perm.refl _)

/-- The two-function program with true contracts. -/
@[expose] def progP2 : Programm ConstWitness.witnessD := { invariante := fun i => i.elim, requires := fun _ => .tru, ensures := fun _ => .tru, rumpf := rumpfBeide }

/-- The same bodies with a failing entry contract on the caller. -/
@[expose] def progPBad : Programm ConstWitness.witnessD := { invariante := fun i => i.elim, requires := fun f => if f.val = 0 then .fls else .tru, ensures := fun _ => .tru, rumpf := rumpfBeide }

/-- Closed metadata for the true-contract program. -/
@[expose] def prog2 : ConstProgram := { D := ConstWitness.witnessD, P := progP2, functions := [0, 1], functions_complete := by decide, sourceId := fun f => f.val, sourceId_injective := fun _ _ h => Fin.ext h, noGlobals := fun g => g.elim, noOracles := fun a => a.elim, noRegisters := fun r => r.elim, noLocks := fun l => l.elim, noMarks := fun m => m.elim, noInvariants := fun i => i.elim, domains := [], domains_complete := fun t => t.elim, noFields := fun t => t.elim, count_nonnegative := fun t => t.elim, domains_closed := fun t => t.elim, noReasons := fun _ => rfl, emptyEntry := fun _ => rfl, emptyExit := fun _ => rfl }

/-- Closed metadata for the failing-contract program. -/
@[expose] def progBad : ConstProgram := { D := ConstWitness.witnessD, P := progPBad, functions := [0, 1], functions_complete := by decide, sourceId := fun f => f.val, sourceId_injective := fun _ _ h => Fin.ext h, noGlobals := fun g => g.elim, noOracles := fun a => a.elim, noRegisters := fun r => r.elim, noLocks := fun l => l.elim, noMarks := fun m => m.elim, noInvariants := fun i => i.elim, domains := [], domains_complete := fun t => t.elim, noFields := fun t => t.elim, count_nonnegative := fun t => t.elim, domains_closed := fun t => t.elim, noReasons := fun _ => rfl, emptyEntry := fun _ => rfl, emptyExit := fun _ => rfl }

/-- The caller runs at rank one, the callee at rank zero. -/
@[expose] def rang2 (f : prog2.D.Fn) : Nat := if f.val = 0 then 1 else 0

set_option maxRecDepth 100000 in
/-- The binding/condition/call body passes the structural whitelist. -/
theorem prog2Rein_zeuge : constAdmissibleB prog2 = true := by decide

set_option maxRecDepth 100000 in
/-- The failing-contract bodies are structurally pure as well. -/
theorem progBadRein_zeuge : constAdmissibleB progBad = true := by decide

set_option maxRecDepth 100000 in
/-- The caller-to-callee edge has a finite rank certificate. -/
theorem prog2Termination_zeuge : constTerminationB prog2 1 rang2 = true := by decide

set_option maxRecDepth 100000 in
/-- The two-function block program evaluates to a certified value through
    the exporter-level evaluator. -/
theorem prog2Wert_zeuge : (evalConstCall prog2 0 .nil 100).istWert = true := by decide

set_option maxRecDepth 100000 in
/-- The false entry contract refuses as a contract violation. -/
theorem progBadVertrag_zeuge : (evalConstCall progBad 0 .nil 100).istVertrag = true := by decide

/-- A zero work limit refuses before any reduction. -/
theorem prog2Erschoepfung_zeuge : (evalConstCall prog2 0 .nil 0).istErschoepfung = true := by decide

/-- The range constructor is inhabited for the refusal mapping. -/
theorem progBereich_zeuge : (ConstCallResult.range (c := prog2) (f := 0) (args := .nil) 1).istBereich = true := rfl

/-- The dependency constructor is inhabited for the refusal mapping. -/
theorem progAbhaengigkeit_zeuge : (ConstCallResult.dependency (c := prog2) (f := 0) (args := .nil) 1).istAbhaengigkeit = true := rfl

end Gabbro.Grammatik
