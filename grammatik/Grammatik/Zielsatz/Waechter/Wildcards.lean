/-
  File:      Grammatik/Zielsatz/Waechter/Wildcards.lean
  Subject:   GUARD 3 (B24 step 0, `dokumente/PERFECT-MODEL.md` §6.4): NO NEW WILDCARD in the semantics of G and in acceptance. A catch-all
             case silently gives every constructor added later the meaning of the catch-all; in the step relations
             and in the checker that is how an unsound new form slips through.

  The declared set is the meaning closure (`Grundlagen.huelle`) of G's step relation `RufSchrittG`, the GX step
  `RufSchrittGX`, the thread machine `FadenSchrittX`/`FadenErreichbarX`, and the acceptance roots of
  `Abhaengigkeit.lean` (which include the interim `I`). For every constant of the set, every matcher its meaning
  uses (type, body, constructor types) is read from its ELABORATED form (`Grundlagen.wildcardAlts`): an alternative
  is a wildcard when it leaves open a position, at any depth, that another alternative of the same match splits by
  a constructor or a literal -- exactly what `_ =>` or a variable pattern after constructor cases compiles to,
  independent of how it was written. Counts are per definition (compiler auxiliaries such as `f._f`, `f.match_1`
  count for `f`).

  RATCHET: `erwartet` is today's measurement; a new definition with a wildcard, or more wildcards in a pinned one,
  fails; fewer fail too until the list is lowered, so it only shrinks.
-/
module
public import Grammatik.Zielsatz.Waechter.Grundlagen
public import Grammatik.Zielsatz.Waechter.Abhaengigkeit
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Fremd
meta import Lean
meta import Grammatik.Zielsatz.Waechter.Grundlagen
meta import Grammatik.Zielsatz.Waechter.Abhaengigkeit
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Waechter.Wildcards

open Lean Meta

/-- The roots of the declared set. -/
def wurzeln : List Name :=
  [``RufSchrittG, ``RufSchrittGX, ``FadenSchrittX, ``FadenErreichbarX] ++ Abhaengigkeit.aWurzeln

/-- RATCHET: (definition, number of wildcard alternatives), measured. -/
def erwartet : List (String × Nat) :=
  [("Gabbro.Grammatik.ArenaOwnership.Body.exprGlob", 1),
   ("Gabbro.Grammatik.ArenaOwnership.Body.exprLit", 1),
   ("Gabbro.Grammatik.ArenaOwnership.Body.exprSlotRead", 1),
   ("Gabbro.Grammatik.ArenaOwnership.Body.exprSucc", 1),
   ("Gabbro.Grammatik.ArenaOwnership.Body.exprVarPos", 1),
   ("Gabbro.Grammatik.ArenaOwnership.Body.positionFits", 2),
   ("Gabbro.Grammatik.ArenaOwnership.Source.Flow.Output.check", 1),
   ("Gabbro.Grammatik.ArenaOwnership.Source.expressionOrigin", 1),
   ("Gabbro.Grammatik.Block.istRueck", 1),
   ("Gabbro.Grammatik.Boundary.requiredB", 1),
   ("Gabbro.Grammatik.Endblock.istRueck", 1),
   ("Gabbro.Grammatik.Fall.ofNutzlast", 1),
   ("Gabbro.Grammatik.Fall.toNutzlast", 1),
   ("Gabbro.Grammatik.GEntfaltbar", 1),
   ("Gabbro.Grammatik.GRest.anRueck", 3),
   ("Gabbro.Grammatik.GRest.scopedGrund", 1),
   ("Gabbro.Grammatik.GRest.scopedWert", 1),
   ("Gabbro.Grammatik.GRest.wartend", 1),
   ("Gabbro.Grammatik.GuestBoundary.inputsB", 1),
   ("Gabbro.Grammatik.GuestBoundary.pointerInputs", 1),
   ("Gabbro.Grammatik.Invarianten.Elim.conj", 5),
   ("Gabbro.Grammatik.Invarianten.Elim.disj", 5),
   ("Gabbro.Grammatik.Invarianten.Elim.lowerBounds", 1),
   ("Gabbro.Grammatik.Invarianten.Elim.minusInfinity", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Payload", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Represents", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.ScalarObservation", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Payload", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.conjunct", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.conjunction", 5),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.definition", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.disjunction", 5),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.equality", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.evaluate", 11),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.existential", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.implication", 5),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.lessEqual", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.lessThan", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.negation", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Reduce.universal", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Represents", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot.decide", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot.literalIndex", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot.observation", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot.observations", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot.zeroCounterexample", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.SymEnv.concrete?", 2),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.SymEnv.dropPrefix", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.concreteEncoding", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.evaluationRelation", 2),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.parameters", 3),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.translateSnapshot", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.Symbolic.valueView?", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.boundIndexB", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.checkMemoryType", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.constantValue", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.encodeConstant", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.encodeObservation", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.literalB", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.payloadObservations", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.scalarValue", 1),
   ("Gabbro.Grammatik.Invarianten.Frag.translate", 2),
   ("Gabbro.Grammatik.Invarianten.Pruefer.checkWriter", 1),
   ("Gabbro.Grammatik.Invarianten.Pruefer.lockFormula", 1),
   ("Gabbro.Grammatik.Invarianten.VC.extendedEnd", 1),
   ("Gabbro.Grammatik.Invarianten.VC.extendedStatement", 2),
   ("Gabbro.Grammatik.Invarianten.VC.finiteDomain", 1),
   ("Gabbro.Grammatik.Invarianten.VC.integerEquality", 1),
   ("Gabbro.Grammatik.Invarianten.VC.leafCondition", 1),
   ("Gabbro.Grammatik.Invarianten.VC.localCode", 1),
   ("Gabbro.Grammatik.Invarianten.VC.localEquality", 1),
   ("Gabbro.Grammatik.Invarianten.VC.localRange", 1),
   ("Gabbro.Grammatik.Invarianten.VC.scalarWP", 2),
   ("Gabbro.Grammatik.Invarianten.VC.translateScalar", 1),
   ("Gabbro.Grammatik.Invarianten.VC.typeFact", 1),
   ("Gabbro.Grammatik.Stmt.ants", 1),
   ("Gabbro.Grammatik.Stmt.gOk", 1),
   ("Gabbro.Grammatik.Stmt.istBlatt", 1),
   ("Gabbro.Grammatik.Stmt.istRueck", 1),
   ("Gabbro.Grammatik.Stmt.regs", 1),
   ("Gabbro.Grammatik.Stmt.scopesOk", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Basic.EndResult", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Basic.StatementResult", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Basic.block", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Basic.ending", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Basic.statement", 2),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Basic.trivialLock", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Symbolic.argumentRelation", 2),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Symbolic.freshValue", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Symbolic.knownValue?", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Symbolic.resultCondition", 2),
   ("Gabbro.Grammatik.Vertraege.Pruefer.Symbolic.selectValue", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.block", 2),
   ("Gabbro.Grammatik.Vertraege.Pruefer.blockSpecializations", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.checkBasicFunction", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.checkEnvironmentAt", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.checkExecution", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.checkFunction", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.checkPointerTarget", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.endSpecializations", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.indirectOutcomes", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.leafCondition", 2),
   ("Gabbro.Grammatik.Vertraege.Pruefer.selectionSpecializations", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.specializationCount", 1),
   ("Gabbro.Grammatik.Vertraege.Pruefer.statement", 2),
   ("Gabbro.Grammatik.Vertraege.Pruefer.statementSpecializations", 2),
   ("Gabbro.Grammatik.Vertraege.Pruefer.uniformPost", 1),
   ("Gabbro.Grammatik.antwortRestG", 2),
   ("Gabbro.Grammatik.armWahlG", 1),
   ("Gabbro.Grammatik.execBlock", 1),
   ("Gabbro.Grammatik.execBlockH", 1),
   ("Gabbro.Grammatik.execBlockHA", 1),
   ("Gabbro.Grammatik.execStmt", 1),
   ("Gabbro.Grammatik.grundWahlG", 1),
   ("Gabbro.Grammatik.nutzBar", 1),
   ("Gabbro.Grammatik.nutzPasst", 1),
   ("Gabbro.Grammatik.resetCarrierB", 1),
   ("Gabbro.Grammatik.roh", 11),
   ("Gabbro.Grammatik.sumWort", 1),
   ("Gabbro.Grammatik.verbrauchLauf", 1),
   ("Gabbro.Grammatik.zeroAdmittingB", 1),
   ("Gabbro.Grammatik.zugriffVon", 1)]

def pruefe : MetaM Unit := do
  let env ← getEnv
  let menge := huelle env wurzeln
  let mut zaehl : Std.HashMap String Nat := {}
  for n in sortiert menge do
    if isMatcherCore env n then continue
    let some ci := env.find? n | continue
    let mut k := 0
    for c in (direkt ci).eraseDups do
      if isMatcherCore env c then k := k + (← wildcardAlts c)
    if k > 0 then
      let b := (basisName n).toString
      zaehl := zaehl.insert b (zaehl.getD b 0 + k)
  let gemessen := (zaehl.toList.toArray.qsort (fun a b => a.1 < b.1)).toList
  let summe := gemessen.foldl (fun s (_, k) => s + k) 0
  melde s!"wildcards in the semantics of G or in acceptance ({gemessen.length} definitions, {summe} alternatives)"
    (ratsche gemessen erwartet)
    ("replace a new catch-all by explicit cases; lower the list where wildcards were removed. " ++
     s!"Measured:\nerwartet := {alsListe gemessen}")

run_meta pruefe

end Gabbro.Grammatik.Zielsatz.Waechter.Wildcards
