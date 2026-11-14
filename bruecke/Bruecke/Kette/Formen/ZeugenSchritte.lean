module
public import Bruecke.Kette.Quelle
public import Grammatik.Parser.Stmt.LibraryFixtureProofs
public import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
@[expose] public section

/-! # Small phase certificates for bridge witnesses

Only witness modules import this module. The actual compiler and bridge do not
evaluate a concrete source or a success-dependent program to establish a duty.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Compose already certified frontend phases with the actual lowering equation.
    All intermediate results remain symbolic while the pipeline is unfolded. -/
theorem witness_translation {source : String} {tokens : List Token}
    {items : List SItemTief} {u : UProg} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn}
    (scanned : lex source = .ok tokens) (parsed : parseTopTief tokens = .ok items)
    (exported : elabU (pre108 items) = .ok u) (lowered : lowerAllg u = .ok (P, fs)) :
    uebersetzeAllg source = .ok ⟨u, P, fs⟩ := by
  unfold uebersetzeAllg
  rw [scanned]
  dsimp only
  rw [parsed]
  dsimp only
  rw [exported]
  dsimp only
  rw [lowered]

/-- Empty source contracts give the real lowered interface duty without evaluating
    the assembled program. The lowered bodies and their success proofs stay opaque. -/
theorem witness_interfaces_empty (u : UProg)
    (needs : ∀ f : Fin u.fns.length, (fnAt u f).needs = [])
    (contracts : ∀ n, (sigFnAt u n).needs = [] ∧ (sigFnAt u n).gives = []) :
    SchnittstellenPflicht u := by
  intro P fs lowered
  unfold lowerAllg at lowered
  split at lowered
  · cases lowered
  · split at lowered
    · cases lowered
    · split at lowered
      · obtain ⟨rfl, _⟩ := Measures.checkedProgram_eq lowered
        apply ptrVerfeinert_trivial
        · intro f s ρ
          simp only [ReqAmEintritt, progOfFn, reqOf, needs f, ↓reduceIte, eval, wahr?]
        · intro n
          change ptrVertragOf u n = CallContract.trivial _ _
          simp only [ptrVertragOf, lowerPtrAt, (contracts n).1, (contracts n).2,
            lowEnsList, Except.toOption, Option.getD] <;> rfl
      · cases lowered

end Gabbro.Bruecke
