/- Canonical consuming witnesses. These are source-semantic witnesses, not
   claims that the unadmitted IR candidate has a connected simulation. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Probe
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Emission
public section

namespace Gabbro.Stage0.Senke.ConsumeProbe
open Gabbro.Grammatik Runner.IR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The actual edge is oriented from predecessor to candidate. Initially
    zero is minimal; after removing zero, one becomes minimal. -/
theorem edge_selection_zeuge :
    wahr? (eval initial edge initial (.cons zero (.cons one .nil))) = true ∧
    wahr? (eval initial edge initial (.cons one (.cons zero .nil))) = false ∧
    (verbrauchSel () member edge initial .nil).2.1 = some zero ∧
    (verbrauchSel () member edge afterFirst .nil).2.1 = some one ∧
    (verbrauchSel () member edge afterSecond .nil).2 = (none, false) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Selection is evaluated against the current state, not a saved sweep.
    Every body pass removes its own live member and the measure falls 2,1,0.
    The final world includes the canonical selection/measure read trace. -/
theorem normal_run_zeuge :
    (eval initial mass initial .nil).n = 2 ∧
    (eval afterFirst mass afterFirst .nil).n = 1 ∧
    (eval afterSecond mass afterSecond .nil).n = 0 ∧
    ∃ σ, execStmt oracle 1 calls (statement true) initial .nil = .ok σ .nil ∧
      (σ.slots () 0 ()).n = 0 ∧ (σ.slots () 1 ()).n = 0 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  refine ⟨?_, rfl, ?_, ?_⟩ <;> rfl

/-- False membership performs no body writes, despite a nonempty index
    domain and an edge expression that is true everywhere. -/
theorem false_membership_zeuge :
    execStmt oracle 1 calls absent initial .nil = .ok initial .nil ∧
    (initial.slots () 0 ()).n = 1 ∧ (initial.slots () 1 ()).n = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- A body mutation alone does not establish the measure duty. A constant
    zero measure fails strictly after the first selected body pass. -/
theorem unchanged_measure_zeuge [Kern] :
    execStmt oracle 1 calls unchanged initial .nil = .logik .schleife ∧
    logikCode (D := D) .schleife = 104 := ⟨rfl, rfl⟩

/-- Invariant failure after the first removal is still a loop failure. -/
theorem invariant_stop_zeuge [Kern] :
    execStmt oracle 1 calls (statement false) initial .nil = .logik .schleife ∧
    logikCode (D := D) .schleife = 104 := ⟨rfl, rfl⟩

/-- Two live nodes preceding each other have no minimal candidate. This is
    distinguished from false membership and must not terminate successfully. -/
theorem cyclic_selection_zeuge [Kern] :
    let cycle : Expr D [.index 2, .index 2] [] .bool :=
      .not (.eq (.var .here) (.var (.there .here)))
    (verbrauchSel () member cycle initial .nil).2 = (none, true) ∧
    execStmt oracle 1 calls
      (.consumeTraverse () member cycle .tru 2 mass body :
        Stmt D (vertragVon D ()) false [] [] []) initial .nil = .logik .schleife ∧
    logikCode (D := D) .schleife = 104 := by
  exact ⟨rfl, rfl, rfl⟩

/-- `leave` checks the post-body measure too; it cannot bypass decrease. -/
theorem leave_measure_zeuge :
    execStmt oracle 1 calls
      (.consumeTraverse () member edge .tru 0 (.lit 0)
        (.cons (.assignSlot () () (.var .here)
          (.widen (by decide) (by decide) (.lit 0)) rfl access)
          (.cons (.leave rfl) .nil)) :
        Stmt D (vertragVon D ()) false [] [] []) initial .nil = .logik .schleife := rfl

/-- `next` performs the same post-body strict-decrease check. -/
theorem next_measure_zeuge :
    execStmt oracle 1 calls
      (.consumeTraverse () member edge .tru 0 (.lit 0)
        (.cons (.assignSlot () () (.var .here)
          (.widen (by decide) (by decide) (.lit 0)) rfl access)
          (.cons (.next rfl) .nil)) :
        Stmt D (vertragVon D ()) false [] [] []) initial .nil = .logik .schleife := rfl

/-- The actual statement path is closed until concrete IR correctness is
    proved. Neither the positive source witness nor its logical failure twin
    is reported as a compiling language case. -/
theorem lowering_refused_zeuge : lowered true = none ∧ lowered false = none := ⟨rfl, rfl⟩

/-- The replacement produces concrete instruction candidates with the real
    table loads, stores and nested scans. This does not assert admission by
    lowS or execution correctness of those candidates. -/
theorem candidate_emission_zeuge :
    (candidate true).isSome = true ∧ (candidate false).isSome = true := by
  decide +kernel

/-- Unsupported scoped return retains its precise refusal, independently of
    the consuming loop's missing simulation. -/
theorem consumeTraverse_refused_zeuge :
    lowS 1 (fun _ => 2048) layout (functionFrame program ()) post [3] (0, 0)
      (.consumeTraverse () member edge .tru 2 mass
        (.cons (.retScoped .empty { scopes := [], genau := .refl [] }) .nil) :
        Stmt D (vertragVon D ()) false [] [] []) = none := rfl

end Gabbro.Stage0.Senke.ConsumeProbe
