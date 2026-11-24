module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level elaboration and acceptance proofs

Resolve the instruction at the source occurrence and show that its one local
plan has empty memory footprint. Catalogue and region facts are in the other
proof modules.

- `ElaboriertAussage`
- `RealisiertAussage`
- `AnnahmeAussage`
-/

namespace Gabbro.Core.Ast.LowLevel

open Maschine

/-! The three statements hold for every form. Elaboration is the defining
    equivalence itself; realization at the canonical start needs only that the
    instruction evaluates there; acceptance needs only that its one plan is the
    fixed empty-footprint plan. -/

theorem elaboriert_form (form : Form) : ElaboriertAussage form := by
  intro k scope tree E
  simp [Elaboriert]

theorem realisiert_form (form : Form) : RealisiertAussage form := by
  intro k scope tree op start _ heval
  let s := (I.start (unit op) start).2
  have hs : s.status entryContext = .laeuft := by
    simp [s, I.start, unit, bootData, entryContext, Zustand.start]
  have hp : (s.lokal entryContext).pc = 0 := by
    simp [s, I.start, unit, bootData, entryContext, Zustand.start]
  have heval' : (op.evaluate s entryContext).isSome := by
    simpa [s] using heval
  change (unit op).system.kopf s entryContext = some op
  simp [unit, system, head, hs, hp, heval']

theorem annahme_form (form : Form) : AnnahmeAussage form := by
  intro k scope tree op _
  constructor
  · intro c s u w P hideal
    simp only [unit, system, Instruction.rule, Instruction.ideal] at hideal
    rcases hideal with ⟨transfer, heval, hP, hu⟩
    have hP' : P = plan := by simpa using hP
    subst P
    simp [Annahme.Befugt, plan]
  · intro s c w plans next hideal
    rcases hideal with ⟨transfer, heval, hplans, hnext⟩
    exact hplans

theorem addressType_elaboriert : ElaboriertAussage .addressType := elaboriert_form .addressType
theorem addressType_realisiert : RealisiertAussage .addressType := realisiert_form .addressType
theorem addressType_annahme : AnnahmeAussage .addressType := annahme_form .addressType

theorem regionAddress_elaboriert : ElaboriertAussage .regionAddress := elaboriert_form .regionAddress
theorem regionAddress_realisiert : RealisiertAussage .regionAddress := realisiert_form .regionAddress
theorem regionAddress_annahme : AnnahmeAussage .regionAddress := annahme_form .regionAddress

theorem view_elaboriert : ElaboriertAussage .view := elaboriert_form .view
theorem view_realisiert : RealisiertAussage .view := realisiert_form .view
theorem view_annahme : AnnahmeAussage .view := annahme_form .view

theorem environment_elaboriert : ElaboriertAussage .environment := elaboriert_form .environment
theorem environment_realisiert : RealisiertAussage .environment := realisiert_form .environment
theorem environment_annahme : AnnahmeAussage .environment := annahme_form .environment

end Gabbro.Core.Ast.LowLevel
