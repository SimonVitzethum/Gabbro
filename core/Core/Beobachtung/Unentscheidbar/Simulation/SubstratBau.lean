module

public import Core.Beobachtung.Unentscheidbar.Simulation.Nummer
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Grundlagen
public import Core.Beobachtung.Unentscheidbar.Simulation.Programm

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

/-- The translator map is computable: it is a `Code` recursion whose branches
    are constant command programs. -/
theorem programm_computable : Computable programm := by
  unfold programm
  apply Nat.Partrec.Code.computable_recOn (c := fun c : Nat.Partrec.Code => c) Computable.id
  · exact Computable.const (progZahl 0)
  · exact Computable.const progSucc
  · exact Computable.const (progZahl 0)
  · exact Computable.const (progZahl 0)
  · exact (Computable.const (progZahl 0)).to₂
  · exact (Computable.const (progZahl 0)).to₂
  · exact (Computable.const (progZahl 0)).to₂
  · exact (Computable.const (progZahl 0)).to₂

/-- The composition of the translator and the Gödel numbering is computable,
    as required by the substrate's reduction function. -/
theorem komposition_berechenbar : Computable (fun c => kodiere (programm c)) := by
  change Computable (fun c => Encodable.encode (programm c))
  exact Computable.encode.comp programm_computable

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
