module

public import Core.Beobachtung.Unentscheidbar.Simulation.Nummer
public import Core.Beobachtung.Unentscheidbar.Simulation.Programm

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The composition of the translator and the Gödel numbering is computable,
    as required by the substrate's reduction function. The computation runs on
    natural numbers throughout, so no `Primcodable` instance for commands is
    needed: only the encodings of the finitely many emitted programs appear. -/
theorem komposition_berechenbar : Computable (fun c => kodiere (programm c)) := by
  unfold kodiere programm
  apply Nat.Partrec.Code.computable_recOn (c := fun c : Nat.Partrec.Code => c) Computable.id
  · exact Computable.const (Encodable.encode (progZahl 0))
  · exact Computable.const (Encodable.encode progSucc)
  · exact Computable.const (Encodable.encode (progZahl 0))
  · exact Computable.const (Encodable.encode (progZahl 0))
  · exact (Computable.const (Encodable.encode (progZahl 0))).to₂
  · exact (Computable.const (Encodable.encode (progZahl 0))).to₂
  · exact (Computable.const (Encodable.encode (progZahl 0))).to₂
  · exact (Computable.const (Encodable.encode (progZahl 0))).to₂

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
