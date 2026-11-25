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
  let e0 := Encodable.encode (progZahl 0)
  let e1 := Encodable.encode progSucc
  have hz : Computable (fun _ : Nat.Partrec.Code => e0) := Computable.const e0
  have hs : Computable (fun _ : Nat.Partrec.Code => e1) := Computable.const e1
  have hl : Computable (fun _ : Nat.Partrec.Code => e0) := Computable.const e0
  have hr : Computable (fun _ : Nat.Partrec.Code => e0) := Computable.const e0
  have hpr : Computable₂ (fun (_ : Nat.Partrec.Code)
      (_ : Nat.Partrec.Code × Nat.Partrec.Code × Nat × Nat) => e0) := (Computable.const e0).to₂
  have hco : Computable₂ (fun (_ : Nat.Partrec.Code)
      (_ : Nat.Partrec.Code × Nat.Partrec.Code × Nat × Nat) => e0) := (Computable.const e0).to₂
  have hpc : Computable₂ (fun (_ : Nat.Partrec.Code)
      (_ : Nat.Partrec.Code × Nat.Partrec.Code × Nat × Nat) => e0) := (Computable.const e0).to₂
  have hrf : Computable₂ (fun (_ : Nat.Partrec.Code)
      (_ : Nat.Partrec.Code × Nat) => e0) := (Computable.const e0).to₂
  have h := Nat.Partrec.Code.computable_recOn (c := fun c : Nat.Partrec.Code => c)
    Computable.id (hz := hz) (hs := hs) (hl := hl) (hr := hr)
    (hpr := hpr) (hco := hco) (hpc := hpc) (hrf := hrf)
  unfold kodiere programm
  refine h.of_eq ?_
  intro c
  cases c <;> rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
