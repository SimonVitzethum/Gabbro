import Stage0.IRBild
import Grammatik.Parser.Elab.ExportWitnesses

namespace Gabbro.Stage0
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.ExportPreservation

/-- The export laws are for the actual elaborator/lowerer consumed by `compile_source_program`.
    This image certificate connects that program to the inherited IR simulation, with precisely
    the same initial-memory, gate/view, call-depth and environment-budget premises. -/
theorem exported_source_ir_correct [Runner.IR.Kern] [Senke.CloneOK]
    (text : String) (K : Nat) (bytes : List Runner.B) {options : Profil.Options}
    (h : irBild text K options = .ok bytes) :
    ∃ output : Emitted text K options,
      emit text K options = .ok output ∧ output.image.bytes = bytes ∧
      CanonicalSourceProgram output.compiled ∧ output.Correct ∧
      (∀ (Γ : Ctx) (Λ : List (Res (declOf output.compiled.unit))) (name : String)
        (value : Expr (declOf output.compiled.unit) Γ Λ .bool),
        lowHeld output.compiled.unit Γ Λ name = .ok value →
        output.compiled.unit.exportGate = .ok () ∧
        ∃ lock, lockIdx output.compiled.unit.locks name = .ok lock ∧
          Res.held lock ∈ Λ ∧ value = .tru) := by
  obtain ⟨output, emitted, image, correct⟩ := irBild_correct text K bytes h
  exact ⟨output, emitted, image, compile_source_program text output.compiled, correct,
    fun Γ Λ name value held => held_lower output.compiled.unit Γ Λ name value held⟩

/-- Every admitted new export is in the metadata domain checked on its original source,
    before old/global normalization or G lowering can discard an annotation. -/
theorem Compiled.exports_metadata {text : String} {options : Profil.Options} (result : Compiled text options)
    (h : result.unit.exportGate = .ok ()) :
    (uMembers (pre108 result.source.items)).any ExportMetadata.itemMetadata = false :=
  ExportMetadata.check_sound _ (result.metadata.symm.trans h)

/-- The entry-global adapter preserves both original operand snapshots inside implication.
    It never treats a current read as an entry read. -/
theorem implication_old_export (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (a b : SExpr) (x y : UEns)
    (p q : Expr (declOf u) Γ Λ .bool)
    (hg : u.exportGate = .ok ())
    (hasOld : (OldSource.hasEntry a || OldSource.hasEntry b) = true)
    (ha : OldSource.predicate u Γ Λ fn er a x = .ok p)
    (hb : OldSource.predicate u Γ Λ fn er b y = .ok q) :
    OldSource.predicate u Γ Λ fn er (.ext .imp [] [a, b]) (.imp x y) =
      .ok (Expr.impl p q) := by
  simp only [OldSource.predicate, OldSource.hasEntry, hasOld, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, hg, bind, Except.bind, ha, hb]
  rfl

end Gabbro.Stage0
