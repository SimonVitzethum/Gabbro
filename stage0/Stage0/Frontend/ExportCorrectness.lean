module
public import Stage0.IRBild
public import Grammatik.Parser.Elab.UebersetzeAllg.RecordLaws
public import Stage0.ArrayWitness
public import Grammatik.Parser.Elab.Export.ExportWitnesses
public import Grammatik.Parser.Elab.Export.ExportWitnesses2
@[expose] public section

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
  obtain ⟨output, emitted, image, correct, _⟩ := irBild_correct text K bytes h
  exact ⟨output, emitted, image, compile_source_program text output.compiled, correct,
    fun Γ Λ name value held => held_lower output.compiled.unit Γ Λ name value held⟩

/-- C01's constructor export law applies to the exact unit checked and emitted by the
    source pipeline, together with the inherited whole-image simulation certificate. -/
theorem exported_records_ir_correct [Runner.IR.Kern] [Senke.CloneOK]
    (text : String) (K : Nat) (bytes : List Runner.B) {options : Profil.Options}
    (h : irBild text K options = .ok bytes) :
    ∃ output : Emitted text K options,
      emit text K options = .ok output ∧ output.image.bytes = bytes ∧ output.Correct ∧
      ∀ (Γ : Ctx) (Λ : List (Res (declOf output.compiled.unit))) (fn : UFn) (er : Option Ty)
        (identity : Nat) (reordered : Bool) (sides : List (Ty × USide))
        (args : Args (declOf output.compiled.unit) Γ Λ (sides.map (·.1)))
        (schema : { s : URecord // s.ty = .prod identity (sides.map (·.1)) }),
        output.compiled.unit.exportGate = .ok () →
        lowProductArgs output.compiled.unit Γ Λ fn er
          (lowWertAtE output.compiled.unit Γ Λ fn er) (sides.map (·.1)) (sides.map (·.2)) = .ok args →
        uRecordOf output.compiled.unit.records (.prod identity (sides.map (·.1))) = .ok schema →
        lowWertE output.compiled.unit Γ Λ fn er (.product identity reordered sides) =
          .ok ⟨.prod identity (sides.map (·.1)), Expr.prod identity args⟩ := by
  obtain ⟨output, emitted, image, correct, _⟩ := irBild_correct text K bytes h
  refine ⟨output, emitted, image, correct, ?_⟩
  intro Γ Λ fn er identity reordered sides args schema gate lowered declared
  exact record_lower output.compiled.unit Γ Λ fn er identity reordered sides args
    gate lowered schema declared

/-- Original-source admission retains the successful certified const substitution
    and all remaining runtime metadata checks before G lowering. -/
theorem Compiled.exports_metadata {text : String} {options : Profil.Options} (result : Compiled text options)
    (h : result.unit.exportGate = .ok ()) :
    ∃ rewritten,
      Konst.konstErsetzePipeline (uMembers (pre108 result.source.prepared.elaborierbar)) = .ok rewritten ∧
      Konst.checkErsetzt (uMembers (pre108 result.source.prepared.elaborierbar)) rewritten = .ok () ∧
      (Konst.ohneKonst rewritten).any ExportMetadata.itemMetadata = false :=
  Konst.checkSourceMetadata_sound _ (result.metadata.symm.trans h)

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

/-- Constant header admission retains its successful original-source expansion. -/
theorem Compiled.constant_exports_metadata {text : String} {options : Profil.Options}
    (result : Compiled text options)
    (used : (uMembers (pre108 result.source.prepared.elaborierbar)).any ExportMetadata.constantExpansion = true) :
    ∃ rewritten,
      Konst.konstErsetzePipeline (uMembers (pre108 result.source.prepared.elaborierbar)) = .ok rewritten ∧
      Konst.checkErsetzt (uMembers (pre108 result.source.prepared.elaborierbar)) rewritten = .ok () ∧
      (Konst.ohneKonst rewritten).any ExportMetadata.itemMetadata = false :=
  Konst.checkSourceConstants_sound _ used result.constantExports

/-- The actual compiler refuses new nonzero scalar initializers until image memory is initialized. -/
theorem Compiled.initializer_exports {text : String} {options : Profil.Options} (result : Compiled text options) :
    Frontend.uninitializedExport (uMembers (pre108 result.source.prepared.elaborierbar)) result.unit = false :=
  Frontend.checkInitializers_sound _ _ result.initializerExports

/-- Every source image from the production compiler has the same canonical source program
    and IR simulation. Reach, tree and array exports retain the original-source duty gate
    at every lexical/result context, including nested and empty quantifiers. -/
theorem exported_batch2_ir_correct [Runner.IR.Kern] [Senke.CloneOK]
    (text : String) (K : Nat) (bytes : List Runner.B) {options : Profil.Options}
    (h : irBild text K options = .ok bytes) :
    ∃ output : Emitted text K options,
      emit text K options = .ok output ∧ output.image.bytes = bytes ∧
      CanonicalSourceProgram output.compiled ∧ output.Correct ∧
      ExportMetadata.checkConstants (uMembers (pre108 output.compiled.source.prepared.elaborierbar)) = .ok () ∧
      (∀ (Γ : Ctx) (Λ : List (Res (declOf output.compiled.unit))) (fn : UFn) (er : Option Ty)
        (universal : Bool) (source : USide) (binder : String) (body : UEns)
        (value : Expr (declOf output.compiled.unit) Γ Λ .bool),
        lowEns output.compiled.unit Γ Λ fn er (.arrayElements universal source binder body) = .ok value →
        (uMembers (pre108 output.compiled.source.prepared.elaborierbar)).any ExportMetadata.itemMetadata = false) ∧
      (∀ (Γ : Ctx) (Λ : List (Res (declOf output.compiled.unit))) (fn : UFn) (shift : Nat)
        (table field : String) (a b : UIdx) (value : Expr (declOf output.compiled.unit) Γ Λ .bool),
        lowReach output.compiled.unit Γ Λ fn shift table field a b = .ok value →
        (uMembers (pre108 output.compiled.source.prepared.elaborierbar)).any ExportMetadata.itemMetadata = false) ∧
      (∀ (Γ : Ctx) (Λ : List (Res (declOf output.compiled.unit))) (fn : UFn) (er : Option Ty)
        (universal reverse : Bool) (table binder field : String) (source : UIdx) (body : UEns)
        (value : Expr (declOf output.compiled.unit) Γ Λ .bool),
        lowEns output.compiled.unit Γ Λ fn er (.filtered universal table binder field reverse source body) = .ok value →
        (uMembers (pre108 output.compiled.source.prepared.elaborierbar)).any ExportMetadata.itemMetadata = false) ∧
      (∀ (Γ : Ctx) (Λ : List (Res (declOf output.compiled.unit))) (fn : UFn) (shift : Nat)
        (table : String) (source : UIdx) (value : Expr (declOf output.compiled.unit) Γ Λ .bool),
        lowMember output.compiled.unit Γ Λ fn shift table source = .ok value →
        (uMembers (pre108 output.compiled.source.prepared.elaborierbar)).any ExportMetadata.itemMetadata = false) ∧
      (∀ (Γ : Ctx) (Λ : List (Res (declOf output.compiled.unit))) (fn : UFn) (er : Option Ty)
        (op : String) (a b : USide) (n m : Nat)
        (x : Expr (declOf output.compiled.unit) Γ Λ (.str n)) (y : Expr (declOf output.compiled.unit) Γ Λ (.str m))
        (value : Expr (declOf output.compiled.unit) Γ Λ .bool),
        lowWertE output.compiled.unit Γ Λ fn er a = .ok ⟨.str n, x⟩ →
        lowWertE output.compiled.unit Γ Λ fn er b = .ok ⟨.str m, y⟩ →
        lowCmp output.compiled.unit Γ Λ fn er op a b = .ok value →
        (uMembers (pre108 output.compiled.source.prepared.elaborierbar)).any ExportMetadata.itemMetadata = false) := by
  obtain ⟨output, emitted, image, correct, _⟩ := irBild_correct text K bytes h
  refine ⟨output, emitted, image, compile_source_program text output.compiled, correct,
    output.compiled.constantExports, ?_, ?_, ?_, ?_, ?_⟩
  · intro Γ Λ fn er universal source binder body value lowered
    exact output.compiled.exports_metadata
      (array_quantifier_gate _ Γ Λ fn er universal source binder body value lowered)
  · intro Γ Λ fn shift table field a b value lowered
    exact output.compiled.exports_metadata (reach_gate _ Γ Λ fn shift table field a b value lowered)
  · intro Γ Λ fn er universal reverse table binder field source body value lowered
    exact output.compiled.exports_metadata
      (tree_quantifier_gate _ Γ Λ fn er universal reverse table binder field source body value lowered)
  · intro Γ Λ fn shift table source value lowered
    exact output.compiled.exports_metadata (member_gate _ Γ Λ fn shift table source value lowered)
  · intro Γ Λ fn er op a b n m x y value first last lowered
    exact output.compiled.exports_metadata (strings_gate _ Γ Λ fn er op a b n m x y first last value lowered)

/-- An actual accepted nonempty nested-array source/image instantiates the generic
    certificate with the original initializer duty and canonical program jointly satisfied. -/
theorem exported_batch2_ir_correct_zeuge [Runner.IR.Kern] [Senke.CloneOK] :
    ∃ output : Emitted ArrayWitness.text 64,
      emit ArrayWitness.text 64 = .ok output ∧ output.Correct ∧
      CanonicalSourceProgram output.compiled ∧
      Frontend.uninitializedExport (uMembers (pre108 output.compiled.source.prepared.elaborierbar)) output.compiled.unit = false := by
  have image : irBild ArrayWitness.text 64 = .ok ArrayWitness.output.image.bytes := by
    change (emit ArrayWitness.text 64).map (fun output => output.image.bytes) = _
    rw [ArrayWitness.accepted_image]
    rfl
  obtain ⟨output, emitted, _, canonical, correct, _⟩ :=
    exported_batch2_ir_correct ArrayWitness.text 64 ArrayWitness.output.image.bytes image
  exact ⟨output, emitted, correct, canonical, output.compiled.initializer_exports⟩

end Gabbro.Stage0
