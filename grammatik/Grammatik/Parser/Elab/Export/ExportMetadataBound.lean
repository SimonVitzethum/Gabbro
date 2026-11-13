/-
  Bound forms of the export gate: forms whose duties have a checked binding, each with its witness
  (moved out of `ExportMetadata.lean`, which holds the gate itself).
-/
module
public import Grammatik.Parser.Elab.Export.ExportMetadata
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportMetadata

/-- C17 retains the exact source tree. Unit alias checks, duplicate-clause refusal and
    certified measure lowering remain mandatory in `uMeasureClause` and Stage 0. -/
theorem drops_bound (e : SExpr)
    (h : (Gabbro.Grammatik.Parser.Uebersetze.uMeasureSource e).toOption.isNone = false) :
    clausesMetadata [.drops e] = false := by
  simp [clausesMetadata, h]

theorem drops_zeuge :
    clausesMetadata [.drops (.variable "n")] = false ∧
    clausesMetadata [.drops (.old (.variable "n"))] = true := by
  exact ⟨rfl, rfl⟩

/-- A consuming header is bound only through the same complete parser used by uLoopExport;
    metadata in every nested continuation is still checked. -/
theorem consuming_bound (fuel : Nat) (binder kind raw touches : String) (origin : Option SExpr)
    (subject measure : SExpr) (invariant : Option SExpr) (body : SAnw)
    (parsed : consumingHeader raw = .ok (measure, touches)) :
    bodyMetadata (fuel + 1) (.each binder origin kind subject "consuming" raw invariant body) =
      bodyMetadata fuel body := by
  simp only [bodyMetadata, BEq.rfl, ↓reduceIte, parsed, Except.toOption,
    Option.isNone_some, Bool.false_or]

/-- C14 gates are consumed only by canonical build selection, before metadata checking.
    Raw wrappers remain refused; selection never suppresses the retained item's duties. -/
theorem gateT_bound (m : Auswahl.BauModus) (items selected : List SItemTief)
    (selection : selected = Auswahl.waehleL m items)
    (clear : unitMetadata selected = false) :
    check (Auswahl.waehleL m items) = .ok () := by
  rw [← selection]
  exact check_clear selected clear

theorem gateT_zeuge :
    check [.gateT (.constT "sample" (.atom "u8") (.one (.lit 1)))] =
      .error "source export: SItemTief.gateT: type/provider/proof duties lack a checked source binding" ∧
    check (Auswahl.waehleL .auslieferung
      [.gateT (.constT "sample" (.atom "u8") (.one (.lit 1)))]) = .ok () ∧
    check (Auswahl.waehleL .pruefbau
      [.gateT (.constT "sample" (.atom "u8") (.one (.lit 1)))]) = .ok () ∧
    check (Auswahl.waehleL .pruefbau [.gateT (.groupT "G" [] [])]) =
      .error "source export: invariant cost/runs/by duties lack a checked source binding" := by
  exact ⟨rfl, rfl, rfl, rfl⟩
/-- The table owner field adds no unbound placement duty; providers and backing remain gated. -/
theorem tableSpace_bound (name owner : String) (count : Option SExpr) (shared : Bool) :
    itemMetadata (.tableT name none count none (some owner) shared []) = false := by rfl

theorem tableSpace_zeuge :
    check [.tableT "T" none (some (.lit 2)) none (some "Data") false []] = .ok () ∧
    itemMetadata (.tableT "T" (some "provider") (some (.lit 2)) none (some "Data") false []) = true ∧
    itemMetadata (.tableT "T" none (some (.lit 2)) (some "place") (some "Data") false []) = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- A nominal space is bound by the table declaration and resolved by the
    canonical collector. It discharges no placement, owner or hardware duty. -/
theorem tableNominalSpace_bound (name space : String) (owner : Option String)
    (count : Option SExpr) (shared : Bool) :
    itemMetadata (.tableT name none count none owner shared [] (some space)) = false := rfl

theorem namedPointer_bound (space target : String) :
    typeMetadata (.ptr space "r" (.atom target)) = (target == "u8") := by
  have hd : (match Gabbro.Grammatik.DataRights.decode (fun _ => none) "r" with
      | some r => r.owner.isSome
      | none => true) = false := rfl
  show ((match Gabbro.Grammatik.DataRights.decode (fun _ => none) "r" with
      | some r => r.owner.isSome
      | none => true) || target == "u8") = (target == "u8")
  rw [hd, Bool.false_or]

theorem namedPointer_zeuge :
    typeMetadata (.ptr "sharedData" "r" (.atom "T")) = false ∧
    typeMetadata (.ptr "sharedData" "x" (.atom "T")) = true ∧
    typeMetadata (.ptr "sharedData" "rw" (.atom "u8")) = true ∧
    typeMetadata (.ptr "sharedData" "r" (.raw "T")) = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩
/-- A nonempty reset range carries no unbound metadata. -/
theorem reset_bound_zeuge :
    bodyMetadata 3 (.reset "A" (some (.lit 1, .lit 2))) = false :=
  reset_bound 2 "A" (some (.lit 1, .lit 2))

/-- Mint output admission still needs the root-once and software-call bridge. -/
theorem mint_effect_metadata_refused :
    clausesMetadata [.effs [.mints "Mark"]] = true ∧
    clausesMetadataWithoutLoad [.effs [.mints "Mark"]] = true := by
  exact ⟨rfl, rfl⟩

/-- Plain marks carry no erased body or proof metadata. -/
theorem linear_mark_metadata_zeuge :
    itemMetadata (.typeT ["linear"] "Mark" [] [] none) = false ∧
    bodyMetadata 1 (.retires "Mark") = false := by
  exact ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.ExportMetadata
