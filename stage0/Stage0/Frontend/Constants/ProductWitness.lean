module
public import Stage0.Frontend.Constants.ArrayConstants
@[expose] public section

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Two differently typed fields and reordered labels exercise actual schema-based collection. -/
def productConstantFixture : List SItemTief :=
  [.typeT [] "Pair" [] [] (some (.raw "{ small : u8, flag : bool, }")),
   .constT "VALUES" (.array (.array (.atom "Pair") (.lit 1)) (.lit 1))
     (.rows [.rows [.one (.call "Pair"
       [.ext .label ["flag"] [.tru], .ext .label ["small"] [.bin "+" (.lit 40) (.lit 2)]])]]),
   .constT "LIMIT" (.atom "u8") (.one (.lit 42))]

def productConstantUnit : UProg :=
  { tabs := [], locks := [], fns := [], records :=
      [{name := "Pair", identity := 0, fields := [("small", .int 0 255), ("flag", .bool)]}] }

def productConstantScope : Scopes productConstantFixture :=
  evaluatedScopes productConstantFixture [("LIMIT", 42)] (by decide +kernel)

/-- A nondegenerate nested product array passes the same strict original-source checker that
    compileChecked consumes; no runtime declaration or use is needed to retain its initializer. -/
theorem constantMeaning_typed_retained_zeuge :
    ∃ τ raw, ∃ term : Expr (declOf productConstantUnit) [] [] τ,
      uTypIn productConstantScope.types [] (uRecordConstantTypes productConstantUnit.records) [] []
        (.array (.array (.atom "Pair") (.lit 1)) (.lit 1)) = .ok τ ∧
      uKonstZeile productConstantScope.types productConstantScope.functions productConstantScope.values τ
        (.rows [.rows [.one (.call "Pair"
          [.ext .label ["flag"] [.tru], .ext .label ["small"] [.bin "+" (.lit 40) (.lit 2)]])]])
        (uRecordConstant productConstantUnit.records productConstantScope.types
          productConstantScope.functions productConstantScope.values) = some raw ∧
      ("VALUES", USide.typed τ raw) ∈ constantValues productConstantUnit productConstantScope ∧
      lowLit (u := productConstantUnit) (Γ := []) (Λ := []) τ raw = .ok term := by
  apply constantMeaning_typed_retained productConstantUnit productConstantScope
    "VALUES" (.array (.array (.atom "Pair") (.lit 1)) (.lit 1))
    (.rows [.rows [.one (.call "Pair"
      [.ext .label ["flag"] [.tru], .ext .label ["small"] [.bin "+" (.lit 40) (.lit 2)]])]])
  · simp [productConstantFixture]
  · exact ((checkArrayItem productConstantUnit productConstantScope _).toOption.get
      (by decide +kernel)).down

/-- An unused declaration with an overflowing intermediate is refused before collection. -/
theorem productConstant_unused_overflow_zeuge :
    (checkArrayItem productConstantUnit productConstantScope
      (.constT "UNUSED" (.atom "Pair") (.one (.call "Pair"
        [.ext .label ["small"] [.bin "-" (.bin "+" (.lit 255) (.lit 1)) (.lit 214)],
         .ext .label ["flag"] [.tru]])))).toOption.isSome = false := by
  decide +kernel

/-- The original scalar guarantee is obtained from the same mandatory final gate. -/
theorem arrayMeaning_scalarStep_zeuge :
    ScalarStep productConstantScope (.constT "LIMIT" (.atom "u8") (.one (.lit 42))) :=
  arrayMeaning_scalarStep productConstantUnit productConstantScope _
    ((checkArrayItem productConstantUnit productConstantScope _).toOption.get (by decide +kernel)).down

theorem constantMeaning_scalarStep_zeuge :
    ScalarStep productConstantScope (.constT "LIMIT" (.atom "u8") (.one (.lit 42))) :=
  constantMeaning_scalarStep productConstantScope _
    (checkConstantMeaning_sound _ _ _ _ (by decide +kernel))

/-- Reuse the existing typed fixture to witness generic retention with production parameters. -/
theorem uKonstArrays_retains_zeuge :
    ∃ ty raw, ("VALUES", USide.typed ty raw) ∈
      uKonstArrays productConstantScope.types productConstantScope.functions productConstantScope.values
        productConstantFixture (uRecordConstantTypes productConstantUnit.records)
        (uRecordConstant productConstantUnit.records productConstantScope.types
          productConstantScope.functions productConstantScope.values) true := by
  obtain ⟨ty, raw, _, _, _, retained, _⟩ := constantMeaning_typed_retained_zeuge
  exact ⟨ty, raw, retained⟩

end Gabbro.Stage0.Frontend
