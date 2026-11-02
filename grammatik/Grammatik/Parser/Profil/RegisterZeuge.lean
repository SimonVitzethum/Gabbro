module

public import Grammatik.Parser.Profil.Register
public import Grammatik.Kern.Syntax.Profil.Teil2
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

/-!
  File:      Grammatik/Parser/Profil/RegisterZeuge.lean
  Subject:   WITNESSES for the source-bound profile (C14): one profile with a library requiring a subset of
             it, an `assume` resolved in the registry, both halves of `bindungB` satisfied together, and the
             model consequences (`modusProfil_modell`, `bindung_fuegt_nichts_hinzu_bindung`) on the same
             fixture; then one negative twin per refusal.
-/

namespace Gabbro.Grammatik.Parser.ProfilBindung

open Gabbro.Grammatik

set_option maxRecDepth 100000

/-- The declaration of the fixture: one assumption, a library requiring a subset of the one profile. -/
def zeugeItems : List SItemTief :=
  [ .assumT "gpu_progress" none "The GPU retires one work item per clock." (.probe "sonde_gpu_tick"),
    .modT "gpu" [ .profT true [.mode "arch" "x86_64", .mode "fp_contract" "off", .assum "gpu_progress"] ],
    .profT false [.mode "arch" "x86_64", .mode "rounding" "nearest", .mode "fp_contract" "off",
      .mode "memory_model" "c11", .assum "gpu_progress"] ]

/-- The fixture is admitted: decodable modes, agreement, a resolved assumption, covered requirements. -/
theorem zeugeBindung_ok : bindungB (ProfileBinding.aus zeugeItems) = true := by decide

/-- The fixture has exactly one profile block. -/
theorem zeugeBindung_profil :
    (ProfileBinding.aus zeugeItems).profile.length = 1 := by decide

/-- JOINT witness: the admitted fixture has a mode assignment under which its decoded modes hold, and
    under any such assignment its library's decoded requirements hold. -/
theorem zeugeBindung_modell :
    ∃ m : ModusBelegung, ∃ p ∈ (ProfileBinding.aus zeugeItems).profile,
      Profil.gilt (modusProfil zeugeD (modi p.eintraege)) m ∧
      ∀ lib ∈ (ProfileBinding.aus zeugeItems).bedarfe,
        Bibliothek.gilt (modusBibliothek zeugeD "gpu" (modi lib.eintraege)) m := by
  have hb := zeugeBindung_ok
  have hp : (ProfileBinding.aus zeugeItems).profile =
      [⟨[], false, [.mode "arch" "x86_64", .mode "rounding" "nearest", .mode "fp_contract" "off",
        .mode "memory_model" "c11", .assum "gpu_progress"]⟩] := by rfl
  have hE : einig (modi [SProfEintrag.mode "arch" "x86_64", .mode "rounding" "nearest",
      .mode "fp_contract" "off", .mode "memory_model" "c11", .assum "gpu_progress"]) = true := by decide
  obtain ⟨m, hm⟩ := modusProfil_modell zeugeD hE
  refine ⟨m, ⟨[], false, [.mode "arch" "x86_64", .mode "rounding" "nearest", .mode "fp_contract" "off",
    .mode "memory_model" "c11", .assum "gpu_progress"]⟩, by rw [hp]; exact List.mem_singleton_self _, hm, ?_⟩
  intro lib hl
  exact bindung_fuegt_nichts_hinzu_bindung zeugeD "gpu" hb hp hl m hm

/-! ### Negative twins: each refusal of `bindungB` -/

/-- Two keyed entries, one key, two values (`N215`). -/
theorem zeuge_konflikt :
    bindungB (ProfileBinding.aus [.profT false [.mode "arch" "x86_64", .mode "arch" "aarch64"]]) = false := by
  decide

/-- An unsupported mode value (`fp_contract fast`, `N218`). -/
theorem zeuge_wert_unbekannt :
    bindungB (ProfileBinding.aus [.profT false [.mode "fp_contract" "fast"]]) = false := by decide

/-- An unknown key. -/
theorem zeuge_schluessel_unbekannt :
    bindungB (ProfileBinding.aus [.profT false [.mode "endian" "little"]]) = false := by decide

/-- A reference to no declared assumption (`N219`). -/
theorem zeuge_annahme_fehlt :
    bindungB (ProfileBinding.aus [.profT false [.assum "nirgends"]]) = false := by decide

/-- The same name with two different statements (`N216`). -/
theorem zeuge_annahme_doppelt :
    bindungB (ProfileBinding.aus
      [ .assumT "a" none "one" (.probe "p"), .assumT "a" none "two" (.probe "p"),
        .profT false [.assum "a"] ]) = false := by decide

/-- A second profile block (`N219`). -/
theorem zeuge_zweites_profil :
    bindungB (ProfileBinding.aus [.profT false [], .profT false []]) = false := by decide

/-- A library requirement the profile does not hold (`N217`). -/
theorem zeuge_bedarf_ungedeckt :
    bindungB (ProfileBinding.aus
      [ .modT "lib" [.profT true [.mode "memory_model" "c11"]],
        .profT false [.mode "arch" "x86_64"] ]) = false := by decide

/-- A library requirement with no profile at all. -/
theorem zeuge_bedarf_ohne_profil :
    bindungB (ProfileBinding.aus [.modT "lib" [.profT true [.mode "arch" "x86_64"]]]) = false := by
  decide

#print axioms Gabbro.Grammatik.Parser.ProfilBindung.zeugeBindung_modell
#print axioms Gabbro.Grammatik.Parser.ProfilBindung.modusProfil_modell
#print axioms Gabbro.Grammatik.Parser.ProfilBindung.bindung_fuegt_nichts_hinzu_bindung

end Gabbro.Grammatik.Parser.ProfilBindung
