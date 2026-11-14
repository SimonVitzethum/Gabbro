module

public import Grammatik.Zielsatz.Projekte.Profil
public import Grammatik.Zielsatz.Atomar.AtomarGoalZeuge
public import Grammatik.Parser.Profil.RegisterZeuge
public import Grammatik.Parser.Profil.PlatzierungZeuge
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

/-! Profile selection and placement witnesses in both build modes.
The flag's concrete checker refuses atomic reads, so no accepted-unit
application of the profile goal theorem is asserted here. -/

namespace Gabbro.Grammatik.AtomarXZeuge

open Gabbro.Grammatik Speichermodell Zielsatz NIZeuge
open Gabbro.Grammatik.Parser.ProfilBindung (zeugeItems pzItems pzPol)

local instance : DecidableEq nD.Ax := inferInstanceAs (DecidableEq Empty)

set_option maxRecDepth 100000

/-- The original items: the profile fixture, the placement fixture and a gated constant. -/
def peItems : List Parser.SItemTief :=
  zeugeItems ++ pzItems ++ [.gateT (.constT "TESTONLY" (.atom "u32") (.one (.lit 1)))]

/-- The selected unit of the flag program in a build mode. -/
def peE (m : Parser.Auswahl.BauModus) : ProfilEinheit nD := ⟨n1E, m, peItems, pzPol⟩

/-- The certificate of the fixture is admitted in both build modes: no reserved name, the binding passes,
    the two statics' placement is admitted by the policy. -/
theorem pe_zulaessig (m : Parser.Auswahl.BauModus) : (peE m).zulaessig = true := by
  cases m <;> decide

/-- Admission above checks actual library requirements in both modes, rather than an empty list. -/
theorem pe_bedarfe_nicht_leer (m : Parser.Auswahl.BauModus) :
    (peE m).zert.bindung.bedarfe ≠ [] := by
  cases m <;> decide


/-- The selection of the fixture differs by mode: the test build keeps the gated constant, the shipping
    build drops it (so a proof in one mode says nothing about the other). -/
theorem pe_modi_verschieden :
    (peE .pruefbau).zert.auswahl.ausgewaehlt.length =
      (peE .auslieferung).zert.auswahl.ausgewaehlt.length + 1 := by
  decide

/-- The profile of the fixture has a model, and the library's requirements follow from it. -/
theorem pe_profil_modell (m : Parser.Auswahl.BauModus) :
    ∃ mb : ModusBelegung, ∃ p ∈ (peE m).zert.bindung.profile,
      Profil.gilt (Parser.ProfilBindung.modusProfil nD (Parser.ProfilBindung.modi p.eintraege)) mb := by
  have hp : (peE m).zert.bindung.profile =
      [⟨[], false, [.mode "arch" "x86_64", .mode "rounding" "nearest", .mode "fp_contract" "off",
        .mode "memory_model" "c11", .assum "gpu_progress"]⟩] := by
    cases m <;> rfl
  obtain ⟨mb, hmb⟩ := profil_modell_einheit (peE m) (pe_zulaessig m) hp
  exact ⟨mb, _, by rw [hp]; exact List.mem_singleton_self _, hmb⟩

end Gabbro.Grammatik.AtomarXZeuge
