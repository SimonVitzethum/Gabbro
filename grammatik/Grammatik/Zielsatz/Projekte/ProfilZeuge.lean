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
The refused atomic flag retains its structural selection witnesses.
The bounded increment supplies the concrete-checker profile goal witness. -/

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

namespace Gabbro.Grammatik.ConcreteGoalZeuge

open Gabbro.Grammatik Speichermodell Zielsatz
open Vertraege.Pruefer.Witness (declaration unit checker_accepted_zeuge
  nutzerPflicht_of_akzeptiert_zeuge)

/-- The accepted increment with the same nonempty profile and placement
    certificate used above, in each of the two build modes. -/
def profileUnit (mode : Parser.Auswahl.BauModus) : ProfilEinheit declaration :=
  ⟨unit, mode, AtomarXZeuge.peItems, Parser.ProfilBindung.pzPol⟩

theorem profile_admitted_zeuge (mode : Parser.Auswahl.BauModus) :
    (profileUnit mode).zulaessig = true :=
  AtomarXZeuge.pe_zulaessig mode

/-- Joint accepted profile, user, hardware and runtime premises, followed
    by the profile goal on every reachable machine. The entry is inhabited
    by concrete_premises_zeuge and has a nontrivial increment contract. -/
theorem gabbro_ziel_profil_zeuge [RootNativeFloat.Hardware]
    (mode : Parser.Auswahl.BauModus) :
    profilAkzeptiert akzeptiertX_pruefer (profileUnit mode) fs.1 ls.1 cs.1 = true ∧
    NutzerPflichtA unit ∧ ProfilAnnahmen (profileUnit mode) oracle ∧
    Laufzeit unit sp init ∧
    ∀ passes K,
      FadenErreichbarX unit.P.mitRuhe oracle.mitRuhe passes
        (GeteiltV (D := declaration) unit.P unit.ws) initial K →
      ZielFX unit.P.mitRuhe unit.S.mitRuhe oracle.mitRuhe passes
        (GeteiltV (D := declaration) unit.P unit.ws)
        (RufStartG unit.P.mitRuhe sp init) [] K := by
  have accepted : profilAkzeptiert akzeptiertX_pruefer (profileUnit mode)
      fs.1 ls.1 cs.1 = true :=
    Bool.and_eq_true.mpr ⟨checker_accepted_zeuge, profile_admitted_zeuge mode⟩
  have hardware : ProfilAnnahmen (profileUnit mode) oracle :=
    (profilAnnahmen_iff (profileUnit mode) oracle).mpr hardware_zeuge
  refine ⟨accepted, nutzerPflicht_of_akzeptiert_zeuge, hardware, laufzeit_voll unit, ?_⟩
  intro passes K reached
  exact gabbro_ziel_profil akzeptiertX_pruefer declaration (profileUnit mode) fs ls cs
    accepted nutzerPflicht_of_akzeptiert_zeuge oracle hardware
    passes sp init (laufzeit_voll unit) (fun _ => true) K reached

#print axioms gabbro_ziel_profil_zeuge

end Gabbro.Grammatik.ConcreteGoalZeuge
