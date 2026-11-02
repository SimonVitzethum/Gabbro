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

/-!
  File:      Grammatik/Zielsatz/Projekte/ProfilZeuge.lean
  Subject:   WITNESS of `gabbro_ziel_profil` (C14): the flag program of `AtomarGoalZeuge` as a selected unit
             whose original items carry a profile with an `assume` and a library requirement, two aligned
             statics in two region labels and a test-build gate; every premise of the statement holds
             jointly (the checker and the structural admission, the user's logic with the rely, the
             profile-selected hardware components, the runtime's full start), and the conclusion `ZielFX`
             follows on every reachable thread machine. Both build modes are separate instances.
-/

namespace Gabbro.Grammatik.AtomarXZeuge

open Gabbro.Grammatik Speichermodell Zielsatz NIZeuge
open Gabbro.Grammatik.Parser.ProfilBindung (zeugeItems pzItems pzPol)

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

/-- **`gabbro_ziel_profil` on the flag program**, in either build mode: `ZielFX` on every reachable thread
    machine over GX of the runtime's full start, every budget, every set of initially live threads. -/
theorem pe_gabbro (m : Parser.Auswahl.BauModus) (passes : Nat) (lebt0 : Faden → Bool)
    (K : FadenMaschine nD.mitRuhe)
    (hK : FadenErreichbarX n1E.P.mitRuhe nO.mitRuhe passes (GeteiltV (D := nD) n1E.P n1E.ws)
      (FadenStart n1E.P.mitRuhe (speicherR n1E.sp0) (initRuhe n1E.starts) lebt0) K) :
    ZielFX n1E.P.mitRuhe n1E.S.mitRuhe nO.mitRuhe passes (GeteiltV (D := nD) n1E.P n1E.ws)
      (RufStartG n1E.P.mitRuhe (speicherR n1E.sp0) (initRuhe n1E.starts)) [] K :=
  gabbro_ziel_profil akzeptiertX_pruefer nD (peE m) ⟨nFs, nFs_voll⟩ ⟨[], fun L => nomatch L⟩
    ⟨nCs, nCs_voll⟩
    (by
      have h1 : akzeptiertX_pruefer.akzeptiert n1E nFs [] nCs = true := by
        show (AkzeptiertX nP SchwachZeuge.nS nFs [] nCs n1ws && besitzB n1E nFs) = true
        rw [n1_akzeptiertX]; rfl
      simp only [profilAkzeptiert, Bool.and_eq_true]
      exact ⟨h1, pe_zulaessig m⟩)
    n1E_nutzerPflichtA nO ((profilAnnahmen_iff (peE m) nO).mpr ⟨nO_gut, nO_lokal, axVertragO_wahr nO⟩)
    passes _ _ (laufzeit_voll n1E) lebt0 K hK

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

#print axioms pe_gabbro

end Gabbro.Grammatik.AtomarXZeuge
