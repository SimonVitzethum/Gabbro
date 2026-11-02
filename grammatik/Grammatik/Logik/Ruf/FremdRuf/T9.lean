/- Part 9 of `FremdRuf` (C08): witnesses on the gate fixture `fdD`/`fdO`.

   * a boundary history of FIVE records on one table: two fresh disjoint success grants
     (the first preserved when the second arrives), a failure that introduces no grant, a
     declared release of the first grant, and the reissue of its base with a shorter extent
     -- realized against the actual binding `fdO` step by step (`ProviderOk`), with the live
     inventory computed by the deterministic fold and pairwise disjoint (`ProviderTreueG`);
   * the narrowed hardware premise and the premise split on the fixture: the oracle meets
     `HardwareAnnahmenHw`, the software part is empty (no item is declared software), and
     together they give the old premise;
   * the footprint cover for the trivial contract.

   The fixture declares no software item and its contracts are trivial, so a software duty
   with a contract that reads memory is covered by the generic theorems only. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T8
public import Grammatik.Logik.Ruf.FremdRuf.T7
public import Grammatik.Logik.Ruf.FremdRuf.T1

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

/-- The first grant: bytes `[0, 8)` of the table. -/
def fdKonz1 : Konzession fdD := { tab := (), basis := 0, laenge := 8 }

/-- The second grant: bytes `[8, 16)`, disjoint from the first. -/
def fdKonz2 : Konzession fdD := { tab := (), basis := 8, laenge := 8 }

/-- The reissue of the first grant's base after its release, with a shorter extent. -/
def fdKonz3 : Konzession fdD := { tab := (), basis := 0, laenge := 4 }

/-- The binding's actual answer of the open gate at the start world. -/
def fdWirkt : World fdD × Int := fdO.wirkt fdOpen fdWelt0 Env.nil

/-- A boundary record of the open gate, linked to the actual answer of `fdO`. -/
def fdRec (erfolg : Bool) (k : Option (Konzession fdD)) (fr : Option (fdD.Tab × Int)) :
    BoundaryRecord fdD :=
  { ax := fdOpen, args := Env.nil, eingabe := fdWelt0, ausgabe := fdWirkt.1, roh := fdWirkt.2, erfolg := erfolg, konzession := k, freigabe := fr }

theorem fdRec_gebunden (e : Bool) (k : Option (Konzession fdD)) (fr : Option (fdD.Tab × Int)) :
    RecordGebunden fdO (fdRec e k fr) := rfl

theorem fdRec_frame (e : Bool) (k : Option (Konzession fdD)) (fr : Option (fdD.Tab × Int)) :
    Rahmen (fdD.aschreibt (fdRec e k fr).ax) (fdD.agschreibt (fdRec e k fr).ax)
      (fdRec e k fr).eingabe (fdRec e k fr).ausgabe :=
  fdO_rahmen_open fdWelt0 Env.nil

/-- The history: grant one, grant two, a failed call, release of grant one, reissue of its base. -/
def fdHistorie : List (BoundaryRecord fdD) :=
  (((([] ++ [fdRec true (some fdKonz1) none]) ++ [fdRec true (some fdKonz2) none]) ++
    [fdRec false none none]) ++ [fdRec true none (some ((), 0))]) ++
    [fdRec true (some fdKonz3) none]

/-- **ZEUGE** (provider realization): the five-record history is realized against the actual
    binding, step by step -- two fresh grants (the second disjoint from the live first), a
    failure without grant, a release of a live grant, a reissue of the released base. -/
theorem fdHistorie_realisiert : ProviderRealisiert fdO fdHistorie := by
  refine ⟨_, ProviderOk.erfolg (ProviderOk.freigabe (ProviderOk.fehler
    (ProviderOk.erfolg (ProviderOk.erfolg ProviderOk.nil (fdRec true (some fdKonz1) none)
      (fdRec_gebunden _ _ _) (fdRec_frame _ _ _) rfl fdKonz1 rfl (by decide) (by decide)
      (by intro j hj; exact absurd hj (by simp)) rfl)
      (fdRec true (some fdKonz2) none) (fdRec_gebunden _ _ _) (fdRec_frame _ _ _) rfl fdKonz2 rfl
      (by decide) (by decide) ?_ rfl)
    (fdRec false none none) (fdRec_gebunden _ _ _) (fdRec_frame _ _ _) rfl rfl rfl)
    (fdRec true none (some ((), 0))) (fdRec_gebunden _ _ _) (fdRec_frame _ _ _) ((), 0) rfl rfl
    ⟨fdKonz1, by simp, rfl⟩)
    (fdRec true (some fdKonz3) none) (fdRec_gebunden _ _ _) (fdRec_frame _ _ _) rfl fdKonz3 rfl
    (by decide) (by decide) ?_ rfl⟩
  · intro j hj
    simp only [List.nil_append, List.mem_singleton] at hj
    rw [hj]
    intro h
    obtain ⟨_, _, h3⟩ := h
    exact absurd h3 (by decide)
  · intro j hj
    obtain ⟨hmem, hp⟩ := List.mem_filter.mp hj
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with h1 | h2
    · rw [h1] at hp
      simp [Konzession.schluessel, fdKonz1] at hp
    · rw [h2]
      intro h
      obtain ⟨_, h2', _⟩ := h
      exact absurd h2' (by decide)

/-- **ZEUGE** (live inventory): after the release and the reissue, two grants are live. -/
theorem fdHistorie_zwei_lebendig : (GrantInventory fdHistorie).length = 2 := by rfl

/-- **ZEUGE** (provider fidelity): the history is realized and the live grants are pairwise
    disjoint, one global inventory. -/
theorem fdHistorie_treu : ProviderTreueG fdO fdHistorie :=
  providerTreueG_of_realisiert fdHistorie_realisiert

/-- **ZEUGE** (negative twin of freshness): a second success grant overlapping the live first one
    is no step of the provider judgment. -/
theorem fdKonz_ueberlappt : fdKonz1.ueberschneidet fdKonz3 := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- The fixture's oracle meets the narrowed hardware premise: frame, register locality, and the
    declared ensures of every item not declared software. -/
theorem fdO_hwHw : HardwareAnnahmenHw fdO fdQ :=
  ⟨fdO_gut, ⟨fun r => (nomatch r), fun g => (nomatch g)⟩, axVertragOHw_of_O fdQ_vertrag⟩

/-- The fixture declares no software item, so the software duty is empty. -/
theorem fdD_ohne_software : ∀ a : fdD.Ax, fdD.axHerkunft a ≠ some AxOrigin.software := by
  intro a h
  have h' : (none : Option AxOrigin) = some AxOrigin.software := h
  cases h'

/-- **ZEUGE** (premise split): the narrowed hardware premise and the empty software duty give the
    old premise (c) on the fixture. -/
theorem fdO_hw_aus_split : HardwareAnnahmen fdO fdQ :=
  hardwareAnnahmen_of_split fdO_hwHw (axVertragOSw_ohne fdD_ohne_software)

/-- The trivial contracts of the fixture read nothing: every frame covers them. -/
theorem fdVertrag_gedeckt :
    AxVorGedeckt (fun a : fdD.Ax => callVertragWahr fdD (fdD.asignatur a)) :=
  axVorGedeckt_wahr _ (fun _ => rfl)

end Gabbro.Grammatik
