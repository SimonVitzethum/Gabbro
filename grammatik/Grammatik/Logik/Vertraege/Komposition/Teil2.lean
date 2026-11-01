module

public import Grammatik.Logik.Vertraege.Komposition.Teil1

@[expose] public section

set_option linter.defProp false
namespace Gabbro.Grammatik

def ein_durchgang_laeuft_gezaehlt :
    SchleifeLaeuftGezaehlt ZweiSchleifen EinDurchgang 0 1 1 := by
  refine ⟨⟨"f", { ruft := [], mass := some 0, schleifen := ["s1", "s2"] },
    rfl, by decide⟩, ?_, rfl⟩
  constructor
  · intro i hi
    simp only [EinDurchgang, List.mem_singleton] at hi
    subst hi
    exact ⟨by decide, by decide⟩
  · decide

/-- ... also laeuft er im Bereich und schlicht. -/
def ein_durchgang_laeuft_bereich :
    SchleifeLaeuftImBereich ZweiSchleifen EinDurchgang 0 1 :=
  gezaehlt_laeuft_bereich ZweiSchleifen EinDurchgang 0 1 1
    ein_durchgang_laeuft_gezaehlt

/-- ... also laeuft er schlicht. -/
def ein_durchgang_laeuft : SchleifeLaeuft ZweiSchleifen EinDurchgang :=
  gezaehlt_laeuft ZweiSchleifen EinDurchgang 0 1 1
    ein_durchgang_laeuft_gezaehlt

/-- **Und trotzdem gilt (U2) nicht:** `s2` ist eingetragen und gilt nicht. -/
def zwei_schleifen_nicht_ok : ¬ SchleifenOk ZweiSchleifen := by
  intro h
  have h2 := h "s2" ⟨"f",
    { ruft := [], mass := some 0, schleifen := ["s1", "s2"] }, rfl, by decide⟩
  simp only [ZweiSchleifen] at h2
  exact absurd h2 (by decide)

/-- **Die Abweisung der Ein-Lauf-Form.** Ein Lauf (`s1`) schliesst NICHT die Regel
    aller Schleifen (`s2` bleibt): `SchleifenOkAusLaeufen` gilt nicht allgemein --
    die Verkleinerung (`schleife_gibt_regel`,
    `schleifen_ok_aus_allen_lauefen`) steht daneben. -/
theorem einzelner_lauf_schliesst_nicht_alle :
    ¬ SchleifenOkAusLaeufen ZweiSchleifen EinDurchgang := by
  intro h
  exact zwei_schleifen_nicht_ok (h ein_durchgang_laeuft)

/-- **Die Abweisung der gezaehlten Ein-Lauf-Form.** Dasselbe fuer
    `SchleifenOkAusGezaehltenLaeufen`: ein gezaehlter Lauf schliesst nicht alle. -/
theorem einzelner_gezaehlter_lauf_schliesst_nicht_alle :
    ¬ SchleifenOkAusGezaehltenLaeufen ZweiSchleifen EinDurchgang 0 1 1 := by
  intro h
  exact zwei_schleifen_nicht_ok (h ein_durchgang_laeuft_gezaehlt)

/-- Die Abweisung aus §7 als Satz: der Zyklus ohne Mass ist nicht getragen. -/
theorem zyklus_ohne_mass_abgewiesen_satz :
    ¬ ZyklusGetragen ZyklusOhneMass ["a", "b"] :=
  ZyklusOhneMassWirdAbgewiesen

/-- Die Abweisung aus §9 als Satz: die umgekehrte Schachtelung schliesst nichts. -/
theorem umgekehrt_abgewiesen_satz :
    ¬ SchleifeAussenMassInnen Umgekehrt UmgekehrteMitglieder UmgekehrterDurchgang :=
  UmgekehrtWirdAbgewiesen

#print axioms Gabbro.Grammatik.zyklus_aus_mass_genau
#print axioms Gabbro.Grammatik.umgebung_ok_aus_pflichten
#print axioms Gabbro.Grammatik.schleife_gibt_regel
#print axioms Gabbro.Grammatik.gezaehlt_laeuft_bereich
#print axioms Gabbro.Grammatik.gezaehlt_schranke_nichtnegativ
#print axioms Gabbro.Grammatik.schleifen_ok_aus_allen_lauefen
#print axioms Gabbro.Grammatik.schleifen_ok_aus_gezaehlten_allen
#print axioms Gabbro.Grammatik.durchgang_falte_erhaelt
#print axioms Gabbro.Grammatik.ein_durchgang_laeuft_gezaehlt
#print axioms Gabbro.Grammatik.zwei_schleifen_nicht_ok
#print axioms Gabbro.Grammatik.einzelner_lauf_schliesst_nicht_alle
#print axioms Gabbro.Grammatik.einzelner_gezaehlter_lauf_schliesst_nicht_alle
#print axioms Gabbro.Grammatik.umgekehrt_abgewiesen_satz

end Gabbro.Grammatik
