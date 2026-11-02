module

public import Grammatik.Logik.Vertraege.Komposition.Teil1Basis
import all Grammatik.Logik.Vertraege.Komposition.Teil1Basis


@[expose] public section


set_option linter.defProp false

namespace Gabbro.Grammatik
/-- Zwei Ruempfe im Kreis, BEIDE mit Mass -- damit die Luecke die Ordnung ist und
    nicht das Mass: `a` traegt die Schleife `s`, `b` kehrt zurueck. -/
def UmgekehrteTabelle : String → Option Routine
  | "a" => some { ruft := ["b"], mass := some 1, schleifen := ["s"] }
  | "b" => some { ruft := ["a"], mass := some 0, schleifen := [] }
  | _ => none

/-- Das Gefuege ueber dieser Tabelle: die Umgebung laeuft alles, die Schleifenregel
    gilt -- aber KEIN Vertrag gilt. Die umgekehrte Ordnung duerfte die vollen
    Vertraege annehmen und schloesse damit nichts. -/
def Umgekehrt : Gefuege :=
  { tabelle := UmgekehrteTabelle
    laeuft := fun _ => True
    vertrag := fun _ => False
    schleifenRegel := fun _ => True }

/-- Die Mitglieder des Kreises als Daten: Namen, Rufe und Masse. -/
def UmgekehrteMitglieder : List Mitglied :=
  [ ({ name := "a", ruft := ["b"], mass := some 1 } : Mitglied),
    ({ name := "b", ruft := ["a"], mass := some 0 } : Mitglied) ]

/-- Der Durchgang der Schleife `s`: ein Durchgang ueber einen Index. -/
def UmgekehrterDurchgang : Durchgang :=
  { kennung := "s", indizes := [0] }

/-- Die Schachtelung als Datum: die Schleife `s` sitzt im Mitglied `a`. -/
def schleife_sitzt_in_a :
    SchleifeInMitglied Umgekehrt UmgekehrteMitglieder UmgekehrterDurchgang := by
  exact ⟨({ name := "a", ruft := ["b"], mass := some 1 } : Mitglied),
    by exact List.Mem.head _,
    ({ ruft := ["b"], mass := some 1, schleifen := ["s"] } : Routine), rfl,
    by decide⟩

/-- **Die Abweisung.** Die Schleife `s` sitzt in `a`, die Schleifenregel schliesst,
    jede Pflicht unter vollen Vertraegen haelt -- und trotzdem schliesst die
    umgekehrte Ordnung KEINEN Vertrag: was sie annimmt, ist, was sie zeigen muesste. -/
def UmgekehrtWirdAbgewiesen :
    ¬ SchleifeAussenMassInnen Umgekehrt UmgekehrteMitglieder UmgekehrterDurchgang := by
  intro h
  have hA : SchleifeLaeuft Umgekehrt UmgekehrterDurchgang → SchleifenOk Umgekehrt := by
    intro _ _ _
    trivial
  have hB : ∀ r ∈ UmgekehrteMitglieder,
      (∀ r' ∈ UmgekehrteMitglieder, Umgekehrt.vertrag r'.name) →
      Umgekehrt.vertrag r.name := by
    intro _ _ hcirc
    exact hcirc ({ name := "a", ruft := ["b"], mass := some 1 } : Mitglied)
      (by exact List.Mem.head _)
  have hC := h schleife_sitzt_in_a hA hB
  exact hC.1 ({ name := "a", ruft := ["b"], mass := some 1 } : Mitglied)
    (by exact List.Mem.head _)

#print axioms Gabbro.Grammatik.schleife_sitzt_in_a
#print axioms Gabbro.Grammatik.UmgekehrtWirdAbgewiesen

/-! ## 10. Die S2-Saetze ueber Grammatik-Koerpern -- bewiesen

    `theorem`, nicht `def`: was §1-§9 als Form hinstellte, schliesst hier, wo es
    schliesst -- und wo es nicht schliesst, steht das Datum daneben (C7). Kein
    Import (C8): die Laufform ist `Durchgang.indizes`, die Induktion laeuft ueber
    diese Liste wie `traverseLauf` ueber der seinen. -/

/-- **Die Zyklushebung IST die getragene Form.** `ZyklusAusMass` und
    `RekursionZyklusGetragen` sind derselbe Satz ueber demselben Gefuege -- die
    Pflicht unter den beschraenkten Vertraegen schliesst jeden Vertrag des Zyklus.
    Das ist die Gestalt von `contracts_of_duties_rec` (`Body.lean`), hier ohne
    fremdes Modell: Voraussetzung und Schluss stehen in dieser Datei. -/
theorem zyklus_aus_mass_genau (G : Gefuege) (rs : List Mitglied) :
    ZyklusAusMass G rs ↔ RekursionZyklusGetragen G rs :=
  Iff.rfl

/-- Die Richtung, die die Komposition verbraucht: wo der getragene Zyklus steht,
    schliesst die Zyklushebung. -/
theorem zyklus_schliesst_aus_getragen (G : Gefuege) (rs : List Mitglied) :
    RekursionZyklusGetragen G rs → ZyklusAusMass G rs :=
  fun h => h

/-- **Die Umgebung aus Deckung plus Pflichten je Zeile.** Jede Zeile der Tabelle
    liegt im azyklischen Teil oder im getragenen Zyklus (die Deckung, wie in
    `UmgebungOkAusLaeufen`); die Pflicht je Zeile -- unter Ordnung oder unter Mass
    geschlossen -- liefert den Vertrag aus dem Lauf. Die Pflichten sind
    Praemissen, nie Axiome: wessen Logik sie einloest, steht in C2. -/
theorem umgebung_ok_aus_pflichten (G : Gefuege) (fs zs : List String)
    (hdeck : ∀ f, (∃ r, G.tabelle f = some r) → f ∈ fs ∨ f ∈ zs)
    (hazy : ∀ f ∈ fs, G.laeuft f → G.vertrag f)
    (hzy : ∀ z ∈ zs, G.laeuft z → G.vertrag z) :
    UmgebungOk G := by
  intro f htab hlauf
  rcases hdeck f htab with h | h
  · exact hazy f h hlauf
  · exact hzy f h hlauf

/-- **Ein Lauf gibt DIESE Regel.** Die Verkleinerung von `SchleifenOkAusLaeufen`
    (C7): ein Lauf schliesst die Regel seiner Kennung, nicht die aller Schleifen. -/
theorem schleife_gibt_regel (G : Gefuege) (d : Durchgang)
    (h : SchleifeLaeuft G d) : G.schleifenRegel d.kennung :=
  h.2

/-- **Ein Bereichslauf gibt DIESE Regel.** Dasselbe fuer `RunsLoopIn`-Gestalt. -/
theorem bereich_gibt_regel (G : Gefuege) (d : Durchgang) (lo hi : Int)
    (h : SchleifeLaeuftImBereich G d lo hi) : G.schleifenRegel d.kennung :=
  h.2.2

/-- **Ein gezaehlter Lauf gibt DIESE Regel.** Dasselbe fuer die `RunsLoopN`-Gestalt. -/
theorem gezaehlt_gibt_regel (G : Gefuege) (d : Durchgang) (lo hi np : Int)
    (h : SchleifeLaeuftGezaehlt G d lo hi np) : G.schleifenRegel d.kennung :=
  h.2.2

/-- **Gezaehlt liegt im Bereich.** Die `RunsLoopN`-Bedingung traegt die von
    `RunsLoopIn`: wer gezaehlt laeuft, besucht nur Indizes im Bereich. -/
theorem gezaehlt_ist_bereich (d : Durchgang) (lo hi np : Int)
    (h : DurchgangGezaehlt d lo hi np) : DurchgangImBereich d lo hi :=
  h.1

/-- **Gezaehlt laeuft im Bereich.** Die Laufform steigt ab: `RunsLoopN`_IMPLIZIERT
    `RunsLoopIn`-Gestalt (Kennung, Bereich, Regel). -/
theorem gezaehlt_laeuft_bereich (G : Gefuege) (d : Durchgang) (lo hi np : Int)
    (h : SchleifeLaeuftGezaehlt G d lo hi np) :
    SchleifeLaeuftImBereich G d lo hi :=
  ⟨h.1, h.2.1.1, h.2.2⟩

/-- **Im Bereich heisst laufend.** Die `RunsLoopIn`-Gestalt steigt weiter ab zur
    `RunsLoop`-Gestalt: Kennung und Regel reisen mit, der Bereich faellt. -/
theorem bereich_laeuft (G : Gefuege) (d : Durchgang) (lo hi : Int)
    (h : SchleifeLaeuftImBereich G d lo hi) : SchleifeLaeuft G d :=
  ⟨h.1, h.2.2⟩

/-- **Gezaehlt heisst laufend.** Die Kette in einem Schritt: `RunsLoopN`-Gestalt
    gibt `RunsLoop`-Gestalt. -/
theorem gezaehlt_laeuft (G : Gefuege) (d : Durchgang) (lo hi np : Int)
    (h : SchleifeLaeuftGezaehlt G d lo hi np) : SchleifeLaeuft G d :=
  bereich_laeuft G d lo hi (gezaehlt_laeuft_bereich G d lo hi np h)

/-- **Die gezaehlte Schranke ist nichtnegativ.** Wer gezaehlt laeuft, zaehlt gegen
    ein `np ≥ 0`: die Laenge ist als `Int` nichtnegativ, also ist es die Schranke
    darueber. -/
theorem gezaehlt_schranke_nichtnegativ (d : Durchgang) (lo hi np : Int)
    (h : DurchgangGezaehlt d lo hi np) : 0 ≤ np := by
  have hle := h.2
  omega

/-- **Alle Schleifen aus je einem Lauf.** Die volle (U2)-Gestalt (C7): wo JEDE
    eingetragene Schleife einen Lauf hat -- Kennung an Kennung --, gilt
    `SchleifenOk`. Das ist `schleifen_ok_of_runsloop` in dieser Gestalt: die
    Induktion je Durchgang steht in `durchgang_falte_erhaelt`, die Deckung ueber
    alle Kennungen steht hier. -/
theorem schleifen_ok_aus_allen_lauefen (G : Gefuege) (ds : List Durchgang)
    (hdeck : ∀ id, (∃ f r, G.tabelle f = some r ∧ id ∈ r.schleifen) →
      ∃ d ∈ ds, d.kennung = id)
    (halle : ∀ d ∈ ds, SchleifeLaeuft G d) :
    SchleifenOk G := by
  intro id hex
  obtain ⟨d, hds, rfl⟩ := hdeck id hex
  exact (halle d hds).2

/-- **Alle Schleifen aus je einem gezaehlten Lauf.** Dasselbe fuer die
    `RunsLoopN`-Gestalt (`looprule_of_body_p` in dieser Gestalt): der Zaehler
    reist im Durchgang mit (`DurchgangGezaehlt`), die Regel folgt je Kennung. -/
theorem schleifen_ok_aus_gezaehlten_allen (G : Gefuege) (ds : List Durchgang)
    (lo hi np : Int)
    (hdeck : ∀ id, (∃ f r, G.tabelle f = some r ∧ id ∈ r.schleifen) →
      ∃ d ∈ ds, d.kennung = id)
    (halle : ∀ d ∈ ds, SchleifeLaeuftGezaehlt G d lo hi np) :
    SchleifenOk G := by
  apply schleifen_ok_aus_allen_lauefen G ds hdeck
  intro d hds
  exact gezaehlt_laeuft G d lo hi np (halle d hds)

/-- **Die Induktion ueber die Durchgaenge.** Wo jeder besuchte Index die
    Invariante erhaelt -- ein Durchgang je Index wie in `traverseLauf` --, erhaelt
    die Faltung ueber `indizes` sie: die Schleifeninduktion in der Gestalt dieser
    Datei (C8). -/
theorem durchgang_falte_erhaelt (inv : Nat → Prop) (step : Nat → Nat → Nat)
    (xs : List Nat) (h : ∀ i ∈ xs, ∀ s, inv s → inv (step s i))
    (s : Nat) (hs : inv s) : inv (xs.foldl step s) := by
  induction xs generalizing s with
  | nil => simpa using hs
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro i hi s' hs'
        exact h i (List.mem_cons_of_mem _ hi) s' hs'
      · exact h x List.mem_cons_self s hs

/-- Dasselbe am Durchgang: die Faltung ueber `d.indizes` erhaelt die Invariante. -/
theorem durchgang_erhaelt (inv : Nat → Prop) (step : Nat → Nat → Nat)
    (d : Durchgang) (h : ∀ i ∈ d.indizes, ∀ s, inv s → inv (step s i))
    (s : Nat) (hs : inv s) : inv (d.indizes.foldl step s) :=
  durchgang_falte_erhaelt inv step d.indizes h s hs

/-! ### Das Datum, das die Ein-Lauf-Formen abweist -/

/-- EIN Rumpf, ZWEI Schleifen: `f` traegt `s1` und `s2`. -/
def ZweiSchleifenTabelle : String → Option Routine
  | "f" => some { ruft := [], mass := some 0, schleifen := ["s1", "s2"] }
  | _ => none

/-- Das Gefuege darueber: die Umgebung laeuft alles, jeder Vertrag gilt -- aber nur
    die Regel von `s1` gilt. `s2` ist eingetragen und gilt nicht. -/
def ZweiSchleifen : Gefuege :=
  { tabelle := ZweiSchleifenTabelle
    laeuft := fun _ => True
    vertrag := fun _ => True
    schleifenRegel := fun id => id = "s1" }

/-- Der Durchgang ueber `s1`: ein Durchgang ueber einen Index im Bereich. -/
def EinDurchgang : Durchgang :=
  { kennung := "s1", indizes := [0] }

end Gabbro.Grammatik
