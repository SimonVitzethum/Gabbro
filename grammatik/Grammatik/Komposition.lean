/-
  Datei:      Grammatik/Komposition.lean
  Gegenstand: **Die Komposition der Ruempfe** -- die Gestalt, in der `UmgebungOK` und
              `SchleifenOK` aus den Laeufen entlassen werden. Nur Gestalt, kein Beweis:
              jede Aussage unten steht als `def` ueber `Prop`, nie als `theorem`.

  Was wo steht:

    §1  `Routine`, `Gefuege`      -- die Koerpertabelle UND die Abbildung in die
                                     Umgebung als Felder EINER Struktur
    §2  `ruftAn`, `Topologisch`, `AzyklischUnter`, `ZyklusGetragen`
                                  -- die Ordnung des Rufgraphen: azyklisch
                                     topologisch, zyklisch ueber das Mass
    §3  `Mitglied`, `UnterMass`, `VertragSchranke`, `RekursionZyklusGetragen`
                                  -- die Zyklusform von `Coverage.lean`
                                     (`recursion_cycle_carried`) als `def`
    §4  `UmgebungOk`, `SchleifenOk` -- die beiden Praemissen als `Prop`-wertige
                                     `def`s ueber dem Graphen
    §5  `Durchgang`, `DurchgangBesucht`, `SchleifeLaeuft`
                                  -- der Schleifendurchgang als Indexliste
    §6  `RufAusOrdnung`, `UmgebungOkAusLaeufen`, `ZyklusAusMass`,
        `SchleifenOkAusLaeufen`   -- die Kompositionssaetze als AussageFORMEN
  §7  `OhneMassTabelle`, `ZyklusOhneMass`, `ohne_mass_ist_none`,
        `ZyklusOhneMassWirdAbgewiesen`
                                   -- der Zyklus ohne `decreases` als DATUM, mit
                                      der Abweisung als pruefbarer Form
  §8  `DurchgangImBereich`, `SchleifeLaeuftImBereich`, `DurchgangGezaehlt`,
      `SchleifeLaeuftGezaehlt`, `SchleifenOkAusGezaehltenLaeufen`
                                   -- die gezaehlte Laufform (`RunsLoopN`) als
                                      `def`s nach dem Muster von `RunsLoop` /
                                      `RunsLoopIn` aus §5
  §9  `SchleifeInMitglied`, `MassAussenSchleifeInnen`, `SchleifeAussenMassInnen`,
      `UmgekehrteTabelle`, `Umgekehrt`, `UmgekehrteMitglieder`,
      `UmgekehrterDurchgang`, `schleife_sitzt_in_a`,
      `UmgekehrtWirdAbgewiesen`  -- die feste Schachtelung (Mass aussen,
                                      Schleife innen) und die Abweisung der
                                      umgekehrten als DATUM mit pruefbarer Form

  Entsprechungen (Namen und Form, kein Bezug -- siehe C1):
    `Gefuege.tabelle`             -- `Programm.sig`/`Programm.schleife`
                                     (`Sicherheit/Anweisung.lean`:206)
    `Gefuege.laeuft`              -- `Runs rho f body` (`Body.lean`:1408)
    `Routine.ruft`                -- die Rufstellen des Rumpfes
    `Routine.mass` (`some`)       -- `decreases e` (`SYNTAX.md` §6, «K5.4»);
                                     `none` heisst: kein Mass erklaert
    `Routine.schleifen`           -- die Schleifenkennungen des Rumpfes
                                     (`Programm.schleife`)
    `Durchgang.indizes`           -- `iterate` (`Body.lean`:1415): ein Durchgang
                                     je Index, die Variable daran gebunden
    `Topologisch`/`AzyklischUnter`-- die Induktion ueber die topologische Ordnung
    `RekursionZyklusGetragen`     -- `RecursionCycleCarried` /
                                     `recursion_cycle_carried`
                                     (`Coverage.lean`:972/979)
    `VertragSchranke`             -- `ContractBelowM` (`Body.lean`:1525): der
                                     Vertrag des Zyklusmitglieds, beschraenkt
                                     durch das Mass des Rufers
  `UmgebungOk`                  -- `UmgebungOK` (`Anweisung.lean`:599)
  `SchleifenOk`                 -- `SchleifenOK` (`Anweisung.lean`:608)
  `SchleifeLaeuftImBereich`     -- `RunsLoopIn` (`Body.lean`:1610)
  `SchleifeLaeuftGezaehlt`      -- `RunsLoopN` (`Body.lean`:1671)
  `SchleifenOkAusGezaehltenLaeufen`
                                -- `looprule_of_body_p` (`Body.lean`:1721)
  `MassAussenSchleifeInnen`     -- die Schachtelung aus `KompositionBeweis.lean`
                                      (C6): die Schleifenregel unter den
                                      beschraenkten Vertraegen, der Zyklus aussen

  VORAUSSETZUNGEN, gebucht:
    (P1) Jede Zeile der Tabelle nennt alle Rufe ihres Rumpfes (`ruft` ist
         vollstaendig) und alle Schleifen (`schleifen` ist vollstaendig).
    (P2) `laeuft f` heisst: wo der Rumpf endet, antwortet die Umgebung mit
         genau diesem Zustand und Wert -- was bei `stuck` gilt, sagt die
         Pflicht, nicht diese Datei.
    (P3) Masse sind `Nat`-Werte; der Fall ist strikt (`<`) an JEDER Kante
         zurueck in den Zyklus.

  SCHNITTE, gebucht und nicht versteckt:
    (C1) Kein Import des Modells: die Bahn verbietet den Indexeingriff, und die
         Pruefung laeuft je Datei -- darum gilt die Entsprechung ueber Namen und
         Form, nicht ueber Bezug. Nichts nennt `traverseLauf`/`Runs`/`Contract`
         als Term.
    (C2) Die Pflicht je Rumpf (`pruefeBlock_sicher` ueber dem Koerper, die
         `exited`- und `left`-Zeilen) steht nicht hier: DASS der Koerper seine
         Pflicht haelt, ist die Logik des Schreibers und die Arbeit des
         Pruefers. Diese Datei zeigt nur, WOHIN die Pflicht gehoben wird.
    (C3) Fremde Ruempfe (`extern`, `asm`, anvertraut) haben keine Zeile und
         damit keinen Vertrag: ihre Vertraege bleiben Hypothesen ueber `laeuft`.
  (C4) Nicht in `Grammatik.lean` verdrahtet: der Bahnumfang verbietet den
       Indexeingriff; pruefe diese Datei unmittelbar mit
       `lake env lean Grammatik/Komposition.lean`.
  (C5) `indizes` bleibt `List Nat`; Bereich und Schranke sprechen `Int` wie im
       Modell (`RunsLoopN` laeuft ueber `List Int`). Die Koerzion traegt nur EINE
       Richtung: ein Durchgang besucht keine negativen Indizes -- was das Modell
       mit negativen Indizes sagt, sagt diese Datei nicht.
  (C6) Die Abweisung der umgekehrten Schachtelung steht als `¬`-Form ueber EINEM
       Datum (`Umgekehrt`) -- wie §7 kein Allgemeinsatz, sondern die Gestalt, in
       der die umgekehrte Ordnung nichts schliesst.

  Kein `mathlib`, kein `sorry`, kein `axiom`.
-/

/- Nur Formen, keine Saetze: `Prop`-wertige Aussagen stehen in dieser Bahn als `def`,
   weil `theorem` der spaeteren Phase gehoert. -/
set_option linter.defProp false

namespace Gabbro.Grammatik

/-! ## 1. Die Ruempfe und das Gefuege -/

/-- Eine Zeile der Koerpertabelle: wen der Rumpf ruft, welches Mass er erklaert
    (`none` = kein `decreases`), und welche Schleifen ihm gehoeren. -/
structure Routine where
  ruft : List String
  mass : Option Nat
  schleifen : List String
  deriving DecidableEq, Repr

/-- Das Gefuege: die Koerpertabelle UND die Abbildung in die Umgebung als Felder
    EINER Struktur -- damit der Zyklus, den ein Beweis schliesst, der Zyklus ist,
    den der Pruefer angenommen oder abgewiesen hat. -/
structure Gefuege where
  tabelle : String → Option Routine
  laeuft : String → Prop
  vertrag : String → Prop
  schleifenRegel : String → Prop

/-! ## 2. Die Ordnung des Rufgraphen -/

/-- Die Kante des Rufgraphen: `f` ruft `g`. -/
def ruftAn (G : Gefuege) (f g : String) : Prop :=
  ∃ r, G.tabelle f = some r ∧ g ∈ r.ruft

/-- Topologisch: jeder Gerufene steht VOR seinen Rufern. -/
def Topologisch (G : Gefuege) (ord : List String) : Prop :=
  ∀ f g, ruftAn G f g → ord.idxOf g < ord.idxOf f

/-- Azyklisch unter `fs`: eine Ordnung traegt alle Routinen von `fs`, und jeder
    Gerufene steht vor seinem Rufer -- die Induktion braucht kein Mass. -/
def AzyklischUnter (G : Gefuege) (fs : List String) : Prop :=
  ∃ ord, (∀ f ∈ fs, f ∈ ord) ∧ Topologisch G ord

/-- Vom Mass getragen: JEDES Mitglied des Zyklus erklaert ein `decreases`. -/
def ZyklusGetragen (G : Gefuege) (zs : List String) : Prop :=
  ∀ f ∈ zs, ∃ r, G.tabelle f = some r ∧ r.mass.isSome = true

/-! ## 3. Die Zyklusform (`Coverage.lean`: `recursion_cycle_carried`) -/

/-- Ein Zyklusmitglied als Datum: Name, Rufe und Mass -- die abstrakte Form von
    `Body.Member` (Name, Rumpf und Mass anstelle der Vor- und Nachbedingung). -/
structure Mitglied where
  name : String
  ruft : List String
  mass : Option Nat
  deriving DecidableEq, Repr

/-- Unter dem Mass: das Mass des Gerufenen faellt strikt gegen das des Rufers. -/
def UnterMass (gerufen rufer : Option Nat) : Prop :=
  ∃ a b, gerufen = some a ∧ rufer = some b ∧ a < b

/-- Der beschraenkte Vertrag: der Vertrag des Mitglieds `r'`, schrankiert durch
    das Mass `m` des Rufers -- die abstrakte Form von `ContractBelowM`. -/
def VertragSchranke (G : Gefuege) (r' : Mitglied) (m : Option Nat) : Prop :=
  UnterMass r'.mass m → G.vertrag r'.name

/-- **Der Zyklus, getragen.** Wo die Umgebung jeden Rumpf laeuft und jede Pflicht
    unter den beschraenkten Vertraegen ALLER Mitglieder den Vertrag haelt, haelt
    jedes Mitglied seinen Vertrag -- die Form von `RecursionCycleCarried`. -/
def RekursionZyklusGetragen (G : Gefuege) (rs : List Mitglied) : Prop :=
  (∀ r ∈ rs, G.laeuft r.name) →
  (∀ r ∈ rs, (∀ r' ∈ rs, VertragSchranke G r' r.mass) → G.vertrag r.name) →
  (∀ r ∈ rs, G.vertrag r.name)

/-! ## 4. Die beiden Praemissen als `Prop`-wertige Formen -/

/-- **(U1)** Jeder erklaerte Gerufene, den die Umgebung laeuft, haelt seinen
    Vertrag -- die Form von `UmgebungOK`. -/
def UmgebungOk (G : Gefuege) : Prop :=
  ∀ f, (∃ r, G.tabelle f = some r) → G.laeuft f → G.vertrag f

/-- **(U2)** Jede eingetragene Schleife haelt ihre Regel -- die Form von
    `SchleifenOK`. -/
def SchleifenOk (G : Gefuege) : Prop :=
  ∀ id, (∃ f r, G.tabelle f = some r ∧ id ∈ r.schleifen) → G.schleifenRegel id

/-! ## 5. Der Schleifendurchgang als Indexliste -/

/-- Ein Schleifendurchgang: die Kennung der Schleife und die Liste der Indizes,
    ein Durchgang je Index -- die Form von `iterate`. -/
structure Durchgang where
  kennung : String
  indizes : List Nat
  deriving DecidableEq, Repr

/-- Der Index `i` wird im Durchgang `d` besucht. -/
def DurchgangBesucht (d : Durchgang) (i : Nat) : Prop :=
  i ∈ d.indizes

/-- Die Schleife laeuft: ihre Kennung gehoert einem Rumpf der Tabelle, und ihre
    Regel gilt -- die Form von `RunsLoop`. -/
def SchleifeLaeuft (G : Gefuege) (d : Durchgang) : Prop :=
  (∃ f r, G.tabelle f = some r ∧ d.kennung ∈ r.schleifen) ∧ G.schleifenRegel d.kennung

/-! ## 6. Die Kompositionssaetze als Aussageformen -/

/-- Azyklisch aus der Ordnung: wo die Ordnung traegt und die Umgebung laeuft,
    haelt jeder Vertrag -- die Hebung ueber den topologischen Fall. -/
def RufAusOrdnung (G : Gefuege) (fs : List String) : Prop :=
  AzyklischUnter G fs → ∀ f ∈ fs, G.laeuft f → G.vertrag f

/-- **Die Form von `umgebung_ok_of_runs`.** Jede Zeile der Tabelle liegt im
    azyklischen Teil oder im getragenen Zyklus; wo die Ordnung traegt, das Mass
    an jeder Zykluskante faellt und die Umgebung jeden Rumpf laeuft, gilt (U1). -/
def UmgebungOkAusLaeufen (G : Gefuege) (fs zs : List String) : Prop :=
  (∀ f, (∃ r, G.tabelle f = some r) → f ∈ fs ∨ f ∈ zs) →
  AzyklischUnter G fs → ZyklusGetragen G zs →
  (∀ f ∈ fs, G.laeuft f) → (∀ z ∈ zs, G.laeuft z) →
  UmgebungOk G

/-- **Die Form der Zyklushebung.** Wo die Umgebung jeden Rumpf laeuft und jede
    Pflicht unter den beschraenkten Vertraegen des Zyklus haelt, haelt jedes
    Mitglied seinen Vertrag -- durch `RekursionZyklusGetragen`. -/
def ZyklusAusMass (G : Gefuege) (rs : List Mitglied) : Prop :=
  (∀ r ∈ rs, G.laeuft r.name) →
  (∀ r ∈ rs, (∀ r' ∈ rs, VertragSchranke G r' r.mass) → G.vertrag r.name) →
  (∀ r ∈ rs, G.vertrag r.name)

/-- **Die Form von `schleifen_ok_of_runsloop`.** Wo die Schleife ueber ihre
    Indexliste laeuft, gilt (U2) -- die Induktion laeuft ueber `indizes`. -/
def SchleifenOkAusLaeufen (G : Gefuege) (d : Durchgang) : Prop :=
  SchleifeLaeuft G d → SchleifenOk G

/-! ## 7. Der Zyklus ohne `decreases` -- als Datum, das abgewiesen wird -/

/-- Zwei Ruempfe im Kreis, `a` mit Mass, `b` ohne: die Tabelle, an der die
    Zyklushebung scheitern MUSS. -/
def OhneMassTabelle : String → Option Routine
  | "a" => some { ruft := ["b"], mass := some 1, schleifen := [] }
  | "b" => some { ruft := ["a"], mass := none, schleifen := [] }
  | _ => none

/-- Das Gefuege ueber dieser Tabelle: die Umgebung laeuft alles, jeder Vertrag
    gilt -- und trotzdem darf die Komposition den Zyklus nicht schliessen, weil
    das Mass an der Kante fehlt. -/
def ZyklusOhneMass : Gefuege :=
  { tabelle := OhneMassTabelle
    laeuft := fun _ => True
    vertrag := fun _ => True
    schleifenRegel := fun _ => True }

/-- Die Luecke als Datum: an `"b"` steht kein Mass. -/
def ohne_mass_ist_none : (ZyklusOhneMass.tabelle "b").bind Routine.mass = none := by
  rfl

/-- **Die Abweisung.** Der Zyklus `["a", "b"]` ist nicht getragen -- `b` nennt
    kein Mass -- also schliesst keine Kompositionsform seinen Vertrag ueber
    `ZyklusGetragen`. -/
def ZyklusOhneMassWirdAbgewiesen : ¬ ZyklusGetragen ZyklusOhneMass ["a", "b"] := by
  intro h
  obtain ⟨r, hr, hm⟩ := h "b" (by decide)
  simp only [ZyklusOhneMass, OhneMassTabelle] at hr
  cases hr
  simp at hm

#print axioms Gabbro.Grammatik.ohne_mass_ist_none
#print axioms Gabbro.Grammatik.ZyklusOhneMassWirdAbgewiesen

/-! ## 8. Die gezaehlte Laufform (`RunsLoopN`) -/

/-- Der Durchgang im Bereich: jeder besuchte Index liegt in `lo ≤ i < hi` -- die
    Bedingung von `RunsLoopIn` (`Body.lean`:1610), ein Durchgang je Index wie in §5.
    (`indizes` bleibt `List Nat`; die Schranken sind `Int` wie im Modell -- siehe C5.) -/
def DurchgangImBereich (d : Durchgang) (lo hi : Int) : Prop :=
  ∀ i ∈ d.indizes, lo ≤ (i : Int) ∧ (i : Int) < hi

/-- Die Schleife laeuft im Bereich: ihre Kennung gehoert einem Rumpf der Tabelle,
    jeder besuchte Index liegt im Bereich, und ihre Regel gilt -- die Form von
    `RunsLoopIn`, das fehlende Mittelstueck zwischen §5 und der gezaehlten Form. -/
def SchleifeLaeuftImBereich (G : Gefuege) (d : Durchgang) (lo hi : Int) : Prop :=
  (∃ f r, G.tabelle f = some r ∧ d.kennung ∈ r.schleifen) ∧
  DurchgangImBereich d lo hi ∧ G.schleifenRegel d.kennung

/-- Der Durchgang gezaehlt: im Bereich UND hoechstens `np` Durchgaenge -- die
    Bedingung von `RunsLoopN` (`Body.lean`:1671): `ks.length ≤ np`, wo `np` die
    Anzahl (`count`) des Bereichs ist. -/
def DurchgangGezaehlt (d : Durchgang) (lo hi np : Int) : Prop :=
  DurchgangImBereich d lo hi ∧ (d.indizes.length : Int) ≤ np

/-- Die Schleife laeuft gezaehlt: ihre Kennung gehoert einem Rumpf der Tabelle, der
    Durchgang ist gezaehlt, und ihre Regel gilt -- die Form von `RunsLoopN`, der
    dritten Laufform neben `RunsLoop` (§5) und `RunsLoopIn` (hier oben). -/
def SchleifeLaeuftGezaehlt (G : Gefuege) (d : Durchgang) (lo hi np : Int) : Prop :=
  (∃ f r, G.tabelle f = some r ∧ d.kennung ∈ r.schleifen) ∧
  DurchgangGezaehlt d lo hi np ∧ G.schleifenRegel d.kennung

/-- **Die Form von `looprule_of_body_p`.** Wo die Schleife gezaehlt laeuft, gilt
    (U2) -- die Induktion laeuft ueber `indizes`, der Zaehler reist mit. -/
def SchleifenOkAusGezaehltenLaeufen (G : Gefuege) (d : Durchgang) (lo hi np : Int) : Prop :=
  SchleifeLaeuftGezaehlt G d lo hi np → SchleifenOk G

/-! ## 9. Die Schachtelung: das Mass aussen, die Schleife innen -/

/-- Die Schleife sitzt in einem Zyklusmitglied: ihre Kennung gehoert dem Rumpf,
    dessen Name ein Mitglied traegt -- die Schleife steht INNEN, das Mass AUSSEN. -/
def SchleifeInMitglied (G : Gefuege) (rs : List Mitglied) (d : Durchgang) : Prop :=
  ∃ r ∈ rs, ∃ rr, G.tabelle r.name = some rr ∧ d.kennung ∈ rr.schleifen

/-- **Die feste Ordnung.** Wo die Schleife in einem Mitglied sitzt, liefert jede
    Pflicht ihren Vertrag UND die Schleifenregel UNTER den beschraenkten Vertraegen:
    die Schleifenregel schliesst innen (je Durchgang, unter dem Mass), die
    Zyklusvertraege schliessen aussen (durch die Massinduktion). -/
def MassAussenSchleifeInnen (G : Gefuege) (rs : List Mitglied) (d : Durchgang) : Prop :=
  SchleifeInMitglied G rs d →
  (∀ r ∈ rs, (∀ r' ∈ rs, VertragSchranke G r' r.mass) →
    (G.vertrag r.name ∧ (SchleifeLaeuft G d → SchleifenOk G))) →
  ((∀ r ∈ rs, G.vertrag r.name) ∧ SchleifenOk G)

/-- **Die umgekehrte Ordnung -- die Form, die abgewiesen werden MUSS.** Die
    Schleifenregel schliesst aussen, und die Zyklusvertraege schliessen innen darunter:
    jede Pflicht darf die VOLLEN Vertraege aller Mitglieder annehmen -- also genau das,
    was erst zu zeigen ist. Wer so schachtelt, nimmt an, was er schliesst. -/
def SchleifeAussenMassInnen (G : Gefuege) (rs : List Mitglied) (d : Durchgang) : Prop :=
  SchleifeInMitglied G rs d →
  (SchleifeLaeuft G d → SchleifenOk G) →
  ((∀ r ∈ rs, (∀ r' ∈ rs, G.vertrag r'.name) → G.vertrag r.name) →
   ((∀ r ∈ rs, G.vertrag r.name) ∧ SchleifenOk G))

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

end Gabbro.Grammatik
