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

end Gabbro.Grammatik
