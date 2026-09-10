/-
  Datei:      Grammatik/Extraktion.lean
  Gegenstand: **DIE FUSSABDRUECKE ALS RECHNUNG** -- aus den Ruempfen gerechnet, nicht
              erklaert: die Rufkanten aus den Rufen im Rumpf, die Fussabdrucklisten aus
              den Effekten, die Paarliste aus der Nebenlauffassung; das Ergebnis hat Feld
              fuer Feld die Gestalt von `Geteilt.Bau`, und die Anknuepfung steht als
              Prop-Form daneben (die `BauLauf`-Form ueber dem errechneten Bau).

  ZIEL (Bahn 38, Entwurf): Die Schnitte C2/C3 aus `Geteilt.lean` schliessen -- dort sind
  `schreibtFn` je Funktion und `neben` als Paarliste DEKLARIERT (getragen, nicht
  gerechnet). Hier steht die Rechnung: `ruftNorm`/`kantenListe` aus den direkten Rufen,
  `fussAus` aus den Effektpraedikaten ueber der erklaerten Domaene, `nebenAus` aus der
  erklaerten Paarliste ueber den Eintritten, und `bauAus` baut daraus den Bau. Was der
  Pruefer heute per Hand schreibt (`H013`), rechnet kuenftig diese Datei aus dem Rumpf.

  STANDALONE -- diese Datei importiert nichts (nicht einmal die Geschwister), aus
  demselben Grund wie `Geteilt.lean`: die Bahn verbietet den Eingriff in den
  `Grammatik.lean`-Index, also kann sie noch nicht eingebunden werden; die Namen sind
  fuer die spaetere Verdrahtung gewaehlt. Die Pruefung laeuft allein ueber
  `lake env lean Grammatik/Extraktion.lean` in `grammatik/`.

  Spiegel (diese Datei ist links, dort steht rechts):

  | hier                  | dort (`Syntax` / `Geteilt` / `Wettlauf`)          |
  |-----------------------|---------------------------------------------------|
  | `Fn := Nat`           | `D.Fn` (Kodierung: die Verdrahtung nennt `fnCode`)|
  | `Carrier := Nat`      | `D.Tab ⊕ D.Glob` in EINEM Traeger (Schnitt C1)    |
  | `ruftDirekt`          | `Programm.rumpf` projiziert (`Stmt.call`,         |
  |                       |  `Block.bindCall`, `bindCallElse`; s. W-EXT unten)|
  | `effSchreibt`         | `Signatur.schreibt`/`gschreibt` (`effects`)       |
  | `marken`              | `D.geteilt`/`D.ggeteilt` (`shared`)               |
  | `paare`               | `concurrent { … }` ueber Fadennummern             |
  | `BauSpiegel`          | `Geteilt.Bau`, Feld fuer Feld derselbe Typ        |
  | `schrittBisSpiegel`   | `Geteilt.schrittBis` (Brennstoff-Rechnung)        |
  | `traegerBisSpiegel`   | `Geteilt.traegerBis` (Traeger-Rechnung)           |
  | `erreichtSpiegel`     | `Geteilt.ErreichtBau` (Mitgliedschaft = Erreichen)|
  | `bauLaufSpiegel`      | `Geteilt.BauLauf` (Deckung UND nur Paare)         |
  | `paarTreue/paarVoll`  | `Nebeneinander` (`Wettlauf.lean` §6, als          |
  |                       |  `Nat → Nat → Prop`: `Faden` IST `Nat`)           |

  SCHNITTE (gebucht, nicht versteckt):
  S1. Kodierung: `D.Fn`, `D.Tab`, `D.Glob` sind hier schon Zahlen. Die
      Kodierungen `fnCode`/`tabCode`/`globCode` (Trennung der Traegerhaelften) bringt die
      Verdrahtung; `geteilt_treu` unterscheidet erst dort wieder Tabelle/Global.
  S2. W-EXT (die Traversierung): `ruftDirekt` ist die PROJEKTION des Rumpfs, nicht die
      Traversierung selbst -- `Stmt`/`Block`/`Endblock` lassen sich ohne Import nicht
      begehen. Die Traversierung sammelt `Stmt.call`, `Block.bindCall`,
      `Block.bindCallElse` als Kanten; `callInd` (Zeigerruf) und `axiomCall` (fremder
      Rumpf) liefern KEINE Kante -- ein Zeigerruf faellt damit aus der Huelle, und der
      Pruefer muss ihn verweigern (fail-closed, wie `W003`), nicht raten.
  S3. Lesen: `effects` erklaert nur Schreiben (`schreibt`/`gschreibt`); eine
      Lesehuelle (`slot`/`glob` in `Expr`) steht nirgends und fehlt hier -- fuer (W5)
      genuegt Schreiben (Erreichen heisst Beruehren zum Schreiben), fuer das
      Zwei-Faden-Modell (`Interferenz.lean`: disjunkte Rahmen) muss sie dazu.
  S4. Haengende Paare: `nebenAus` wirft Paare ausserhalb der Eintritte weg -- die
      Form `paarVoll` unten nennt die Pflicht des Pruefers: was faellt, wird
      verweigert, nicht verschwiegen.
  S5. Unbekannt heisst geteilt: `geteiltAus` antwortet `true` ausserhalb der Marken --
      fail-closed in die Richtung, in der ein Irrtum laut wird (`geteilt_treu`
      verlangt dann den Waechter statt der Einzigkeit).

  Kern nur: kein `mathlib`, kein Import, kein `sorry`, kein Satz -- nur `def`,
  `abbrev`, `structure`. Jede Form unten ist eine `def` mit Ergebnis `Prop`.
-/

namespace Gabbro.Grammatik.Extraktion

/-! ## 1. Die Spiegeltypen: Funktionen und Traeger als Nummern -/

/-- Funktionen als Nummern. Spiegelt `D.Fn` (Schnitt S1: die Kodierung bringt die
    Verdrahtung). -/
abbrev Fn := Nat

/-- Traeger als Nummern. Spiegelt `D.Tab ⊕ D.Glob` in einem Traeger (derselbe
    Schnitt C1 wie in `Geteilt.lean`). -/
abbrev Carrier := Nat

/-- Der errechnete Bau: Feld fuer Feld `Geteilt.Bau` -- dieselben Namen, dieselben
    Typen. Die Verdrahtung ersetzt `BauSpiegel` durch `Geteilt.Bau`, sobald der
    Index es zulaesst; bis dahin prueft diese Datei die Formen schon hier. -/
structure BauSpiegel where
  /-- Faden `f` startet in `eintritt[f]?`; Faeden jenseits des Endes treten nie. -/
  eintritt : List Fn
  /-- Die gerechneten Rufkanten (Uebernaeherung; Schnitt S2). -/
  ruft : Fn → List Fn
  /-- Die gerechnete Fussabdruckliste je Funktion (aus den Effekten; Schnitt S3). -/
  schreibtFn : Fn → List Carrier
  /-- Die Markierung unter der Pruefung. Spiegelt `D.geteilt` / `D.ggeteilt`. -/
  geteilt : Carrier → Bool
  /-- Alle Traeger der Einheit (die Domaene des Pruefers). -/
  traeger : List Carrier
  /-- Die gerechneten Nebenlaufpaare (endliche Liste, derselbe Schnitt C3). -/
  neben : List (Nat × Nat)

/-! ## 2. Die Eingaben: Projektionen der Syntax (getragen, nicht gerechnet)

    Drei Projektionen traegt die Verdrahtung aus `Syntax.lean` hierher -- sie sind
    die Stellen, an denen der Rumpf und die Erklaerung in die Rechnung eintreten:

    * `ruftDirekt : Fn → List Fn` -- die direkten Rufe je Rumpf (`Stmt.call`,
      `Block.bindCall`, `Block.bindCallElse` ueber `Programm.rumpf`; Schnitt S2).
    * `effSchreibt : Fn → Carrier → Bool` -- die Effekte (`Signatur.schreibt` und
      `gschreibt` ueber der Traegerkodierung; `effects { writes … }`).
    * `marken : List (Carrier × Bool)` -- die `shared`-Marken (`D.geteilt` und
      `D.ggeteilt`) als EINE Tabelle: Domaene UND Markierung aus einer Quelle,
      damit kein Traeger ohne Marke laufen kann (Schnitt S5).
    * `eintritt : List Fn` -- die Startkoerper (Fassungen von `entry`/`boot`).
    * `paare : List (Nat × Nat)` -- die Fassung von `concurrent { … }` ueber
      Fadennummern (Stellen in `eintritt`). -/

/-! ## 3. Die Kantenrechnung: aus den Rufen, ueber der Domaene -/

/-- Die normierte Kante: nur Rufe in die erklaerte Funktionsdomaene ueberleben.
    Ein Ruf ins Unerklaerte faellt hier weg -- und die Form `kantenTreue` (§6)
    verlangt ihn dort zurueck: was faellt, verweigert der Pruefer. -/
def ruftNorm (ruftDirekt : Fn → List Fn) (fns : List Fn) : Fn → List Fn :=
  fun f => (ruftDirekt f).filter fns.contains

/-- Die Kantenliste der Einheit: je erklaerter Funktion ihre normierten Ziele. -/
def kantenListe (ruftDirekt : Fn → List Fn) (fns : List Fn) : List (Nat × Nat) :=
  fns.flatMap fun f => (ruftNorm ruftDirekt fns f).map fun g => (f, g)

/-! ## 4. Die Fussabdruckrechnung: aus den Effekten, ueber der Domaene -/

/-- Der Fussabdruck je Funktion: was die Effekte nennen, aus der erklaerten
    Domaene herausgefiltert. Ein Effekt ausserhalb der Domaene faellt weg -- wie
    die Kante: was faellt, verweigert der Pruefer (`fussTreue`, §6). -/
def fussAus (effSchreibt : Fn → Carrier → Bool) (traegerAlle : List Carrier) :
    Fn → List Carrier :=
  fun f => traegerAlle.filter (effSchreibt f)

/-! ## 5. Die Markenrechnung: Domaene und Markierung aus einer Tabelle -/

/-- Die Traegerdomaene: die erste Spalte der Markentabelle. -/
def traegerAus (marken : List (Carrier × Bool)) : List Carrier :=
  marken.map Prod.fst

/-- Die Markierungsfunktion: Nachschlagen in der Tabelle, ausserhalb `true` --
    unbekannt heisst geteilt (Schnitt S5: fail-closed zur lauten Seite). -/
def geteiltAus (marken : List (Carrier × Bool)) : Carrier → Bool :=
  fun c => ((marken.find? (fun p => p.1 == c)).map Prod.snd).getD true

/-! ## 6. Die Paarrechnung: aus der Fassung, ueber den Eintritten -/

/-- Die Nebenlaufpaare: nur Paare innerhalb der Eintritte ueberleben. Ein Paar
    mit haengender Nummer faellt weg -- und `paarVoll` (§7) verlangt es zurueck:
    was faellt, verweigert der Pruefer (Schnitt S4). -/
def nebenAus (eintritt : List Fn) (paare : List (Nat × Nat)) :
    List (Nat × Nat) :=
  paare.filter fun p => decide (p.1 < eintritt.length ∧ p.2 < eintritt.length)

/-! ## 7. Der Zusammenbau: der Bau als Rechnung -/

/-- **Der Bau aus der Rechnung.** Jede Stelle nennt ihre Herkunft: die Eintritte
    getragen, die Kanten aus den Rufen (§3), die Fuesse aus den Effekten (§4),
    Markierung und Domaene aus einer Tabelle (§5), die Paare aus der Fassung
    (§6). Das Ergebnis hat den Typ `BauSpiegel` -- Feld fuer Feld `Geteilt.Bau`. -/
def bauAus (ruftDirekt : Fn → List Fn) (fns : List Fn)
    (effSchreibt : Fn → Carrier → Bool) (marken : List (Carrier × Bool))
    (eintritt : List Fn) (paare : List (Nat × Nat)) : BauSpiegel where
  eintritt := eintritt
  ruft := ruftNorm ruftDirekt fns
  schreibtFn := fussAus effSchreibt (traegerAus marken)
  geteilt := geteiltAus marken
  traeger := traegerAus marken
  neben := nebenAus eintritt paare

/-! ## 8. Die Brennstoff-Rechnung: Erreichen als Mitgliedschaft -/

/-- Die Rufhuelle in hoechstens `fuel` Schritten. Spiegelt `Geteilt.schrittBis`:
    `refl` bei jedem Brennstoff -- "erreichbar in `fuel`". -/
def schrittBisSpiegel (ruft : Fn → List Fn) (fuel : Nat) (e : Fn) : List Fn :=
  match fuel with
  | 0 => [e]
  | n + 1 => schrittBisSpiegel ruft n e ++ (schrittBisSpiegel ruft n e).flatMap ruft

/-- Die Traegermenge EINES Fadens. Spiegelt `Geteilt.traegerBis`: kein Eintritt,
    keine Traeger. -/
def traegerBisSpiegel (B : BauSpiegel) (fuel f : Nat) : List Carrier :=
  match B.eintritt[f]? with
  | none => []
  | some e => (schrittBisSpiegel B.ruft fuel e).flatMap B.schreibtFn

/-- **Erreichen als Form.** Spiegelt `Geteilt.ErreichtBau` ueber die
    `traegerBis`-Seite (`traegerBis_genau` dort): Faden `f` erreicht Traeger `c`
    in `fuel` heisst `c` steht in seiner gerechneten Menge. -/
def erreichtSpiegel (B : BauSpiegel) (fuel f : Nat) (c : Carrier) : Prop :=
  c ∈ traegerBisSpiegel B fuel f

/-! ## 9. Die Lauf-Form: die `BauLauf`-Gestalt ueber dem errechneten Bau -/

/-- **Deckung als Form.** Jeder Zugriff des Laufs ist statisch gedeckt -- die
    erste Haelfte von `Geteilt.BauLauf`, ueber dem errechneten Bau (Schnitt C2
    dort: die Koerper-Extraktionspflicht, hier als Form beim Namen genannt). -/
def laufGedeckt (B : BauSpiegel) (fuel : Nat) (l : List (Nat × Carrier)) : Prop :=
  ∀ s ∈ l, erreichtSpiegel B fuel s.1 s.2

/-- **Nur Paare als Form.** Zwei Schritte verschiedener Faeden nennen ein
    erklaertes Paar -- die zweite Haelfte von `Geteilt.BauLauf`, ueber der
    gerechneten Paarliste. -/
def nurPaareLaufen (B : BauSpiegel) (l : List (Nat × Carrier)) : Prop :=
  ∀ s₁ ∈ l, ∀ s₂ ∈ l,
    s₁.1 = s₂.1 ∨ (s₁.1, s₂.1) ∈ B.neben ∨ (s₂.1, s₁.1) ∈ B.neben

/-- **Die Lauf-Form.** Spiegelt `Geteilt.BauLauf` Satz fuer Satz: Deckung UND nur
    Paare -- ausgewertet am errechneten Bau statt am erklaerten. -/
def bauLaufSpiegel (B : BauSpiegel) (fuel : Nat) (l : List (Nat × Carrier)) :
    Prop :=
  laufGedeckt B fuel l ∧ nurPaareLaufen B l

/-! ## 10. Die Treue-Formen: was die Rechnung dem Pruefer schuldet -/

/-- **Kantentreue.** Kein direkter Ruf faellt aus der Rechnung: was der Rumpf
    ruft, steht in `B.ruft`. Die Richtung ist Absicht -- die Rechnung darf MEHR
    sehen (Uebernaeherung), nie weniger. -/
def kantenTreue (B : BauSpiegel) (ruftDirekt : Fn → List Fn) : Prop :=
  ∀ f g, g ∈ ruftDirekt f → g ∈ B.ruft f

/-- **Fusstreue.** Kein Effekt faellt aus der Rechnung: was die Signatur
    schreibt, steht in `B.schreibtFn` -- ueber der getragenen Domaene. -/
def fussTreue (B : BauSpiegel) (effSchreibt : Fn → Carrier → Bool)
    (traegerAlle : List Carrier) : Prop :=
  ∀ f t, t ∈ traegerAlle → effSchreibt f t = true → t ∈ B.schreibtFn f

/-- **Paartreue.** Jedes gerechnete Paar ist ein deklariertes: aus der Liste in
    die `Nebeneinander`-Form (`Wettlauf.lean` §6; `Faden` ist `Nat`, also ist
    `Nat → Nat → Prop` genau diese Gestalt). -/
def paarTreue (B : BauSpiegel) (Nb : Nat → Nat → Prop) : Prop :=
  ∀ i j, (i, j) ∈ B.neben → Nb i j

/-- **Paarvollstaendigkeit (die Pflicht des Pruefers).** Jedes deklarierte Paar
    steht in der Liste -- sonst duerfte der Lauf weniger, als die Fassung
    verspricht, und `nebenAus` haette still verschwiegen, was es warf
    (Schnitt S4). -/
def paarVoll (B : BauSpiegel) (Nb : Nat → Nat → Prop) : Prop :=
  ∀ i j, Nb i j → (i, j) ∈ B.neben ∨ (j, i) ∈ B.neben

/-! ## 11. Sprechprobe: die Rechnung rechnet (Werte, keine Saetze) -/

/-- Zwei Faeden, je ein Koerper, je ein Traeger, beide ungeteilt: die Eingaben
    der Probe -- Rufe, Effekte, Marken, Eintritte, Paare. -/
def miniRuft : Fn → List Fn
  | 0 => [1]
  | _ => []

/-- Die Effekte der Probe: Koerper `0` schreibt Traeger `7`, Koerper `1`
    schreibt Traeger `9`. -/
def miniEff : Fn → Carrier → Bool
  | 0, 7 => true
  | 1, 9 => true
  | _, _ => false

/-- Die Markentabelle der Probe: beide Traeger erklaert ungeteilt. -/
def miniMarken : List (Carrier × Bool) := [(7, false), (9, false)]

/-- Der Probenbau: alles Assemblierte an einer Stelle. -/
def miniBau : BauSpiegel :=
  bauAus miniRuft [0, 1] miniEff miniMarken [0, 1] [(0, 1)]

/-- Die gerechnete Kantenliste der Probe. -/
def miniKanten : List (Nat × Nat) := kantenListe miniRuft [0, 1]

/-- Die gerechnete Fussliste des Koerpers `0` der Probe. -/
def miniFuss : List Carrier := miniBau.schreibtFn 0

/-- Die gerechnete Traegermenge des Fadens `0` bei Brennstoff `3` der Probe. -/
def miniTraeger : List Carrier := traegerBisSpiegel miniBau 3 0

end Gabbro.Grammatik.Extraktion
