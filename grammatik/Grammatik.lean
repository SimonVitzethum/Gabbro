/-
  Grammatik -- die Grammatik von Gabbro als GETYPTE Grammatik, in Lean 4, ueber die GANZE
  Sprache.

  Der Satz: ein Satz dieser Grammatik hat eine totale Bedeutung, und seine Bedeutung kennt
  genau zwei Fehlerausgaenge -- die Logik des Schreibers (`requires`, `ensures`,
  `invariant`, `decreases`, ein `state`-Uebergang) und eine Hardwareannahme (fremder Rumpf,
  `progress`, IEEE, ein Register, sein Versprechen, das Speichermodell). Es gibt keinen
  dritten, weil der Ausgangstyp keinen dritten hat. Und ueber Verschraenkungen: zwei Faeden
  beruehren einen bewachten Traeger nie im Wettlauf (`Wettlauf.lean`).

  Kein `mathlib`, kein Import aus `programmlogik/` oder `passlogik/`: hier steht nur die
  Grammatik und was ihre Saetze bedeuten -- nichts ueber den Pruefer, nichts ueber den
  Erzeuger.

  | Datei               | Gegenstand                                                        |
  |---------------------|-------------------------------------------------------------------|
  | `Typen.lean`        | die Typen mit Bereich, ihre Werte, die Rechnung (auch mit Vorzeichen), Bytes |
  | `Syntax.lean`       | die GRAMMATIK: Ausdruecke und Anweisungen als getypte Familie      |
  | `Semantik.lean`     | was ein Satz bedeutet: `eval` total, `exec` mit zwei Ausgaengen, die Spur |
  | `Satz.lean`         | der Satz: Rahmen UND Spur in einer Induktion, die Inversionen, `#print axioms` |
  | `Wettlauf.lean`     | Faeden verschraenkt: kein Wettlauf, keine Ueberkreuzung der Sperrordnung |
  | `Zucker.lean`       | jede Schreibweise ohne eigenen Konstruktor, als Definition ueber dem Kern |
| `Ziel.lean`         | DAS ZIEL als Satz ueber der Grammatik -- unabhaengig vom `.rs`-Code       |
  | `Interferenz.lean`  | das Verbundmodell deklarierter Paare: gueltige Vertraege ueberleben Verschraenkung |
  | `Koernung.lean`     | die Ereigniskoernung als benannte Praemisse: keine Zerreissung darunter, Bytes als n Ereignisse |
  | `Geteilt.lean`      | Erreichbarkeit als Konstruktion: ungeteilt heisst von hoechstens einem Faden erreichbar |
  | `Geraet.lean`       | das Geraet als Laufteilnehmer: Ordnung bewiesen, Inhalt benannte Annahme |
  | `Unterbrechung.lean`| der Handler als Faden: HB-Deckung ueber Sperrkante oder Maske            |
  | `Zeugnis.lean`      | die gedruckte Ableitung als Datum: gueltiges Zeugnis heisst Urteil        |
  | `Budget.lean`       | die ops-Frist als Rechnung: im Budget oder benannt erschoepft, nie still drueber |
  | `Terminierung.lean` | das Mass faellt heisst der Lauf endet: traversieren, Wiederholung, forever nie |
  | `InterferenzAllgemein.lean` | N Faeden, beliebig viele Schritte: Stabilitaet als Gestalt, Beweis spaeter |
  | `Komposition.lean` | Rufgraph und Schleifenregel als Gestalt: Ordnung ohne Mass, Zyklen mit |
  | `Fehler.lean`     | der Fehlerausgang als paralleles Modell: Klasse, Ergebnis, evalF-Gestalt |
  | `Erhaltung.lean`  | der Erzeugervertrag als Pflichtenheft: Entsprechung, Alias, Kosten, Tafel |
  | `Extraktion.lean` | berechnete Huellen: Kanten und Fuesse aus Ruempfen, Bau als Ergebnis     |
  | `Marken.lean`     | lineare Marken als Konstruktion: Besitz als Zustand, Einfaedigkeit als Gestalt |
  | `Fristlauf.lean`  | Fristablauf zwischen Pruefung und Lauf als benanntes Ergebnis, keine Wanduhr |
  | `Adressraum.lean` | Nutzerspeicher als Gestalt: gepruefte Kopie oder benannte Luecke          |
  | `LesenStabil.lean` | lesestabile Form: Vertragsgelesenes im Rahmen, Kette bis zum letzten Lauf |
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Satz
import Grammatik.Wettlauf
import Grammatik.Zucker
import Grammatik.Ziel
import Grammatik.Interferenz
import Grammatik.Koernung
import Grammatik.Geteilt
import Grammatik.Geraet
import Grammatik.Unterbrechung
import Grammatik.Zeugnis
import Grammatik.Budget
import Grammatik.Terminierung
import Grammatik.InterferenzAllgemein
import Grammatik.Komposition
import Grammatik.Fehler
import Grammatik.Erhaltung
import Grammatik.Extraktion
import Grammatik.Marken
import Grammatik.Fristlauf
import Grammatik.Adressraum
import Grammatik.LesenStabil
import Grammatik.Maschine
import Grammatik.MaschinenKette
import Grammatik.VertragOrtB
