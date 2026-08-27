/-
  Datei:      Passlogik/Rumpf.lean
  Gegenstand: Was ein Gabbro-RUMPF BEDEUTET -- der Anweisungsabstieg als Zustandsuebergang.

  WARUM DIESE DATEI DIE LUECKE DER ANDEREN SIEBEN IST
    `passlogik/README.md` bucht denselben Posten viermal (`B1`, `L1`, `P2`, `R1`):

        „Der ANWEISUNGSABSTIEG -- was ein Rumpf Anweisung fuer Anweisung tut -- steht in
         KEINER der sieben Dateien."

    Er steht ab hier. Und `messung/P6.md` misst, was daran haengt: von 62 Pflichten sagt
    `refinement.rs` siebzehn mit `body-effect` ab, weil es keine Bedeutung eines Rumpfes
    gibt -- zehn `N`, sechs `E` und die eine `R`.

  MODELLIERT WIRD
    Eine WELT als Belegung von Orten (Slotfeld einer Tabelle, `static`) mit Werten, eine
    lokale Bindung fuer `let`-Namen, und der Abstieg ueber den SEQUENTIELLEN KERN:
    `let`, Zuweisung, `if`, `match` ueber `option`, `return`.

  WAS DIE KLEMPNEREI SCHON TRAEGT -- und was dieses Modell deshalb NICHT bauen muss
    Das ist der ganze Grund, warum diese Datei klein ist. Jede Zeile nennt den Satz, der
    sie erlaubt:

      Ueberlauf   Ganzzahlen sind `Int`, unbeschraenkt.
                  -> `Bereich.passt_dann_kein_ueberlauf` (`M104`)
      Rahmen      Der Rahmen IST die deklarierte `effects`-Liste; ein Ort ausserhalb bleibt.
                  -> `Wirkung.huelle_deckt` (`E005`/`E008`)
      Alias       Zwei verschiedene `Ort` sind verschiedene Orte, Punkt.
                  -> die Aliaspaesse; `A1` seit 2026-08-24 mit `R007`
      Terminierung Der Kern hat keine Schleife -- und die Schleifenformen tragen ihr Mass.
                  -> `K008`/`K009`, `Bereich.keine_unendliche_verengung`
      Rennen      Sequentielles Lesen ist zulaessig, `Held(L)` gilt am Rumpfeingang.
                  -> `H005`/`H006`/`H012`/`H016`

    **Deshalb gibt es hier KEIN Haldenmodell, KEINE Trennungslogik, KEINE Zeiger und
    KEINE Nebenlaeufigkeit.** Ein Zustand ist eine Abbildung von Orten auf Werte. Wer
    diese Datei liest und die Klempnerei nicht mitliest, haelt das Modell fuer naiv --
    es ist die eingeloeste Form der These dieses Ordners.

  ANGENOMMEN STATT BEWIESEN
    (U1) Dass der ERZEUGER (`crates/gabbro-check/src/lean.rs`) einen Gabbro-Rumpf richtig
         in ein `Anweisung`-Datum uebersetzt, steht hier nicht. Das ist dieselbe Naht wie
         bei den sieben anderen Dateien -- nur diesmal maschinell gezogen und darum
         mutierbar. `instrumente/pruefe-lean-beweis.sh` faehrt sie in beide Richtungen.
    (U2) Der WOHLGEFORMTE Zustand -- dass ein Slotfeld den Wert seiner erklaerten Art
         traegt -- ist eine Voraussetzung und keine Folgerung. Der Erzeuger schreibt sie
         je Einheit aus der `table`-Deklaration hin; sie steht sichtbar in der Theorie.

  BEWEIST NICHT
    Dass ein Rumpf terminiert (der Kern hat keine Schleife -- es gibt nichts zu zeigen),
    dass er keinen Ueberlauf hat (`M104`), und dass er den Rahmen einhaelt (`E005`).
-/

namespace Passlogik.Rumpf

/-! ## 1. Werte

    Vier Formen, und die Liste ist geschlossen. `option index into T` ist `nichts`/`etwas`
    -- **kein `Option Int`**, denn ein Wert muss mit jedem anderen Wert vergleichbar sein,
    und ein Summentyp ueber `Int` waere zwei Ebenen.
-/

inductive Wert where
  | z (n : Int)
  | b (t : Bool)
  | nichts
  | etwas (n : Int)
  deriving DecidableEq, Repr

/-! ## 2. Orte

    Ein Ort ist eine Stelle in der WELT. Zwei Formen: ein Slotfeld einer Tabelle, mit
    ausgewertetem Index, und ein `static`.

    **`DecidableEq` ist hier die Aliasfreiheit.** Zwei Orte sind gleich oder verschieden,
    und nichts dazwischen -- das ist die Aussage, die im allgemeinen Fall eine
    Aliasanalyse kostet und die Gabbro traegt.
-/

inductive Ort where
  | slot (traeger : String) (index : Int) (feld : String)
  | statisch (name : String)
  deriving DecidableEq

abbrev Welt := Ort → Wert
abbrev Bindung := String → Wert

/-- Die Lage: die Welt und die lokalen Namen. -/
structure Lage where
  welt : Welt
  lokal : Bindung

/-- Punktweises Schreiben. **Der Rahmen faellt hier heraus** -- jeder andere Ort bleibt. -/
def setze (σ : Welt) (o : Ort) (w : Wert) : Welt :=
  fun p => if p = o then w else σ p

def binde (β : Bindung) (n : String) (w : Wert) : Bindung :=
  fun m => if m = n then w else β m

@[simp] theorem setze_hier (σ : Welt) (o : Ort) (w : Wert) : setze σ o w o = w := by
  simp [setze]

@[simp] theorem setze_daneben (σ : Welt) (o p : Ort) (w : Wert) (h : p ≠ o) :
    setze σ o w p = σ p := by
  simp [setze, h]

@[simp] theorem binde_hier (β : Bindung) (n : String) (w : Wert) : binde β n w n = w := by
  simp [binde]

@[simp] theorem binde_daneben (β : Bindung) (n m : String) (w : Wert) (h : m ≠ n) :
    binde β n w m = β m := by
  simp [binde, h]

/-! ## 3. Ausdruecke

    Die Liste deckt genau das, was `refinement.rs` heute schon als Term kennt, plus den
    ORT MIT SUFFIX -- und der ist der ganze Zugewinn. `messung/P6.md` §4.3 nennt ihn als
    das, wovon der Isabelle-Erzeuger kein Modell hat: *„ein Ort mit Suffix ist eine Stelle
    in der WELT"*. Hier ist die Welt.
-/

inductive UnOp where
  | nicht
  | negativ
  deriving DecidableEq, Repr

inductive BinOp where
  | plus | minus | mal
  | gleich | ungleich | kleiner | kleinergleich | groesser | groessergleich
  | und | oder
  deriving DecidableEq, Repr

inductive Ausdruck where
  | lit (w : Wert)
  | name (n : String)
  | platz (traeger : String) (index : Ausdruck) (feld : String)
  | stat (name : String)
  | un (op : UnOp) (a : Ausdruck)
  | bin (op : BinOp) (a b : Ausdruck)
  deriving Repr

/-- **Eine Auswertung darf STECKENBLEIBEN.** `none` heisst: der Wert hatte nicht die Form,
    die der Operator braucht. Das ist kein Fehlerfall, den man wegdefinieren darf -- die
    Welt ist eine unbeschraenkte Abbildung, und dass ein Slotfeld die Art traegt, die seine
    Deklaration nennt, ist Annahme `U2` und steht je Einheit als Voraussetzung da.

    *Ein Modell, das hier einen Ersatzwert einsetzte, bewiese Saetze aus einem Grund, den
    die Maschine nicht hat* -- dieselbe Falle, die `messung/P6.md` §2.1 fuer `nat` nennt. -/
def unwert : UnOp → Wert → Option Wert
  | .nicht, .b t => some (.b (!t))
  | .negativ, .z n => some (.z (-n))
  | _, _ => none

def binwert : BinOp → Wert → Wert → Option Wert
  | .plus, .z a, .z b => some (.z (a + b))
  | .minus, .z a, .z b => some (.z (a - b))
  | .mal, .z a, .z b => some (.z (a * b))
  | .kleiner, .z a, .z b => some (.b (decide (a < b)))
  | .kleinergleich, .z a, .z b => some (.b (decide (a ≤ b)))
  | .groesser, .z a, .z b => some (.b (decide (a > b)))
  | .groessergleich, .z a, .z b => some (.b (decide (a ≥ b)))
  | .und, .b x, .b y => some (.b (x && y))
  | .oder, .b x, .b y => some (.b (x || y))
  -- **Gleichheit steht ueber ALLEN Werten**, nicht nur ueber Zahlen: `c.slots[s].elter
  -- == None` ist genau diese Form, und sie ist die haeufigste Nachbedingung des Korpus.
  | .gleich, x, y => some (.b (decide (x = y)))
  | .ungleich, x, y => some (.b (decide (x ≠ y)))
  | _, _, _ => none

def werte (l : Lage) : Ausdruck → Option Wert
  | .lit w => some w
  | .name n => some (l.lokal n)
  | .stat s => some (l.welt (.statisch s))
  | .platz t i f =>
      match werte l i with
      | some (.z k) => some (l.welt (.slot t k f))
      | _ => none
  | .un op a =>
      match werte l a with
      | some w => unwert op w
      | none => none
  | .bin op a b =>
      match werte l a, werte l b with
      | some x, some y => binwert op x y
      | _, _ => none

/-! ### 3.1 Die WOHLGEFORMTHEIT eines Ortes

    Die Welt ist eine unbeschraenkte Abbildung: nichts an `Ort → Wert` sagt, dass ein
    `bool`-Slotfeld eine Wahrheit traegt. **Das ist Absicht** -- ein Modell, das die Art
    in den Typ baut, kann die Voraussetzung nicht mehr NENNEN, und eine ungenannte
    Voraussetzung ist die teuerste Sorte.

    Der Erzeuger schreibt je Einheit hin, welche Form ein Feld hat, **und er liest sie aus
    der DEKLARATION** -- nicht daraus, wie der Rumpf das Feld benutzt. *Eine aus dem
    Gebrauch erratene Voraussetzung macht das Ziel leichter, nicht haerter; sie ist genau
    die stille Abschwaechung, gegen die dieser Kanal gebaut ist.*
-/

def istZahl (w : Wert) : Prop := ∃ n, w = .z n
def istWahrheit (w : Wert) : Prop := ∃ t, w = .b t
def istWahl (w : Wert) : Prop := w = .nichts ∨ ∃ n, w = .etwas n

/-! ## 4. Anweisungen -- der SEQUENTIELLE KERN

    Sieben Arten von `StmtArt`, und `messung/` misst, dass sie **12 der 17** offenen
    Rumpfpflichten tragen: `Let`, `LetSonst`, `Zuweisung`, `Wenn`, `Match`, `Return`,
    `Ruf`. Was hier NICHT steht, sagt der Erzeuger mit Namen ab.

    `Ruf` fehlt mit Absicht und ist keine Auslassung: ein Ruf ist KOMPOSITIONELL ueber den
    Vertrag des Gerufenen zu nehmen, nicht ueber seinen Rumpf. Solange der Erzeuger dafuer
    kein Tor hat, sagt er ihn ab -- **eine abgesagte Pflicht kostet eine Zahl, ein
    eingesetzter Rumpf kostet die Bedeutung der Zahl.**
-/

inductive Anweisung where
  /-- `traeger.slots[index].feld = wert;` -/
  | zuw (traeger : String) (index : Ausdruck) (feld : String) (wert : Ausdruck)
  /-- `name = wert;` an einem `static`. -/
  | zuwStat (name : String) (wert : Ausdruck)
  /-- `let name = wert;` -/
  | binde (name : String) (wert : Ausdruck)
  | wenn (bed : Ausdruck) (dann sonst : List Anweisung)
  /-- `match e { Some(b) => …, None => … }` -- die einzige `match`-Form des Kerns. -/
  | aufOption (gegenstand : Ausdruck) (binder : String)
      (beiEtwas beiNichts : List Anweisung)
  | rueckgabe (w : Option Ausdruck)
  deriving Repr

/-- Wie ein Abstieg endet. **`steckt` ist ein eigener Ausgang und kein `weiter`** -- ein
    Modell, das Steckenbleiben mit Weiterlaufen zusammenwirft, beweist ueber einem Rumpf,
    der gar nicht laeuft. -/
inductive Ausgang where
  | weiter (l : Lage)
  | zurueck (l : Lage) (w : Option Wert)
  | steckt

mutual

def schritt : Anweisung → Lage → Ausgang
  | .zuw t i f e, l =>
      match werte l i, werte l e with
      | some (.z k), some w => .weiter { l with welt := setze l.welt (.slot t k f) w }
      | _, _ => .steckt
  | .zuwStat n e, l =>
      match werte l e with
      | some w => .weiter { l with welt := setze l.welt (.statisch n) w }
      | none => .steckt
  | .binde n e, l =>
      match werte l e with
      | some w => .weiter { l with lokal := binde l.lokal n w }
      | none => .steckt
  | .wenn c d s, l =>
      match werte l c with
      | some (.b true) => fuehre d l
      | some (.b false) => fuehre s l
      | _ => .steckt
  | .aufOption g bn be bk, l =>
      match werte l g with
      | some (.etwas k) => fuehre be { l with lokal := binde l.lokal bn (.z k) }
      | some .nichts => fuehre bk l
      | _ => .steckt
  | .rueckgabe none, l => .zurueck l none
  | .rueckgabe (some e), l =>
      match werte l e with
      | some w => .zurueck l (some w)
      | none => .steckt

def fuehre : List Anweisung → Lage → Ausgang
  | [], l => .weiter l
  | a :: rest, l =>
      match schritt a l with
      | .weiter l' => fuehre rest l'
      | e => e

end

/-- Die Lage am Ende -- **`return` und Durchlaufen enden beide in einer Lage**, und beide
    sind fuer eine Nachbedingung dasselbe: der Zustand danach. Nur `steckt` hat keinen. -/
def endLage : Ausgang → Option Lage
  | .weiter l => some l
  | .zurueck l _ => some l
  | .steckt => none

/-- Das Ergebnis, falls der Rumpf eines lieferte. Fuer `ensures`, die `result` nennen. -/
def endWert : Ausgang → Option Wert
  | .zurueck _ (some w) => some w
  | _ => none

/-! ## 5. Was ueber JEDEM Rumpf gilt

    Diese Saetze gehoeren zum Modell und nicht zu einer Einheit -- der Erzeuger darf sie
    benutzen, ohne sie je Datei neu zu schreiben.
-/

/-- **Eine leere Folge aendert nichts.** -/
@[simp] theorem fuehre_leer (l : Lage) : fuehre [] l = .weiter l := by
  simp [fuehre]

/-- **Der Abstieg ist deterministisch** -- er ist eine Funktion, also gilt es per
    Konstruktion. Der Satz steht trotzdem da, weil er die Aussage ist, die ein
    RELATIONALES Modell an dieser Stelle erst beweisen muesste. -/
theorem fuehre_bestimmt (as : List Anweisung) (l : Lage) (e₁ e₂ : Ausgang)
    (h₁ : fuehre as l = e₁) (h₂ : fuehre as l = e₂) : e₁ = e₂ := by
  subst h₁; exact h₂

/-- **Ein Ort, den keine Zuweisung nennt, ueberlebt einen einzelnen Schritt.**

    Das ist die Rahmenaussage in ihrer kleinsten Form. Sie steht hier fuer die Zuweisung,
    weil dort der Rahmen entsteht; ueber der ganzen Folge traegt sie `Wirkung.huelle_deckt`
    aus der `effects`-Liste, und die beiden treffen sich am Pass. -/
theorem zuw_laesst_andere (t : String) (i e : Ausdruck) (f : String) (l l' : Lage)
    (o : Ort) (h : schritt (.zuw t i f e) l = .weiter l')
    (hne : ∀ k, o ≠ .slot t k f) : l'.welt o = l.welt o := by
  simp only [schritt] at h
  split at h
  · rename_i k w hi he
    injection h with h
    subst h
    simp only [setze]
    rw [if_neg (hne k)]
  · exact absurd h (by simp)

end Passlogik.Rumpf
