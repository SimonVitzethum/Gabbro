/-
  Datei:      Grammatik/Fehler.lean
  Gegenstand: **Der Fehlerausgang als PARALLELES Modell** -- neben `Semantik.lean`, nicht
              darin. Nichts an `eval`, `exec` oder `Ausgang` aendert sich; diese Datei legt
              daneben, was ein benannter Fehler waere, und in welcher Form die Ueberein-
              stimmung stuende, faellt er nicht.

    `Fehlerklasse` -- die vier benannten Fehler: `index` (Index ausserhalb), `ueberlauf`
                      (Ablage ausserhalb der erklaerten Breite), `nenner` (Nenner null),
                      `gestalt` (Gestalt passt nicht).
    `ErgebnisF`    -- der parallele Ausgang eines Ausdrucks: `wert` oder `fehler`.
    `evalF`        -- die parallele Auswertung: `State -> Expr -> Wert plus Fehlerklasse`
                      als Gestalt (`World D -> Expr D Γ Λ τ -> ErgebnisF D τ`, mit
                      Eintrittswelt und Sichtbereich als Argumenten wie bei `eval`).
    `evalF_ok` / `evalF_stimmt`
                   -- die Uebereinstimmungsform als `Prop`-Definitionen: kein Fehler
                      heisst, `eval` stimmt zu -- plus die Beweise, wo sie schliessen
                      (`evalF_ok_halt`, `evalF_stimmt_halt`).
    `IndexFalle` / `FehlerFall`
                   -- die Geschenk-Falsifizierer als DATEN, nicht als Beweise: ein Index
                      ausserhalb seines Bereichs erreicht `fehler .index` per Definition.
    `ErgebnisF.bind` / `map`
                   -- der Ausbreitungskern: ein fehlerhafter Eingang fehlert die Ausgabe.
    `evalArgsMit` / `evalArgsF`
                   -- die `evalAll`-Gestalt: ein fehlerhaftes Argument fehlert die Liste
                      (`evalArgsMit_kopf_fehler`, `_rest_fehler`); was heute nie fehlt,
                      steht als Satz (`evalArgsMit_ok`, `evalArgsF_ok`).
    `AusF` / `AusF.folge`
                   -- die Schrittfolge-Gestalt neben `Ausgang`: ein Fehler laeuft nicht
                      weiter (`folge_fehler`), `ok` schon (`folge_ok`), `logik` und
                      `hardware` bleiben stehen (`folge_logik`, `folge_hardware`).
    `schrittFolge` -- die Blockfolge ueber Welt-Schritte: ein fehlerhafter Schritt
                      fehlert die Folge                       (`schrittFolge_vorn`, `_hinten`).
    `schleifeF` / `durchlaufF`
                   -- der Schleifendurchgang (`foreverLauf`- / `traverseLauf`-Gestalt):
                      ein fehlerhafter Durchgang fehlert den Lauf (`schleifeF_fehler`,
                      `schleifeF_spaeter`, `durchlaufF_kopf`, `durchlaufF_rest`).
    `endZustandF`  -- die `finalState`-Gestalt: ein Fehler hat keinen Nachzustand
                      (`endZustandF_fehler`, `_logik`, `_hardware`, `_ok`).
    `IstBenannt`   -- die Sicherheitsform: `stuck`-oder-Fehler heisst eigene Logik
                      oder benannter Fehler (`fehler_ist_benannt`, `logik_ist_benannt`,
                      `hardware_ist_benannt`, `folge_benannt_bleibt`,
                      `ausF_klassifikation`).

  Warum `evalF` heute nie fehlt -- und das ist die Aussage, kein Mangel: ein
  `Expr.slot`-Index hat den Typ `.index (D.count t)` und traegt seinen Bereichsbeweis
  bei sich; ausserhalb ist nicht schreibbar. Der Fehlerarm ist nur ueber ROHE Daten
  (`IndexFalle`: Tabelle plus nacktes `Int`) erreichbar -- genau die Stelle, an der
  der Pruefer heute den Bereich haelt (`S3-FEHLER-ENTWURF.md`).

  DURCHGEFAEDELT (parallel, nicht am Anschluss): die Ausbreitung steht als parallele
    Form MIT Beweisen -- je eine Ausbreitungsaussage pro Kombinator (siehe oben).
    Was fehlt, ist der ANSCHLUSS, nicht die Form: `evalF` ruft `eval` auf und meldet
    `wert` (Schnitt S2), und `AusF` liegt neben `Ausgang`, statt dessen `fehler`-Fall
    zu tragen (Schnitt S1').

  Vorausgesetzt (vertraut, nicht bewiesen):
    P1  `eval` aus `Semantik.lean` ist die Bedeutung: `evalF` ruft es auf, statt es
        nachzubauen. Zwei Auswerter waeren zwei Bedeutungen.
    P2  Rohe Indizes kommen von aussen (`Orakel`, Maschine): `IndexFalle.k` ist ein
        Datum, kein Term der Grammatik.

  Schnitte (gebucht, nicht versteckt):
    S1' Anschluss an `exec` weiterhin offen: die Ausbreitung steht als parallele Form
        mit Beweisen; `Ausgang` bekommt keinen `fehler`-Fall, und `execStmt`/
        `execBlock`/`traverseLauf` faedeln ihn nicht durch. Die Koordination bleibt,
        was `S3-FEHLER-ENTWURF.md` §6 nennt.
    S2  `evalF` reicht jeden Aufruf an `eval` durch und meldet `wert`: die Fehler-
        arme sind erreichbar nur ueber die Fallen-Daten, nicht ueber Terme.
        Geschlossen dagegen, was schloss: `evalF_ok_halt`, `evalF_stimmt_halt`,
        `evalArgsF_ok` -- was heute nie fehlt, steht als Satz, nicht als Behauptung.
    S3  Nicht in `Grammatik.lean` verdrahtet: die Bahnbreite verbietet den
        Indexeingriff; pruefen allein mit `lake env lean Grammatik/Fehler.lean`.

  Kein `mathlib`, kein `sorry`, kein `axiom`, kein Import aus `programmlogik/`.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}

/-- Die vier benannten Fehler -- die Aufzaehlung neben den Ausgaengen, nicht darin. -/
inductive Fehlerklasse where
  | index
  | ueberlauf
  | nenner
  | gestalt
  deriving DecidableEq, Repr

/-- Der parallele Ausgang eines Ausdrucks: ein Wert seines Typs oder ein benannter
    Fehler. Daneben `Ausgang` aus `Semantik.lean`, der unveraendert bleibt. -/
inductive ErgebnisF (D : Deklaration) (τ : Ty) where
  | wert (v : Wert D τ)
  | fehler (k : Fehlerklasse)

/-- Die parallele Auswertung: `State -> Expr -> Wert plus Fehlerklasse` als Gestalt.
    Heute immer `wert`, per P1 durch `eval` hindurch -- der Fehlerarm wartet auf den
    Anschluss (Schnitt S2), nicht auf einen zweiten Auswerter. -/
def evalF (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) : ErgebnisF D τ :=
  .wert (eval σ₀ e σ ρ)

/-- Kein Fehler: das Ergebnis traegt einen Wert. Die Voraussetzung der
    Uebereinstimmung, als `Prop`-Definition, nicht als Satz. -/
def evalF_ok : ErgebnisF D τ → Prop
  | .wert _ => True
  | .fehler _ => False

/-- Die Uebereinstimmungsform: faellt kein Fehler, stimmt `eval` zu -- bewiesen in
    `evalF_stimmt_halt` fuer den heutigen Auswerter, der nie fehlt. -/
def evalF_stimmt (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) (v : Wert D τ) : Prop :=
  evalF σ₀ σ ρ e = .wert v → eval σ₀ e σ ρ = v

/-- Ein Index ausserhalb als DATUM: die Tabelle und das nackte `Int` -- ohne
    Bereichsbeweis, denn mit Beweis waere es kein Falsifizierer, sondern ein Term. -/
structure IndexFalle (D : Deklaration) where
  tab : D.Tab
  k : Int

/-- Ein Index ausserhalb erreicht `fehler .index` -- per Definition, nicht per Beweis. -/
def indexFalleErgebnis {τ : Ty} (_ : IndexFalle D) : ErgebnisF D τ :=
  .fehler .index

/-- Ein benannter Fehlerfall als Datum: die Klasse plus die Beschreibung, woher das
    rohe Datum kam (Orakel, Maschine, Prueferstelle). -/
structure FehlerFall where
  klasse : Fehlerklasse
  beschreibung : String

/-- Jeder benannte Fall erreicht seinen Fehler -- per Definition. -/
def fehlerFallErgebnis {τ : Ty} (f : FehlerFall) : ErgebnisF D τ :=
  .fehler f.klasse

/-! ## 1. Die Uebereinstimmung, bewiesen wo sie schliesst -/

/-- `evalF` meldet heute immer einen Wert -- als Satz ueber der Definition, nicht als
    Behauptung daneben (Schnitt S2, geschlossene Haelfte). -/
theorem evalF_ok_halt (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) :
    evalF_ok (evalF σ₀ σ ρ e) :=
  trivial

/-- Faellt kein Fehler, stimmt `eval` zu -- und heute faellt keiner: der Wert, den
    `evalF` traegt, ist der, den `eval` liefert. -/
theorem evalF_stimmt_halt (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) :
    evalF_stimmt σ₀ σ ρ e (eval σ₀ e σ ρ) :=
  fun _ => rfl

/-! ## 2. Der Ausbreitungskern: ein fehlerhafter Eingang fehlert die Ausgabe -/

/-- Die Fehlerfortpflanzung in einem Schritt: ein Wert laeuft weiter, ein Fehler
    bleibt stehen -- die Form, die jede zusammengesetzte Auswertung traegt. -/
def ErgebnisF.bind {τ' : Ty} : ErgebnisF D τ → (Wert D τ → ErgebnisF D τ') → ErgebnisF D τ'
  | .wert v, f => f v
  | .fehler k, _ => .fehler k

/-- Dieselbe Form ohne Fortsetzung: ein Wert wird abgebildet, ein Fehler bleibt. -/
def ErgebnisF.map {τ' : Ty} (f : Wert D τ → Wert D τ') : ErgebnisF D τ → ErgebnisF D τ'
  | .wert v => .wert (f v)
  | .fehler k => .fehler k

/-- Ein fehlerhafter Eingang fehlert die Bindung -- die Fortsetzung laeuft nicht. -/
theorem ErgebnisF.bind_fehler {τ' : Ty} (k : Fehlerklasse)
    (f : Wert D τ → ErgebnisF D τ') :
    (.fehler k : ErgebnisF D τ).bind f = .fehler k :=
  rfl

/-- Ein Wert laeuft in die Fortsetzung. -/
theorem ErgebnisF.bind_wert {τ' : Ty} (v : Wert D τ)
    (f : Wert D τ → ErgebnisF D τ') :
    (.wert v : ErgebnisF D τ).bind f = f v :=
  rfl

/-- Ein fehlerhafter Eingang fehlert die Abbildung. -/
theorem ErgebnisF.map_fehler {τ' : Ty} (f : Wert D τ → Wert D τ') (k : Fehlerklasse) :
    (.fehler k : ErgebnisF D τ).map f = .fehler k :=
  rfl

/-- Ein Wert wird abgebildet. -/
theorem ErgebnisF.map_wert {τ' : Ty} (f : Wert D τ → Wert D τ') (v : Wert D τ) :
    (.wert v : ErgebnisF D τ).map f = .wert (f v) :=
  rfl

/-! ## 3. Die `evalAll`-Gestalt: ein fehlerhaftes Argument fehlert die Liste -/

/-- Die fehlerfuehrende Auswertung einer Argumentliste, ueber einem beliebigen
    Einzelauswerter `aus`: der erste Fehler gewinnt, sonst steht die Belegung.
    Der Auswerter ist ein Parameter, damit die Ausbreitung fuer JEDEN gilt -- auch
    fuer einen, der spaeter einmal fehlt (heute tut es `evalF` nicht: S2). -/
def evalArgsMit {τs : List Ty} (aus : ∀ {t}, Expr D Γ Λ t → ErgebnisF D t)
    (as : Args D Γ Λ τs) : Env D τs ⊕ Fehlerklasse :=
  match as with
  | .nil => .inl .nil
  | .cons e rest =>
      match aus e, evalArgsMit aus rest with
      | .wert v, .inl vs => .inl (.cons v vs)
      | .fehler k, _ => .inr k
      | _, .inr k => .inr k

/-- Ein fehlerhafter Kopf fehlert die Liste -- der Rest laeuft nicht mehr. -/
theorem evalArgsMit_kopf_fehler {τs : List Ty}
    (aus : ∀ {t}, Expr D Γ Λ t → ErgebnisF D t)
    (e : Expr D Γ Λ τ) (rest : Args D Γ Λ τs)
    (k : Fehlerklasse) (h : aus e = .fehler k) :
    evalArgsMit aus (.cons e rest) = .inr k := by
  simp only [evalArgsMit, h]

/-- Ein fehlerhafter Rest fehlert die Liste -- bei fehlerfreiem Kopf. -/
theorem evalArgsMit_rest_fehler {τs : List Ty}
    (aus : ∀ {t}, Expr D Γ Λ t → ErgebnisF D t)
    (e : Expr D Γ Λ τ) (rest : Args D Γ Λ τs)
    (v : Wert D τ) (k : Fehlerklasse)
    (hv : aus e = .wert v) (hr : evalArgsMit aus rest = .inr k) :
    evalArgsMit aus (.cons e rest) = .inr k := by
  simp only [evalArgsMit, hv, hr]

/-- Fehlt kein Einzelauswerter, fehlt die Liste nicht. -/
theorem evalArgsMit_ok {τs : List Ty}
    (aus : ∀ {t}, Expr D Γ Λ t → ErgebnisF D t)
    (as : Args D Γ Λ τs)
    (h : ∀ {t} (e : Expr D Γ Λ t), ∃ v, aus e = .wert v) :
    ∃ ρ', evalArgsMit aus as = .inl ρ' := by
  induction as with
  | nil => exact ⟨.nil, rfl⟩
  | cons e rest ih =>
      obtain ⟨v, hv⟩ := h e
      obtain ⟨vs, hs⟩ := ih
      exact ⟨.cons v vs, by simp only [evalArgsMit, hv, hs]⟩

/-- Die `evalAll`-Gestalt ueber dem heutigen Auswerter: `evalArgs` mit Fehlerkanal. -/
def evalArgsF {τs : List Ty} (σ₀ σ : World D) (ρ : Env D Γ)
    (as : Args D Γ Λ τs) : Env D τs ⊕ Fehlerklasse :=
  evalArgsMit (evalF σ₀ σ ρ) as

/-- Heute fehlt die Liste nie -- der Satz zu Schnitt S2. -/
theorem evalArgsF_ok {τs : List Ty} (σ₀ σ : World D) (ρ : Env D Γ)
    (as : Args D Γ Λ τs) : ∃ ρ', evalArgsF σ₀ σ ρ as = .inl ρ' := by
  unfold evalArgsF
  exact evalArgsMit_ok _ _ fun e => ⟨_, rfl⟩

/-! ## 4. Die Schrittfolge-Gestalt neben `Ausgang` -/

/-- Der parallele Ausgang einer Anweisung: der Ausgang aus `Semantik.lean`, oder ein
    benannter Fehler -- daneben, nicht darin (Schnitt S1'). -/
inductive AusF (V : Vertrag D) (l : Bool) (Γ : Ctx) where
  | weiter (a : Ausgang V l Γ)
  | fehler (k : Fehlerklasse)

variable {V : Vertrag D} {l : Bool}

/-- Die Folge: ein Fehler laeuft nicht weiter; `ok` uebergibt Welt und Sichtbereich;
    jeder andere Ausgang bleibt stehen. -/
def AusF.folge : AusF V l Γ → (World D → Env D Γ → AusF V l Γ) → AusF V l Γ
  | .fehler k, _ => .fehler k
  | .weiter (.ok σ ρ), nach => nach σ ρ
  | .weiter o, _ => .weiter o

/-- Ein Fehler laeuft nicht weiter -- die Fortsetzung wird nicht aufgerufen. -/
theorem AusF.folge_fehler (k : Fehlerklasse)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.fehler k : AusF V l Γ).folge nach = .fehler k :=
  rfl

/-- `ok` uebergibt Welt und Sichtbereich an die Fortsetzung. -/
theorem AusF.folge_ok (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.weiter (.ok σ ρ) : AusF V l Γ).folge nach = nach σ ρ :=
  rfl

/-- Die Logik des Schreibers bleibt stehen. -/
theorem AusF.folge_logik (e : Logik D)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.weiter (.logik e) : AusF V l Γ).folge nach = .weiter (.logik e) :=
  rfl

/-- Eine widerlegte Maschinenannahme bleibt stehen. -/
theorem AusF.folge_hardware (e : Hardware D)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.weiter (.hardware e) : AusF V l Γ).folge nach = .weiter (.hardware e) :=
  rfl

/-- Die Blockfolge ueber Welt-Schritten: ein fehlerhafter Schritt beendet die Folge;
    sonst traegt die Welt weiter. -/
def schrittFolge : List (World D → (World D ⊕ Fehlerklasse)) → World D →
    (World D ⊕ Fehlerklasse)
  | [], σ => .inl σ
  | s :: ss, σ =>
      match s σ with
      | .inr k => .inr k
      | .inl σ' => schrittFolge ss σ'

/-- Ein fehlerhafter Schritt fehlert die Folge -- der Rest laeuft nicht. -/
theorem schrittFolge_vorn (s : World D → (World D ⊕ Fehlerklasse))
    (ss : List (World D → (World D ⊕ Fehlerklasse))) (σ : World D)
    (k : Fehlerklasse) (h : s σ = .inr k) :
    schrittFolge (s :: ss) σ = .inr k := by
  simp only [schrittFolge, h]

/-- Ein fehlerhafter Rest fehlert die Folge -- bei fehlerfreiem Kopf. -/
theorem schrittFolge_hinten (s : World D → (World D ⊕ Fehlerklasse))
    (ss : List (World D → (World D ⊕ Fehlerklasse))) (σ σ' : World D)
    (k : Fehlerklasse) (h : s σ = .inl σ') (hr : schrittFolge ss σ' = .inr k) :
    schrittFolge (s :: ss) σ = .inr k := by
  simp only [schrittFolge, h, hr]

/-! ## 5. Der Schleifendurchgang: ein fehlerhafter Durchgang fehlert den Lauf -/

/-- Die treibstoffbegrenzte Wiederholung (`foreverLauf`-Gestalt): ein fehlerhafter
    Schritt beendet den Lauf mit seinem Fehler. -/
def schleifeF (schritt : World D → (World D ⊕ Fehlerklasse)) :
    Nat → World D → (World D ⊕ Fehlerklasse)
  | 0, σ => .inl σ
  | n + 1, σ =>
      match schritt σ with
      | .inr k => .inr k
      | .inl σ' => schleifeF schritt n σ'

/-- Ein fehlerhafter Schritt fehlert den Lauf -- sofort, in jedem Durchgang. -/
theorem schleifeF_fehler (schritt : World D → (World D ⊕ Fehlerklasse))
    (n : Nat) (σ : World D) (k : Fehlerklasse) (h : schritt σ = .inr k) :
    schleifeF schritt (n + 1) σ = .inr k := by
  simp only [schleifeF, h]

/-- Ein fehlerhafter spaeterer Durchgang fehlert den Lauf -- bei fehlerfreiem ersten. -/
theorem schleifeF_spaeter (schritt : World D → (World D ⊕ Fehlerklasse))
    (n : Nat) (σ σ' : World D) (k : Fehlerklasse)
    (h : schritt σ = .inl σ') (hr : schleifeF schritt n σ' = .inr k) :
    schleifeF schritt (n + 1) σ = .inr k := by
  simp only [schleifeF, h, hr]

/-- Der Durchlauf ueber jedes Element einmal (`traverseLauf`-Gestalt): ein
    fehlerhaftes Element beendet den Lauf mit seinem Fehler. -/
def durchlaufF {α : Type} (schritt : α → World D → (World D ⊕ Fehlerklasse)) :
    List α → World D → (World D ⊕ Fehlerklasse)
  | [], σ => .inl σ
  | x :: xs, σ =>
      match schritt x σ with
      | .inr k => .inr k
      | .inl σ' => durchlaufF schritt xs σ'

/-- Ein fehlerhaftes Element fehlert den Durchlauf. -/
theorem durchlaufF_kopf {α : Type}
    (schritt : α → World D → (World D ⊕ Fehlerklasse))
    (x : α) (xs : List α) (σ : World D) (k : Fehlerklasse)
    (h : schritt x σ = .inr k) :
    durchlaufF schritt (x :: xs) σ = .inr k := by
  simp only [durchlaufF, h]

/-- Ein fehlerhafter Rest fehlert den Durchlauf -- bei fehlerfreiem Kopf. -/
theorem durchlaufF_rest {α : Type}
    (schritt : α → World D → (World D ⊕ Fehlerklasse))
    (x : α) (xs : List α) (σ σ' : World D) (k : Fehlerklasse)
    (h : schritt x σ = .inl σ') (hr : durchlaufF schritt xs σ' = .inr k) :
    durchlaufF schritt (x :: xs) σ = .inr k := by
  simp only [durchlaufF, h, hr]

/-! ## 6. Die `finalState`-Gestalt: ein Fehler hat keinen Nachzustand -/

/-- Der Nachzustand: was eine Welt traegt (`ok`, `zurueck`, `grund`, `leave`,
    `next`), sonst nichts -- ein Fehler hat keinen, wie `stuck` keinen haette. -/
def endZustandF : AusF V l Γ → Option (World D)
  | .weiter (.ok σ _) => some σ
  | .weiter (.zurueck σ _) => some σ
  | .weiter (.grund σ _) => some σ
  | .weiter (.leave _ σ _) => some σ
  | .weiter (.next _ σ _) => some σ
  | .weiter (.logik _) => none
  | .weiter (.hardware _) => none
  | .fehler _ => none

/-- Ein benannter Fehler hat keinen Nachzustand. -/
theorem endZustandF_fehler (k : Fehlerklasse) :
    endZustandF (AusF.fehler k : AusF V l Γ) = none :=
  rfl

/-- Die widerlegte Schreiberlogik hat keinen Nachzustand. -/
theorem endZustandF_logik (e : Logik D) :
    endZustandF (AusF.weiter (.logik e) : AusF V l Γ) = none :=
  rfl

/-- Die widerlegte Maschinenannahme hat keinen Nachzustand. -/
theorem endZustandF_hardware (e : Hardware D) :
    endZustandF (AusF.weiter (.hardware e) : AusF V l Γ) = none :=
  rfl

/-- `ok` traegt seine Welt weiter. -/
theorem endZustandF_ok (σ : World D) (ρ : Env D Γ) :
    endZustandF (AusF.weiter (.ok σ ρ) : AusF V l Γ) = some σ :=
  rfl

/-! ## 7. Die Sicherheitsform: gestoert heisst eigene Logik oder benannter Fehler -/

/-- Benannt: ein Fehler aus der Aufzaehlung, oder einer der zwei Ausgaenge, die
    `Semantik.lean` kennt -- die Logik des Schreibers, die Annahme ueber die Maschine. -/
def IstBenannt : AusF V l Γ → Prop
  | .fehler _ => True
  | .weiter (.logik _) => True
  | .weiter (.hardware _) => True
  | .weiter _ => False

/-- Ein benannter Fehler ist benannt. -/
theorem fehler_ist_benannt (k : Fehlerklasse) :
    IstBenannt (AusF.fehler k : AusF V l Γ) :=
  trivial

/-- Die widerlegte Schreiberlogik ist benannt. -/
theorem logik_ist_benannt (e : Logik D) :
    IstBenannt (AusF.weiter (.logik e) : AusF V l Γ) :=
  trivial

/-- Die widerlegte Maschinenannahme ist benannt. -/
theorem hardware_ist_benannt (e : Hardware D) :
    IstBenannt (AusF.weiter (.hardware e) : AusF V l Γ) :=
  trivial

/-- Die Folge erhaelt das Benannte: war der erste Ausgang benannt, ist es auch die
    Folge -- ein Fehler wird nicht still zu einem Wert. -/
theorem folge_benannt_bleibt (a : AusF V l Γ)
    (nach : World D → Env D Γ → AusF V l Γ) (h : IstBenannt a) :
    IstBenannt (a.folge nach) := by
  cases a with
  | fehler k => trivial
  | weiter o =>
      cases o with
      | ok σ ρ => exact False.elim h
      | zurueck σ v => exact False.elim h
      | grund σ r => exact False.elim h
      | leave h' σ ρ => exact False.elim h
      | next h' σ ρ => exact False.elim h
      | logik e => trivial
      | hardware e => trivial

/-- Jeder Ausgang ist entweder weitergetragen oder benannt fehlert -- die Form, in
    der `stuck`-oder-Fehler die eigene Logik oder den benannten Fehler stuende. -/
theorem ausF_klassifikation (a : AusF V l Γ) :
    (∃ o, a = .weiter o) ∨ (∃ k, a = .fehler k) := by
  cases a with
  | weiter o => exact .inl ⟨o, rfl⟩
  | fehler k => exact .inr ⟨k, rfl⟩

#print axioms Gabbro.Grammatik.evalF
#print axioms Gabbro.Grammatik.evalF_ok
#print axioms Gabbro.Grammatik.evalF_stimmt
#print axioms Gabbro.Grammatik.indexFalleErgebnis
#print axioms Gabbro.Grammatik.fehlerFallErgebnis
#print axioms Gabbro.Grammatik.evalF_ok_halt
#print axioms Gabbro.Grammatik.evalF_stimmt_halt
#print axioms Gabbro.Grammatik.ErgebnisF.bind
#print axioms Gabbro.Grammatik.ErgebnisF.bind_fehler
#print axioms Gabbro.Grammatik.ErgebnisF.bind_wert
#print axioms Gabbro.Grammatik.ErgebnisF.map_fehler
#print axioms Gabbro.Grammatik.ErgebnisF.map_wert
#print axioms Gabbro.Grammatik.evalArgsMit
#print axioms Gabbro.Grammatik.evalArgsMit_kopf_fehler
#print axioms Gabbro.Grammatik.evalArgsMit_rest_fehler
#print axioms Gabbro.Grammatik.evalArgsMit_ok
#print axioms Gabbro.Grammatik.evalArgsF
#print axioms Gabbro.Grammatik.evalArgsF_ok
#print axioms Gabbro.Grammatik.AusF.folge
#print axioms Gabbro.Grammatik.AusF.folge_fehler
#print axioms Gabbro.Grammatik.AusF.folge_ok
#print axioms Gabbro.Grammatik.AusF.folge_logik
#print axioms Gabbro.Grammatik.AusF.folge_hardware
#print axioms Gabbro.Grammatik.schrittFolge
#print axioms Gabbro.Grammatik.schrittFolge_vorn
#print axioms Gabbro.Grammatik.schrittFolge_hinten
#print axioms Gabbro.Grammatik.schleifeF
#print axioms Gabbro.Grammatik.schleifeF_fehler
#print axioms Gabbro.Grammatik.schleifeF_spaeter
#print axioms Gabbro.Grammatik.durchlaufF
#print axioms Gabbro.Grammatik.durchlaufF_kopf
#print axioms Gabbro.Grammatik.durchlaufF_rest
#print axioms Gabbro.Grammatik.endZustandF
#print axioms Gabbro.Grammatik.endZustandF_fehler
#print axioms Gabbro.Grammatik.endZustandF_logik
#print axioms Gabbro.Grammatik.endZustandF_hardware
#print axioms Gabbro.Grammatik.endZustandF_ok
#print axioms Gabbro.Grammatik.IstBenannt
#print axioms Gabbro.Grammatik.fehler_ist_benannt
#print axioms Gabbro.Grammatik.logik_ist_benannt
#print axioms Gabbro.Grammatik.hardware_ist_benannt
#print axioms Gabbro.Grammatik.folge_benannt_bleibt
#print axioms Gabbro.Grammatik.ausF_klassifikation

end Gabbro.Grammatik
