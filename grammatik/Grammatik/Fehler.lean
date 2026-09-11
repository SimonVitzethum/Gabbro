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
    `AusF.vonAusgang` / `zuAusgang`
                   -- die Einbettung in die Ausfuehrung: jeder `Ausgang` laeuft als
                      `weiter` weiter (`zuAusgang_vonAusgang`), ein benannter Fehler
                      hat keinen `Ausgang` (`zuAusgang_fehler`); `folge_weiter`
                      stimmt die Folge mit `execBlock` (`ok` weiter, sonst `o`),
                      je ein Fortpflanzungssatz pro Ausgang (`folge_zurueck`,
                      `_grund`, `_leave`, `_next` neben `_ok`, `_logik`,
                      `_hardware`).
    `IstStecken`   -- `stuck` als Abwesenheit eines Nachzustands; `stuck` heisst
                      benannt (`stecken_heisst_benannt`) und umgekehrt
                      (`benannt_heisst_stecken`), in disjunktiver Form
                      (`stecken_klassifikation`): die `exec_sicher`-Gestalt.
    `evalArgsMit_stimmt` / `evalArgsF_stimmt`
                   -- die Uebereinstimmung DURCH die `evalAll`-Gestalt: was die
                      fehlerfuehrende Liste traegt, rechnet `evalArgs`.
    `schrittRein` / `schrittFolge_rein`
                   -- die Schrittfolge ohne Fehler faltet die Welt
                      (`execBlock`-Gestalt ohne Fehlerarm).
    `durchlaufRein` / `durchlaufF_rein`
                   -- der Durchlauf ohne Fehler faltet ueber die Elemente
                      (`traverseLauf`-Geruest ohne Invarianten-, `leave`-,
                      `next`-Arme).
    `schleifeF_als_folge`
                   -- die treibstoffbegrenzte Schleife ohne Fehler IST die
                      Schrittfolge ihrer Abwicklungen (`foreverLauf`-Geruest
                      ohne `fortschritt`-Arm).
     `endZustandF_*` -- die `finalState`-Abbildung, vollstaendig: je ein Satz pro
                       Ausgang (`_zurueck`, `_grund`, `_leave`, `_next` neben
                       `_ok`, `_logik`, `_hardware`, `_fehler`).
     `blockF` / `traverseAusF` / `foreverAusF`
                    -- die `execBlock`- / `traverseLauf`- / `foreverLauf`-Gestalt mit
                       Fehlerarm: ein fehlerhafter Kopf fehlert den Block
                       (`blockF_cons_fehler`), `ok` uebergibt (`blockF_cons_ok`),
                       jeder andere Ausgang bleibt stehen (`blockF_cons_weiter`);
                       ein fehlerhaftes Element fehlert den Durchlauf
                       (`traverseAusF_kopf_fehler`), `ok`/`next` laufen weiter
                       (`traverseAusF_kopf_ok`, `_kopf_next`), der fehlerhafte
                       Rest traegt durch (`traverseAusF_ok_rest_fehler`);
                       fehlerfrei stimmt der Durchlauf mit `traverseLauf`
                       (`traverseAusF_stimmt`); der treibstoffbegrenzte Lauf
                       ebenso (`foreverAusF_kopf_fehler`, `_kopf_ok`); ein
                       fehlerhafter Kopf ist benannt
                       (`blockF_cons_fehler_benannt`).

  Warum `evalF` heute nie fehlt -- und das ist die Aussage, kein Mangel: ein
  `Expr.slot`-Index hat den Typ `.index (D.count t)` und traegt seinen Bereichsbeweis
  bei sich; ausserhalb ist nicht schreibbar. Der Fehlerarm ist nur ueber ROHE Daten
  (`IndexFalle`: Tabelle plus nacktes `Int`) erreichbar -- genau die Stelle, an der
  der Pruefer heute den Bereich haelt (`S3-FEHLER-ENTWURF.md`).

  DURCHGEFAEDELT (parallel, nicht am Anschluss): die Ausbreitung steht als parallele
    Form MIT Beweisen -- je eine Ausbreitungsaussage pro Kombinator (siehe oben).
    Der ANSCHLUSS steht als Einbettung mit Uebereinstimmung: `vonAusgang` traegt
    jeden `Ausgang` als `weiter`, `folge_weiter` stimmt die Folge mit `execBlock`,
    `stecken_heisst_benannt`/`benannt_heisst_stecken` sagen `stuck` GENAU DANN,
    wenn benannt, und `evalArgsF_stimmt`/`schrittFolge_rein`/`durchlaufF_rein`/
     `schleifeF_als_folge` stimmen `evalF` DURCH Schritt- und Schleifengestalten
     mit `eval`/`evalArgs`. Was fehlt, ist die Durchfaedelung, nicht die Form:
     `execStmt`/`execBlock`/`traverseLauf` rufen die parallelen Formen nicht auf
     (Schnitt S1'). Seit §11 stehen auch die Block- und Schleifenformen mit
     Fehlerarm als parallele Form mit Beweisen (`blockF_*`, `traverseAusF_*`,
     `foreverAusF_*` samt `traverseAusF_stimmt`); was weiterhin fehlt, ist die
     echte Rekursion ueber `Stmt`/`Block` -- sie steht in `Semantik.lean` und
     ruft die parallelen Formen nicht auf.

  Vorausgesetzt (vertraut, nicht bewiesen):
    P1  `eval` aus `Semantik.lean` ist die Bedeutung: `evalF` ruft es auf, statt es
        nachzubauen. Zwei Auswerter waeren zwei Bedeutungen.
    P2  Rohe Indizes kommen von aussen (`Orakel`, Maschine): `IndexFalle.k` ist ein
        Datum, kein Term der Grammatik.

  Schnitte (gebucht, nicht versteckt):
     S1' Anschluss an `exec` halb geschlossen: Einbettung (`vonAusgang`,
         `zuAusgang`), Folgen-Uebereinstimmung (`folge_weiter` plus je ein Satz
         pro Ausgang), `stuck`-genau-dann-benannt (`stecken_heisst_benannt`,
         `benannt_heisst_stecken`, `stecken_klassifikation`) und die
         Uebereinstimmung durch `evalAll`- (`evalArgsF_stimmt`), Schritt-
         (`schrittFolge_rein`) und Schleifengestalten (`durchlaufF_rein`,
         `schleifeF_als_folge`) stehen mit Beweisen; dazu seit §11 die Block-
         und Schleifenfortpflanzung mit Fehlerarm (`blockF_cons_fehler`,
         `_cons_ok`, `_cons_weiter`, `traverseAusF_kopf_fehler`, `_kopf_ok`,
         `_kopf_next`, `_ok_rest_fehler`, `foreverAusF_kopf_fehler`,
         `_kopf_ok`), die Durchlauf-Uebereinstimmung (`traverseAusF_stimmt`)
         und der Benannt-Anschluss (`blockF_cons_fehler_benannt`); `Ausgang`
         bekommt keinen `fehler`-Fall, und `execStmt`/`execBlock`/`traverseLauf`
         faedeln ihn nicht durch. Die Koordination bleibt, was
         `S3-FEHLER-ENTWURF.md` §6 nennt.
         Offen (braucht `Semantik.lean`, exakt gebucht): die echte
         Durchfaedelung durch `Stmt`/`Block` -- `execStmt`/`execBlock`/`execEnd`
         ueber `P`/`O`/`passes`/`R` und `traverseLauf` mit `Block`-Ruempfen.
         Fehlendes Lemma, exakt: `execBlock_cons_fehler` -- fuer alle `P O`
         `passes R s rest σ ρ k` gilt: liefert die fehlerfuehrende Form von
         `execStmt s σ ρ` den Fehler `k`, so liefert die fehlerfuehrende Form
         von `execBlock (cons s rest) σ ρ` den Fehler `k`. Es schliesst hier
         nicht, weil `Ausgang` keinen `fehler`-Fall traegt und `execStmt`/
         `execBlock` weder `AusF.folge` noch `blockF` rufen; es zu schliessen
         verlangt den Fehlerarm in `Semantik.lean` (Rueckgabe `AusF` statt
         `Ausgang`), und das ist gebucht, nicht getan.
    S2  `evalF` reicht jeden Aufruf an `eval` durch und meldet `wert`: die Fehler-
        arme sind erreichbar nur ueber die Fallen-Daten, nicht ueber Terme.
        Geschlossen dagegen, was schloss: `evalF_ok_halt`, `evalF_stimmt_halt`,
        `evalArgsF_ok` -- und die Uebereinstimmung DURCH die Gestalten:
        `evalArgsMit_stimmt`/`evalArgsF_stimmt` gegen `evalArgs`,
        `schrittFolge_rein`/`durchlaufF_rein`/`schleifeF_als_folge` als Faltung
        ohne Fehlerarm, `endZustandF` je Ausgang. Was heute nie fehlt, steht
        als Satz, nicht als Behauptung.
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

/-- An out-of-range index reaches `fehler .index` -- by definition: the
    raw-datum falsifier faults where no grammar term can (`indexFalleErgebnis`). -/
theorem indexFalleErgebnis_fehler (F : IndexFalle D) :
    (indexFalleErgebnis F : ErgebnisF D τ) = .fehler .index :=
  rfl

/-- A named fault datum reaches its own fault -- by definition
    (`fehlerFallErgebnis`). -/
theorem fehlerFallErgebnis_fehler (f : FehlerFall) :
    (fehlerFallErgebnis f : ErgebnisF D τ) = .fehler f.klasse :=
  rfl

/-- The index falsifier never counts as ok: raw data faults, it does not agree. -/
theorem evalF_ok_nicht_indexFalle (F : IndexFalle D) :
    ¬ evalF_ok (indexFalleErgebnis F : ErgebnisF D τ) := by
  unfold evalF_ok indexFalleErgebnis
  exact id

/-- A named fault datum never counts as ok. -/
theorem evalF_ok_nicht_fehlerFall (f : FehlerFall) :
    ¬ evalF_ok (fehlerFallErgebnis f : ErgebnisF D τ) := by
  unfold evalF_ok fehlerFallErgebnis
  exact id

#print axioms Gabbro.Grammatik.indexFalleErgebnis_fehler
#print axioms Gabbro.Grammatik.fehlerFallErgebnis_fehler
#print axioms Gabbro.Grammatik.evalF_ok_nicht_indexFalle
#print axioms Gabbro.Grammatik.evalF_ok_nicht_fehlerFall

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

/-! ## 8. The embedding into execution: `AusF` carries `Ausgang` -/

/-- The embedding: every `Ausgang` of `Semantik.lean` runs on as `weiter` --
    the hook, not a third exit: `Ausgang` gains no constructor. -/
def AusF.vonAusgang : Ausgang V l Γ → AusF V l Γ
  | o => .weiter o

/-- Back: `weiter` projects, a named fault has no `Ausgang` -- as `finalState`
    maps `fehler` (and `stuck`) to `none` (S3 design A, §6). -/
def AusF.zuAusgang : AusF V l Γ → Option (Ausgang V l Γ)
  | .weiter o => some o
  | .fehler _ => none

/-- There and back: the embedding loses nothing. -/
theorem AusF.zuAusgang_vonAusgang (o : Ausgang V l Γ) :
    (AusF.vonAusgang o).zuAusgang = some o :=
  rfl

/-- A named fault has no `Ausgang` to project to. -/
theorem AusF.zuAusgang_fehler (k : Fehlerklasse) :
    (AusF.fehler k : AusF V l Γ).zuAusgang = none :=
  rfl

/-- The sequencing agreement, end to end: `folge` over an embedded `Ausgang`
    calls the continuation exactly where `execBlock` continues (`ok`), and
    carries every other exit unchanged -- as `execBlock`'s `| o => o` arm. -/
theorem AusF.folge_weiter (o : Ausgang V l Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.weiter o).folge nach =
      match o with
      | .ok σ ρ => nach σ ρ
      | .zurueck σ v => .weiter (.zurueck σ v)
      | .grund σ r => .weiter (.grund σ r)
      | .leave h σ ρ => .weiter (.leave h σ ρ)
      | .next h σ ρ => .weiter (.next h σ ρ)
      | .logik e => .weiter (.logik e)
      | .hardware e => .weiter (.hardware e) := by
  cases o <;> rfl

/-- A returned answer does not continue. -/
theorem AusF.folge_zurueck (σ : World D) (v : ErgVal D V.erg)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.weiter (.zurueck σ v) : AusF V l Γ).folge nach =
      .weiter (.zurueck σ v) :=
  rfl

/-- A raised ground does not continue. -/
theorem AusF.folge_grund (σ : World D) (r : Fin V.gruende)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.weiter (.grund σ r) : AusF V l Γ).folge nach =
      .weiter (.grund σ r) :=
  rfl

/-- A consumed `leave` does not continue. -/
theorem AusF.folge_leave (h : l = true) (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.weiter (.leave h σ ρ) : AusF V l Γ).folge nach =
      .weiter (.leave h σ ρ) :=
  rfl

/-- A consumed `next` does not continue. -/
theorem AusF.folge_next (h : l = true) (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.weiter (.next h σ ρ) : AusF V l Γ).folge nach =
      .weiter (.next h σ ρ) :=
  rfl

/-! ## 9. Stuck-or-fault implies own logic or named fault -/

/-- Stuck: the run carries no post-state. In `Semantik.lean` there is no stuck
    VALUE -- `eval` is total, `exec` always answers -- so stuck is the ABSENCE
    of a post-state, which a named fault shares (`endZustandF_fehler`). -/
def IstStecken : AusF V l Γ → Prop
  | a => endZustandF a = none

/-- Stuck implies named: a run without post-state is the author's logic or a
    named fault -- the `exec_sicher` shape of S3 design A, §6, proved on the
    parallel outcome without touching `Ausgang`. -/
theorem stecken_heisst_benannt (a : AusF V l Γ) (h : IstStecken a) :
    IstBenannt a := by
  cases a with
  | fehler k => trivial
  | weiter o =>
      cases o with
      | ok σ ρ => exact absurd h (by simp [IstStecken, endZustandF])
      | zurueck σ v => exact absurd h (by simp [IstStecken, endZustandF])
      | grund σ r => exact absurd h (by simp [IstStecken, endZustandF])
      | leave h' σ ρ => exact absurd h (by simp [IstStecken, endZustandF])
      | next h' σ ρ => exact absurd h (by simp [IstStecken, endZustandF])
      | logik e => trivial
      | hardware e => trivial

/-- Named implies stuck: the converse -- together they say stuck MEANS named. -/
theorem benannt_heisst_stecken (a : AusF V l Γ) (h : IstBenannt a) :
    IstStecken a := by
  cases a with
  | fehler k => rfl
  | weiter o =>
      cases o with
      | ok σ ρ => exact False.elim h
      | zurueck σ v => exact False.elim h
      | grund σ r => exact False.elim h
      | leave h' σ ρ => exact False.elim h
      | next h' σ ρ => exact False.elim h
      | logik e => rfl
      | hardware e => rfl

/-- Stuck-or-fault in the disjunctive form: own logic or named fault. -/
theorem stecken_klassifikation (a : AusF V l Γ) (h : IstStecken a) :
    (∃ e : Logik D, a = .weiter (.logik e)) ∨
    (∃ e : Hardware D, a = .weiter (.hardware e)) ∨
    (∃ k, a = .fehler k) := by
  cases a with
  | fehler k => exact .inr (.inr ⟨k, rfl⟩)
  | weiter o =>
      cases o with
      | ok σ ρ => simp [IstStecken, endZustandF] at h
      | zurueck σ v => simp [IstStecken, endZustandF] at h
      | grund σ r => simp [IstStecken, endZustandF] at h
      | leave h' σ ρ => simp [IstStecken, endZustandF] at h
      | next h' σ ρ => simp [IstStecken, endZustandF] at h
      | logik e => exact .inl ⟨e, rfl⟩
      | hardware e => exact .inr (.inl ⟨e, rfl⟩)

/-! ## 10. `evalF` agreement through the step and loop shapes, end to end -/

/-- Agreement through the `evalAll` shape, for EVERY pointwise-agreeing
    evaluator -- including one that faults one day (unlike today's `evalF`). -/
theorem evalArgsMit_stimmt {τs : List Ty}
    (aus : ∀ {t}, Expr D Γ Λ t → ErgebnisF D t)
    (σ₀ σ : World D) (ρ : Env D Γ) (as : Args D Γ Λ τs) (ρ' : Env D τs)
    (hstim : ∀ {t} (e : Expr D Γ Λ t), aus e = .wert (eval σ₀ e σ ρ))
    (h : evalArgsMit aus as = .inl ρ') :
    evalArgs σ₀ as σ ρ = ρ' := by
  induction as with
  | nil =>
      simp only [evalArgsMit] at h
      cases h
      rfl
  | cons e rest ih =>
      simp only [evalArgsMit, hstim] at h
      obtain ⟨vs, hs⟩ := evalArgsMit_ok aus rest (fun e => ⟨_, hstim e⟩)
      simp only [hs] at h
      cases h
      exact congrArg (Env.cons (eval σ₀ e σ ρ)) (ih _ hs)

/-- Agreement end to end: what today's fault-free argument list carries is what
    `evalArgs` of `Semantik.lean` computes. -/
theorem evalArgsF_stimmt {τs : List Ty} (σ₀ σ : World D) (ρ : Env D Γ)
    (as : Args D Γ Λ τs) (ρ' : Env D τs)
    (h : evalArgsF σ₀ σ ρ as = .inl ρ') :
    evalArgs σ₀ as σ ρ = ρ' :=
  evalArgsMit_stimmt _ σ₀ σ ρ as ρ' (fun _ => rfl) h

/-- A fault-free world step, lifted into the fault channel. -/
def schrittRein (f : World D → World D) : World D → (World D ⊕ Fehlerklasse) :=
  fun σ => .inl (f σ)

/-- Step-sequence agreement end to end: fault-free steps thread the world as the
    fold does -- the `execBlock` sequencing shape without the fault arm. -/
theorem schrittFolge_rein (fs : List (World D → World D)) (σ : World D) :
    schrittFolge (fs.map schrittRein) σ = .inl (fs.foldl (fun σ f => f σ) σ) := by
  induction fs generalizing σ with
  | nil => rfl
  | cons f fs ih =>
      simp only [List.map_cons, schrittFolge, schrittRein, List.foldl_cons]
      exact ih _

/-- A fault-free element step, lifted into the fault channel. -/
def durchlaufRein {α : Type} (f : α → World D → World D) :
    α → World D → (World D ⊕ Fehlerklasse) :=
  fun x σ => .inl (f x σ)

/-- Traversal agreement end to end: one fault-free pass per element folds the
    world -- the `traverseLauf` skeleton without invariant, `leave` and `next`
    arms (control, carried by `weiter`, not by the fault channel). -/
theorem durchlaufF_rein {α : Type} (f : α → World D → World D) (xs : List α)
    (σ : World D) :
    durchlaufF (durchlaufRein f) xs σ = .inl (xs.foldl (fun σ x => f x σ) σ) := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih =>
      simp only [durchlaufF, durchlaufRein, List.foldl_cons]
      exact ih _

/-- Loop agreement end to end: a fuel-bounded fault-free loop IS the step
    sequence of its unfoldings -- the `foreverLauf` skeleton without the
    `fortschritt` arm (a hardware assumption, not a fault). -/
theorem schleifeF_als_folge (f : World D → World D) (n : Nat) (σ : World D) :
    schleifeF (schrittRein f) n σ =
      schrittFolge (List.replicate n (schrittRein f)) σ := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
      simp only [schleifeF, schrittRein, List.replicate_succ, schrittFolge]
      exact ih _

/-- A returned answer carries its world. -/
theorem endZustandF_zurueck (σ : World D) (v : ErgVal D V.erg) :
    endZustandF (AusF.weiter (.zurueck σ v) : AusF V l Γ) = some σ :=
  rfl

/-- A raised ground carries its world. -/
theorem endZustandF_grund (σ : World D) (r : Fin V.gruende) :
    endZustandF (AusF.weiter (.grund σ r) : AusF V l Γ) = some σ :=
  rfl

/-- A consumed `leave` carries its world. -/
theorem endZustandF_leave (h : l = true) (σ : World D) (ρ : Env D Γ) :
    endZustandF (AusF.weiter (.leave h σ ρ) : AusF V l Γ) = some σ :=
  rfl

/-- A consumed `next` carries its world. -/
theorem endZustandF_next (h : l = true) (σ : World D) (ρ : Env D Γ) :
    endZustandF (AusF.weiter (.next h σ ρ) : AusF V l Γ) = some σ :=
  rfl

/-! ## 11. Fault threading through the `execBlock`/`traverseLauf` shapes -/

/-- The `execBlock` sequencing shape over fault-carrying steps: `nil` answers
    `ok`, `cons` continues through `AusF.folge` -- a faulted head faults the
    block, a non-`ok` exit stops it, exactly as `execBlock`'s `| o => o` arm. -/
def blockF : List (World D → Env D Γ → AusF V l Γ) → World D → Env D Γ → AusF V l Γ
  | [], σ, ρ => .weiter (.ok σ ρ)
  | s :: ss, σ, ρ => (s σ ρ).folge (fun σ' ρ' => blockF ss σ' ρ')

/-- The empty block answers `ok` -- the `execBlock.nil` shape. -/
theorem blockF_nil (σ : World D) (ρ : Env D Γ) :
    blockF ([] : List (World D → Env D Γ → AusF V l Γ)) σ ρ = .weiter (.ok σ ρ) :=
  rfl

/-- A faulted head faults the block -- the rest does not run. -/
theorem blockF_cons_fehler (s : World D → Env D Γ → AusF V l Γ)
    (ss : List (World D → Env D Γ → AusF V l Γ)) (σ : World D) (ρ : Env D Γ)
    (k : Fehlerklasse) (h : s σ ρ = (AusF.fehler k : AusF V l Γ)) :
    blockF (s :: ss) σ ρ = (AusF.fehler k : AusF V l Γ) := by
  simp only [blockF, h, AusF.folge_fehler]

/-- An `ok` head hands world and scope to the rest -- the `execBlock` step. -/
theorem blockF_cons_ok (s : World D → Env D Γ → AusF V l Γ)
    (ss : List (World D → Env D Γ → AusF V l Γ)) (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : s σ ρ = (AusF.weiter (.ok σ' ρ') : AusF V l Γ)) :
    blockF (s :: ss) σ ρ = blockF ss σ' ρ' := by
  simp only [blockF, h, AusF.folge_ok]

/-- Any other head unfolds to its `folge` -- in particular every non-`ok` exit
    stops the block, as `execBlock`'s `| o => o` arm. -/
theorem blockF_cons_weiter (s : World D → Env D Γ → AusF V l Γ)
    (ss : List (World D → Env D Γ → AusF V l Γ)) (σ : World D) (ρ : Env D Γ)
    (o : Ausgang V l Γ) (h : s σ ρ = (AusF.weiter o : AusF V l Γ)) :
    blockF (s :: ss) σ ρ = (AusF.weiter o).folge (fun σ' ρ' => blockF ss σ' ρ') := by
  simp only [blockF, h]

/-- A faulted head is named -- the sequencing-to-safety link for blocks. -/
theorem blockF_cons_fehler_benannt (s : World D → Env D Γ → AusF V l Γ)
    (ss : List (World D → Env D Γ → AusF V l Γ)) (σ : World D) (ρ : Env D Γ)
    (k : Fehlerklasse) (h : s σ ρ = (AusF.fehler k : AusF V l Γ)) :
    IstBenannt (blockF (s :: ss) σ ρ) := by
  rw [blockF_cons_fehler s ss σ ρ k h]
  trivial

/-- The `traverseLauf` shape with a fault arm: the step answers in `AusF`, so a
    faulted element faults the run; every `Ausgang` arm continues exactly as
    `traverseLauf` does (`ok`/`next` recurse, `leave` checks the invariant,
    everything else stops). -/
def traverseAusF (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) :
    List (Wert D τ) → World D → Env D Γ → AusF V l Γ
  | [], σ, ρ =>
      if (inv σ ρ).2 = true then .weiter (.ok (inv σ ρ).1 ρ)
      else .weiter (.logik .schleife)
  | k :: ks, σ, ρ =>
      if (inv σ ρ).2 = false then .weiter (.logik .schleife)
      else match schrittF (inv σ ρ).1 (.cons k ρ) with
        | .fehler e => .fehler e
        | .weiter (.ok σ' ρ') => traverseAusF schrittF inv ks σ' ρ'.tail
        | .weiter (.next _ σ' ρ') => traverseAusF schrittF inv ks σ' ρ'.tail
        | .weiter (.leave _ σ' ρ') =>
            if (inv σ' ρ'.tail).2 = true then .weiter (.ok (inv σ' ρ'.tail).1 ρ'.tail)
            else .weiter (.logik .schleife)
        | .weiter (.zurueck σ' v) => .weiter (.zurueck σ' v)
        | .weiter (.grund σ' r) => .weiter (.grund σ' r)
        | .weiter (.logik e) => .weiter (.logik e)
        | .weiter (.hardware e) => .weiter (.hardware e)

/-- A faulted element faults the run -- at a held invariant boundary. -/
theorem traverseAusF_kopf_fehler
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (k : Wert D τ) (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ)
    (e : Fehlerklasse)
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 (.cons k ρ) = (AusF.fehler e : AusF V true (τ :: Γ))) :
    traverseAusF schrittF inv (k :: ks) σ ρ = (AusF.fehler e : AusF V l Γ) := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [traverseAusF, if_neg hneg, h]

/-- An `ok` element hands world and scope to the rest of the run. -/
theorem traverseAusF_kopf_ok
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (k : Wert D τ) (ks : List (Wert D τ)) (σ σ' : World D) (ρ : Env D Γ)
    (ρ' : Env D (τ :: Γ))
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 (.cons k ρ) =
      (AusF.weiter (.ok σ' ρ') : AusF V true (τ :: Γ))) :
    (traverseAusF schrittF inv (k :: ks) σ ρ : AusF V l Γ) =
      traverseAusF schrittF inv ks σ' ρ'.tail := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [traverseAusF, if_neg hneg, h]

/-- A `next` element ends its pass and hands world and scope to the rest. -/
theorem traverseAusF_kopf_next
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (k : Wert D τ) (ks : List (Wert D τ)) (σ σ' : World D) (ρ : Env D Γ)
    (ρ' : Env D (τ :: Γ))
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 (.cons k ρ) =
      (AusF.weiter (.next rfl σ' ρ') : AusF V true (τ :: Γ))) :
    (traverseAusF schrittF inv (k :: ks) σ ρ : AusF V l Γ) =
      traverseAusF schrittF inv ks σ' ρ'.tail := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [traverseAusF, if_neg hneg, h]

/-- A faulted rest faults the run -- past a fault-free head. -/
theorem traverseAusF_ok_rest_fehler
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (k : Wert D τ) (ks : List (Wert D τ)) (σ σ' : World D) (ρ : Env D Γ)
    (ρ' : Env D (τ :: Γ)) (e : Fehlerklasse)
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 (.cons k ρ) =
      (AusF.weiter (.ok σ' ρ') : AusF V true (τ :: Γ)))
    (hr : traverseAusF schrittF inv ks σ' ρ'.tail = (AusF.fehler e : AusF V l Γ)) :
    traverseAusF schrittF inv (k :: ks) σ ρ = (AusF.fehler e : AusF V l Γ) := by
  rw [traverseAusF_kopf_ok schrittF inv k ks σ σ' ρ ρ' hinv h, hr]

/-- Agreement end to end: a fault-free pass IS the `traverseLauf` pass -- the
    `traverseLauf` skeleton with the fault arm never taken (control, carried by
    `weiter`, not by the fault channel). -/
theorem traverseAusF_stimmt
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (schrittF : World D → Env D (τ :: Γ) → AusF V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (xs : List (Wert D τ)) (σ : World D) (ρ : Env D Γ)
    (h : ∀ σ ρ, ∃ o, schrittF σ ρ = AusF.weiter o ∧ schritt σ ρ = o) :
    (traverseAusF schrittF inv xs σ ρ : AusF V l Γ) =
      AusF.vonAusgang (traverseLauf schritt inv xs σ ρ) := by
  induction xs generalizing σ ρ with
  | nil =>
      by_cases hg : (inv σ ρ).2 = true
      · simp only [traverseAusF, traverseLauf, AusF.vonAusgang, if_pos hg]
      · simp only [traverseAusF, traverseLauf, AusF.vonAusgang, if_neg hg]
  | cons k ks ih =>
      by_cases hg : (inv σ ρ).2 = false
      · simp only [traverseAusF, traverseLauf, AusF.vonAusgang, if_pos hg]
      · obtain ⟨o, ho1, ho2⟩ := h (inv σ ρ).1 (.cons k ρ)
        simp only [traverseAusF, traverseLauf, AusF.vonAusgang, if_neg hg, ho1, ho2]
        cases o with
        | ok σ' ρ' => exact ih _ _
        | zurueck σ' v => rfl
        | grund σ' r => rfl
        | leave h' σ' ρ' =>
            by_cases hi : (inv σ' ρ'.tail).2 = true
            · simp only [if_pos hi]
            · simp only [if_neg hi]
        | next h' σ' ρ' => exact ih _ _
        | logik e => rfl
        | hardware e => rfl

/-- The `foreverLauf` shape with a fault arm: fuel bounds the run, a faulted
    pass faults it; every `Ausgang` arm continues exactly as `foreverLauf`
    does (`ok`/`next` recurse, `leave` answers `ok`, everything else stops). -/
def foreverAusF (a : D.Annahme) (schrittF : World D → Env D Γ → AusF V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    Nat → World D → Env D Γ → AusF V l Γ
  | 0, _, _ => .weiter (.hardware (.fortschritt a))
  | n + 1, σ, ρ =>
      if (inv σ ρ).2 = false then .weiter (.logik .schleife)
      else match schrittF (inv σ ρ).1 ρ with
        | .fehler e => .fehler e
        | .weiter (.ok σ' ρ') => foreverAusF a schrittF inv n σ' ρ'
        | .weiter (.next _ σ' ρ') => foreverAusF a schrittF inv n σ' ρ'
        | .weiter (.leave _ σ' ρ') => .weiter (.ok σ' ρ')
        | .weiter (.zurueck σ' v) => .weiter (.zurueck σ' v)
        | .weiter (.grund σ' r) => .weiter (.grund σ' r)
        | .weiter (.logik e) => .weiter (.logik e)
        | .weiter (.hardware e) => .weiter (.hardware e)

/-- A faulted pass faults the fuel-bounded run -- in every pass. -/
theorem foreverAusF_kopf_fehler (a : D.Annahme)
    (schrittF : World D → Env D Γ → AusF V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (n : Nat) (σ : World D) (ρ : Env D Γ) (e : Fehlerklasse)
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 ρ = (AusF.fehler e : AusF V true Γ)) :
    foreverAusF a schrittF inv (n + 1) σ ρ = (AusF.fehler e : AusF V l Γ) := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [foreverAusF, if_neg hneg, h]

/-- A fault-free `ok` pass hands world and scope to the remaining fuel. -/
theorem foreverAusF_kopf_ok (a : D.Annahme)
    (schrittF : World D → Env D Γ → AusF V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (n : Nat) (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hinv : (inv σ ρ).2 = true)
    (h : schrittF (inv σ ρ).1 ρ = (AusF.weiter (.ok σ' ρ') : AusF V true Γ)) :
    (foreverAusF a schrittF inv (n + 1) σ ρ : AusF V l Γ) =
      foreverAusF a schrittF inv n σ' ρ' := by
  have hneg : (inv σ ρ).2 ≠ false := by simp [hinv]
  simp only [foreverAusF, if_neg hneg, h]

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
#print axioms Gabbro.Grammatik.AusF.vonAusgang
#print axioms Gabbro.Grammatik.AusF.zuAusgang
#print axioms Gabbro.Grammatik.AusF.zuAusgang_vonAusgang
#print axioms Gabbro.Grammatik.AusF.zuAusgang_fehler
#print axioms Gabbro.Grammatik.AusF.folge_weiter
#print axioms Gabbro.Grammatik.AusF.folge_zurueck
#print axioms Gabbro.Grammatik.AusF.folge_grund
#print axioms Gabbro.Grammatik.AusF.folge_leave
#print axioms Gabbro.Grammatik.AusF.folge_next
#print axioms Gabbro.Grammatik.IstStecken
#print axioms Gabbro.Grammatik.stecken_heisst_benannt
#print axioms Gabbro.Grammatik.benannt_heisst_stecken
#print axioms Gabbro.Grammatik.stecken_klassifikation
#print axioms Gabbro.Grammatik.evalArgsMit_stimmt
#print axioms Gabbro.Grammatik.evalArgsF_stimmt
#print axioms Gabbro.Grammatik.schrittRein
#print axioms Gabbro.Grammatik.schrittFolge_rein
#print axioms Gabbro.Grammatik.durchlaufRein
#print axioms Gabbro.Grammatik.durchlaufF_rein
#print axioms Gabbro.Grammatik.schleifeF_als_folge
#print axioms Gabbro.Grammatik.endZustandF_zurueck
#print axioms Gabbro.Grammatik.endZustandF_grund
#print axioms Gabbro.Grammatik.endZustandF_leave
#print axioms Gabbro.Grammatik.endZustandF_next
#print axioms Gabbro.Grammatik.blockF
#print axioms Gabbro.Grammatik.blockF_nil
#print axioms Gabbro.Grammatik.blockF_cons_fehler
#print axioms Gabbro.Grammatik.blockF_cons_ok
#print axioms Gabbro.Grammatik.blockF_cons_weiter
#print axioms Gabbro.Grammatik.blockF_cons_fehler_benannt
#print axioms Gabbro.Grammatik.traverseAusF
#print axioms Gabbro.Grammatik.traverseAusF_kopf_fehler
#print axioms Gabbro.Grammatik.traverseAusF_kopf_ok
#print axioms Gabbro.Grammatik.traverseAusF_kopf_next
#print axioms Gabbro.Grammatik.traverseAusF_ok_rest_fehler
#print axioms Gabbro.Grammatik.traverseAusF_stimmt
#print axioms Gabbro.Grammatik.foreverAusF
#print axioms Gabbro.Grammatik.foreverAusF_kopf_fehler
#print axioms Gabbro.Grammatik.foreverAusF_kopf_ok

end Gabbro.Grammatik
