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
import Grammatik.Kern.Semantik.Semantik

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
  | val (v : Wert D τ)
  | fehler (k : Fehlerklasse)

/-- Die parallele Auswertung: `State -> Expr -> Wert plus Fehlerklasse` als Gestalt.
    Heute immer `wert`, per P1 durch `eval` hindurch -- der Fehlerarm wartet auf den
    Anschluss (Schnitt S2), nicht auf einen zweiten Auswerter. -/
def evalF (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) : ErgebnisF D τ :=
  .val (eval σ₀ e σ ρ)

/-- Kein Fehler: das Ergebnis traegt einen Wert. Die Voraussetzung der
    Uebereinstimmung, als `Prop`-Definition, nicht als Satz. -/
def evalF_ok : ErgebnisF D τ → Prop
  | .val _ => True
  | .fehler _ => False

/-- Die Uebereinstimmungsform: faellt kein Fehler, stimmt `eval` zu -- bewiesen in
    `evalF_stimmt_halt` fuer den heutigen Auswerter, der nie fehlt. -/
def evalF_stimmt (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) (v : Wert D τ) : Prop :=
  evalF σ₀ σ ρ e = .val v → eval σ₀ e σ ρ = v

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
  | .val v, f => f v
  | .fehler k, _ => .fehler k

/-- Dieselbe Form ohne Fortsetzung: ein Wert wird abgebildet, ein Fehler bleibt. -/
def ErgebnisF.map {τ' : Ty} (f : Wert D τ → Wert D τ') : ErgebnisF D τ → ErgebnisF D τ'
  | .val v => .val (f v)
  | .fehler k => .fehler k

/-- Ein fehlerhafter Eingang fehlert die Bindung -- die Fortsetzung laeuft nicht. -/
theorem ErgebnisF.bind_fehler {τ' : Ty} (k : Fehlerklasse)
    (f : Wert D τ → ErgebnisF D τ') :
    (.fehler k : ErgebnisF D τ).bind f = .fehler k :=
  rfl

/-- Ein Wert laeuft in die Fortsetzung. -/
theorem ErgebnisF.bind_wert {τ' : Ty} (v : Wert D τ)
    (f : Wert D τ → ErgebnisF D τ') :
    (.val v : ErgebnisF D τ).bind f = f v :=
  rfl

/-- Ein fehlerhafter Eingang fehlert die Abbildung. -/
theorem ErgebnisF.map_fehler {τ' : Ty} (f : Wert D τ → Wert D τ') (k : Fehlerklasse) :
    (.fehler k : ErgebnisF D τ).map f = .fehler k :=
  rfl

/-- Ein Wert wird abgebildet. -/
theorem ErgebnisF.map_wert {τ' : Ty} (f : Wert D τ → Wert D τ') (v : Wert D τ) :
    (.val v : ErgebnisF D τ).map f = .val (f v) :=
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
      | .val v, .inl vs => .inl (.cons v vs)
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
    (hv : aus e = .val v) (hr : evalArgsMit aus rest = .inr k) :
    evalArgsMit aus (.cons e rest) = .inr k := by
  simp only [evalArgsMit, hv, hr]

/-- Fehlt kein Einzelauswerter, fehlt die Liste nicht. -/
theorem evalArgsMit_ok {τs : List Ty}
    (aus : ∀ {t}, Expr D Γ Λ t → ErgebnisF D t)
    (as : Args D Γ Λ τs)
    (h : ∀ {t} (e : Expr D Γ Λ t), ∃ v, aus e = .val v) :
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
  | widen (a : Ausgang V l Γ)
  | fehler (k : Fehlerklasse)

variable {V : Vertrag D} {l : Bool}

/-- Die Folge: ein Fehler laeuft nicht weiter; `ok` uebergibt Welt und Sichtbereich;
    jeder andere Ausgang bleibt stehen. -/
def AusF.folge : AusF V l Γ → (World D → Env D Γ → AusF V l Γ) → AusF V l Γ
  | .fehler k, _ => .fehler k
  | .widen (.ok σ ρ), nach => nach σ ρ
  | .widen o, _ => .widen o

/-- Ein Fehler laeuft nicht weiter -- die Fortsetzung wird nicht aufgerufen. -/
theorem AusF.folge_fehler (k : Fehlerklasse)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.fehler k : AusF V l Γ).folge nach = .fehler k :=
  rfl

/-- `ok` uebergibt Welt und Sichtbereich an die Fortsetzung. -/
theorem AusF.folge_ok (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.ok σ ρ) : AusF V l Γ).folge nach = nach σ ρ :=
  rfl

/-- Die Logik des Schreibers bleibt stehen. -/
theorem AusF.folge_logik (e : Logik D)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.logik e) : AusF V l Γ).folge nach = .widen (.logik e) :=
  rfl

/-- Eine widerlegte Maschinenannahme bleibt stehen. -/
theorem AusF.folge_hardware (e : Hardware D)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.hardware e) : AusF V l Γ).folge nach = .widen (.hardware e) :=
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
  | .widen (.ok σ _) => some σ
  | .widen (.zurueck σ _) => some σ
  | .widen (.why σ _) => some σ
  | .widen (.leave _ σ _) => some σ
  | .widen (.next _ σ _) => some σ
  | .widen (.logik _) => none
  | .widen (.hardware _) => none
  | .fehler _ => none

/-- Ein benannter Fehler hat keinen Nachzustand. -/
theorem endZustandF_fehler (k : Fehlerklasse) :
    endZustandF (AusF.fehler k : AusF V l Γ) = none :=
  rfl

/-- Die widerlegte Schreiberlogik hat keinen Nachzustand. -/
theorem endZustandF_logik (e : Logik D) :
    endZustandF (AusF.widen (.logik e) : AusF V l Γ) = none :=
  rfl

/-- Die widerlegte Maschinenannahme hat keinen Nachzustand. -/
theorem endZustandF_hardware (e : Hardware D) :
    endZustandF (AusF.widen (.hardware e) : AusF V l Γ) = none :=
  rfl

/-- `ok` traegt seine Welt weiter. -/
theorem endZustandF_ok (σ : World D) (ρ : Env D Γ) :
    endZustandF (AusF.widen (.ok σ ρ) : AusF V l Γ) = some σ :=
  rfl

/-! ## 7. Die Sicherheitsform: gestoert heisst eigene Logik oder benannter Fehler -/

/-- Benannt: ein Fehler aus der Aufzaehlung, oder einer der zwei Ausgaenge, die
    `Semantik.lean` kennt -- die Logik des Schreibers, die Annahme ueber die Maschine. -/
def IstBenannt : AusF V l Γ → Prop
  | .fehler _ => True
  | .widen (.logik _) => True
  | .widen (.hardware _) => True
  | .widen _ => False

/-- Ein benannter Fehler ist benannt. -/
theorem fehler_ist_benannt (k : Fehlerklasse) :
    IstBenannt (AusF.fehler k : AusF V l Γ) :=
  trivial

/-- Die widerlegte Schreiberlogik ist benannt. -/
theorem logik_ist_benannt (e : Logik D) :
    IstBenannt (AusF.widen (.logik e) : AusF V l Γ) :=
  trivial

/-- Die widerlegte Maschinenannahme ist benannt. -/
theorem hardware_ist_benannt (e : Hardware D) :
    IstBenannt (AusF.widen (.hardware e) : AusF V l Γ) :=
  trivial

/-- Die Folge erhaelt das Benannte: war der erste Ausgang benannt, ist es auch die
    Folge -- ein Fehler wird nicht still zu einem Wert. -/
theorem folge_benannt_bleibt (a : AusF V l Γ)
    (nach : World D → Env D Γ → AusF V l Γ) (h : IstBenannt a) :
    IstBenannt (a.folge nach) := by
  cases a with
  | fehler k => trivial
  | widen o =>
      cases o with
      | ok σ ρ => exact False.elim h
      | zurueck σ v => exact False.elim h
      | why σ r => exact False.elim h
      | leave h' σ ρ => exact False.elim h
      | next h' σ ρ => exact False.elim h
      | logik e => trivial
      | hardware e => trivial

/-- Jeder Ausgang ist entweder weitergetragen oder benannt fehlert -- die Form, in
    der `stuck`-oder-Fehler die eigene Logik oder den benannten Fehler stuende. -/
theorem ausF_klassifikation (a : AusF V l Γ) :
    (∃ o, a = .widen o) ∨ (∃ k, a = .fehler k) := by
  cases a with
  | widen o => exact .inl ⟨o, rfl⟩
  | fehler k => exact .inr ⟨k, rfl⟩

/-! ## 8. The embedding into execution: `AusF` carries `Ausgang` -/

/-- The embedding: every `Ausgang` of `Semantik.lean` runs on as `weiter` --
    the hook, not a third exit: `Ausgang` gains no constructor. -/
def AusF.vonAusgang : Ausgang V l Γ → AusF V l Γ
  | o => .widen o

/-- Back: `weiter` projects, a named fault has no `Ausgang` -- as `finalState`
    maps `fehler` (and `stuck`) to `none` (S3 design A, §6). -/
def AusF.zuAusgang : AusF V l Γ → Option (Ausgang V l Γ)
  | .widen o => some o
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
    (AusF.widen o).folge nach =
      match o with
      | .ok σ ρ => nach σ ρ
      | .zurueck σ v => .widen (.zurueck σ v)
      | .why σ r => .widen (.why σ r)
      | .leave h σ ρ => .widen (.leave h σ ρ)
      | .next h σ ρ => .widen (.next h σ ρ)
      | .logik e => .widen (.logik e)
      | .hardware e => .widen (.hardware e) := by
  cases o <;> rfl

/-- A returned answer does not continue. -/
theorem AusF.folge_zurueck (σ : World D) (v : ErgVal D V.erg)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.zurueck σ v) : AusF V l Γ).folge nach =
      .widen (.zurueck σ v) :=
  rfl

/-- A raised ground does not continue. -/
theorem AusF.folge_grund (σ : World D) (r : Fin V.gruende)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.why σ r) : AusF V l Γ).folge nach =
      .widen (.why σ r) :=
  rfl

/-- A consumed `leave` does not continue. -/
theorem AusF.folge_leave (h : l = true) (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.leave h σ ρ) : AusF V l Γ).folge nach =
      .widen (.leave h σ ρ) :=
  rfl

/-- A consumed `next` does not continue. -/
theorem AusF.folge_next (h : l = true) (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.next h σ ρ) : AusF V l Γ).folge nach =
      .widen (.next h σ ρ) :=
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
  | widen o =>
      cases o with
      | ok σ ρ => exact absurd h (by simp [IstStecken, endZustandF])
      | zurueck σ v => exact absurd h (by simp [IstStecken, endZustandF])
      | why σ r => exact absurd h (by simp [IstStecken, endZustandF])
      | leave h' σ ρ => exact absurd h (by simp [IstStecken, endZustandF])
      | next h' σ ρ => exact absurd h (by simp [IstStecken, endZustandF])
      | logik e => trivial
      | hardware e => trivial

/-- Named implies stuck: the converse -- together they say stuck MEANS named. -/
theorem benannt_heisst_stecken (a : AusF V l Γ) (h : IstBenannt a) :
    IstStecken a := by
  cases a with
  | fehler k => rfl
  | widen o =>
      cases o with
      | ok σ ρ => exact False.elim h
      | zurueck σ v => exact False.elim h
      | why σ r => exact False.elim h
      | leave h' σ ρ => exact False.elim h
      | next h' σ ρ => exact False.elim h
      | logik e => rfl
      | hardware e => rfl


end Gabbro.Grammatik
