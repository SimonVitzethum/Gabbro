module

public import Grammatik.Kern.Semantik.Semantik

@[expose] public section



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
  by rfl

/-- A named fault datum reaches its own fault -- by definition
    (`fehlerFallErgebnis`). -/
theorem fehlerFallErgebnis_fehler (f : FehlerFall) :
    (fehlerFallErgebnis f : ErgebnisF D τ) = .fehler f.klasse :=
  by rfl

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
  by rfl

/-- Ein Wert laeuft in die Fortsetzung. -/
theorem ErgebnisF.bind_wert {τ' : Ty} (v : Wert D τ)
    (f : Wert D τ → ErgebnisF D τ') :
    (.val v : ErgebnisF D τ).bind f = f v :=
  by rfl

/-- Ein fehlerhafter Eingang fehlert die Abbildung. -/
theorem ErgebnisF.map_fehler {τ' : Ty} (f : Wert D τ → Wert D τ') (k : Fehlerklasse) :
    (.fehler k : ErgebnisF D τ).map f = .fehler k :=
  by rfl

/-- Ein Wert wird abgebildet. -/
theorem ErgebnisF.map_wert {τ' : Ty} (f : Wert D τ → Wert D τ') (v : Wert D τ) :
    (.val v : ErgebnisF D τ).map f = .val (f v) :=
  by rfl

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
  by rfl

/-- `ok` uebergibt Welt und Sichtbereich an die Fortsetzung. -/
theorem AusF.folge_ok (σ : World D) (ρ : Env D Γ)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.ok σ ρ) : AusF V l Γ).folge nach = nach σ ρ :=
  by rfl

/-- Die Logik des Schreibers bleibt stehen. -/
theorem AusF.folge_logik (e : Logik D)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.logik e) : AusF V l Γ).folge nach = .widen (.logik e) :=
  by rfl

/-- Eine widerlegte Maschinenannahme bleibt stehen. -/
theorem AusF.folge_hardware (e : Hardware D)
    (nach : World D → Env D Γ → AusF V l Γ) :
    (AusF.widen (.hardware e) : AusF V l Γ).folge nach = .widen (.hardware e) :=
  by rfl

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
  by rfl

/-- Die widerlegte Schreiberlogik hat keinen Nachzustand. -/
theorem endZustandF_logik (e : Logik D) :
    endZustandF (AusF.widen (.logik e) : AusF V l Γ) = none :=
  by rfl

/-- Die widerlegte Maschinenannahme hat keinen Nachzustand. -/
theorem endZustandF_hardware (e : Hardware D) :
    endZustandF (AusF.widen (.hardware e) : AusF V l Γ) = none :=
  by rfl

/-- `ok` traegt seine Welt weiter. -/
theorem endZustandF_ok (σ : World D) (ρ : Env D Γ) :
    endZustandF (AusF.widen (.ok σ ρ) : AusF V l Γ) = some σ :=
  by rfl

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
  by rfl

/-- A named fault has no `Ausgang` to project to. -/
theorem AusF.zuAusgang_fehler (k : Fehlerklasse) :
    (AusF.fehler k : AusF V l Γ).zuAusgang = none :=
  by rfl

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
  by rfl

/-- A raised ground does not continue. -/
end Gabbro.Grammatik
