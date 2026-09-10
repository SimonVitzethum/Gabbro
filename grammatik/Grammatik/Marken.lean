/-
  Datei:      Grammatik/Marken.lean
  Gegenstand: **Die linearen Marken als Konstruktion** -- der Schrittstand, der W4
              (`Wettlauf.lean`) aus einer Praemisse in eine Form macht.

  ## Das Modell

  Eine Marke ist entweder frei oder in genau einem Faden auf genau einer Stufe: der
  Stand ist eine FUNKTION (`Stand`), kein Behaelter. Was ein Faden HAELT, faedelt der
  Schritt explizit durch (`MarkenSchritt`, `Verlauf`): erzeugen nur aus dem Leeren,
  fuehren nur in der Hand desselben Fadens auf die naechste Stufe, verbrauchen nur
  aus der Hand ins Leere. Einen vierten Konstruktor gibt es nicht -- kein Schmieden,
  keine Verdopplung, keine Uebergabe an einen anderen Faden. Dass die Konstruktoren
  eng sind, IST die Disziplin; was hier als `def` mit `Prop` steht, benennt die
  Invarianten, ohne sie zu beweisen.

  QUELLSAETZE (nur gelesen, nichts ausserhalb dieser Datei ist angeruehrt)
    dokumente/SYNTAX.md:256  -- `typedecl … "linear" … [ markorder ]`
    dokumente/SYNTAX.md:259  -- `order` sagt, welche Schritte auf dem Wert zulaessig sind
    dokumente/SYNTAX.md:321  -- `linear type Parked;`, `linear ghost type BootPhase order { … }`
    dokumente/SYNTAX.md:555  -- `advances a -> b`: die Marke steht auf `a`, der Rumpf
                                laesst sie auf `b = a + 1`
    dokumente/SYNTAX.md:558  -- `retires m from s …`: die Marke verlaesst Λ
    dokumente/SYNTAX.md:590  -- "linear, not affine": `return` verlangt Mengengleichheit
    dokumente/SYNTAX.md:729  -- `Λ nach advances = Λ − marke(m, a) + marke(m, b)`
    dokumente/SYNTAX.md:730  -- `Λ nach retires = Λ − marke(m, s)`
    Syntax.lean:207           -- `Res.marke (m : D.Marke) (stufe : Nat)`
    Syntax.lean:149           -- `eigner_nie_erzeugt`: Eignermarken erzeugt keine Signatur
    Syntax.lean:461           -- `Stmt.advances`: `h : Res.marke m a ∈ Λ`, `hs : a + 1 < D.stufen m`
    Syntax.lean:464           -- `Stmt.retires`: `h : Res.marke m s ∈ Λ`
    Wettlauf.lean:18          -- (W4): eine Marke ist in EINEM Faden
    Wettlauf.lean:188         -- `marke_eindeutig`, WORTLAUT siehe unten bei `Einfaedig`

  WAS HIER STEHT
    `Stand`          -- das Eigentum als Schrittzustand: jede Marke frei oder in
                        (Faden, Stufe)
    `belebe/loesche`-- die zwei Zustandswechsel, als Definitionen
    `MarkenSchritt`  -- erzeugen/fuehren/verbrauchen, jeder mit seiner Praemisse;
                        Eignermarken sind von der Erzeugung ausgenommen
    `Verlauf`        -- die Laeufe ueber dem Stand, von `Anfang` an
    `Besitzt`, `StufenTreu`, `StandEinfaedig`
                     -- die Strukturinvarianten als `def`s mit `Prop`
    `Einfaedig`      -- die Einzelfaedrigkeit JEDER Marke als `def` mit `Prop`, im
                        WORTLAUT von `marke_eindeutig`: was `Gesittet` liefert,
                        nimmt diese Definition ohne Uebersetzung

  Spiegel (diese Datei steht allein -- der Zweig verbietet den Eingriff in den
  `Grammatik.lean`-Index, also kann sie noch nicht eingebunden werden; die Namen
  sind fuer das spaetere Verdrahten gewaehlt):

  | hier                  | dort (`Syntax` / `Wettlauf`)                  |
  |-----------------------|-----------------------------------------------|
  | `Marke := Nat`        | `D.Marke`                                     |
  | `Faden := Nat`        | `Wettlauf.Faden`                              |
  | `MarkDekl.stufen`     | `D.stufen`                                    |
  | `MarkDekl.istEigner`  | `∃ t, m ∈ D.eigner t` (gefaltet)              |
  | `Res.marke`           | `Res.marke` (`Syntax.lean:207`)               |
  | `Stand`               | das Λ-seitige Eigentum je Faden               |
  | `MarkenSchritt`       | Ruf-Erzeugung / `Stmt.advances` / `Stmt.retires` |
  | `Verlauf`             | der Markenlauf ueber dem Stand                |
  | `Einfaedig`           | (W4) `Gesittet.marke_eindeutig`               |

  SCHNITTE (gebucht, nicht versteckt):
  C1. Keine Saetze: dass erreichbare Staende `StufenTreu` und `StandEinfaedig`
      erfuellen, waere eine Induktion ueber `Verlauf` -- also ein `theorem`, und
      der steht hier nicht. Die Definitionen nennen die Form, die er haette.
  C2. Keine Verdrahtung: `Einfaedig` hat GENAU die Gestalt des W4-Feldes, aber die
      Projektion (`Gesittet.marke_eindeutig` liefert `Einfaedig`) steht nirgends --
      sie braucht den Indexeintrag, den dieser Zweig nicht anfassen darf.
  C3. Kein Uebergabekonstruktor: dass keine Anweisung eine Marke an einen anderen
      Faden weiterreicht (W4), steht hier als Abwesenheit -- `fuehre` und
      `verbrauche` binden den Schritt an den besitzenden Faden, und einen
      Konstruktor mit zwei verschiedenen Faeden gibt es nicht.
  C4. Eignermarken entstehen nie (`erzeuge` verlangt `¬ istEigner`, nach
      `eigner_nie_erzeugt`); woher das ANFAENGLICHE Eigentum kommt (Signaturkopf),
      sagt `Signatur.anfang`, nicht diese Datei.

  Nur Kern-Lean, kein `mathlib`, kein Import -- auch nicht der Geschwisterdateien
  (siehe Spiegel oben). Kein `sorry`.
-/

namespace Gabbro.Grammatik.Marken

/-! ## 1. Die Marken und ihre Erklaerung -/

/-- Die Marken, als Kennungen. Spiegelt `D.Marke`. -/
abbrev Marke := Nat

/-- Die Faeden, als Kennungen. Spiegelt `Wettlauf.Faden`. -/
abbrev Faden := Nat

/-- Die Markenerklaerung einer Einheit: wie viele Stufen jede Marke kennt (`order`),
    und welche Marken Eigner sind (`owner`, `D.eigner t` gefaltet: `istEigner m`
    heisst, IRGENDEIN Traeger nennt `m` als Eigner). -/
structure MarkDekl where
  /-- `order { … }`: die Stufenzahl je Marke (`D.stufen`). -/
  stufen : Marke → Nat
  /-- `owner`: die Eignermarken (`∃ t, m ∈ D.eigner t`). -/
  istEigner : Marke → Prop

/-! ## 2. Der Stand -- das Eigentum als Schrittzustand -/

/-- Der Markenstand: jede Marke ist frei (`none`) oder in genau einem Faden auf
    genau einer Stufe. Dass es eine FUNKTION ist, ist die halbe Einzelfaedrigkeit:
    eine Marke an zwei Faeden ist nicht falsch -- sie ist nicht schreibbar. -/
def Stand : Type := Marke → Option (Faden × Nat)

/-- Der leere Stand: keine Marke in irgendeiner Hand (`Signatur.anfang` davor). -/
def Anfang : Stand := fun _ => none

/-- Beleben: `m` kommt in die Hand von `f` auf Stufe `s`. -/
def belebe (σ : Stand) (m : Marke) (f : Faden) (s : Nat) : Stand :=
  fun m' => if m' = m then some (f, s) else σ m'

/-- Loeschen: `m` wird frei. -/
def loesche (σ : Stand) (m : Marke) : Stand :=
  fun m' => if m' = m then none else σ m'

/-! ## 3. Die Schritte -- erzeugen, fuehren, verbrauchen; kein Schmieden -/

/-- EIN Markenschritt von `σ` nach `σ'`, mit dem Faden im Schritt. Die drei
    Konstruktoren sind die ganze Disziplin:
    - `erzeuge`: nur aus dem Leeren, nur unter der Stufenzahl, nie eine Eignermarke
      (W4: "Eigentumsmarken erzeugt niemand", `eigner_nie_erzeugt`);
    - `fuehre`: nur in der Hand DESSELBEN Fadens, nur auf die naechste Stufe unter
      der Stufenzahl (`Stmt.advances`: `h`, `hs`);
    - `verbrauche`: nur aus der Hand ins Leere (`Stmt.retires`: `h`).
    Was fehlt, fehlt mit Absicht (Schnitt C3): kein Konstruktor schmiedet aus dem
    Nichts ueber einer besetzten Marke, keiner verdoppelt, keiner reicht weiter. -/
inductive MarkenSchritt (κ : MarkDekl) : Stand → Stand → Type where
  | erzeuge (m : Marke) (f : Faden) (s : Nat) {σ : Stand}
      (hfrei : σ m = none) (hstufe : s < κ.stufen m)
      (hfremd : ¬ κ.istEigner m) :
      MarkenSchritt κ σ (belebe σ m f s)
  | fuehre (m : Marke) (f : Faden) (a : Nat) {σ : Stand}
      (hbesitz : σ m = some (f, a)) (hstufe : a + 1 < κ.stufen m) :
      MarkenSchritt κ σ (belebe σ m f (a + 1))
  | verbrauche (m : Marke) (f : Faden) (s : Nat) {σ : Stand}
      (hbesitz : σ m = some (f, s)) :
      MarkenSchritt κ σ (loesche σ m)

/-- Der Faden des Schritts: der Zustand faedelt durch DEN Schritt, der ihn nennt. -/
def MarkenSchritt.faden {κ : MarkDekl} {σ σ' : Stand} (h : MarkenSchritt κ σ σ') :
    Faden :=
  match h with
  | .erzeuge _ f _ _ _ _ => f
  | .fuehre _ f _ _ _ => f
  | .verbrauche _ f _ _ => f

/-- Ein Verlauf: von `Anfang` an, Schritt an Schritt. -/
inductive Verlauf (κ : MarkDekl) : Stand → Type where
  | anfang : Verlauf κ Anfang
  | weiter {σ σ' : Stand} (v : Verlauf κ σ) (h : MarkenSchritt κ σ σ') :
      Verlauf κ σ'

/-! ## 4. Die Strukturinvarianten, als Definitionen -/

/-- `f` besitzt `m` (auf irgendeiner Stufe). -/
def Besitzt (σ : Stand) (f : Faden) (m : Marke) : Prop :=
  ∃ s, σ m = some (f, s)

/-- Stufentreue: eine besessene Marke steht unter ihrer Stufenzahl. -/
def StufenTreu (κ : MarkDekl) (σ : Stand) : Prop :=
  ∀ m f s, σ m = some (f, s) → s < κ.stufen m

/-- Einzelfaedrigkeit des Standes: zwei Faeden, die dieselbe Marke besitzen, sind
    derselbe Faden. Ueber einer Funktion ist das die Gestalt, keine Leistung --
    die Leistung steht in `Einfaedig` unten, am Lauf. -/
def StandEinfaedig (σ : Stand) : Prop :=
  ∀ m f g, Besitzt σ f m → Besitzt σ g m → f = g

/-! ## 5. Die Einzelfaedrigkeit am Lauf -- die Form, die W4 nimmt -/

/-- Die Ereignisse des Laufs, auf das Markentragende gekuerzt: jedes Ereignis nennt
    sein statisches Λ (`Ereignis.lambda`), und darin stehen die Marken
    (`Res.marke`). Spiegelt `Ereignis` / `Ereignis.lambda` / `Res`. -/
inductive Res where
  | held
  | marke (m : Marke) (stufe : Nat)
  deriving DecidableEq

structure Ereignis where
  lambda : List Res

structure Schritt where
  faden : Faden
  ereignis : Ereignis

abbrev Lauf := List Schritt

/-- **Eine Marke ist in einem Faden.** WORTLAUT von (W4)
    (`Wettlauf.lean:188-190`, nur gelesen):

        marke_eindeutig : ∀ (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat)
          (ei ej : Ereignis D),
          l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
          Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g

    Dieselben Binder, dieselben Vorderglieder -- nur stehen hier die Spiegel, wo
    dort `Lauf D`, `Schritt D`, `Ereignis D`, `D.Marke`, `Res D` und
    `Ereignis.lambda` stehen. Darum nimmt diese Definition, was `Gesittet`
    liefert, ohne Uebersetzung (Schnitt C2: die Projektion selbst braucht den
    Indexeintrag und steht hier nicht). Dass BEIDE Stufen `s s'` vorkommen, ist
    kein Versehen: `fuehre` wechselt die Stufe bei gleichem Faden, also muss die
    Form markengleich, nicht stufengleich lesen. -/
def Einfaedig (l : Lauf) : Prop :=
  ∀ (i j : Nat) (f g : Faden) (m : Marke) (s s' : Nat) (ei ej : Ereignis),
    l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
    Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g

end Gabbro.Grammatik.Marken
