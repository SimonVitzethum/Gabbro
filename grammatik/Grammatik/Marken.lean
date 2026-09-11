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
  C1. Erhaltung BEWIESEN (§6 unten): jeder erreichbare Stand ist stufentreu und
      einfaedrig -- Induktion ueber `Verlauf`, je Schritt Fallunterscheidung.
  C2. Verdrahtung: `Einfaedig` hat GENAU die Gestalt des W4-Feldes; die Projektion
      (`marke_eindeutig_aus_einfaedig`, `gesittet_aus_einfaedig`) steht in
      `Wettlauf.lean` §7 -- sie braucht `Lauf D` und kann darum nicht hier stehen
      (Importrichtung: `Wettlauf` liest `Marken`, nie umgekehrt).
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

/-! ## 6. Die Erhaltung -- was jeder Verlauf traegt (Schnitt C1, bewiesen)

    Jeder Schritt erhaelt beide Invarianten: `erzeuge` stellt die Marke in genau
    EINE Hand (sie war frei), `fuehre` behaelt die Hand bei Stufenwechsel, und
    `verbrauche` nimmt die Hand weg -- was danach zwei Haende zeigt, zeigte sie
    schon vorher. Darum traegt jeder Verlauf von `Anfang` an beide Formen. -/

/-- Beleben stellt die Marke genau dorthin. -/
theorem belebe_bei (σ : Stand) (m : Marke) (f : Faden) (s : Nat) :
    belebe σ m f s m = some (f, s) := by
  unfold belebe
  simp

/-- Beleben ruehrt keine andere Marke an. -/
theorem belebe_anders (σ : Stand) (m m' : Marke) (f : Faden) (s : Nat)
    (h : m' ≠ m) : belebe σ m f s m' = σ m' := by
  unfold belebe
  rw [if_neg h]

/-- Loeschen macht die Marke frei. -/
theorem loesche_bei (σ : Stand) (m : Marke) : loesche σ m m = none := by
  unfold loesche
  simp

/-- Loeschen ruehrt keine andere Marke an. -/
theorem loesche_anders (σ : Stand) (m m' : Marke) (h : m' ≠ m) :
    loesche σ m m' = σ m' := by
  unfold loesche
  rw [if_neg h]

/-- Ein Schritt erhaelt die Stufentreue. -/
theorem schritt_stufentreu (κ : MarkDekl) {σ σ' : Stand}
    (hσ : StufenTreu κ σ) (h : MarkenSchritt κ σ σ') : StufenTreu κ σ' := by
  cases h with
  | erzeuge m f s _ hstufe _ =>
      intro m' f' s' hmem
      by_cases heq : m' = m
      · subst heq
        rw [belebe_bei] at hmem
        simp at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact hstufe
      · rw [belebe_anders _ _ _ _ _ heq] at hmem
        exact hσ m' f' s' hmem
  | fuehre m f a _ hstufe =>
      intro m' f' s' hmem
      by_cases heq : m' = m
      · subst heq
        rw [belebe_bei] at hmem
        simp at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact hstufe
      · rw [belebe_anders _ _ _ _ _ heq] at hmem
        exact hσ m' f' s' hmem
  | verbrauche m f s _ =>
      intro m' f' s' hmem
      by_cases heq : m' = m
      · subst heq
        rw [loesche_bei] at hmem
        simp at hmem
      · rw [loesche_anders _ _ _ heq] at hmem
        exact hσ m' f' s' hmem

/-- Ein Schritt erhaelt die Einzelfaedrigkeit des Standes. -/
theorem schritt_einfaedig (κ : MarkDekl) {σ σ' : Stand}
    (hσ : StandEinfaedig σ) (h : MarkenSchritt κ σ σ') :
    StandEinfaedig σ' := by
  cases h with
  | erzeuge m₀ f₀ s₀ _ _ _ =>
      intro m f g hf hg
      obtain ⟨s₁, h1⟩ := hf
      obtain ⟨s₂, h2⟩ := hg
      by_cases heq : m = m₀
      · subst heq
        rw [belebe_bei] at h1 h2
        have e1 := Option.some_inj.mp h1
        have e2 := Option.some_inj.mp h2
        have f1 : f = f₀ := (congrArg Prod.fst e1).symm
        have g1 : g = f₀ := (congrArg Prod.fst e2).symm
        rw [f1, g1]
      · rw [belebe_anders _ _ _ _ _ heq] at h1 h2
        exact hσ m f g ⟨s₁, h1⟩ ⟨s₂, h2⟩
  | fuehre m₀ f₀ a _ _ =>
      intro m f g hf hg
      obtain ⟨s₁, h1⟩ := hf
      obtain ⟨s₂, h2⟩ := hg
      by_cases heq : m = m₀
      · subst heq
        rw [belebe_bei] at h1 h2
        have e1 := Option.some_inj.mp h1
        have e2 := Option.some_inj.mp h2
        have f1 : f = f₀ := (congrArg Prod.fst e1).symm
        have g1 : g = f₀ := (congrArg Prod.fst e2).symm
        rw [f1, g1]
      · rw [belebe_anders _ _ _ _ _ heq] at h1 h2
        exact hσ m f g ⟨s₁, h1⟩ ⟨s₂, h2⟩
  | verbrauche m₀ f₀ s₀ _ =>
      intro m f g hf hg
      obtain ⟨s₁, h1⟩ := hf
      obtain ⟨s₂, h2⟩ := hg
      by_cases heq : m = m₀
      · subst heq
        rw [loesche_bei] at h1
        simp at h1
      · rw [loesche_anders _ _ _ heq] at h1 h2
        exact hσ m f g ⟨s₁, h1⟩ ⟨s₂, h2⟩

/-- Jeder erreichbare Stand ist stufentreu. -/
theorem verlauf_stufentreu (κ : MarkDekl) {σ : Stand} (v : Verlauf κ σ) :
    StufenTreu κ σ := by
  induction v with
  | anfang =>
      intro m f s h
      simp [Anfang] at h
  | weiter _ h ih =>
      exact schritt_stufentreu κ ih h

/-- Jeder erreichbare Stand ist einfaedrig. -/
theorem verlauf_einfaedig (κ : MarkDekl) {σ : Stand} (v : Verlauf κ σ) :
    StandEinfaedig σ := by
  induction v with
  | anfang =>
      intro m f g hf hg
      obtain ⟨s₁, h1⟩ := hf
      simp [Anfang] at h1
  | weiter _ h ih =>
      exact schritt_einfaedig κ ih h

#print axioms Gabbro.Grammatik.Marken.verlauf_stufentreu
#print axioms Gabbro.Grammatik.Marken.verlauf_einfaedig

/-! ## 7. Die Projektion -- was ohne den Index schliesst (Schnitt C2, Anteil hier)

    Die eigentliche Projektion (`marke_eindeutig_aus_einfaedig`,
    `gesittet_aus_einfaedig`) braucht `Lauf D` und steht darum in
    `Wettlauf.lean` §7 -- sie kann nicht hier stehen (Importrichtung:
    `Wettlauf` liest `Marken`, nie umgekehrt). Was OHNE den Indexeintrag
    schliesst, steht hier: die beiden `Anfang`-Faelle als benannte Saetze,
    die Verbindung beider Invarianten in EINEM Satz, die Eindeutigkeit von
    Faden UND Stufe an einer besessenen Marke, und die W4-Form ueber den
    markenlosen Laeufen -- leer, einzeln, ohne Marken: wo keine Marke
    getragen wird, ist keine zu verwechseln. -/

/-- Der Anfang ist stufentreu: keine Hand, keine verletzte Stufe. -/
theorem anfang_stufentreu (κ : MarkDekl) : StufenTreu κ Anfang := by
  intro m f s h
  simp [Anfang] at h

/-- Der Anfang ist einfaedrig: keine Hand, keine zweite. -/
theorem anfang_einfaedig : StandEinfaedig Anfang := by
  intro m f g hf hg
  obtain ⟨s₁, h1⟩ := hf
  simp [Anfang] at h1

/-- Jeder erreichbare Stand traegt BEIDE Formen in einem Satz. -/
theorem verlauf_treu_und_einfaedig (κ : MarkDekl) {σ : Stand}
    (v : Verlauf κ σ) : StufenTreu κ σ ∧ StandEinfaedig σ :=
  ⟨verlauf_stufentreu κ v, verlauf_einfaedig κ v⟩

/-- Was ein erreichbarer Stand haelt, steht unter der Stufenzahl -- die
    Besitzform der Stufentreue, benannt fuer die spaetere Verdrahtung. -/
theorem verlauf_besitz_stufe (κ : MarkDekl) {σ : Stand} (v : Verlauf κ σ)
    (f : Faden) (m : Marke) (h : Besitzt σ f m) :
    ∃ s, s < κ.stufen m ∧ σ m = some (f, s) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, verlauf_stufentreu κ v m f s hs, hs⟩

/-- Eine besessene Marke nennt Faden UND Stufe eindeutig: zwei Haende an
    derselben Marke sind dieselbe Hand auf derselben Stufe. -/
theorem stand_besitz_eindeutig {σ : Stand} (hσ : StandEinfaedig σ)
    (m : Marke) (f g : Faden) (s t : Nat)
    (h1 : σ m = some (f, s)) (h2 : σ m = some (g, t)) :
    f = g ∧ s = t := by
  have hst : (f, s) = (g, t) := Option.some_inj.mp (h1.symm.trans h2)
  exact ⟨hσ m f g ⟨s, h1⟩ ⟨t, h2⟩, congrArg Prod.snd hst⟩

/-- Der leere Lauf ist einfaedrig: kein Ereignis, keine Marke. -/
theorem einfaedig_leer : Einfaedig [] := by
  intro i j f g m s s' ei ej hi hj _ _
  simp at hi

/-- Der einzelne Schritt ist einfaedrig: beide Treffer meinen denselben. -/
theorem einfaedig_einzel (q : Schritt) : Einfaedig [q] := by
  intro i j f g m s s' ei ej hi hj _ _
  have hlen : ∀ (k : Nat) (x : Schritt), [q][k]? = some x → x = q := by
    intro k x hx
    cases k with
    | zero => exact (by simpa using hx : q = x).symm
    | succ k => simp at hx
  have e1 := hlen i _ hi
  have e2 := hlen j _ hj
  have hf : f = q.faden := congrArg Schritt.faden e1
  have hg : g = q.faden := congrArg Schritt.faden e2
  rw [hf, hg]

/-- Wo keine Marke getragen wird, ist keine zu verwechseln: ein markenloser
    Lauf erfuellt die W4-Form leer. -/
theorem einfaedig_ohne_marken (l : Lauf)
    (h : ∀ (i : Nat) (f : Faden) (ei : Ereignis),
      l[i]? = some (Schritt.mk f ei) → ∀ (m : Marke) (s : Nat),
      Res.marke m s ∉ ei.lambda) :
    Einfaedig l := by
  intro i j f g m s s' ei ej hi hj hmi hmj
  exact absurd hmi (h i f ei hi m s)

/-- Der Zugriff in die gekuerzte Liste trifft dieselbe Stelle in der vollen:
    `take` liest vorne weg, nicht um. -/
theorem nimm_zugriff (l : Lauf) (n i : Nat) (q : Schritt)
    (h : (l.take n)[i]? = some q) : l[i]? = some q := by
  induction l generalizing n i with
  | nil =>
      simp at h
  | cons hd tl ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          cases i with
          | zero =>
              simp at h ⊢
              exact h
          | succ i =>
              simp at h ⊢
              exact ih n i h

/-- Jede beobachtete Vorsilbe eines einfaedrigen Laufs ist einfaedrig: der
    Zugriff in die Vorsilbe trifft dieselbe Stelle im vollen Lauf, also
    entscheidet dort dieselbe Hand. -/
theorem einfaedig_nimm (l : Lauf) (n : Nat) (hEin : Einfaedig l) :
    Einfaedig (l.take n) := by
  intro i j f g m s s' ei ej hi hj hmi hmj
  exact hEin i j f g m s s' ei ej
    (nimm_zugriff l n i _ hi) (nimm_zugriff l n j _ hj) hmi hmj

/-- Ein markenloser Schritt vorne dran aendert nichts an der W4-Form: zwei
    Treffer im alten Lauf meint dieselbe Hand wie vorher, und ein Treffer im
    neuen Schritt traegt keine Marke, ueber die man sich streiten koennte. -/
theorem einfaedig_cons_ohne_marke (q : Schritt) (l : Lauf)
    (hq : ∀ (m : Marke) (s : Nat), Res.marke m s ∉ q.ereignis.lambda)
    (hEin : Einfaedig l) : Einfaedig (q :: l) := by
  intro i j f g m s s' ei ej hi hj hmi hmj
  cases i with
  | zero =>
      cases j with
      | zero =>
          have h1 : q = Schritt.mk f ei := by simpa using hi
          have h2 : q = Schritt.mk g ej := by simpa using hj
          have hf : f = q.faden := congrArg Schritt.faden h1.symm
          have hg : g = q.faden := congrArg Schritt.faden h2.symm
          rw [hf, hg]
      | succ j =>
          have h1 : q = Schritt.mk f ei := by simpa using hi
          have he : ei = q.ereignis := congrArg Schritt.ereignis h1.symm
          exact absurd (he ▸ hmi) (hq m s)
  | succ i =>
      cases j with
      | zero =>
          have h2 : q = Schritt.mk g ej := by simpa using hj
          have he : ej = q.ereignis := congrArg Schritt.ereignis h2.symm
          exact absurd (he ▸ hmj) (hq m s')
      | succ j =>
          have hi' : l[i]? = some (Schritt.mk f ei) := by simpa using hi
          have hj' : l[j]? = some (Schritt.mk g ej) := by simpa using hj
          exact hEin i j f g m s s' ei ej hi' hj' hmi hmj

#print axioms Gabbro.Grammatik.Marken.anfang_stufentreu
#print axioms Gabbro.Grammatik.Marken.anfang_einfaedig
#print axioms Gabbro.Grammatik.Marken.verlauf_treu_und_einfaedig
#print axioms Gabbro.Grammatik.Marken.verlauf_besitz_stufe
#print axioms Gabbro.Grammatik.Marken.stand_besitz_eindeutig
#print axioms Gabbro.Grammatik.Marken.einfaedig_leer
#print axioms Gabbro.Grammatik.Marken.einfaedig_einzel
#print axioms Gabbro.Grammatik.Marken.einfaedig_ohne_marken
#print axioms Gabbro.Grammatik.Marken.nimm_zugriff
#print axioms Gabbro.Grammatik.Marken.einfaedig_nimm
#print axioms Gabbro.Grammatik.Marken.einfaedig_cons_ohne_marke

end Gabbro.Grammatik.Marken
