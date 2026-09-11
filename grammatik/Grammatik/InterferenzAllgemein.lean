/-
  Datei:      Grammatik/InterferenzAllgemein.lean
  Gegenstand: **DAS GEMEINSAME MODELL BELIEBIG VIELER FAEDEN** -- N Faeden (`List Faden`),
               beliebig viele Schritte (eine Weltenkette), geteilte Traeger eingeschlossen
               ueber Invariantendisziplin (CSL-Gestalt: ein Invariantenpraedikat je Traeger,
               Beruehren nur unter der Wache).

  ## Das Modell

  Ein `GemeinsamerLauf` traegt, was die angefuehrten Stellen liefern:

    * `hSchritt` -- jeder Schritt der Kette bleibt im Rahmen seines Fadens (je Schritt
      das, was `exec_rahmen` je Rumpf liefert, `Satz.lean`; die Kette zaehlt die Schritte
      in `schrittFaden`, die Welten in `welten`, verkettet ueber `hKette`),
    * `hPaar` -- je zwei verschiedene Faeden der Liste stehen in `Nb` (deklarierte Paare,
      `Wettlauf.lean` §6; geschlossene Welt ueber den N Faeden),
    * `hGesittet` -- der Lauf ist sperrdiszipliniert (`Gesittet`, `Wettlauf.lean`),
    * `hBeschraenkt` -- nur Deklarierte teilen sich den Lauf (`BeschraenkteVerschraenkung`),
    * `hEintritt` -- jeder Faden haelt beim Eintritt genau seine erklaerten Sperren
      (`EintrittPasst`: die Form von `RufPasst.hh`, SG-20, die Sperrmenge in BEIDEN
      Richtungen, je Faden),
    * `hSchuld` -- jeder Faden haelt die Sperren aller Traeger jeder geschuldeten
      Invariante (`SchuldnerHaelt`: die Gestalt von `invarianten_gehalten`, U003, mit
      `schuldet` als Bedingung; je Rumpf ableitbar, `schuldnerHaelt_gilt`),
    * `hInvSicht` -- die Invariantensicht liest unter gehaltenen Sperren (`InvSichtHaelt`:
      die Gestalt von `heldIn_invarianten` ueber `hEintritt`, je Faden am Eintritt;
      aus `hEintritt` ableitbar, `invSichtHaelt_aus_Eintritt`).

  ## Die Disziplin ueber geteilten Traegern

  `Interferenz.lean` schliesst gemeinsame Schreibtraeger AUS (`Disjunkt`). Hier sind sie
  EINGESCHLOSSEN, aber nur unter Disziplin: `TraegerInv` traegt ein Praedikat je Traeger
  (`inv`) plus die Beruehrregel (`disziplin`: wer schreibt, haelt die Waechter --
  Anfassen nur unter der Wache). `GeteiltGedeckt` sagt, was das fuer die Faeden heisst:
  schreibt ein zweiter Faden denselben Traeger, so ist der Traeger geteilt UND beide
  halten eine gemeinsame Sperre seines Waechter (`GemeinsameSperre`). `InvariantenKontext`
  verlangt das Praedikat an jeder Welt der Kette.

  ## Die Aussage -- Satz, verengt, aber bewiesen

  `StabilSchritt` ist `stabil` (`Interferenz.lean`) als `Prop`-Gestalt; `stabilSchritt_gilt`
  loest sie ein. `StabilKette` faltet die Gestalt ueber die Kette; `stabilKette_gilt` loest
  sie aus `HaengtAb` ein. `allgemeinStabil` ist der Hauptsatz: unter Invariantenkontext,
  geteilter Deckung, rahmenabhaengigen Zusicherungen je Faden, Gueltigkeit am Kettenkopf
  und schrittweiser Erhaltung gilt jede Zusicherung jedes Fadens an der letzten Welt der
   Kette. Die Erhaltung ist je fremdem Schritt eine Disjunktion -- disjunkt (faellt auf
   `stabil` zurueck) ODER erhaltend (die geteilte Seite, von der Invariantendisziplin von
   aussen einzuloesen) -- und je eigenem Schritt eine Erhaltpraemisse. Die Induktion
   (`kette_erhaelt`) laeuft ueber die Schrittzahl; drei kleine Listenhelfer
   (`kette_welt_belegt`, `lt_of_belegt`, `getLast?_eq_getElem` aus dem Kern) tragen die
   Indexrechnung, ganz ohne `mathlib`. `FremdDisziplin` traegt je Schritt Wache plus
   Rahmen; `fremdDisziplin_gilt` loest beides ein (Wache aus der Beruehrregel, Rahmen
   aus `hSchritt`), und `fremdErhalt_disjunkt_aus_Disziplin` zieht die disjunkte
   Erhaltung daraus ueber `stabil`. `invErhalt_aus_Kontext` zieht die invariante
   Erhaltung aus dem Kontext, und `allgemeinStabil_invariant` faltet sie zur Kette:
   dort ist keine geteilte Praemisse mehr anzunehmen. `schuldnerHaelt_gilt` (U003 je
   Rumpf) und `invSichtHaelt_aus_Eintritt` (ueber der beidseitigen Eintrittsmenge)
   loesen die Eintrittsdisziplin ein, soweit die Pruefung sie liefert.

  ## Was dieser Satz NICHT sagt -- jeder Schnitt gebucht

  (G1) `AllgemeinStabil` als voraussetzungslose `def`-Gestalt ist GESTRICHEN; an ihrer
       Stelle steht `allgemeinStabil` mit verengten Praemissen (`hInit` am Kettenkopf,
       `hFremd` als Disjunktion, `hEigen` je eigenem Schritt). Die Induktion ueber die
       Kette wird hier gefuehrt (`kette_erhaelt`), nicht vertagt.
  (G2) Die vorausgesetzte Menge ist der volle Vertragsrahmen (`D.schreibt` /
       `D.gschreibt`), nicht der syntaktische Fussabdruck. Wie in (S1) wird angenommen,
       dass eine Zusicherung nur ihren Rahmen liest (`HaengtAb` als Praemisse, `hAb`).
   (G3) Die Beruehrregel (`disziplin`) ist eine Praemisse, aber je Schritt EINGELOEST
        (`fremdDisziplin_gilt`: Wache aus der Regel, Rahmen aus `exec_rahmen` via
        `hSchritt`); die disjunkte Seite von `hFremd` fliesst daraus ueber `stabil`
        (`fremdErhalt_disjunkt_aus_Disziplin`), die invariante Seite aus dem Kontext
        (`invErhalt_aus_Kontext`, `allgemeinStabil_invariant`). Was BLEIBT, ist die
        geteilte Seite fuer beliebiges rahmenlokales `Q` (rechte Seite von `hFremd` in
        `allgemeinStabil`): dass der Pruefer die gehaltenen Mengen je Schreibstelle
        nachweist, steht nirgends -- der Pruefer kennt keine Haltemengenanalyse
        (`NEBENLAEUFIGKEIT-ENTWURF.md` §6, Punkt 1).
(G4) Sperrgeteilte Traeger sind EINGESCHLOSSEN (rechte Seite von `hFremd`, Deckung als
     `GeteiltGedeckt` getragen). `atomic`-Globale (A10, die Maschine ordnet) und
     `publishes`/`awaits`-Paare (die Paarung ordnet) stehen als Ausnahmen NEBEN
     `GeteiltGedeckt` (`AtomarAusgenommen`, `PaarungAusgenommen`,
     `GeteiltGedecktMitAusnahmen`, §13): befreite Traeger brauchen kein
     Sperrargument (`atomarAusgenommen_entlaedt`, `paarungAusgenommen_entlaedt`,
     `geteiltGedecktMitAusnahmen_von_Ausnahmen`, §15). Was BLEIBT, ist die
     Einloesung je Schreibstelle im Pruefer (G3) -- die Ausnahme entlaedt den
     Traeger, nicht den Nachweis, dass sie greift.
   (G5) `Gesittet` wird getragen, nicht verbraucht (wie S2): HB-Ordnung aus `kein_wettlauf`
        ist unverbunden mit Stabilitaet -- geordnete Schreibzugriffe bleiben
        Schreibzugriffe. `hSchuld` wird ABGELEITET, nicht getragen (`schuldnerHaelt_gilt`:
        U003 gilt je Rumpf, ohne Laufpraemisse); `hDeck` wird weiter getragen: es
        beurkundet die Disziplin, unter der die geteilte Restseite von `hFremd` steht;
        `hInv` wird im invarianten Satz verbraucht (`invErhalt_aus_Kontext`).
 (G6) Der Eintritt je Faden ist eine eigene Welt (`eintritt`), kein Gabelmodell: wie
     Faeden starten und enden, steht nirgends. Erzeugung und Vereinigung stehen als
     Eintraege daneben (`SpawnEintrag`/`JoinEintrag`: die Kindwelt ist die Kettenwelt
     an der eingetragenen Stelle, §12, eingelöst in §16
     `kindEintrittAusSpawn_belegt/mem`, `kindEintrittAusJoin_belegt/mem`,
     `kindEintrittAusGabel_belegt_aus_find/mem`). Was BLEIBT: kein
     Ausfuehrungsmodell der Gabel -- die Eintraege nennen die Stelle, sie erzeugen
     sie nicht. Darum gilt die sequenzielle Gueltigkeit (`hInit`) weiter am
     Kettenkopf, nicht am Eintritt -- `hEintritt` wird getragen, aber `hInvSicht`
     folgt daraus (`invSichtHaelt_aus_Eintritt`: die Gestalt von
     `heldIn_invarianten` ueber der beidseitigen Sperrmenge).
(G7) `Q` des Hauptsatzes spricht nur ueber die Welt; Belegungen stehen als Gestalt
     daneben (`EnvZusicherung`, `FadenEnvZusicherung`, `EnvErhalt`, §14, eingelöst
     in §17: Kette `kette_erhaelt_env`, `fadenEnv_kette_erhaelt`,
     `fadenEnv_letzte_erhaelt`, Hebung `envErhalt_aus_weltErhalt`, Schrittgleichheit
     `envErhalt_refl/symm/trans`): die eigene Belegung bleibt je Schritt fest, kein
     Faden teilt sie. Was BLEIBT (wie in S6): `hEigen` wird angenommen, nicht aus
     der sequenziellen Ausfuehrung abgeleitet -- eigene Schritte erhalten `Q`,
     statt es erst herzustellen.
-/
import Grammatik.Interferenz

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Traegerworte: wer schreibt, und unter welcher Wache -/

/-- Der Schreibschalter je Traeger: Tabellen ueber `D.schreibt`, Globale ueber
    `D.gschreibt`. -/
def TraegerSchreibt (f : D.Fn) : D.Tab ⊕ D.Glob → Bool
  | .inl t => D.schreibt f t
  | .inr g => D.gschreibt f g

/-- Die Wache eines Traegers, gehalten im Eintritt von `f`: jeder genannte Waechter steht
    in den Anfangsmitteln der Signatur (`darf`-Gestalt, statisch). -/
def WaechterGehalten (f : D.Fn) : D.Tab ⊕ D.Glob → Prop
  | .inl t => ∀ w ∈ D.braucht t, Res.von D w ∈ Signatur.anfang D (D.signatur f)
  | .inr g => ∀ w ∈ D.gbraucht g, Res.von D w ∈ Signatur.anfang D (D.signatur f)

/-- Geteilt heisst hier: von mehr als einem Faden erreichbar (`H013` als Erklaerung). -/
def Geteilt : D.Tab ⊕ D.Glob → Bool
  | .inl t => D.geteilt t
  | .inr g => D.ggeteilt g

/-- Eine gemeinsame Sperre ueber einem Traeger: beide Faeden nennen `L` in ihren
    erklaerten Sperren, und `L` steht in seiner Wache. -/
def GemeinsameSperre (f g : D.Fn) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ L : D.Lock, L ∈ D.haelt f ∧ L ∈ D.haelt g ∧
    (match c with
    | .inl t => Sum.inl L ∈ D.braucht t
    | .inr x => Sum.inl L ∈ D.gbraucht x)

/-! ## 2. Die Invariantendisziplin je Traeger (CSL-Gestalt) -/

/-- Ein Invariantenpraedikat je Traeger plus die Beruehrregel: wer schreibt, haelt die
    Waechter (Anfassen nur unter der Wache). -/
structure TraegerInv where
  inv : D.Tab ⊕ D.Glob → World D → Prop
  /-- Die Beruehrregel, statisch je Rumpf: Schreiben setzt gehaltene Waechter voraus. -/
  disziplin : ∀ (f : D.Fn) (c : D.Tab ⊕ D.Glob), TraegerSchreibt f c = true → WaechterGehalten f c

/-- Der Eintritt passt: der Faden haelt genau seine erklaerten Sperren (die Form von
    `RufPasst.hh`, SG-20, in beiden Richtungen). -/
def EintrittPasst (f : D.Fn) (σ : World D) : Prop :=
  HeldGenau (Signatur.anfang D (D.signatur f)) σ.haelt

/-- Wer eine Invariante schuldet, haelt die Sperren ALLER ihrer Traeger (die Gestalt von
    `invarianten_gehalten`, U003, mit `schuldet` als Bedingung). -/
def SchuldnerHaelt (f : D.Fn) : Prop :=
  ∀ (i : D.Inv), schuldet f i = true →
    ∀ (t : D.Tab), t ∈ D.traeger i →
      ∀ (L : D.Lock), Sum.inl L ∈ D.braucht t → L ∈ D.haelt f

/-- Die Invariantensicht liest unter gehaltenen Sperren (die Gestalt von
    `heldIn_invarianten` am Eintritt). -/
def InvSichtHaelt (f : D.Fn) (σ : World D) : Prop :=
  ∀ (i : D.Inv), schuldet f i = true → HeldIn (invSicht D i) σ.haelt

/-! ## 3. Der gemeinsame Lauf: N Faeden, beliebig viele Schritte -/

/-- N Faeden in einer Weltenkette: `welten` zaehlt die Welten, `schrittFaden` je Uebergang
    den schreibenden Faden; jeder Schritt bleibt im Rahmen seines Fadens, je zwei
    verschiedene Faeden sind deklariert, der Lauf ist gesittet und beschraenkt, jeder
    Faden tritt erklaert ein und schuldet unter Sperren. -/
structure GemeinsamerLauf (Nb : Nebeneinander) where
  faeden : List Faden
  code : Faden → D.Fn
  eintritt : Faden → World D
  welten : List (World D)
  schrittFaden : List Faden
  l : Lauf D
  /-- Die Kette ist lueckenlos: ein Schritt je Uebergang. -/
  hKette : welten.length = schrittFaden.length + 1
  /-- Jeder Schritt bleibt im Rahmen seines Fadens (das liefert `exec_rahmen` je Rumpf). -/
  hSchritt : ∀ (k : Nat) (f : Faden) (vor nach : World D),
    schrittFaden[k]? = some f → welten[k]? = some vor → welten[k + 1]? = some nach →
      f ∈ faeden ∧ Rahmen (D.schreibt (code f)) (D.gschreibt (code f)) vor nach
  /-- Je zwei verschiedene Faeden sind deklariert (geschlossene Welt ueber den N Faeden). -/
  hPaar : ∀ (f : Faden), f ∈ faeden → ∀ (g : Faden), g ∈ faeden → f ≠ g → Nb f g
  /-- Der Lauf ist sperrdiszipliniert. -/
  hGesittet : Gesittet l
  /-- Nur Deklarierte teilen sich den Lauf. -/
  hBeschraenkt : BeschraenkteVerschraenkung Nb l
  /-- Jeder Faden haelt beim Eintritt genau seine erklaerten Sperren. -/
  hEintritt : ∀ (f : Faden), f ∈ faeden → EintrittPasst (code f) (eintritt f)
  /-- Jeder Faden haelt die Sperren aller Traeger jeder geschuldeten Invariante. -/
  hSchuld : ∀ (f : Faden), f ∈ faeden → SchuldnerHaelt (code f)
  /-- Die Invariantensicht jedes Fadens liest am Eintritt unter gehaltenen Sperren. -/
  hInvSicht : ∀ (f : Faden), f ∈ faeden → InvSichtHaelt (code f) (eintritt f)

/-! ## 4. Invariantenkontext und geteilte Deckung -/

/-- Der Invariantenkontext: das Praedikat jedes Traegers gilt an jeder Welt der Kette. -/
def InvariantenKontext (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) : Prop :=
  ∀ (c : D.Tab ⊕ D.Glob) (σ : World D), σ ∈ J.welten → I.inv c σ

/-- Geteilte Deckung: schreibt ein zweiter Faden denselben Traeger, so ist der Traeger
    geteilt UND beide halten eine gemeinsame Sperre seiner Wache. Das schliesst
    sperrgeteilte Traeger ein, wo `Disjunkt` sie ausschloss. -/
def GeteiltGedeckt (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) : Prop :=
  ∀ (f : Faden), f ∈ J.faeden → ∀ (g : Faden), g ∈ J.faeden → f ≠ g →
    ∀ (c : D.Tab ⊕ D.Glob),
      TraegerSchreibt (J.code f) c = true → TraegerSchreibt (J.code g) c = true →
        Geteilt c = true ∧ GemeinsameSperre (J.code f) (J.code g) c

/-! ## 5. Stabilitaet als `Prop`-Gestalten -/

/-- **Stabilitaet in einem fremden Schritt** (`stabil` als Gestalt): was nur am Rahmen
    `(W, G)` haengt, ueberlebt einen Schritt im dazu disjunkten Rahmen. -/
def StabilSchritt (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (fremd : D.Fn) : Prop :=
  HaengtAb W G Q →
    ∀ (σ σ' : World D),
      Rahmen (D.schreibt fremd) (D.gschreibt fremd) σ σ' →
        Disjunkt W G (D.schreibt fremd) (D.gschreibt fremd) → (Q σ ↔ Q σ')

/-- **Stabilitaet ueber der Kette**: an jedem Uebergang erhaelt der fremde Schritt jedes
    `Q`, das nur am eigenen Rahmen haengt und zum Rahmen des Schreibenden disjunkt ist. -/
def StabilKette (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop) : Prop :=
  HaengtAb W G Q ∧
    ∀ (k : Nat) (f : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        Disjunkt W G (D.schreibt (J.code f)) (D.gschreibt (J.code f)) → (Q vor ↔ Q nach)

/-! ## 6. Die Saetze: Gestalt eingelöst, Kette gefaltet -/

/-- **Der fremde Schritt gilt.** `StabilSchritt` ist genau das, was `stabil`
    (`Interferenz.lean`) liefert: Rahmen plus Disjunktheit erhalten jedes
    rahmenabhaengige `Q`. -/
theorem stabilSchritt_gilt (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (fremd : D.Fn) : StabilSchritt W G Q fremd := by
  intro hQ σ σ' hR hd
  exact stabil hQ hR hd

/-- **Die Kette gilt.** Aus `HaengtAb` folgt `StabilKette`: jeder Uebergang bleibt im
    Rahmen seines Fadens (`hSchritt`), also faellt der bedingte Erhalt auf `stabil`. -/
theorem stabilKette_gilt (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (hQ : HaengtAb W G Q) : StabilKette Nb J W G Q := by
  refine ⟨hQ, ?_⟩
  intro k g vor nach hkg hkv hkn hd
  obtain ⟨_, hR⟩ := J.hSchritt k g vor nach hkg hkv hkn
  exact stabil hQ hR hd

/-- **The chain from the checked steps.** Where every thread keeps every
    frame-local `Q` across its own steps (`StabilSchritt` per thread), the
    whole chain keeps `Q` (`StabilKette`): each link stays inside its
    writer's frame (`hSchritt`), and the step shape closes it via `stabil`. -/
theorem stabilKette_aus_Schritt (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (hQ : HaengtAb W G Q)
    (hS : ∀ (g : Faden), g ∈ J.faeden → StabilSchritt W G Q (J.code g)) :
    StabilKette Nb J W G Q := by
  refine ⟨hQ, ?_⟩
  intro k g vor nach hkg hkv hkn hd
  obtain ⟨hgm, hR⟩ := J.hSchritt k g vor nach hkg hkv hkn
  exact hS g hgm hQ vor nach hR hd

#print axioms Gabbro.Grammatik.stabilKette_aus_Schritt

/-! ## 7. Gepruefte Eintrittsdisziplin: U003 und `RufPasst.hh` -/

/-- **U003 je Rumpf, ohne Laufpraemisse.** Wer eine Invariante schuldet, haelt die
    Sperren ALLER ihrer Traeger -- `D.invarianten_gehalten`, eingeloest ueber
    `schuldet` (dass `schuldet` genau die `any`-Bedingung von U003 traegt, zeigt
    `inv_schreiber_sperren` in `Interferenz.lean`). Darum ist `hSchuld` im Lauf keine
    Annahme, die je Kette faellt: sie gilt je Rumpf von vornherein. -/
theorem schuldnerHaelt_gilt (f : D.Fn) : SchuldnerHaelt (D := D) f := by
  intro i hs t ht L hL
  exact D.invarianten_gehalten (D.sig f) i hs t ht L hL

/-- **Beidseitige Eintrittsmenge, einseitig verbraucht.** `EintrittPasst` nennt die
    Sperrmenge in BEIDEN Richtungen (die Form von `RufPasst.hh`, SG-20); wo nur das
    Halten zaehlt, genuegt die `HeldIn`-Haelfte. -/
theorem eintrittHeldIn_aus_Passt {f : D.Fn} {σ : World D}
    (h : EintrittPasst (D := D) f σ) :
    HeldIn (Signatur.anfang D (D.signatur f)) σ.haelt :=
  HeldGenau.heldIn h

/-- **Die Invariantensicht folgt aus dem Eintritt.** Am Eintritt jedes Fadens liest die
    Sicht jeder geschuldeten Invariante unter gehaltenen Sperren -- `hInvSicht` im Lauf
    ist keine eigene Annahme, sondern `heldIn_invarianten` ueber der beidseitigen
    Eintrittsmenge (`hEintritt`). -/
theorem invSichtHaelt_aus_Eintritt (P : Programm D) (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (f : Faden) (hf : f ∈ J.faeden) : InvSichtHaelt (D := D) (J.code f) (J.eintritt f) := by
  intro i hi
  exact heldIn_invarianten P (J.code f) (eintrittHeldIn_aus_Passt (J.hEintritt f hf)) i hi

/-! ## 8. Fremddisziplin je Schritt: Wache plus Rahmen -/

/-- **Die gepruefte Fremddisziplin je Schritt**: der fremde Schritt bleibt in seinem
    Rahmen (das liefert `exec_rahmen` je Rumpf, hier als `hSchritt` getragen) UND
    respektiert die Wachen jedes Traegers, den er schreibt (das liefert die
    Beruehrregel `I.disziplin` je Rumpf, statisch). -/
def FremdDisziplin (g : D.Fn) (vor nach : World D) : Prop :=
  Rahmen (D.schreibt g) (D.gschreibt g) vor nach ∧
    ∀ (c : D.Tab ⊕ D.Glob), TraegerSchreibt g c = true → WaechterGehalten g c

/-- **Jeder Kettenschritt ist fremddiszipliniert.** Der Rahmen kommt aus `hSchritt`
    (`exec_rahmen` je Rumpf), die Wachen aus der Beruehrregel -- je Schritt geprueft,
    nicht angenommen. -/
theorem fremdDisziplin_gilt (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D))
    (k : Nat) (g : Faden) (vor nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    FremdDisziplin (J.code g) vor nach := by
  obtain ⟨_, hR⟩ := J.hSchritt k g vor nach hkg hkv hkn
  exact ⟨hR, fun c hc => I.disziplin (J.code g) c hc⟩

/-- **Die disjunkte Seite, aus der Disziplin.** Was nur am eigenen Rahmen haengt,
    ueberlebt einen fremddisziplinierten Schritt in Disjunktheit -- der Rahmen kommt
    aus der geprueften Fremddisziplin, der Schluss ist `stabil`. -/
theorem fremdErhalt_disjunkt_aus_Disziplin (g : D.Fn)
    (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop)
    (hQ : HaengtAb W G Q) {vor nach : World D}
    (hD : FremdDisziplin (D := D) g vor nach)
    (hd : Disjunkt W G (D.schreibt g) (D.gschreibt g)) : Q vor ↔ Q nach :=
  stabil hQ hD.1 hd

/-- **Die invariante Seite, aus dem Kontext.** Das Praedikat jedes Traegers gilt an
    jeder Welt der Kette (`hInv`) -- also vor UND nach jedem Schritt. Wo `Q` die
    Invariante selbst ist, ist die geteilte Erhaltpraemisse keine Annahme, sondern
    diese Aequivalenz. -/
theorem invErhalt_aus_Kontext (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (vor nach : World D)
    (hkv : vor ∈ J.welten) (hkn : nach ∈ J.welten) :
    I.inv c vor ↔ I.inv c nach :=
  ⟨fun _ => hInv c nach hkn, fun _ => hInv c vor hkv⟩

/-! ## 9. Kettenrechnung im Kern: drei kleine Helfer, handbewiesen -/

/-- An der Stelle `k` steht eine Welt: jede Zahl unter der Laenge trifft. -/
theorem kette_welt_belegt {α : Type} (w : List α) (k : Nat) (hk : k < w.length) :
    ∃ σ, w[k]? = some σ := by
  induction w generalizing k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero => exact ⟨a, by simp⟩
    | succ k =>
      have hk' : k < as.length := by
        simp only [List.length_cons] at hk
        omega
      obtain ⟨σ, hσ⟩ := ih k hk'
      exact ⟨σ, by simpa using hσ⟩

/-- Wo eine Welt steht, liegt die Stelle unter der Laenge. -/
theorem lt_of_belegt {α : Type} (w : List α) (k : Nat) (σ : α)
    (h : w[k]? = some σ) : k < w.length := by
  induction w generalizing k with
  | nil => simp at h
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h' : as[k]? = some σ := by simpa using h
      have hk := ih k h'
      simp only [List.length_cons]
      omega

/-- **Die Induktion ueber die Kette.** Was am Kopf gilt und jeden Schritt ueberlebt,
    gilt an jeder Stelle: `hKette` zaehlt einen Schritt je Uebergang, also liefert jede
    Nachfolgerstelle ihren Schreiber (`kette_welt_belegt`) und ihren Vorgaenger. -/
theorem kette_erhaelt (welten : List (World D)) (schrittFaden : List Faden)
    (hKette : welten.length = schrittFaden.length + 1)
    (Qf : World D → Prop)
    (hInit : ∀ σ₀ : World D, welten[0]? = some σ₀ → Qf σ₀)
    (hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      schrittFaden[k]? = some g → welten[k]? = some vor →
        welten[k + 1]? = some nach → (Qf vor ↔ Qf nach)) :
    ∀ (k : Nat) (σ : World D), welten[k]? = some σ → Qf σ := by
  intro k
  induction k with
  | zero => exact hInit
  | succ k ih =>
    intro σ hσ
    have hlen : k + 1 < welten.length := lt_of_belegt welten (k + 1) σ hσ
    have hsk : k < schrittFaden.length := by omega
    have hwk : k < welten.length := by omega
    obtain ⟨g, hg⟩ := kette_welt_belegt schrittFaden k hsk
    obtain ⟨vor, hvor⟩ := kette_welt_belegt welten k hwk
    exact (hStep k g vor σ hg hvor hσ).mp (ih vor hvor)

/-! ## 10. Der Hauptsatz: N Faeden, geteilte Traeger eingeschlossen -/

/-- **Allgemeine Stabilitaet (N Faeden).** Unter Invariantenkontext und geteilter Deckung
    ueberlebt jede rahmenabhaengige Zusicherung jedes Fadens -- gueltig am Kettenkopf --
    die ganze Kette bis zu ihrer letzten Welt, sofern jeder fremde Schritt sie entweder
    in Disjunktheit schreibt (dann greift `stabil`, aus der Fremddisziplin
    `fremdErhalt_disjunkt_aus_Disziplin`) oder erhaelt (die geteilte Seite:
    sperrgeteilt, von der Invariantendisziplin von aussen einzuloesen, G3/G4; wo `Q`
    die Invariante selbst ist, loest `allgemeinStabil_invariant` sie aus dem Kontext
    ein) und jeder eigene Schritt sie erhaelt (G7). `hInv` und `hDeck` werden getragen, nicht
    verbraucht (G5): sie beurkunden die Disziplin, unter der die geteilte Seite steht. -/
theorem allgemeinStabil (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (Q f))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ₀ : World D),
      J.welten[0]? = some σ₀ → Q f σ₀)
    (hFremd : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          Disjunkt (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (D.schreibt (J.code g)) (D.gschreibt (J.code g)) ∨ (Q f vor ↔ Q f nach))
    (hEigen : ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ↔ Q f nach)) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → Q f σ := by
  intro σ hletzte f hf
  have hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ↔ Q f nach) := by
    intro k g vor nach hkg hkv hkn
    by_cases heq : g = f
    · subst heq
      exact hEigen g hf k vor nach hkg hkv hkn
    · obtain ⟨hgm, hR⟩ := J.hSchritt k g vor nach hkg hkv hkn
      cases hFremd f hf k g vor nach hgm heq hkg hkv hkn with
      | inl hd => exact stabil (hAb f hf) hR hd
      | inr hiff => exact hiff
  have hall := kette_erhaelt J.welten J.schrittFaden J.hKette (Q f) (hInit f hf) hStep
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hall _ σ hlast

/-! ## 11. Der invariante Hauptsatz: keine geteilte Praemisse mehr -/

/-- **Allgemeine Stabilitaet der Invarianten (N Faeden).** Wo `Q` die Invariante selbst
    ist, faellt die geteilte Erhaltpraemisse weg: jeder Schritt -- fremd wie eigen --
    wird vom Kontext getragen (`invErhalt_aus_Kontext`), die Kette faltet wie gehabt
    (`kette_erhaelt` via `allgemeinStabil`). `hDeck` wird getragen, nicht verbraucht:
    es beurkundet die Disziplin, unter der der Rest -- beliebiges rahmenlokales `Q`
    ueber geteilten Traegern -- weiter anzunehmen ist (G3); `atomic`-Globale und
    `publishes`/`awaits`-Paare bleiben ausserhalb (G4). -/
theorem allgemeinStabil_invariant (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (I.inv c))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → I.inv c σ := by
  have hErhalt : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (I.inv c vor ↔ I.inv c nach) := by
    intro k g vor nach _ hkv hkn
    exact invErhalt_aus_Kontext Nb J I hInv c vor nach
      (List.mem_of_getElem? hkv) (List.mem_of_getElem? hkn)
  refine allgemeinStabil Nb J I (fun _ => I.inv c) hInv hDeck hAb hInit ?_ ?_
  · intro f hf k g vor nach _ _ hkg hkv hkn
    exact .inr (hErhalt k g vor nach hkg hkv hkn)
  · intro f hf k vor nach hkg hkv hkn
    exact hErhalt k f vor nach hkg hkv hkn

#print axioms Gabbro.Grammatik.stabilSchritt_gilt
#print axioms Gabbro.Grammatik.stabilKette_gilt
#print axioms Gabbro.Grammatik.kette_erhaelt
#print axioms Gabbro.Grammatik.allgemeinStabil
#print axioms Gabbro.Grammatik.schuldnerHaelt_gilt
#print axioms Gabbro.Grammatik.eintrittHeldIn_aus_Passt
#print axioms Gabbro.Grammatik.invSichtHaelt_aus_Eintritt
#print axioms Gabbro.Grammatik.fremdDisziplin_gilt
#print axioms Gabbro.Grammatik.fremdErhalt_disjunkt_aus_Disziplin
#print axioms Gabbro.Grammatik.invErhalt_aus_Kontext
#print axioms Gabbro.Grammatik.allgemeinStabil_invariant

/-! ## 12. Gabelmodell: Erzeugung und Vereinigung als Gestalt (G6) -/

/-- Ein Erzeugungseintrag: der Elternfaden `eltern` gibt dem Kindfaden `kind` an der
    Kettenstelle `k` seine Eintrittswelt -- die Welt der Kette an eben dieser Stelle. -/
def SpawnEintrag : Type := Faden × Faden × Nat

/-- Ein Vereinigungseintrag: der Elternfaden `eltern` nimmt den Kindfaden `kind` an der
    Kettenstelle `k` zurueck -- die Welt der Kette an eben dieser Stelle. -/
def JoinEintrag : Type := Faden × Faden × Nat

/-- Die Eintrittswelt des Kindfadens aus der Erzeugung: die Kettenwelt an der
    eingetragenen Stelle. Keine eigene Eintrittswelt mehr -- der Gabeleintrag nennt sie. -/
def KindEintrittAusSpawn (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (s : SpawnEintrag) : Option (World D) :=
  J.welten[s.2.2]?

/-- Die Rueckkehrwelt des Kindfadens aus der Vereinigung: die Kettenwelt an der
    eingetragenen Stelle. -/
def KindEintrittAusJoin (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (j : JoinEintrag) : Option (World D) :=
  J.welten[j.2.2]?

/-- Die Eintrittswelt eines Kindfadens aus der ganzen Erzeugungsliste: der erste Eintrag,
    der ihn als Kind nennt, bestimmt die Stelle; ohne Eintrag gibt es keine Welt. -/
def KindEintrittAusGabel (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (spawns : List SpawnEintrag) (kind : Faden) : Option (World D) :=
  match spawns.find? (fun s => decide (s.2.1 = kind)) with
  | none => none
  | some s => J.welten[s.2.2]?

/-! ## 13. Ausnahmen neben der geteilten Deckung: Atomar und Paarung als Gestalt (G4) -/

/-- Atomare Ausnahme: der Traeger ist ein `atomic`-Global -- seine Zugriffe ordnet die
    Maschine (A10), nicht die gemeinsame Sperre. -/
def AtomarAusgenommen (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ g : D.Glob, c = .inr g ∧ D.atomar g = true

/-- Paarungsausnahme: der Traeger ist Nutzlast einer Veroeffentlichung -- die Paarung von
    `publishes` und `awaits` ueber `D.nutzlast` ordnet, nicht die gemeinsame Sperre. -/
def PaarungAusgenommen (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ a p : D.Glob, c = .inr p ∧ p ∈ D.nutzlast a ∧ D.atomar a = true

/-- Geteilte Deckung mit Ausnahmen: schreibt ein zweiter Faden denselben Traeger, so ist
    der Traeger geteilt UND beide halten entweder eine gemeinsame Sperre seiner Wache
    ODER eine Ausnahme greift (atomar oder Paarung). Das steht NEBEN `GeteiltGedeckt`,
    nicht an seiner Stelle. -/
def GeteiltGedecktMitAusnahmen (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) : Prop :=
  ∀ (f : Faden), f ∈ J.faeden → ∀ (g : Faden), g ∈ J.faeden → f ≠ g →
    ∀ (c : D.Tab ⊕ D.Glob),
      TraegerSchreibt (J.code f) c = true → TraegerSchreibt (J.code g) c = true →
        Geteilt c = true ∧ (GemeinsameSperre (J.code f) (J.code g) c ∨
          AtomarAusgenommen (D := D) c ∨ PaarungAusgenommen (D := D) c)

/-! ## 14. Zusicherungen mit Umgebung: Q ueber Welt mal Belegung als Gestalt (G7) -/

/-- Eine Zusicherung mit Umgebung: sie spricht ueber die Welt UND die Belegung des
    Sichtbereichs -- kein Faden teilt sie, jeder traegt seine eigene. -/
def EnvZusicherung (Γ : Ctx) : Type := World D → Env D Γ → Prop

/-- Eine Zusicherung mit Umgebung je Faden: jeder Faden traegt seine Belegung ueber
    seinen eigenen Parametern (`D.params` seines Rumpfs). -/
def FadenEnvZusicherung (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) : Type :=
  ∀ (f : Faden), World D → Env D (D.params (J.code f)) → Prop

/-- Der Umgebungserhalt in einem Schritt: die fremde Welt bewegt sich, die eigene
    Belegung bleibt -- die Gestalt, die `hFremd` und `hEigen` je Belegung annimmt. -/
def EnvErhalt (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    (vor nach : World D) (ρ : Env D Γ) : Prop :=
  Q vor ρ ↔ Q nach ρ

/-! ## 15. G4-Einloesung: befreite Traeger brauchen kein Sperrargument -/

/-- **Deckung mit Ausnahmen aus Deckung ohne.** Wer die gemeinsame Sperre je
    doppelt geschriebenem Traeger nachweist, erfuellt erst recht die Deckung mit
    Ausnahmen -- die linke Seite der Disjunktion genuegt. -/
theorem geteiltGedecktMitAusnahmen_aus_gedeckt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (hD : GeteiltGedeckt Nb J) : GeteiltGedecktMitAusnahmen Nb J := by
  intro f hf g hg hne c hfc hgc
  obtain ⟨hT, hS⟩ := hD f hf g hg hne c hfc hgc
  exact ⟨hT, Or.inl hS⟩

/-- **Atomar entlaedt.** Ein `atomic`-Global braucht kein Sperrargument und keine
    Paarung: die mittlere Seite der Disjunktion steht von vornherein, gleichgueltig
    was links (`S`) und rechts (`P`) stuende. -/
theorem atomarAusgenommen_entlaedt (c : D.Tab ⊕ D.Glob)
    (hT : Geteilt c = true) (hA : AtomarAusgenommen (D := D) c)
    (S P : Prop) :
    Geteilt c = true ∧ (S ∨ AtomarAusgenommen (D := D) c ∨ P) :=
  ⟨hT, Or.inr (Or.inl hA)⟩

/-- **Paarung entlaedt.** Nutzlast einer Veroeffentlichung braucht kein
    Sperrargument und keine Atomarseite: die rechte Seite der Disjunktion steht von
    vornherein, gleichgueltig was links (`S`, `A`) stuende. -/
theorem paarungAusgenommen_entlaedt (c : D.Tab ⊕ D.Glob)
    (hT : Geteilt c = true) (hP : PaarungAusgenommen (D := D) c)
    (S A : Prop) :
    Geteilt c = true ∧ (S ∨ A ∨ PaarungAusgenommen (D := D) c) :=
  ⟨hT, Or.inr (Or.inr hP)⟩

/-- **Deckung aus lauter Ausnahmen.** Ist jeder doppelt geschriebene Traeger geteilt
    und ausgenommen (atomar oder Paarung), so gilt die Deckung mit Ausnahmen ganz
    ohne Sperrargument -- die rechte Seite der Disjunktion traegt jeden Fall. -/
theorem geteiltGedecktMitAusnahmen_von_Ausnahmen (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (h : ∀ (f : Faden), f ∈ J.faeden → ∀ (g : Faden), g ∈ J.faeden → f ≠ g →
      ∀ (c : D.Tab ⊕ D.Glob),
        TraegerSchreibt (J.code f) c = true → TraegerSchreibt (J.code g) c = true →
          Geteilt c = true ∧
            (AtomarAusgenommen (D := D) c ∨ PaarungAusgenommen (D := D) c)) :
    GeteiltGedecktMitAusnahmen Nb J := by
  intro f hf g hg hne c hfc hgc
  obtain ⟨hT, hA⟩ := h f hf g hg hne c hfc hgc
  exact ⟨hT, Or.inr hA⟩

/-- **Invariant stability under the exceptions deck.** Where `Q` is the
    invariant itself, the shared side needs no lock argument: every step --
    foreign or own -- is carried by the context (`invErhalt_aus_Kontext`),
    and the chain folds as usual (`kette_erhaelt`, the discharge engine
    behind `allgemeinStabil`). `hDeck` is carried, not consumed: freed
    carriers change nothing for invariant `Q`, since the invariant comes
    from the context rather than from the lock. -/
theorem allgemeinStabil_invariant_mitAusnahmen (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedecktMitAusnahmen Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (I.inv c))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → I.inv c σ := by
  intro σ hletzte f hf
  have hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (I.inv c vor ↔ I.inv c nach) := by
    intro k g vor nach _ hkv hkn
    exact invErhalt_aus_Kontext Nb J I hInv c vor nach
      (List.mem_of_getElem? hkv) (List.mem_of_getElem? hkn)
  have hall := kette_erhaelt J.welten J.schrittFaden J.hKette (I.inv c) (hInit f hf) hStep
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hall _ σ hlast

#print axioms Gabbro.Grammatik.allgemeinStabil_invariant_mitAusnahmen

/-! ## 16. G6-Einloesung: die Kindwelt kommt aus der eingetragenen Stelle -/

/-- **Erzeugung nennt eine Welt.** Steht die eingetragene Stelle noch in der Kette,
    so nennt der Erzeugungseintrag eine Eintrittswelt -- keine eigene Welt, die
    Kettenwelt an eben dieser Stelle. -/
theorem kindEintrittAusSpawn_belegt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (eltern kind : Faden) (k : Nat) (hk : k < J.welten.length) :
    ∃ σ, KindEintrittAusSpawn Nb J (eltern, kind, k) = some σ := by
  unfold KindEintrittAusSpawn
  show ∃ σ, J.welten[k]? = some σ
  exact kette_welt_belegt J.welten k hk

/-- **Vereinigung nennt eine Welt.** Dasselbe an der Rueckkehrstelle: die
    Rueckkehrwelt ist die Kettenwelt an der eingetragenen Stelle. -/
theorem kindEintrittAusJoin_belegt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (eltern kind : Faden) (k : Nat) (hk : k < J.welten.length) :
    ∃ σ, KindEintrittAusJoin Nb J (eltern, kind, k) = some σ := by
  unfold KindEintrittAusJoin
  show ∃ σ, J.welten[k]? = some σ
  exact kette_welt_belegt J.welten k hk

/-- **Was die Erzeugung nennt, liegt in der Kette.** Jede genannte Eintrittswelt ist
    eine Kettenwelt. -/
theorem kindEintrittAusSpawn_mem (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (s : SpawnEintrag) (σ : World D)
    (h : KindEintrittAusSpawn Nb J s = some σ) : σ ∈ J.welten := by
  unfold KindEintrittAusSpawn at h
  exact List.mem_of_getElem? h

/-- **Was die Vereinigung nennt, liegt in der Kette.** Dasselbe an der
    Rueckkehrstelle. -/
theorem kindEintrittAusJoin_mem (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (j : JoinEintrag) (σ : World D)
    (h : KindEintrittAusJoin Nb J j = some σ) : σ ∈ J.welten := by
  unfold KindEintrittAusJoin at h
  exact List.mem_of_getElem? h

/-- **Die Gabel nennt eine Welt, wo der Eintrag eine nennt.** Findet die
    Erzeugungsliste das Kind an gueltiger Stelle, so nennt die Liste seine
    Eintrittswelt. -/
theorem kindEintrittAusGabel_belegt_aus_find (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (spawns : List SpawnEintrag) (kind : Faden) (s : SpawnEintrag)
    (hfind : spawns.find? (fun s => decide (s.2.1 = kind)) = some s)
    (hk : s.2.2 < J.welten.length) :
    ∃ σ, KindEintrittAusGabel Nb J spawns kind = some σ := by
  unfold KindEintrittAusGabel
  rw [hfind]
  exact kette_welt_belegt J.welten s.2.2 hk

/-- **Was die Gabel nennt, liegt in der Kette.** Jede genannte Kindwelt -- ueber
    welchen Eintrag auch immer -- ist eine Kettenwelt. -/
theorem kindEintrittAusGabel_mem (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (spawns : List SpawnEintrag) (kind : Faden) (σ : World D)
    (h : KindEintrittAusGabel Nb J spawns kind = some σ) : σ ∈ J.welten := by
  unfold KindEintrittAusGabel at h
  cases heq : spawns.find? (fun s => decide (s.2.1 = kind)) with
  | none => simp [heq] at h
  | some s => simp only [heq] at h; exact List.mem_of_getElem? h

/-- **The spawned entry keeps the invariant.** The named entry world is a
    chain world (`kindEintrittAusSpawn_mem`), and the context holds the
    invariant at every chain world -- so the child starts under it. -/
theorem kindEintrittAusSpawn_inv (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (s : SpawnEintrag) (σ : World D)
    (h : KindEintrittAusSpawn Nb J s = some σ) : I.inv c σ :=
  hInv c σ (kindEintrittAusSpawn_mem Nb J s σ h)

/-- **The joined return keeps the invariant.** Same, at the reunion entry. -/
theorem kindEintrittAusJoin_inv (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (j : JoinEintrag) (σ : World D)
    (h : KindEintrittAusJoin Nb J j = some σ) : I.inv c σ :=
  hInv c σ (kindEintrittAusJoin_mem Nb J j σ h)

/-- **The fork-list entry keeps the invariant.** Same, through the whole
    spawn list (`kindEintrittAusGabel_mem`). -/
theorem kindEintrittAusGabel_inv (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (hInv : InvariantenKontext Nb J I)
    (c : D.Tab ⊕ D.Glob) (spawns : List SpawnEintrag) (kind : Faden) (σ : World D)
    (h : KindEintrittAusGabel Nb J spawns kind = some σ) : I.inv c σ :=
  hInv c σ (kindEintrittAusGabel_mem Nb J spawns kind σ h)

#print axioms Gabbro.Grammatik.kindEintrittAusSpawn_inv
#print axioms Gabbro.Grammatik.kindEintrittAusJoin_inv
#print axioms Gabbro.Grammatik.kindEintrittAusGabel_inv

/-! ## 17. G7-Einloesung: die eigene Belegung bleibt je Schritt fest -/

/-- **Gleichheit je Schritt, reflexiv.** Wo die Welt steht, steht sie -- die eigene
    Belegung stellt keine Frage. -/
theorem envErhalt_refl (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    (σ : World D) (ρ : Env D Γ) : EnvErhalt Γ Q σ σ ρ := by
  rfl

/-- **Gleichheit je Schritt, symmetrisch.** -/
theorem envErhalt_symm (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    {vor nach : World D} {ρ : Env D Γ}
    (h : EnvErhalt Γ Q vor nach ρ) : EnvErhalt Γ Q nach vor ρ :=
  Iff.symm h

/-- **Gleichheit je Schritt, transitiv.** -/
theorem envErhalt_trans (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ)
    {a b c : World D} {ρ : Env D Γ}
    (h1 : EnvErhalt Γ Q a b ρ) (h2 : EnvErhalt Γ Q b c ρ) :
    EnvErhalt Γ Q a c ρ :=
  Iff.trans h1 h2

/-- **Die Kette mit Umgebung.** Was am Kopf fuer die eigene Belegung gilt und jeden
    Schritt bei fester Belegung ueberlebt, gilt an jeder Stelle -- `kette_erhaelt`
    mit der Belegung als stummer Zeugin. -/
theorem kette_erhaelt_env (welten : List (World D)) (schrittFaden : List Faden)
    (hKette : welten.length = schrittFaden.length + 1)
    (Γ : Ctx) (Q : EnvZusicherung (D := D) Γ) (ρ : Env D Γ)
    (hInit : ∀ σ₀ : World D, welten[0]? = some σ₀ → Q σ₀ ρ)
    (hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      schrittFaden[k]? = some g → welten[k]? = some vor →
        welten[k + 1]? = some nach → EnvErhalt Γ Q vor nach ρ) :
    ∀ (k : Nat) (σ : World D), welten[k]? = some σ → Q σ ρ := by
  exact kette_erhaelt welten schrittFaden hKette (fun σ => Q σ ρ) hInit hStep

/-- **Hebung aus der Welt.** Wo die Zusicherung mit Umgebung nur die Welt liest,
    traegt der Welterhalt den Umgebungserhalt -- die Gestalt, die `hFremd` und
    `hEigen` je Belegung annehmen, ohne je die Belegung anzufassen. -/
theorem envErhalt_aus_weltErhalt (Γ : Ctx) (P : World D → Prop)
    (Q : EnvZusicherung (D := D) Γ)
    (hQ : ∀ (σ : World D) (ρ : Env D Γ), Q σ ρ ↔ P σ)
    {vor nach : World D} (hP : P vor ↔ P nach) (ρ : Env D Γ) :
    EnvErhalt Γ Q vor nach ρ := by
  unfold EnvErhalt
  rw [hQ vor ρ, hQ nach ρ]
  exact hP

/-- **Die Fadenskette mit Umgebung.** Je Faden und eigener Belegung ueber seinen
    Parametern: Kopf plus schrittweiser Erhalt bei fester Belegung falten zur
    Kette -- die Form, die `allgemeinStabil` je Belegung annimmt. -/
theorem fadenEnv_kette_erhaelt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Q : FadenEnvZusicherung Nb J) (f : Faden) (ρ : Env D (D.params (J.code f)))
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q f σ₀ ρ)
    (hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ρ ↔ Q f nach ρ)) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → Q f σ ρ :=
  kette_erhaelt J.welten J.schrittFaden J.hKette (fun σ => Q f σ ρ) hInit hStep

/-- **Die letzte Welt mit Umgebung.** Kopf plus schrittweiser Erhalt bei fester
    Belegung gelten an der letzten Welt der Kette -- der Schluss von
    `allgemeinStabil`, je Belegung. -/
theorem fadenEnv_letzte_erhaelt (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Q : FadenEnvZusicherung Nb J) (f : Faden) (ρ : Env D (D.params (J.code f)))
    (hInit : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q f σ₀ ρ)
    (hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ρ ↔ Q f nach ρ))
    (σ : World D) (hletzte : J.welten.getLast? = some σ) : Q f σ ρ := by
  have hall := fadenEnv_kette_erhaelt Nb J Q f ρ hInit hStep
  have hlast : J.welten[J.welten.length - 1]? = some σ := by
    rw [← List.getLast?_eq_getElem?]
    exact hletzte
  exact hall _ σ hlast

/-- **General stability with environments (N threads).** The main theorem
    lifted to per-thread scopes: where every thread's world-and-scope claim
    depends only on its own frame (per scope value), holds at the chain head,
    and survives foreign steps in disjointness or by preservation and own
    steps by preservation, it holds at the last world under every scope.
    The foreign disjoint side closes via `stabil` over the checked step
    frames (`hSchritt`); the chain folds at fixed scope
    (`fadenEnv_letzte_erhaelt`). Scopes stay per-thread throughout -- no
    thread ever reads another's. -/
theorem allgemeinStabil_env (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : FadenEnvZusicherung Nb J)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden → ∀ (ρ : Env D (D.params (J.code f))),
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (fun σ => Q f σ ρ))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (ρ : Env D (D.params (J.code f)))
      (σ₀ : World D), J.welten[0]? = some σ₀ → Q f σ₀ ρ)
    (hFremd : ∀ (f : Faden), f ∈ J.faeden → ∀ (ρ : Env D (D.params (J.code f)))
      (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          Disjunkt (D.schreibt (J.code f)) (D.gschreibt (J.code f))
            (D.schreibt (J.code g)) (D.gschreibt (J.code g)) ∨ (Q f vor ρ ↔ Q f nach ρ))
    (hEigen : ∀ (f : Faden), f ∈ J.faeden → ∀ (ρ : Env D (D.params (J.code f)))
      (k : Nat) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ρ ↔ Q f nach ρ)) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden →
      ∀ (ρ : Env D (D.params (J.code f))), Q f σ ρ := by
  intro σ hletzte f hf ρ
  have hStep : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (Q f vor ρ ↔ Q f nach ρ) := by
    intro k g vor nach hkg hkv hkn
    by_cases heq : g = f
    · subst heq
      exact hEigen g hf ρ k vor nach hkg hkv hkn
    · obtain ⟨hgm, hR⟩ := J.hSchritt k g vor nach hkg hkv hkn
      cases hFremd f hf ρ k g vor nach hgm heq hkg hkv hkn with
      | inl hd => exact stabil (hAb f hf ρ) hR hd
      | inr hiff => exact hiff
  exact fadenEnv_letzte_erhaelt Nb J Q f ρ (hInit f hf ρ) hStep σ hletzte

#print axioms Gabbro.Grammatik.allgemeinStabil_env

#print axioms Gabbro.Grammatik.geteiltGedecktMitAusnahmen_aus_gedeckt
#print axioms Gabbro.Grammatik.atomarAusgenommen_entlaedt
#print axioms Gabbro.Grammatik.paarungAusgenommen_entlaedt
#print axioms Gabbro.Grammatik.geteiltGedecktMitAusnahmen_von_Ausnahmen
#print axioms Gabbro.Grammatik.kindEintrittAusSpawn_belegt
#print axioms Gabbro.Grammatik.kindEintrittAusJoin_belegt
#print axioms Gabbro.Grammatik.kindEintrittAusSpawn_mem
#print axioms Gabbro.Grammatik.kindEintrittAusJoin_mem
#print axioms Gabbro.Grammatik.kindEintrittAusGabel_belegt_aus_find
#print axioms Gabbro.Grammatik.kindEintrittAusGabel_mem
#print axioms Gabbro.Grammatik.envErhalt_refl
#print axioms Gabbro.Grammatik.envErhalt_symm
#print axioms Gabbro.Grammatik.envErhalt_trans
#print axioms Gabbro.Grammatik.kette_erhaelt_env
#print axioms Gabbro.Grammatik.envErhalt_aus_weltErhalt
#print axioms Gabbro.Grammatik.fadenEnv_kette_erhaelt
#print axioms Gabbro.Grammatik.fadenEnv_letzte_erhaelt

/-! ## 18. Owicki-Gries step: sequential triples plus interference freedom (P15) -/

/-- Sequential triple for one thread `f`: valid at the chain head and preserved
    by its own steps. This is the sequential-logic side of the Owicki-Gries
    method: each thread is proved in isolation, carrying exactly the `hInit`
    and `hEigen` premises that `allgemeinStabil` consumes. -/
def SeqTriple (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop) (f : Faden) : Prop :=
  (∀ σ₀ : World D, J.welten[0]? = some σ₀ → Q f σ₀) ∧
    ∀ (k : Nat) (vor nach : World D),
      J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → (Q f vor ↔ Q f nach)

/-- Interference freedom for `Q`: every assertion of `f` survives every step
    of every distinct thread `g`. This is the Owicki-Gries check: one
    preservation obligation per foreign step, discharged independently of the
    sequential proofs. It feeds the shared (preserved) side of the `hFremd`
    disjunction of `allgemeinStabil`. -/
def InterferenceFree (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop) : Prop :=
  ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
    g ∈ J.faeden → g ≠ f →
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → (Q f vor ↔ Q f nach)

/-- Interference freedom discharges the foreign premise of `allgemeinStabil`
    through the shared (preserved) side of the disjunction. -/
theorem interferenceFree_gives_hFremd (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Q : Faden → World D → Prop)
    (hFree : InterferenceFree Nb J Q)
    (f : Faden) (hf : f ∈ J.faeden)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hgm : g ∈ J.faeden) (hne : g ≠ f)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    Disjunkt (D.schreibt (J.code f)) (D.gschreibt (J.code f))
      (D.schreibt (J.code g)) (D.gschreibt (J.code g)) ∨
      (Q f vor ↔ Q f nach) :=
  Or.inr (hFree f hf k g vor nach hgm hne hkg hkv hkn)

/-- Owicki-Gries stability (N threads): sequential triples plus interference
    freedom give stable assertions at the last world, via the proved N-thread
    theorem `allgemeinStabil`. The sequential proofs supply `hInit`/`hEigen`;
    the interference check supplies `hFremd` through its preserved side. -/
theorem owickiGries_stabil (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (Q f))
    (hSeq : ∀ (f : Faden), f ∈ J.faeden → SeqTriple Nb J Q f)
    (hFree : InterferenceFree Nb J Q) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → Q f σ := by
  refine allgemeinStabil Nb J I Q hInv hDeck hAb
    (fun f hf σ₀ h₀ => (hSeq f hf).1 σ₀ h₀) ?_ ?_
  · intro f hf k g vor nach hgm hne hkg hkv hkn
    exact Or.inr (hFree f hf k g vor nach hgm hne hkg hkv hkn)
  · intro f hf k vor nach hkg hkv hkn
    exact (hSeq f hf).2 k vor nach hkg hkv hkn

#print axioms Gabbro.Grammatik.interferenceFree_gives_hFremd
#print axioms Gabbro.Grammatik.owickiGries_stabil

end Gabbro.Grammatik

/-! ## 19. Sequential contracts as triples: the Owicki-Gries bind (P15 to shape)

    `owickiGries_stabil` (§18) consumes abstract assertions `Q` with sequential
    validity (`SeqTriple`) plus interference freedom (`InterferenceFree`). This
    section binds that shape to CONTRACT-shaped obligations, without importing
    them: `QRequires`/`QEnsures` live downstream in `Extraktion.lean`, which
    already imports THIS file -- importing them here would be circular (and
    `Interferenz.lean` (S1) books exactly this cut: contracts as abstract `Q`,
    substitution downstream). So the triple below is stated over explicit
    `Pre`/`Post` predicates (`D.Fn → World D → Prop`), and the remainder names
    precisely where each premise is discharged.

    Covered fragment (named): the HEAD-VALID CONTRACT CONJUNCTION -- for one
    thread `f` running `J.code f`, the assertion
    `SpecQ Pre Post f σ := Pre (J.code f) σ ∧ Post (J.code f) σ`, valid at the
    chain head (`requiresHead`/`ensuresHead`), preserved by its own steps
    (`requiresEigen`/`ensuresEigen`, the sequential-logic side), and preserved
    by every foreign step (`InterferenceFree`, the Owicki-Gries check).
    `seqTriple_from_spec` folds the triple into `SeqTriple`;
    `stabil_from_spec` closes it to the last world via `owickiGries_stabil`.

    Honest remainder:
    (R1) The instantiation `Pre := QRequires P`, `Post := QEnsures P`
    (`Extraktion.lean`) happens downstream, where the import direction allows
    it -- not here.
    (R2) `hAb` (frame-locality of the conjunction) stays a premise; downstream
    it is `haengtAb_vertrag_gesamt` once both footprints lie in the signature
    frame (the checker's footprint duty).
    (R3) `hFree` (interference freedom) stays a premise; it IS the
    Owicki-Gries check, discharged per program by the verifier (own logic).
    (R4) `requiresEigen`/`ensuresEigen` are carried, not derived from `exec`
    (G7 carries over: own-step preservation is assumed, not executed).
    (R5) `Ziel.lean`'s `hSeqLogic` premise (`ziel_nutzer_last`) still needs
    rewriting to consume `stabil_from_spec` -- owned by the proof architect
    (`Ziel.lean` is not touched here).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The contract conjunction for one thread: `Pre` (requires-side) and `Post`
    (ensures-side) over the function that thread runs. This is the covered
    fragment -- the head-valid contract conjunction -- as an assertion. -/
def SpecQ (Pre Post : D.Fn → World D → Prop)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) :
    Faden → World D → Prop :=
  fun f σ => Pre (J.code f) σ ∧ Post (J.code f) σ

/-- A sequential contract triple for one thread `f`: both sides valid at the
    chain head and both preserved by its own steps. The MINIMAL spec-triple
    predicate: exactly the `SeqTriple` obligations under contract names, so
    that `seqTriple_from_spec` is a folding, not a claim. -/
structure SpecTriple (Pre Post : D.Fn → World D → Prop)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (f : Faden) : Prop where
  /-- The requires-side holds at the chain head (caller obligation at entry). -/
  requiresHead : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Pre (J.code f) σ₀
  /-- The ensures-side holds at the chain head (sequential proof concludes). -/
  ensuresHead : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Post (J.code f) σ₀
  /-- Own steps preserve the requires-side. -/
  requiresEigen : ∀ (k : Nat) (vor nach : World D),
    J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
      J.welten[k + 1]? = some nach → (Pre (J.code f) vor ↔ Pre (J.code f) nach)
  /-- Own steps preserve the ensures-side. -/
  ensuresEigen : ∀ (k : Nat) (vor nach : World D),
    J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
      J.welten[k + 1]? = some nach → (Post (J.code f) vor ↔ Post (J.code f) nach)

/-- The triple folds into `SeqTriple` over the conjunction: head validity
    pairs up, own-step preservation meets under `and_congr`. -/
theorem seqTriple_from_spec (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Pre Post : D.Fn → World D → Prop) (f : Faden)
    (h : SpecTriple Pre Post Nb J f) :
    SeqTriple Nb J (SpecQ Pre Post Nb J) f := by
  refine ⟨?_, ?_⟩
  · intro σ₀ h₀
    show Pre (J.code f) σ₀ ∧ Post (J.code f) σ₀
    exact ⟨h.requiresHead σ₀ h₀, h.ensuresHead σ₀ h₀⟩
  · intro k vor nach hkg hkv hkn
    show (Pre (J.code f) vor ∧ Post (J.code f) vor) ↔
      (Pre (J.code f) nach ∧ Post (J.code f) nach)
    exact and_congr (h.requiresEigen k vor nach hkg hkv hkn)
      (h.ensuresEigen k vor nach hkg hkv hkn)

/-- Stability from specifications (N threads): sequential contract triples
    plus interference freedom over the conjunction give stable contract
    assertions at the last world, via the proved `owickiGries_stabil`. The
    sequential triples supply `hInit`/`hEigen` (folded above); the
    interference check supplies `hFremd` through its preserved side. -/
theorem stabil_from_spec (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hFree : InterferenceFree Nb J (SpecQ Pre Post Nb J)) :
    ∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ := by
  refine owickiGries_stabil Nb J I _ hInv hDeck hAb ?_ hFree
  intro f hf
  exact seqTriple_from_spec Nb J Pre Post f (hSpec f hf)

#print axioms Gabbro.Grammatik.seqTriple_from_spec
#print axioms Gabbro.Grammatik.stabil_from_spec

end Gabbro.Grammatik

/-! ## 20. CSL discharge: invariant-form assertions need no per-run check (x02)

    The auditor's finding: `ziel_seqLogic_aus_spec` (Ziel.lean §6, bound to
    `stabil_from_spec`, §19 above) books `hFree : InterferenceFree` as user
    OWN-LOGIC -- and `InterferenceFree` (§18, `:891`) is verbatim the
    Owicki-Gries condition (every foreign step preserves every assertion), so
    concurrent code over shared carriers forces the user into a per-run
    non-interference proof.

    The full derivation -- `InterferenceFree` for ARBITRARY `Q` from
    `TraegerInv` + `HaengtAb` -- does NOT close, and the reason is one line:
    `HaengtAb` says `Q` reads only its frame, but a foreign step writing
    INSIDE that frame may still break `Q`. Frame-locality is not preservation.
    So the CSL restriction is taken: assertions over lock-shared carriers are
    allowed ONLY in invariant (resource-invariant) form -- and invariant-form
    assertions are interference-free BY CONSTRUCTION, on the same engine that
    carries `allgemeinStabil_invariant` (§11): the context holds the invariant
    at every chain world (`invErhalt_aus_Kontext`), so each foreign step goes
    from one invariant world to another and `Q`, being the invariant, follows.

    What this section proves (no `sorry`, no `axiom`):

    * `InvariantForm` -- the covered fragment, named: per thread, `Q f`
      coincides with some carrier invariant `I.inv c` (the carrier may differ
      per thread; shared carriers are the point, disjoint ones already travel
      through the `stabil` side of `hFremd`).
    * `interferenceFree_of_invariantForm` -- the discharge: form plus context
      yields `InterferenceFree`. This is the theorem that removes the per-run
      proof for the covered class.
    * `owickiGries_stabil_invariantForm` -- the Owicki-Gries corollary with
      `hFree` replaced by `hForm` (same conclusion as `owickiGries_stabil`).
    * `stabil_from_spec_invariantForm` -- the contract-level corollary with
      `hFree` replaced by `hForm` over `SpecQ` (same conclusion as
      `stabil_from_spec`, §19).

    User-obligation delta, stated exactly (BEFORE = §19 R3, AFTER = this section):

    * BEFORE: the user owes `hFree` -- for every thread `f` and every foreign
      step, `Q f` survives the step. A per-run preservation proof, OWN-LOGIC.
    * AFTER (covered class -- `Q` in invariant form): `hFree` is DERIVED. The
      user owes instead (U1) `hForm` -- exhibit, per thread, the carrier `c`
      with `Q f σ ↔ I.inv c σ` for all `σ`: a static shape check, no per-step
      reasoning; and (U2) `hInv` (`InvariantenKontext`) -- UNCHANGED, it was
      already a premise of `stabil_from_spec`. `hSpec` and `hAb` are likewise
      unchanged.
    * NOT covered: assertions over shared carriers that are NOT in invariant
      form. There `hFree` remains OWN-LOGIC, exactly as §19 R3 books it. This
      section narrows R3 for the invariant fragment; it does not delete it.

    Remainder (not here, named so no wave re-measures it):

    * The Ziel-level binder -- a `ziel_seqLogic_aus_spec` variant consuming
      `stabil_from_spec_invariantForm` (with `hForm` instead of `hFree`) --
      belongs to the proof architect: `Ziel.lean` is owned by another wave and
      is not touched here (§19 R5 carries over).
    * `hInv` itself (establishing the context per run: entry plus discipline)
      is carried as before, not discharged; `hDeck` is carried, not consumed
      (G5 carries over).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- An assertion in invariant (resource-invariant) form: for every thread, `Q f`
    coincides, at every world, with the invariant of some carrier. This is the
    CSL fragment -- assertions over lock-shared carriers are allowed only in
    this form; the carrier may differ per thread. -/
def InvariantForm (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop) : Prop :=
  ∀ (f : Faden), f ∈ J.faeden → ∃ c : D.Tab ⊕ D.Glob, ∀ (σ : World D), Q f σ ↔ I.inv c σ

/-- **Interference freedom by construction.** An invariant-form assertion
    survives every foreign step: both worlds of the step are chain worlds, the
    context holds the invariant at each (`invErhalt_aus_Kontext`, the engine
    behind `allgemeinStabil_invariant`), and `Q` IS the invariant -- so there
    is nothing per-run left to prove. -/
theorem interferenceFree_of_invariantForm (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hForm : InvariantForm Nb J I Q)
    (hInv : InvariantenKontext Nb J I) :
    InterferenceFree Nb J Q := by
  intro f hf k g vor nach _ _ hkg hkv hkn
  obtain ⟨c, hc⟩ := hForm f hf
  rw [hc vor, hc nach]
  exact invErhalt_aus_Kontext Nb J I hInv c vor nach
    (List.mem_of_getElem? hkv) (List.mem_of_getElem? hkn)

/-- Owicki-Gries stability for the invariant fragment: sequential triples plus
    the FORM check give stable assertions at the last world -- `hFree` is
    derived above, not assumed. Same conclusion as `owickiGries_stabil`. -/
theorem owickiGries_stabil_invariantForm (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (Q f))
    (hSeq : ∀ (f : Faden), f ∈ J.faeden → SeqTriple Nb J Q f)
    (hForm : InvariantForm Nb J I Q) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → Q f σ :=
  owickiGries_stabil Nb J I Q hInv hDeck hAb hSeq
    (interferenceFree_of_invariantForm Nb J I Q hForm hInv)

/-- Stability from specifications for the invariant fragment: sequential
    contract triples plus the FORM check over the conjunction give stable
    contract assertions at the last world. Same conclusion as
    `stabil_from_spec` (§19), with `hFree` derived instead of owed. -/
theorem stabil_from_spec_invariantForm (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J)) :
    ∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ := by
  refine stabil_from_spec Nb J I Pre Post hInv hDeck hAb hSpec ?_
  exact interferenceFree_of_invariantForm Nb J I _ hForm hInv

#print axioms Gabbro.Grammatik.interferenceFree_of_invariantForm
#print axioms Gabbro.Grammatik.owickiGries_stabil_invariantForm
#print axioms Gabbro.Grammatik.stabil_from_spec_invariantForm

end Gabbro.Grammatik

/-! ## 21. CSL-exact discipline: the invariant from entry plus return (Posten 1)

    The auditor's finding against §20: `interferenceFree_of_invariantForm` derives
    interference freedom from `InvariantenKontext` (`∀ c σ, σ ∈ J.welten → I.inv c σ` --
    the invariant at EVERY world), but that context is discharged nowhere and is
    STRONGER than CSL: real code breaks the invariant mid-critical-section at
    instruction granularity, so the theorem fits no real code unless a chain step is
    a whole critical section -- and no file fixed what a `GemeinsamerLauf` step is.

    This section fixes the grain FIRST, then proves the context FROM DISCIPLINE.

    GRAIN (stated and used): one `GemeinsamerLauf` step is ONE WHOLE CRITICAL SECTION --
    one sequential body execution, indivisible at chain level. The step stays inside the
    writer's whole frame (`hSchritt`, discharged per body by `exec_rahmen`, `Satz.lean`:1323,
    named at `rahmen_aus_exec`, `Interferenz.lean`:148). It is NOT one machine event:
    `Koernung.lean` proves an n-byte `schreibBytes` leaves exactly n events
    (`schreibBytes_event_count`:158) and is NOT one event for 2 <= n
    (`schreibBytes_not_single`:173); a `leseBytes` records ONE event while folding over
    n cells (`leseBytes_not_atomic`:195); and the interrupted middle IS the witnessed
    tear (`two_byte_tear`:208, `mid_interruption_tears`:617). So at event grain the
    invariant DOES break mid-step, and a context claimed at every event-world would fit
    no real code -- exactly the auditor's charge. The chain therefore resolves bodies,
    not events (the same reason `Wettlauf.lean` §5, honest passage, builds no general
    interleaving semantics for `eval`): the invariant is claimed only at chain worlds,
    which are section boundaries, and each step re-establishes what it owes at return
    (`rufAt`, `Semantik.lean`:778-780: a normal return carries every owed invariant).
    `schritt_rahmen_aus_korn` is the grain as a theorem, CONSUMED below: the non-writer
    preservation (`nichtschreiber_erhaelt`) runs `stabil` over exactly that whole-frame
    step.

    DISCIPLINE (proved, not assumed): `hinv_aus_disziplin` derives the invariant from
    (E) entry -- it holds at the chain head (caller/sequential side, same shape as `hInit`);
    (R) return -- every WRITING step re-establishes it at its end world, conditioned on
    holding the guard (the `rufAt` return-check shape under `schuldet`, `Semantik.lean`:374);
    (W) THE single lock-holding premise, bounded -- writing steps hold the guard, as a
    STATIC declared-holds fact (`D.haelt` shape, exactly like `SchuldnerHaelt`, §3:162,
    which already travels per thread in `GemeinsamerLauf.hSchritt`'s sibling `hSchuld`,
    §3:200, proved per body by `schuldnerHaelt_gilt`, §7:283, from U003
    `invarianten_gehalten`, `Syntax.lean`:181, via `inv_schreiber_sperren`,
    `Interferenz.lean`:159); plus the standard frame-locality of the invariant
    (`HaengtAb` over its carrier singleton, with the carrier-frame link) and the static
    guard link (`Bewacht`). The conclusion is CSL-exact: `LockFrei L σ → I.inv c σ`
    (lock free implies invariant), NOT at every world. `hinv_kette_aus_disziplin` is the
    unconditional chain lemma underneath (forward induction over `k`, reusing §9
    `lt_of_belegt`/`kette_welt_belegt`); `hinv_aus_disziplin` is its CSL-exact weakening.

    What exists and is CITED, not rebuilt: `SchuldnerHaelt` (§3:162), `schuldet`
    (`Semantik.lean`:374), U003 (`Syntax.lean`:181), `schuldnerHaelt_gilt` (§7:283),
    `inv_schreiber_sperren` (`Interferenz.lean`:159), `heldIn_invarianten`
    (`Satz.lean`:1249), `eintrittHeldIn_aus_Passt` (§7:290, entry declared-holds goes
    dynamic at entry). `wache_aus_schuld` DISCHARGES the watch premise for TABLE carriers
    from `J.hSchuld` plus invariant coverage (every written table sits in some owed
    invariant's carrier list -- the CSL coverage side condition, per thread, no run
    reasoning); the guard fact `Sum.inl L ∈ D.braucht t` is consumed there.

    Scope, honestly narrowed: U003 (`Syntax.lean`:181-182) quantifies over TABLE carriers
    (`D.traeger : Inv → List Tab`) only -- globals have no `schuldet` coverage, so the
    derived watch (`wache_aus_schuld`) and the named `hinv_aus_disziplin` are TABLE-scoped.
    Shared globals stay on the §13-§15 exception track (`AtomarAusgenommen` via A10
    machine ordering, `PaarungAusgenommen` via publishes/awaits); the general per-carrier
    lemma (`hinv_kette_aus_disziplin`, `invariantenKontext_aus_disziplin`) keeps the watch
    as its single named premise, which for globals is checker-side. Per-site dynamic
    holding (that the checker proves held sets at every write site) stands nowhere --
    the G3 remainder (`messung/NEBENLAEUFIGKEIT-ENTWURF.md` §6 point 1); the static
    declared-holds side is what U003 delivers, and the interior of a step (take at
    entry, release at return) is the body's own critical-section discipline, booked as
    checker remainder beside `hReturn`.

    Re-derivation (§20 untouched): `invariantenKontext_aus_disziplin` folds the lemma to
    the full `InvariantenKontext` (per carrier, via `kette_belegt_of_mem`);
    `interferenceFree_of_invariantForm_aus_disziplin` feeds that derived context into
    `interferenceFree_of_invariantForm` (§20:1128) -- the §20 chain now runs on a derived
    premise. `interferenceFree_wo_frei` is the literal CSL interface: invariant-form
    assertions (uniform shared carrier, the standard CSL case) are interference-free
    WHERE THE LOCK IS FREE, both step worlds free.
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The guard lock of a carrier: the lock in the carrier's watch list (`D.braucht`
    for tables, `D.gbraucht` for globals -- the static side of the touch rule
    `TraegerInv.disziplin`). -/
def Bewacht (c : D.Tab ⊕ D.Glob) (L : D.Lock) : Prop :=
  match c with
  | .inl t => Sum.inl L ∈ D.braucht t
  | .inr x => Sum.inl L ∈ D.gbraucht x

/-- CSL lock-freedom at a world: the guard is not held (`World.haelt`,
    `Semantik.lean`: `offen` of the trace; `nimmt` takes, `gibt` releases). -/
def LockFrei (L : D.Lock) (σ : World D) : Prop :=
  L ∉ σ.haelt

/-- **The grain, as a theorem.** Every chain step is a whole-frame step of its writer:
    one sequential body execution (`hSchritt`, per body `exec_rahmen`), indivisible at
    chain level -- NOT one machine event (cf. `Koernung.lean`: an n-byte transfer is n
    events, `schreibBytes_not_single`). Consumed by `nichtschreiber_erhaelt`. -/
theorem schritt_rahmen_aus_korn (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    Rahmen (D.schreibt (J.code g)) (D.gschreibt (J.code g)) vor nach :=
  (J.hSchritt k g vor nach hkg hkv hkn).2

/-- **Non-writers preserve.** Where the invariant reads only its carrier (frame covered
    by `c`) and the step's writer does not write `c`, the whole-frame step (`hSchritt`
    via `schritt_rahmen_aus_korn`) preserves the invariant by `stabil`. -/
theorem nichtschreiber_erhaelt (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv c))
    (hFrameT : ∀ t : D.Tab, Wc t = true → c = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → c = .inr x)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach)
    (hN : TraegerSchreibt (J.code g) c = false) :
    I.inv c vor ↔ I.inv c nach := by
  refine stabil hAb (schritt_rahmen_aus_korn Nb J k g vor nach hkg hkv hkn) ?_
  constructor
  · intro t ht
    have hc := hFrameT t ht
    cases c with
    | inl t₀ =>
      simp at hc
      subst hc
      simp only [TraegerSchreibt] at hN
      exact hN
    | inr x₀ => simp at hc
  · intro x hx
    have hc := hFrameG x hx
    cases c with
    | inl t₀ => simp at hc
    | inr x₀ =>
      simp at hc
      subst hc
      simp only [TraegerSchreibt] at hN
      exact hN

/-- **The chain lemma: entry plus return plus watch.** The invariant holds at every
    chain world: at the head by entry; across a writing step by return-under-guard
    (unlocked by the single watch premise); across a non-writing step by frame
    preservation (`nichtschreiber_erhaelt`). The guard link `hGuard` is carried
    (G5-style): it ties `L` to `c`, and is consumed where the watch is discharged
    (`wache_aus_schuld`). -/
theorem hinv_kette_aus_disziplin (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv c))
    (hFrameT : ∀ t : D.Tab, Wc t = true → c = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → c = .inr x)
    (hGuard : Bewacht (D := D) c L)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) c = true →
          L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) c = true →
          L ∈ D.haelt (J.code g)) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → I.inv c σ := by
  intro k
  induction k with
  | zero => exact hEntry
  | succ k ih =>
    intro σ hσ
    have hK := J.hKette
    have hlen : k + 1 < J.welten.length := lt_of_belegt J.welten (k + 1) σ hσ
    have hsk : k < J.schrittFaden.length := by omega
    have hwk : k < J.welten.length := by omega
    obtain ⟨g, hg⟩ := kette_welt_belegt J.schrittFaden k hsk
    obtain ⟨vor, hvor⟩ := kette_welt_belegt J.welten k hwk
    have hgm : g ∈ J.faeden := (J.hSchritt k g vor σ hg hvor hσ).1
    cases heq : TraegerSchreibt (J.code g) c with
    | true =>
      exact hReturn k g vor σ hgm hg hvor hσ heq
        (hWatch k g vor σ hgm hg hvor hσ heq)
    | false =>
      exact (nichtschreiber_erhaelt Nb J I c Wc Gc hAb hFrameT hFrameG
        k g vor σ hg hvor hσ heq).mp (ih vor hvor)

/-- Membership anywhere in a list is membership at some index. -/
theorem kette_belegt_of_mem {α : Type} (w : List α) (σ : α) (h : σ ∈ w) :
    ∃ k : Nat, w[k]? = some σ := by
  induction w with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by simp⟩
    · obtain ⟨k, hk⟩ := ih h
      exact ⟨k + 1, by simp only [List.getElem?_cons_succ]; exact hk⟩

/-- A `schreibt`-hit inside a carrier list fires the `any`: the `schuldet` unfolding
    step for `wache_aus_schuld`. -/
theorem any_of_mem_true (ts : List D.Tab) (P : D.Tab → Bool) (t₀ : D.Tab)
    (hm : t₀ ∈ ts) (hP : P t₀ = true) : ts.any P = true := by
  induction ts with
  | nil => simp at hm
  | cons a as ih =>
    simp only [List.mem_cons] at hm
    simp only [List.any_cons]
    rcases hm with rfl | hm
    · simp [hP]
    · cases hPa : P a with
      | true => simp
      | false => simp [ih hm]

/-- **The watch, discharged for tables.** A writer of table `t₀` holds every guard in
    `t₀`'s watch list: coverage gives an owed invariant over `t₀` (its carrier list hits
    the writer's frame, so `schuldet` fires), U003 (`J.hSchuld`, proved per body by
    `schuldnerHaelt_gilt`) gives the declared holds, and the guard fact picks `L`.
    Globals are OUTSIDE this discharge: U003 is table-only (`Syntax.lean`:181-182). -/
theorem wache_aus_schuld (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (g : Faden) (hg : g ∈ J.faeden)
    (hW : TraegerSchreibt (J.code g) (.inl t₀) = true)
    (hCov : ∃ i : D.Inv, t₀ ∈ D.traeger i) :
    L ∈ D.haelt (J.code g) := by
  obtain ⟨i, hi⟩ := hCov
  have hP : D.schreibt (J.code g) t₀ = true := by
    unfold TraegerSchreibt at hW
    exact hW
  have hs : schuldet (J.code g) i = true := by
    unfold schuldet
    exact any_of_mem_true (D.traeger i) _ t₀ hi hP
  exact J.hSchuld g hg i hs t₀ hi L hGuardT

/-- **The invariant from discipline, CSL-exact (`lockFree → inv`).** For a table carrier
    with guard `L`: entry plus return-under-guard plus frame-locality, where the watch
    premise is DISCHARGED (`wache_aus_schuld` from `J.hSchuld` plus coverage) rather than
    assumed -- so no lock premise is owed here; the discipline cited above does the work.
    Table-scoped because U003 is table-only; see the section prose. -/
theorem hinv_aus_disziplin (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (t₀ : D.Tab) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv (.inl t₀)))
    (hFrameT : ∀ t : D.Tab, Wc t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → LockFrei (D := D) L σ →
      I.inv (.inl t₀) σ := by
  intro k σ h _
  exact hinv_kette_aus_disziplin Nb J I (.inl t₀) L Wc Gc hAb hFrameT hFrameG
    hGuardT hEntry hReturn
    (fun k g vor nach hgm hkg hkv hkn hW =>
      wache_aus_schuld Nb J t₀ L hGuardT g hgm hW (hCov g hgm hW))
    k σ h

/-- **The derived context.** The per-carrier lemma folded over all carriers: entry,
    return-under-guard, frame-locality, guard existence, and the single watch premise
    per carrier yield the full `InvariantenKontext` (§4:207) -- the premise §20 assumed.
    For tables the watch discharges via `wache_aus_schuld`; for globals it is
    checker-side (see section prose). -/
theorem invariantenKontext_aus_disziplin (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (I : TraegerInv (D := D))
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAb : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameT : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameG : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g)) :
    InvariantenKontext Nb J I := by
  intro c σ hmem
  obtain ⟨k, hk⟩ := kette_belegt_of_mem J.welten σ hmem
  obtain ⟨L, hL⟩ := hGuardEx c
  exact hinv_kette_aus_disziplin Nb J I c L (Wc c) (Gc c) (hAb c) (hFrameT c)
    (hFrameG c) hL (hEntry c)
    (fun k g vor nach hgm hkg hkv hkn hW hHold =>
      hReturn c L k g vor nach hL hgm hkg hkv hkn hW hHold)
    (fun k g vor nach hgm hkg hkv hkn hW =>
      hWatch c L k g vor nach hL hgm hkg hkv hkn hW)
    k σ hk

/-- **The §20 chain on the derived premise.** `interferenceFree_of_invariantForm`
    (§20:1128) with the context derived above instead of assumed: same conclusion
    (`InterferenceFree`), §20 itself untouched. -/
theorem interferenceFree_of_invariantForm_aus_disziplin (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAb : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameT : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameG : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g))
    (hForm : InvariantForm Nb J I Q) :
    InterferenceFree Nb J Q :=
  interferenceFree_of_invariantForm Nb J I Q hForm
    (invariantenKontext_aus_disziplin Nb J I Wc Gc hAb hFrameT hFrameG hGuardEx
      hEntry hReturn hWatch)

/-- **Invariant-form assertions are interference-free WHERE THE LOCK IS FREE.**
    The literal CSL interface over one shared table carrier (the standard CSL case):
    `Q` coincides with the carrier invariant per thread, and each foreign step goes
    from one lock-free world to another -- so `Q` follows from `hinv_aus_disziplin`
    at both ends. No per-run preservation proof is owed for the covered class. -/
theorem interferenceFree_wo_frei (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (t₀ : D.Tab) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv (.inl t₀)))
    (hFrameT : ∀ t : D.Tab, Wc t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hFormU : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ : World D),
      Q f σ ↔ I.inv (.inl t₀) σ) :
    ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
          J.welten[k + 1]? = some nach →
            LockFrei (D := D) L vor → LockFrei (D := D) L nach → (Q f vor ↔ Q f nach) := by
  intro f hf k g vor nach _ _ _ hkv hkn hFreiVor hFreiNach
  have hInv := hinv_aus_disziplin Nb J I t₀ L Wc Gc hAb hFrameT hFrameG hGuardT
    hEntry hReturn hCov
  rw [hFormU f hf vor, hFormU f hf nach]
  exact ⟨fun _ => hInv _ nach hkn hFreiNach, fun _ => hInv _ vor hkv hFreiVor⟩

#print axioms Gabbro.Grammatik.Bewacht
#print axioms Gabbro.Grammatik.LockFrei
#print axioms Gabbro.Grammatik.schritt_rahmen_aus_korn
#print axioms Gabbro.Grammatik.nichtschreiber_erhaelt
#print axioms Gabbro.Grammatik.hinv_kette_aus_disziplin
#print axioms Gabbro.Grammatik.kette_belegt_of_mem
#print axioms Gabbro.Grammatik.any_of_mem_true
#print axioms Gabbro.Grammatik.wache_aus_schuld
#print axioms Gabbro.Grammatik.hinv_aus_disziplin
#print axioms Gabbro.Grammatik.invariantenKontext_aus_disziplin
#print axioms Gabbro.Grammatik.interferenceFree_of_invariantForm_aus_disziplin
#print axioms Gabbro.Grammatik.interferenceFree_wo_frei

end Gabbro.Grammatik
