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

end Gabbro.Grammatik
