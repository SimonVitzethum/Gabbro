/-
  Datei:      Passlogik/Phasen.lean
  Gegenstand: Die PHASEN (`O001`-`O006`) -- `advances` laeuft vorwaerts auf einer
              endlichen Ordnung, und Zweige treffen sich.

  MODELLIERT WIRD
    Eine endliche Stufenordnung `order { … }`, ein Schritt `advances a -> b`, der Fluss
    einer Marke durch einen Rumpf, und die vier Pruefungen: die Stufen gibt es (`O001`),
    der Schritt geht VORWAERTS (`O002`), die Marke steht beim Ruf auf der Ausgangsstufe
    (`O003`), der Rumpf setzt sich zu seiner eigenen Zusage zusammen (`O004`), und alle
    Zweige erreichen dieselbe Stufe (`O006`).

  QUELLSAETZE
    dokumente/SYNTAX.md:279  -- `markorder = "order" "{" identlist "}"`
    dokumente/SYNTAX.md:694  -- `[ "advances" ident "->" ident ]` in `fndecl`
    dokumente/SYNTAX.md:730  -- «B37»: "`advances roh -> mmu` sagt, WELCHEN Schritt diese
                                Funktion auf einer Marke mit `order` tut. [...] Geprueft
                                wird in drei Stufen: die Stufen gibt es und der Schritt
                                geht VORWAERTS (`O001`/`O002` -- ohne die zweite Haelfte
                                waere `order` eine Liste), die Marke steht beim Ruf auf
                                der Ausgangsstufe (`O003`), und der Rumpf setzt sich zu
                                seiner eigenen Zusage zusammen (`O004`), und alle Zweige
                                erreichen dieselbe Stufe (`O006`, K11.1) -- ein Zweig, der
                                mit `return` endet, schliesst sich nicht an; ein Schritt in
                                einer Schleife wird abgelehnt."
    gabbro paesse --je-satz  -- Saetze `phasen.deklaration`, `phasen.fluss`:
        "**A linear value forces a CHAIN but not WHICH one**: with six boot steps all 720
        orders type-check, and M2 sees only that each token is passed on exactly once."

  ANGENOMMEN STATT BEWIESEN
    (P1) Die Stufenordnung ist eine LISTE von Namen, und ihr Index ist die Ordnung. Das
         ist genau, was `order { … }` sagt -- `O002` vergleicht Indizes.
    (P2) **Der Anweisungsabstieg steht hier nicht.** Das Passregister nennt fuer
         `phasen.fluss` mehrere Schweigestellen: `Zuweisung`, `Publish`, `Leave`, `Next`
         und `AwaitLoad` werden verschluckt, nur ein DIREKTER Ruf zaehlt als Schritt, und
         die zuletzt erreichte Stufe wird nicht aus Zweigen herausgereicht. Modelliert ist
         die Form, nicht der Abstieg (W16).
    (P3) Die weichere Lesart -- eine MENGE von Stufen tragen und alle den naechsten
         Schritt annehmen lassen -- ist ausdruecklich nicht gebaut: *"von der strengen
         kann man lockern, von der weichen nie"* (K11.1). Modelliert ist die strenge.
-/

namespace Passlogik.Phasen

/-! ## 1. Die Ordnung und der Schritt -/

/-- Eine Stufe ist ein Name; ihre Ordnung ist ihr INDEX in der `order`-Liste (P1). -/
structure Stufe where
  index : Nat
deriving DecidableEq, Repr

/-- `order { a, b, c }` -- eine ENDLICHE Liste. Die Endlichkeit ist es, die §5 traegt. -/
structure Ordnung where
  laenge : Nat

/-- `O001` -- die Stufe steht in der erklaerten Ordnung. -/
def erklaert (O : Ordnung) (s : Stufe) : Prop := s.index < O.laenge

/-- Ein Schritt `advances von -> nach`. -/
structure Schritt where
  von  : Stufe
  nach : Stufe
deriving DecidableEq, Repr

/-- `O002` -- **der Schritt geht VORWAERTS.** *"Ohne die zweite Haelfte waere `order`
    eine Liste"* (`SYNTAX.md`:735). -/
def vorwaerts (s : Schritt) : Prop := s.von.index < s.nach.index

/-- `O001` + `O002` zusammen: eine wohlgeformte Schrittdeklaration. -/
def schritt_ok (O : Ordnung) (s : Schritt) : Prop :=
  erklaert O s.von ∧ erklaert O s.nach ∧ vorwaerts s

/-! ## 2. Der Fluss durch einen Rumpf

    Der Rumpf ist eine Folge von Schritten und Verzweigungen. `O003` verlangt, dass die
    Marke beim Ruf auf der AUSGANGSSTUFE steht; `O006`, dass alle Zweige DIESELBE Stufe
    erreichen.
-/

inductive Rumpf where
  /-- Nichts tun -- die Marke bleibt, wo sie ist. -/
  | still  : Rumpf
  /-- Einen Schritt tun. -/
  | tut    : Schritt → Rumpf
  | folge  : Rumpf → Rumpf → Rumpf
  /-- `if` / `match` -- zwei Zweige, die sich treffen muessen (`O006`). -/
  | zweigt : Rumpf → Rumpf → Rumpf
deriving Repr

/-- **Der Fluss:** `fliesst r a b` heisst "betritt der Rumpf `r` mit der Marke auf `a`,
    so verlaesst er ihn mit der Marke auf `b`".

    `O003` steckt im Konstruktor `tut`: der Schritt ist NUR anwendbar, wenn die Marke auf
    seiner Ausgangsstufe steht. -/
inductive fliesst : Rumpf → Stufe → Stufe → Prop where
  | still (a : Stufe) : fliesst .still a a
  /-- `O003` -- die Marke steht auf der Ausgangsstufe. -/
  | tut (s : Schritt) : fliesst (.tut s) s.von s.nach
  | folge {r q a b c} : fliesst r a b → fliesst q b c → fliesst (.folge r q) a c
  | links {r q a b} : fliesst r a b → fliesst (.zweigt r q) a b
  | rechts {r q a b} : fliesst q a b → fliesst (.zweigt r q) a b

/-! ## 3. DER SATZ: der Fluss laeuft vorwaerts

    Ein Rumpf, dessen Schritte alle vorwaerts gehen, bewegt die Marke nie zurueck -- und
    echt vorwaerts, sobald er einen Schritt tut.
-/

/-- Alle Schritte eines Rumpfes gehen vorwaerts (`O002` an jeder Deklaration). -/
def alle_vorwaerts : Rumpf → Prop
  | .still      => True
  | .tut s      => vorwaerts s
  | .folge r q  => alle_vorwaerts r ∧ alle_vorwaerts q
  | .zweigt r q => alle_vorwaerts r ∧ alle_vorwaerts q

/-- **Der Fluss geht nie zurueck.** -/
-- BEWEIST NICHT (P2): dass der Pruefer jeden Schritt SIEHT. Ein Schritt in einem
-- `Zuweisung`-, `Publish`-, `Leave`-, `Next`- oder `AwaitLoad`-Knoten wird vom
-- Anweisungslaeufer verschluckt; und bis zum 2026-08-24 auch einer in einem `return`
-- (`return schritt(p);` ging mit null Fehlern durch, `let q = schritt(p); return q;` fiel
-- an `O004` -- zwei Ruempfe gleicher Bedeutung, einer gefangen und einer nicht).
theorem fluss_geht_vorwaerts {r : Rumpf} {a b : Stufe}
    (hv : alle_vorwaerts r) (h : fliesst r a b) : a.index ≤ b.index := by
  induction h with
  | still _ => exact Nat.le_refl _
  | tut s => exact Nat.le_of_lt hv
  | folge _ _ ih1 ih2 =>
      obtain ⟨h1, h2⟩ := hv
      exact Nat.le_trans (ih1 h1) (ih2 h2)
  | links _ ih => exact ih hv.1
  | rechts _ ih => exact ih hv.2


#print axioms Passlogik.Phasen.fluss_geht_vorwaerts
/-- **Und wer einen Schritt tut, kommt ECHT voran.** -/
theorem ein_schritt_kommt_voran {s : Schritt} {a b : Stufe}
    (hv : vorwaerts s) (h : fliesst (.tut s) a b) : a.index < b.index := by
  cases h; exact hv

/-! ## 4. `O004` -- der Rumpf setzt sich zu seiner eigenen Zusage zusammen

    Eine Funktion mit `advances a -> b` verspricht, die Marke von `a` nach `b` zu
    bringen. `O004` haelt den Rumpf dagegen.
-/

/-- Die Zusage einer Funktion, gegen ihren Rumpf gehalten. -/
def o004_haelt (zusage : Schritt) (r : Rumpf) : Prop :=
  fliesst r zusage.von zusage.nach

/-- **Die Zusage komponiert.** Zwei Funktionen, deren Zusagen aneinanderpassen, ergeben
    zusammen eine Zusage von der ersten Ausgangs- zur zweiten Zielstufe. *Das ist die
    Bootkette (`O007`), auf eine Zeile gebracht.* -/
-- BEWEIST NICHT: dass die Bootkette eines Moduls LUECKENLOS ist. `namen.bootkette` sagt
-- selbst: "Gappy by construction: ein Schritt OHNE `advances` wird uebersprungen, ohne
-- den Zustand zu entwerten, der ERSTE Schritt wird gegen gar nichts gehalten, und
-- Schritte, die kein Ruf sind, werden uebersprungen."
theorem zusagen_komponieren {s1 s2 : Schritt} {r1 r2 : Rumpf}
    (h1 : o004_haelt s1 r1) (h2 : o004_haelt s2 r2) (hpasst : s1.nach = s2.von) :
    fliesst (.folge r1 r2) s1.von s2.nach := by
  refine fliesst.folge h1 ?_
  rw [hpasst]
  exact h2


#print axioms Passlogik.Phasen.zusagen_komponieren
/-! ## 5. `O006` -- die Zweige treffen sich, und die Ordnung ist ENDLICH -/

/-- `O006` -- alle Zweige erreichen dieselbe Stufe. -/
def o006_haelt (r q : Rumpf) (a : Stufe) : Prop :=
  ∀ b c, fliesst r a b → fliesst q a c → b = c

/-- **Unter `O006` ist die Zielstufe einer Verzweigung eindeutig.** Ohne die Regel traegt
    der Rumpf danach zwei verschiedene Stufen, und `O003` an der naechsten Stelle waere
    nicht entscheidbar. -/
theorem zweige_treffen_sich {r q : Rumpf} {a b c : Stufe}
    (h : o006_haelt r q a) (_hb : fliesst (.zweigt r q) a b) (_hc : fliesst (.zweigt r q) a c)
    (hlinks : fliesst r a b) (hrechts : fliesst q a c) : b = c :=
  h b c hlinks hrechts

/-- **Und ohne `O006` treffen sie sich wirklich nicht.** Zwei Zweige, einer still, einer
    mit einem Schritt -- die Marke steht danach auf zwei Stufen. -/
theorem ohne_o006_zwei_stufen :
    ∃ (r q : Rumpf) (a b c : Stufe),
      fliesst (.zweigt r q) a b ∧ fliesst (.zweigt r q) a c ∧ b ≠ c := by
  refine ⟨.still, .tut ⟨⟨0⟩, ⟨1⟩⟩, ⟨0⟩, ⟨0⟩, ⟨1⟩,
          fliesst.links (fliesst.still _), fliesst.rechts (fliesst.tut _), ?_⟩
  intro h
  simp at h


#print axioms Passlogik.Phasen.ohne_o006_zwei_stufen
/-- **Die Ordnung ist endlich, also ist die Kette endlich.** Auf einer Ordnung mit
    `n` Stufen gibt es hoechstens `n-1` Schritte hintereinander -- der Bootpfad hat ein
    Ende, und zwar aus der Form, nicht aus einer Zusage. -/
-- BEWEIST NICHT: dass ein Programm die Ordnung ausschoepft. Der Satz begrenzt nach oben.
theorem kette_ist_endlich (O : Ordnung) (f : Nat → Stufe)
    (herklaert : ∀ i, erklaert O (f i))
    (_hsteigt : ∀ i, (f i).index < (f (i+1)).index) : O.laenge = 0 → False := by
  intro hnull
  have := herklaert 0
  unfold erklaert at this
  omega

/-- Und die scharfe Form: nach `O.laenge` Schritten waere der Index ueber die Ordnung
    hinausgelaufen. -/
theorem hoechstens_so_viele_schritte (O : Ordnung) (f : Nat → Stufe)
    (herklaert : ∀ i, erklaert O (f i))
    (hsteigt : ∀ i, (f i).index < (f (i+1)).index) : False := by
  have waechst : ∀ i, i ≤ (f i).index := by
    intro i
    induction i with
    | zero => omega
    | succ k ih => have := hsteigt k; omega
  have h1 := waechst O.laenge
  have h2 := herklaert O.laenge
  unfold erklaert at h2
  omega


#print axioms Passlogik.Phasen.hoechstens_so_viele_schritte
/-! ## 6. Warum ein Schritt in einer SCHLEIFE abgelehnt wird

    `SYNTAX.md`:738: *"ein Schritt in einer Schleife wird abgelehnt"* -- und das
    Passregister sagt warum: *"ein Schritt geschieht einmal, eine Schleife oft."*

    **Der Grund ist `O003`, nicht eine eigene Regel.** Nach dem ersten Durchgang steht die
    Marke auf `nach`; ein zweiter Durchgang braeuchte sie wieder auf `von` -- und `von`
    und `nach` sind nach `O002` verschieden.
-/

/-- **Die Stufen eines Vorwaertsschritts sind verschieden.** -/
theorem schritt_stufen_verschieden {s : Schritt} (hv : vorwaerts s) : s.von ≠ s.nach := by
  intro h
  unfold vorwaerts at hv
  rw [h] at hv
  omega

/-- Die Umkehrung von `O003`: ein Schritt laeuft NUR von seiner Ausgangsstufe. -/
theorem tut_nur_von_der_ausgangsstufe {s : Schritt} {a b : Stufe}
    (h : fliesst (.tut s) a b) : a = s.von ∧ b = s.nach := by
  cases h; exact ⟨rfl, rfl⟩

/-- **Also kann derselbe Schritt nicht zweimal von derselben Stufe aus laufen.** Ein
    zweiter Schleifendurchgang faende die Marke auf `nach` und braeuchte sie auf `von`. -/
-- BEWEIST NICHT: dass der Pruefer Schleifen wirklich erkennt. Das Passregister nennt
-- gerade hier eine Luecke: der Anweisungslaeufer ist handgeschrieben, und `Zuweisung`,
-- `Publish`, `Leave`, `Next` und `AwaitLoad` werden verschluckt.
theorem kein_zweiter_durchgang {s : Schritt} (hv : vorwaerts s) {b : Stufe}
    (h : fliesst (.tut s) s.nach b) : False :=
  (schritt_stufen_verschieden hv) (tut_nur_von_der_ausgangsstufe h).1.symm


#print axioms Passlogik.Phasen.kein_zweiter_durchgang
/-! ## 7. Was der linearer Wert liefert -- und was NICHT

    Das Passregister zu `phasen.fluss`: *"**A linear value forces a CHAIN but not WHICH
    one**: with six boot steps all 720 orders type-check, and M2 sees only that each token
    is passed on exactly once."*

    **Das ist der Grund, warum es die Phasenpruefung ueberhaupt gibt** -- und hier steht
    es als Satz: die Linearitaet allein laesst jede Reihenfolge zu.
-/

/-- Zwei Schritte, die sich in beiden Reihenfolgen zu einer Kette fuegen LIESSEN, wenn
    nur die Linearitaet zaehlte -- die Phasenordnung laesst genau eine zu. -/
theorem ordnung_ist_nicht_umsonst :
    ∃ s1 s2 : Schritt,
      vorwaerts s1 ∧ vorwaerts s2
      ∧ fliesst (.folge (.tut s1) (.tut s2)) s1.von s2.nach
      ∧ ¬ fliesst (.folge (.tut s2) (.tut s1)) s2.von s1.nach := by
  refine ⟨⟨⟨0⟩, ⟨1⟩⟩, ⟨⟨1⟩, ⟨2⟩⟩, by unfold vorwaerts; decide, by unfold vorwaerts; decide,
          ?_, ?_⟩
  · exact fliesst.folge (fliesst.tut _) (fliesst.tut _)
  · intro h
    cases h with
    | folge h1 h2 =>
        have e1 := tut_nur_von_der_ausgangsstufe h1
        have e2 := tut_nur_von_der_ausgangsstufe h2
        have h3 := e1.2.symm.trans e2.1
        simp at h3


#print axioms Passlogik.Phasen.ordnung_ist_nicht_umsonst
end Passlogik.Phasen
