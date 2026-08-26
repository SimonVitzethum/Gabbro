/-
  Datei:      Passlogik/Linear.lean
  Gegenstand: M2 -- LINEAR heisst genau einmal, nicht hoechstens einmal.

  MODELLIERT WIRD
    Eine Anweisungssprache mit Verbrauchsstellen, Zweigen und einer Schleife; die
    Verbrauchszahl je Pfad; und die drei Regeln, die der Pass prueft (Folge addiert,
    Zweige gleichen ab, ein Wert von VOR der Schleife wird im Rumpf nicht verbraucht).
    Der Satz: unter diesen Regeln verbraucht JEDER Pfad genau so oft wie der Pass
    rechnet -- also genau einmal, wo der Pass eins rechnet.

  QUELLSAETZE
    dokumente/SPRACHE.md:758  -- "**Linear means linear, not affine:** a linear value is
                                 consumed exactly once. Dropping it is a compile error;
                                 `leave`/`return` from a scope holding linear values
                                 demands that they be named (`leaves`). There is no
                                 copying (E3)."
    gabbro paesse --je-satz   -- Satz `m2.linear-genau-einmal`:
        HOLDS: "A linear value that is a PARAMETER of the function, or is bound by
        `let x = f()` from a direct call, is consumed exactly once on every path the pass
        models: branches of an `if`/`match` are walked on copies and reconciled, a value
        living before a loop may not be consumed in its body, and neither zero
        consumptions (a leak) nor two (a use after its end) pass. **Real linearity is the
        one mechanism no existing tool supplies** -- Verus' `tracked` is AFFINE, Rust is
        affine, and affine forbids only the second use, never the missing one."
        BUT NOT: "consumption matches on the BASE NAME, so `wecken(p.feld)` counts as
        consuming `p`."
    gabbro paesse --je-satz   -- Satz `m2.leaves` (L106), `m2.geisterloeschung`

  ANGENOMMEN STATT BEWIESEN
    (L1) **Die Verbrauchsstellen sind gegeben.** Welche Anweisung eine ist, liest der Pass
         aus dem Rumpf. Das Passregister nennt dort mehrere Luecken: ein linearer
         Rueckgabewert an ANWEISUNGSPOSITION erzeugt gar keinen Eintrag, ein Rufargument
         wird nicht betreten, und der `_`-Arm des Anweisungslaeufers verschluckt
         `publish`, `exchange`, `narrow`, `await` und die Schleifenkoepfe. **Der Abstieg
         steht hier nicht** -- er ist die Klasse W16.
    (L2) **Divergenz.** Ein Zweig, der mit `return` oder `-> never` endet, schliesst sich
         nicht an. Der Pass hat dafuer eine schwaechere eigene Probe, die von Divergenz
         nichts weiss. Modelliert ist der Fall OHNE Divergenz.
    (L3) **Alias und Geisterloeschung sind ausdruecklich draussen.** Zwei Namen fuer
         dasselbe Objekt sind hier zwei Variablen; `m2.geisterloeschung` steht auf
         `CONJECTURED` und liegt im Erzeuger.
-/

namespace Passlogik.Linear

variable {V : Type u} [DecidableEq V]

/-! ## 1. Die Sprache und die Verbrauchszahl -/

/-- Eine Anweisung, soweit sie fuer die Linearitaet zaehlt. -/
inductive Anw (V : Type u) where
  | leer       : Anw V
  /-- Eine Verbrauchsstelle: `consumes x`, ein Ruf, der `x` verbraucht (L1). -/
  | verbraucht : V → Anw V
  | folge      : Anw V → Anw V → Anw V
  /-- `if` / `match` -- **zwei Zweige, auf Kopien gelaufen und abgeglichen**. -/
  | wenn       : Anw V → Anw V → Anw V
  /-- Eine Schleife. Ihr Rumpf laeuft null-, ein- oder mehrmals. -/
  | schleife   : Anw V → Anw V

/-- **Was ein PFAD wirklich verbraucht.** Nichtdeterministisch: die Relation beschreibt
    jeden moeglichen Durchlauf, mit der Zaehlfunktion je Variable. -/
inductive laeuft : Anw V → (V → Nat) → Prop where
  | leer : laeuft .leer (fun _ => 0)
  | verbraucht (x : V) : laeuft (.verbraucht x) (fun y => if y = x then 1 else 0)
  | folge {a b f g} : laeuft a f → laeuft b g → laeuft (.folge a b) (fun y => f y + g y)
  | links {a b f} : laeuft a f → laeuft (.wenn a b) f
  | rechts {a b f} : laeuft b f → laeuft (.wenn a b) f
  /-- Null Durchgaenge. -/
  | null {r} : laeuft (.schleife r) (fun _ => 0)
  /-- Ein Durchgang mehr. -/
  | mehr {r f g} : laeuft r f → laeuft (.schleife r) g →
      laeuft (.schleife r) (fun y => f y + g y)

/-- **Was der PASS rechnet.** Ein Zweig zaehlt wie sein linker Arm -- das ist nur richtig,
    wenn die Zweige abgeglichen sind, und genau das prueft `L104`. Eine Schleife zaehlt
    null -- das ist nur richtig, wenn ihr Rumpf nichts von vorher verbraucht. -/
def zaehlt : Anw V → V → Nat
  | .leer,         _ => 0
  | .verbraucht x, y => if y = x then 1 else 0
  | .folge a b,    y => zaehlt a y + zaehlt b y
  | .wenn a _,     y => zaehlt a y
  | .schleife _,   _ => 0

/-! ## 2. Was der Pass PRUEFT -- die zwei Bedingungen -/

/-- **`L104` -- der Zweigabgleich, und die Schleifenregel.**
    *"branches of an `if`/`match` are walked on copies and reconciled, a value living
    before a loop may not be consumed in its body"* -/
def abgeglichen : Anw V → Prop
  | .leer         => True
  | .verbraucht _ => True
  | .folge a b    => abgeglichen a ∧ abgeglichen b
  | .wenn a b     => abgeglichen a ∧ abgeglichen b ∧ ∀ y, zaehlt a y = zaehlt b y
  | .schleife r   => abgeglichen r ∧ ∀ y, zaehlt r y = 0

/-! ## 3. DER SATZ -/

/-- **Jeder Pfad verbraucht genau so oft, wie der Pass rechnet.** -/
-- BEWEIST NICHT (L1): dass `zaehlt` die Verbrauchsstellen richtig FINDET. Der Satz
-- spricht ueber die Baumform, nicht ueber den Anweisungsabstieg -- und der Abstieg ist
-- genau die Stelle, an der das Passregister mehrere Luecken nennt.
-- BEWEIST AUCH NICHT (L2): irgendetwas ueber divergierende Zweige. In diesem Modell
-- endet jeder Zweig; ein Zweig mit `return` verbraucht in Wirklichkeit gar nicht mehr
-- weiter, und der Abgleich muesste ihn AUSLASSEN statt gleichzusetzen.
theorem pfad_zaehlt_genau {s : Anw V} {f : V → Nat}
    (hab : abgeglichen s) (h : laeuft s f) : ∀ y, f y = zaehlt s y := by
  induction h with
  | leer => intro y; rfl
  | verbraucht x => intro y; rfl
  | folge _ _ iha ihb =>
      intro y
      obtain ⟨h1, h2⟩ := hab
      simp only [zaehlt, iha h1 y, ihb h2 y]
  | links _ ih =>
      intro y
      obtain ⟨h1, _, _⟩ := hab
      simp only [zaehlt, ih h1 y]
  | rechts _ ih =>
      intro y
      obtain ⟨_, h2, hgl⟩ := hab
      simp only [zaehlt, ← hgl y, ih h2 y]
  | null => intro y; rfl
  | mehr _ _ ihr ihs =>
      intro y
      obtain ⟨h1, hnull⟩ := hab
      have hr := ihr h1 y
      have hs := ihs ⟨h1, hnull⟩ y
      have hz := hnull y
      simp only [zaehlt] at *
      omega


#print axioms Passlogik.Linear.pfad_zaehlt_genau
/-- **GENAU EINMAL.** Rechnet der Pass fuer jeden linearen Wert eine `1`, so verbraucht
    ihn jeder Pfad genau einmal -- weder null (ein Leck) noch zwei (Gebrauch nach dem
    Ende). -/
theorem genau_einmal {s : Anw V} {f : V → Nat}
    (hab : abgeglichen s) (heins : ∀ y, zaehlt s y = 1) (h : laeuft s f) :
    ∀ y, f y = 1 := by
  intro y
  rw [pfad_zaehlt_genau hab h y, heins y]


#print axioms Passlogik.Linear.genau_einmal
/-! ## 4. Linear ist NICHT affin -- und der Unterschied ist der ganze Punkt

    `SPRACHE.md`:758 und das Passregister: *"Verus' `tracked` ist AFFIN, Rust ist affin,
    und affin verbietet nur den zweiten Gebrauch, nie den fehlenden."*
-/

/-- Was ein AFFINES System verlangt: hoechstens einmal. -/
def affin (s : Anw V) : Prop := ∀ y, zaehlt s y ≤ 1

/-- Was ein LINEARES System verlangt: genau einmal. -/
def linear (s : Anw V) : Prop := ∀ y, zaehlt s y = 1

/-- Linear ist strenger. -/
theorem linear_dann_affin {s : Anw V} (h : linear s) : affin s := by
  intro y; rw [h y]; omega

/-- **Und der Abstand ist genau das LECK.** Ein leerer Rumpf ist affin einwandfrei --
    er gebraucht nichts zweimal -- und laesst den linearen Wert fallen. *Das ist der
    Fehler, den kein affines System sieht.* -/
-- BEWEIST NICHT: dass Verus oder Rust ihn wirklich nicht sehen. Das ist eine Aussage
-- ueber fremde Werkzeuge und steht in `MESSUNGEN.md`, nicht hier. Was hier steht, ist
-- der Unterschied der beiden BEDINGUNGEN.
theorem affin_sieht_das_leck_nicht :
    ∃ s : Anw Nat, affin s ∧ ¬ linear s ∧ laeuft s (fun _ => 0) := by
  refine ⟨.leer, ?_, ?_, laeuft.leer⟩
  · intro y; simp [zaehlt]
  · intro h; have := h 0; simp [zaehlt] at this


#print axioms Passlogik.Linear.affin_sieht_das_leck_nicht
/-! ## 5. Warum der Zweigabgleich gebraucht wird

    Ohne `L104` waere `zaehlt (.wenn a b) = zaehlt a` schlicht falsch: der rechte Zweig
    kann etwas anderes tun. **Der Satz aus §3 faellt dann.**
-/

/-- Ein `if`, dessen linker Zweig verbraucht und dessen rechter nichts tut. -/
def unabgeglichen : Anw Nat := .wenn (.verbraucht 0) .leer

theorem unabgeglichen_faellt : ¬ abgeglichen unabgeglichen := by
  rintro ⟨_, _, hgl⟩
  have := hgl 0
  simp [zaehlt] at this

/-- **Und ohne den Abgleich stimmt die Rechnung nicht mehr.** Der Pass rechnet `1`, ein
    Pfad verbraucht `0` -- ein Leck, das durchgeht. -/
theorem ohne_abgleich_leck :
    ∃ f, laeuft unabgeglichen f ∧ f 0 ≠ zaehlt unabgeglichen 0 := by
  refine ⟨fun _ => 0, laeuft.rechts laeuft.leer, ?_⟩
  simp [zaehlt, unabgeglichen]


#print axioms Passlogik.Linear.ohne_abgleich_leck
/-! ## 6. Warum ein Wert von VOR der Schleife im Rumpf nicht verbraucht werden darf -/

/-- Eine Schleife, deren Rumpf verbraucht. -/
def schleife_verbraucht : Anw Nat := .schleife (.verbraucht 0)

theorem schleife_verbraucht_faellt : ¬ abgeglichen schleife_verbraucht := by
  rintro ⟨_, hnull⟩
  have := hnull 0
  simp [zaehlt] at this

/-- **Und der Grund ist der zweite Durchgang.** Zwei Durchgaenge verbrauchen zweimal --
    Gebrauch nach dem Ende. -/
theorem zwei_durchgaenge_verbrauchen_zweimal :
    ∃ f, laeuft schleife_verbraucht f ∧ f 0 = 2 := by
  refine ⟨fun y => (if y = 0 then 1 else 0) + ((if y = 0 then 1 else 0) + 0), ?_, ?_⟩
  · exact laeuft.mehr (laeuft.verbraucht 0)
      (laeuft.mehr (laeuft.verbraucht 0) laeuft.null)
  · simp


#print axioms Passlogik.Linear.zwei_durchgaenge_verbrauchen_zweimal
/-! ## 7. FUND: der Vergleich am BASISNAMEN

    Das Passregister zu `m2.linear-genau-einmal`: *"consumption matches on the BASE NAME,
    so `wecken(p.feld)` counts as consuming `p`."*

    **Was das kostet, steht hier als Satz:** zwei verschiedene lineare Orte mit demselben
    Basisnamen sind fuer den Pass EIN Wert. Der Pass rechnet `1`, und einer der beiden
    wird nie verbraucht.
-/

/-- Ein Ort: ein Basisname plus ein Feld. -/
structure Ort where
  basis : Nat
  feld  : Nat
deriving DecidableEq, Repr

/-- Was der Pass sieht: nur die Basis. -/
def vergroebert (s : Anw Ort) : Anw Nat :=
  match s with
  | .leer         => .leer
  | .verbraucht o => .verbraucht o.basis
  | .folge a b    => .folge (vergroebert a) (vergroebert b)
  | .wenn a b     => .wenn (vergroebert a) (vergroebert b)
  | .schleife r   => .schleife (vergroebert r)

/-- **Der Satz.** Es gibt ein Programm, in dem der vergroeberte Blick fuer die Basis `0`
    genau eine Verbrauchsstelle sieht -- waehrend der Ort `⟨0,1⟩` NIE verbraucht wird.
    *Ein Leck, das der Pass nicht sehen kann, weil er die Feldunterscheidung wegwirft.* -/
-- BEWEIST NICHT: dass daraus im Korpus ein Fehler folgt. Es ist eine Aussage ueber die
-- REGEL: die Vergroeberung ist eine Abstraktion, und sie geht in der unsicheren Richtung
-- verloren -- der Pass sieht eine `1`, wo die Wirklichkeit `1` und `0` hat.
theorem basisname_verwischt :
    ∃ s : Anw Ort,
      zaehlt (vergroebert s) 0 = 1
      ∧ zaehlt s ⟨0, 0⟩ = 1
      ∧ zaehlt s ⟨0, 1⟩ = 0 := by
  refine ⟨.verbraucht ⟨0, 0⟩, ?_, ?_, ?_⟩ <;> simp [vergroebert, zaehlt]


#print axioms Passlogik.Linear.basisname_verwischt
/-! ## 8. `leaves` -- was den Ausgang ueberlebt

    `SPRACHE.md`:758: *"`leave`/`return` aus einem Bereich, der lineare Werte haelt,
    verlangt, dass sie GENANNT werden (`leaves`)."*

    Der Pass prueft (`L106`), dass jeder Name in `leaves` ein PARAMETER ist und sein Typ
    linear -- und dass `leaves` NICHT verbraucht. Das ist eine Aussage ueber die
    Deklaration, nicht ueber den Pfad, und sie steht hier so.
-/

/-- `leaves` nennt Werte, die den Ausgang UEBERLEBEN -- es ist keine Verbrauchsstelle. -/
def leaves_verbraucht_nicht (_namen : List V) : Anw V := .leer

-- BEWEIST NICHT: dass die genannten Werte spaeter noch verbraucht WERDEN. `leaves`
-- verschiebt die Pflicht aus dem Bereich hinaus; wer sie draussen einloest, sagt diese
-- Datei nicht. Das Passregister nennt dazu die einzige gebaute Pruefung: nur PARAMETER
-- zaehlen als Bindung, ein `let`-gebundener linearer Wert in `leaves` wird gemeldet.
theorem leaves_ist_kein_verbrauch (namen : List V) (y : V) :
    zaehlt (leaves_verbraucht_nicht namen) y = 0 := rfl

end Passlogik.Linear
