/-
  Datei:      Passlogik/Rang.lean
  Gegenstand: Die RANGORDNUNG (`H006`) -- Nehmen unter echt kleinerem Rang schliesst
              zirkulaeres Warten aus.

  MODELLIERT WIRD
    Ein Zustand aus Faeden, die Sperren HALTEN und auf hoechstens eine WARTEN; die
    Rangdisziplin, die der Pass an jeder Nahmestelle herstellt; und die Verklemmung als
    geschlossene Wartekette. Bewiesen wird der klassische Schluss aus `messung/H006.md`
    §2 -- und daneben stehen die vier Raender aus §5 als eigene Saetze.

  QUELLSAETZE
    dokumente/SPRACHE.md:1272 -- `lockdecl = "lock" ident "protects" "{" placelist "}"
                                 "rank" constexpr [ "held" "<=" constexpr "ops" ] …`
    dokumente/SPRACHE.md:1278 -- "`rank`: taking demands a strictly smaller rank."
    messung/H006.md §1        -- "Endlich viele Sperren `L`, jede mit einem Rang
                                 `r(L) ∈ ℤ`. Ein Zustand ist eine Menge von Faeden, jeder
                                 haelt eine Menge von Sperren und wartet auf hoechstens
                                 eine. Eine Verklemmung ist ein zirkulaeres Warten:
                                 Faeden `T₁ … Tₙ` und Sperren `L₁ … Lₙ` mit `Tᵢ` haelt
                                 `Lᵢ₋₁` und wartet auf `Lᵢ` (zyklisch)."
    messung/H006.md §2        -- der Beweis, und `>=` statt `>`: "Gleichheit faellt mit"
    messung/H006.md §3        -- die drei Praemissen P1 (`H016`), P2 (`H014`), P3 (`H012`)
    messung/H006.md §5        -- die vier Raender
    messung/PASSREGISTER.md   -- `U005`, 2026-08-24: "der Modulpfad war leer: ein Rang als
                                 Modulkonstante loeste gar nicht auf, wurde `0`, und zwei
                                 Sperren mit VERSCHIEDENEN Raengen galten als gleich."

  ANGENOMMEN STATT BEWIESEN
    (R1) **Die Disziplin wird als Zustandsinvariante GEGEBEN.** Dass `geteilt.rs` sie an
         JEDER Nahmestelle herstellt -- also ueber alle Anweisungsformen absteigt, in
         Schleifenruempfe, in `match`-Zweige, in `observes`-Bloecke -- ist genau das, was
         `messung/H006.md` §6 als offenen Posten nennt: *"Das habe ich nicht Fall fuer Fall
         nachgesehen."* **Der Abstieg steht hier nicht.**
    (R2) Der Rang ist eine TOTALE Funktion `L → Int`. Dass er zur Uebersetzungszeit
         feststeht, ist `H014`; dass jeder Name erklaert ist, ist `H016`. §5 zeigt, was
         geschieht, wenn eine der beiden fehlt.
    (R3) Nur DEKLARIERTE Sperren. Ein Hardware-Handschlag, die interne Sperre eines
         fremden Rumpfs, eine Warteschlange -- alles das ist kein `lock` und faellt
         ausserhalb (§5b in `messung/H006.md`). §6 macht das als Satz sichtbar.
-/

namespace Passlogik.Rang

variable {T L : Type u}

/-! ## 1. Der Zustand -/

/-- Ein Zustand: wer haelt was, und wer wartet worauf.
    `messung/H006.md` §1, woertlich. -/
structure Zustand (T L : Type u) where
  haelt  : T → L → Prop
  wartet : T → Option L

/-- **Was der Pass herstellt** (`geteilt.rs::rangprobe`): an jeder Nahmestelle von `L`
    unter der gehaltenen Kette `C` gilt `r(M) < r(L)` fuer alle `M ∈ C`.

    Als Zustandsinvariante: wartet ein Faden auf `A` und haelt er `B`, so ist
    `r B < r A`. -/
def rangdisziplin (r : L → Int) (Z : Zustand T L) : Prop :=
  ∀ t A B, Z.wartet t = some A → Z.haelt t B → r B < r A

/-! ## 2. Die Wartekette und der Satz

    Ein Glied ist ein Paar (Faden, Sperre, auf die er wartet). Eine Kante geht vom Glied
    `p` zum Glied `q`, wenn `q`s Faden die Sperre haelt, auf die `p`s Faden wartet.
-/

/-- `Kette Z p s`: von Glied `p` fuehrt eine Wartekette zu Glied `s`. -/
inductive Kette (Z : Zustand T L) : (T × L) → (T × L) → Prop where
  | eins (p : T × L) : Z.wartet p.1 = some p.2 → Kette Z p p
  | mehr {p q s : T × L} :
      Z.wartet p.1 = some p.2 → Z.haelt q.1 p.2 → Kette Z q s → Kette Z p s

/-- Jedes Glied einer Kette WARTET -- sonst waere es kein Glied. -/
theorem kette_wartet {Z : Zustand T L} {p s : T × L} (h : Kette Z p s) :
    Z.wartet p.1 = some p.2 := by
  cases h with
  | eins _ hw => exact hw
  | mehr hw _ _ => exact hw

/-- Und das LETZTE Glied wartet ebenso -- die Kette endet nicht an einem freien Faden. -/
theorem kette_endet_wartend {Z : Zustand T L} {p s : T × L} (h : Kette Z p s) :
    Z.wartet s.1 = some s.2 := by
  induction h with
  | eins _ hw => exact hw
  | mehr _ _ _ ih => exact ih

/-- **Der Rang steigt laengs jeder Wartekette.** Das ist der Kern des klassischen
    Arguments: `r(L₁) < r(L₂) < … < r(Lₙ)`. -/
theorem rang_steigt {r : L → Int} {Z : Zustand T L}
    (hd : rangdisziplin r Z) {p s : T × L} (h : Kette Z p s) : r p.2 ≤ r s.2 := by
  induction h with
  | eins p _ => exact Int.le_refl _
  | mehr hw hh hk ih =>
      -- `q` haelt `p.2` und wartet auf `q.2`, also `r p.2 < r q.2`.
      have := hd _ _ _ (kette_wartet hk) hh
      omega

/-- ## DER SATZ

    **Eine Verklemmung ist unmoeglich.** Schliesst sich die Wartekette -- haelt also der
    ERSTE Faden die Sperre, auf die der LETZTE wartet --, so entsteht
    `r(L₁) < … < r(Lₙ) < r(L₁)`, ein Widerspruch in einer Totalordnung.

    `messung/H006.md` §2. -/
-- BEWEIST NICHT (R1): dass der Pruefer die Disziplin wirklich an jeder Nahmestelle
-- herstellt. `rangdisziplin` ist hier eine PRAEMISSE. Das ist genau der offene Posten,
-- den `messung/H006.md` §6 selbst nennt -- und es ist die Klasse W16, in der
-- `enthaelt_schritt` und die Wirkungshuelle schon einmal zu flach lasen.
-- BEWEIST AUCH NICHT: Fortschritt. "Keine Verklemmung" heisst nicht "jeder Faden kommt
-- dran" (`messung/H006.md` §5d). Aushungern ist eine andere Aussage, und sie steht in
-- keiner Zeile dieser Datei.
theorem keine_verklemmung {r : L → Int} {Z : Zustand T L}
    (hd : rangdisziplin r Z) {p s : T × L}
    (hk : Kette Z p s) (hschliesst : Z.haelt p.1 s.2) : False := by
  have h1 : r p.2 ≤ r s.2 := rang_steigt hd hk
  have h2 : r s.2 < r p.2 := hd _ _ _ (kette_wartet hk) hschliesst
  omega


#print axioms Passlogik.Rang.keine_verklemmung
/-- **Der Sonderfall, der mitfaellt:** ein Faden, der auf eine Sperre wartet, die er
    selbst haelt. Er ist die Kette der Laenge eins. -/
theorem kein_selbstwarten {r : L → Int} {Z : Zustand T L}
    (hd : rangdisziplin r Z) (t : T) (A : L)
    (hw : Z.wartet t = some A) (hh : Z.haelt t A) : False :=
  keine_verklemmung hd (Kette.eins (t, A) hw) hh


#print axioms Passlogik.Rang.kein_selbstwarten
/-! ## 3. Warum `>=` und nicht `>` -- Gleichheit faellt mit

    `messung/H006.md` §2: *"zwei Sperren gleichen Rangs stehen in keiner Ordnung, zwei
    Halter koennen sie in zwei Richtungen nehmen -- genau daher kommt eine Verklemmung."*

    Der Pass sagt bei `alt >= neu` ab. Waere die Regel `alt > neu` -- also "gleicher Rang
    ist erlaubt" --, gaebe es eine Verklemmung, und sie steht hier als Modell.
-/

/-- Die GELOCKERTE Disziplin: gleicher Rang waere erlaubt. -/
def rangdisziplin_lasch (r : L → Int) (Z : Zustand T L) : Prop :=
  ∀ t A B, Z.wartet t = some A → Z.haelt t B → r B ≤ r A

/-- Zwei Faeden, zwei Sperren. -/
inductive Zwei where | eins | zwei
deriving DecidableEq, Repr

/-- Der klassische Deadlock: `eins` haelt Sperre `eins` und wartet auf `zwei`,
    `zwei` haelt Sperre `zwei` und wartet auf `eins`. Beide Sperren haben Rang 7. -/
def kreuz : Zustand Zwei Zwei where
  haelt  := fun t A => t = A
  wartet := fun t => match t with | .eins => some .zwei | .zwei => some .eins

def gleicher_rang : Zwei → Int := fun _ => 7

theorem kreuz_erfuellt_lasch : rangdisziplin_lasch gleicher_rang kreuz := by
  intro t A B _ _; exact Int.le_refl _

/-- **Und `kreuz` ist eine Verklemmung.** Also traegt die gelockerte Regel den Satz
    nicht -- `>=` ist keine Vorsicht, sondern die Bedingung. -/
theorem lasch_laesst_verklemmung_zu :
    Kette kreuz (Zwei.eins, Zwei.zwei) (Zwei.zwei, Zwei.eins)
      ∧ kreuz.haelt Zwei.eins Zwei.eins := by
  constructor
  · exact Kette.mehr (q := (Zwei.zwei, Zwei.eins)) rfl rfl
      (Kette.eins (Zwei.zwei, Zwei.eins) rfl)
  · rfl


#print axioms Passlogik.Rang.lasch_laesst_verklemmung_zu
/-! ## 4. FUND: der Rueckfall auf `0` -- `U005`, gemessen am 2026-08-24

    `messung/PASSREGISTER.md`: *"der Modulpfad war leer: ein Rang als Modulkonstante loeste
    gar nicht auf, wurde `0`, und zwei Sperren mit VERSCHIEDENEN Raengen galten als gleich.
    Ein KORREKTES Programm fiel -- mit einer Zahl, die nirgends in seiner Quelle steht."*

    Der Ordner nennt die eine Richtung (ein korrektes Programm faellt). **Die andere ist
    schlimmer und steht hier:** derselbe Rueckfall macht die Disziplin fuer zwei
    unaufloesbare Raenge VAKUUM -- und dann geht eine Verklemmung durch.
-/

/-- Der Rang, wie er wirklich ist: eine PARTIELLE Funktion. Ein unbekannter Name hat
    keinen Rang -- `H016` sorgt dafuer, dass es ihn nicht gibt. -/
abbrev Rangtafel (L : Type u) := L → Option Int

/-- Der Rueckfall, der den Fehler trug: was nicht aufloest, wird `0`. -/
def rang_mit_null (t : Rangtafel L) : L → Int := fun A => (t A).getD 0

/-- **Der Satz.** Es gibt eine Rangtafel, unter der zwei verschiedene Sperren beide `0`
    lesen -- und dann erfuellt der Deadlock `kreuz` sogar die STRENGE Disziplin nicht,
    aber der Pass, der mit `rang_mit_null` rechnet, sieht keinen Unterschied zwischen
    ihnen. Formal: die beiden Raenge sind gleich, obwohl die Tafel sie nicht kennt. -/
-- BEWEIST NICHT: dass der heutige Pruefer so rechnet. Er tut es seit dem 2026-08-24
-- nicht mehr -- "der Rang bleibt ein `Option`; ein unbekannter Rang ist kein Rang, und
-- zwei davon sind nicht gleich". Was hier steht, ist WARUM diese Korrektur noetig war.
theorem null_rueckfall_verwischt :
    ∃ (t : Rangtafel Zwei) (A B : Zwei),
      A ≠ B ∧ t A = none ∧ t B = none ∧ rang_mit_null t A = rang_mit_null t B := by
  refine ⟨fun _ => none, .eins, .zwei, ?_, rfl, rfl, rfl⟩
  intro h; cases h


#print axioms Passlogik.Rang.null_rueckfall_verwischt
/-- **Die richtige Form:** ein unbekannter Rang ist KEIN Rang. Die Disziplin ueber einer
    partiellen Tafel verlangt, dass BEIDE Raenge dastehen. -/
def rangdisziplin_partiell (t : Rangtafel L) (Z : Zustand T L) : Prop :=
  ∀ th A B a b, Z.wartet th = some A → Z.haelt th B →
    t A = some a → t B = some b → b < a

/-- Und der Satz gilt weiter, sobald jeder Rang aufloest -- das ist `H016` + `H014`
    (Praemissen P1 und P2 aus `messung/H006.md` §3). -/
theorem keine_verklemmung_partiell {t : Rangtafel L} {Z : Zustand T L}
    (hvoll : ∀ A : L, ∃ a, t A = some a)
    (hd : rangdisziplin_partiell t Z) {p s : T × L}
    (hk : Kette Z p s) (hschliesst : Z.haelt p.1 s.2) : False := by
  -- Aus der vollstaendigen Tafel wird eine totale Rangfunktion, und §2 greift.
  refine keine_verklemmung (r := fun A => (t A).getD 0) ?_ hk hschliesst
  intro th A B hw hh
  obtain ⟨a, ha⟩ := hvoll A
  obtain ⟨b, hb⟩ := hvoll B
  have := hd th A B a b hw hh ha hb
  simp only [ha, hb, Option.getD]
  omega


#print axioms Passlogik.Rang.keine_verklemmung_partiell
/-! ## 5. Was der Satz NICHT deckt -- die Raender aus `messung/H006.md` §5

    ### 5a/5b -- nur DEKLARIERTE Sperren, und nur ueber vollstaendiger Huelle
-/

/-- Ein Zustand, in dem manche Sperren DEKLARIERT sind und andere nicht. Die Disziplin
    gilt nur ueber den deklarierten -- das ist (R3), und es ist keine Nachlaessigkeit,
    sondern die Reichweite der Sprache. -/
def rangdisziplin_nur_deklariert
    (r : L → Int) (deklariert : L → Prop) (Z : Zustand T L) : Prop :=
  ∀ t A B, deklariert A → deklariert B → Z.wartet t = some A → Z.haelt t B → r B < r A

/-- **Und darum ist die Klasse "Verklemmung" groesser als der Satz.** Es gibt einen
    Zustand, der die Disziplin ueber den deklarierten Sperren erfuellt und trotzdem
    verklemmt -- ueber zwei undeklarierten. -/
-- BEWEIST NICHT: dass das im Korpus vorkommt. Es ist eine Aussage ueber die REICHWEITE:
-- ein Warten, das keine `lock` ist -- ein Hardware-Handschlag, die interne Sperre eines
-- fremden Rumpfs --, liegt ausserhalb (`messung/H006.md` §5b).
theorem undeklarierte_sperren_bleiben_draussen :
    ∃ (deklariert : Zwei → Prop),
      rangdisziplin_nur_deklariert gleicher_rang deklariert kreuz
      ∧ Kette kreuz (Zwei.eins, Zwei.zwei) (Zwei.zwei, Zwei.eins)
      ∧ kreuz.haelt Zwei.eins Zwei.eins := by
  refine ⟨fun _ => False, ?_, ?_, rfl⟩
  · intro _ _ _ hA _ _ _; exact hA.elim
  · exact Kette.mehr (q := (Zwei.zwei, Zwei.eins)) rfl rfl
      (Kette.eins (Zwei.zwei, Zwei.eins) rfl)


#print axioms Passlogik.Rang.undeklarierte_sperren_bleiben_draussen
/-! ### 5c -- die Raenge sind ABSOLUTE Zahlen und komponieren nicht

    `messung/H006.md` §5c: *"wenn zwei Bibliotheken denselben Rang fuer unverwandte
    Sperren waehlen, entsteht kein Fehler, sondern eine FEHLENDE ORDNUNG."*
-/

/-- **Die Bedingung ist HINREICHEND, nicht notwendig.** Es gibt einen Zustand ohne jede
    Verklemmung, in dem die Rangdisziplin dennoch verletzt ist -- ein Programm, das der
    Pass absagt, obwohl nichts schiefgehen kann. *Das ist eine Vollstaendigkeitsluecke,
    keine Soundnessluecke.* -/
-- BEWEIST NICHT: dass «ABI2» (Ordnung statt Rang) sie schliesst. Der Ordner nennt das
-- als den Ort, an dem sie beantwortet wird; hier steht nur, dass sie existiert.
theorem rangregel_ist_nicht_notwendig :
    ∃ (Z : Zustand Unit Zwei) (r : Zwei → Int),
      ¬ rangdisziplin r Z
      ∧ (∀ p s : Unit × Zwei, Kette Z p s → ¬ Z.haelt p.1 s.2) := by
  -- Ein einziger Faden haelt Sperre `zwei` (Rang 7) und wartet auf `eins` (Rang 3).
  -- Der Rang laeuft ABWAERTS -- der Pass sagt ab. Verklemmen kann nichts: NIEMAND
  -- haelt `eins`, also schliesst sich keine Kette.
  refine ⟨⟨fun _ A => A = .zwei, fun _ => some .eins⟩,
          fun A => if A = .eins then 3 else 7, ?_, ?_⟩
  · intro h
    have := h () .eins .zwei rfl rfl
    simp at this
  · intro p s hk hc
    have h1 := kette_endet_wartend hk
    have h2 : Zwei.eins = s.2 := by injection h1
    have h3 : s.2 = Zwei.zwei := hc
    rw [← h2] at h3
    exact Zwei.noConfusion h3


#print axioms Passlogik.Rang.rangregel_ist_nicht_notwendig
/-! ## 6. Die Naht zu `Kosten.lean`: die gehaltene Kette ist WIEDERHOLUNGSFREI

    `SPRACHE.md`:1176 Punkt 4 rechnet die Wartezeit als SUMME der `held` ueber die
    hoeherrangigen Halter. Diese Summe ist nur dann eine Zahl, wenn keine Sperre zweimal
    in der Kette steht -- und genau das liefert der echt steigende Rang.
-/

/-- Die gehaltene Kette, in der Reihenfolge des Nehmens: jeder Rang ist echt kleiner als
    alle spaeteren. -/
def rangSteigend (r : L → Int) : List L → Prop
  | []      => True
  | a :: rest => (∀ b ∈ rest, r a < r b) ∧ rangSteigend r rest

/-- **Keine Sperre steht zweimal in der gehaltenen Kette.** -/
-- BEWEIST NICHT: dass die Kette ENDLICH ist. Ueber endlich vielen deklarierten Sperren
-- folgt das; der Typ `L` ist hier nicht als endlich verlangt, und der Satz sagt nur,
-- dass sich nichts wiederholt.
theorem kette_ohne_wiederholung {r : L → Int} {a : L} {rest : List L}
    (h : rangSteigend r (a :: rest)) : a ∉ rest := by
  intro hmem
  have := h.1 a hmem
  omega


#print axioms Passlogik.Rang.kette_ohne_wiederholung
/-- Und der Rang steigt auch ueber Zwischenglieder: die Kette ist transitiv geordnet. -/
theorem rangSteigend_schwanz {r : L → Int} {a : L} {rest : List L}
    (h : rangSteigend r (a :: rest)) : rangSteigend r rest := h.2

end Passlogik.Rang
