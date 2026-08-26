/-
  Datei:      Passlogik/Bereich.lean
  Gegenstand: Der BEREICHSVERBAND von M1 und die drei Flussregeln V1-V3.

  MODELLIERT WIRD
    Intervalle ueber ganzen Zahlen fester Breite, die abstrakten Operationen des Passes
    (`+`, `-`, `*`, unaeres Minus, Schnitt, Huelle), das Ueberlauf-Kriterium `M104`
    ("passt das gerechnete Intervall in den erklaerten Bereich des Ziels?") und die
    Verengungsregeln V1 (Bereichsbedingung) und V2 (Relation zwischen zwei Stellen).

  QUELLSAETZE
    dokumente/SPRACHE.md:641  -- `intty = ( "u8"|...|"i64" ) [ "in" range ]`,
                                 `range = expr ".." expr | expr "..<" expr`
    dokumente/SPRACHE.md:647  -- "Every operation must stay inside the range of its result
                                 type; if `a + b` does not fit the target, that is a
                                 compile error, not a runtime check. Division and remainder
                                 demand a denominator whose range excludes zero."
    dokumente/SPRACHE.md:651  -- 3.2 "The three flow rules -- closed, local, predictable":
                                 "syntax-directed, without fixpoint, without solver: the
                                 checker keeps a fact set per block that grows only at the
                                 three named places and dies on every write to a
                                 participating place."
    dokumente/SPRACHE.md:684  -- Tafel V1 / V2 / V3
    dokumente/SPRACHE.md:685  -- V2: "under the fact `a >= b`, `a - b` has type
                                 `0 .. a.max - b.min`, under `a > b` type
                                 `1 .. a.max - b.min`"
    dokumente/SPRACHE.md:688  -- ZWEITE VORBEDINGUNG (2026-08-20): eine Stelle durch ein
                                 `device`-Register traegt KEINEN Fakt.
    dokumente/SPRACHE.md:717  -- VORBEDINGUNG (2026-08-18): der `else`-Zweig setzt
                                 TRICHOTOMIE voraus.
    gabbro paesse --je-satz   -- Satz `m1.bereich`, `v1.bereichsverengung`,
                                 `v2.relationale-verengung`

  ANGENOMMEN STATT BEWIESEN
    (A1) Die Zielbreite wird als Intervall `[lo,hi]` GEGEBEN. Dass `u32` gerade
         `[0, 4294967295]` ist, ist eine Ablesung aus der Lexik und steht hier nicht.
    (A2) Die konkrete Semantik der Rechenoperationen ist die UNBESCHRAENKTE Rechnung
         ueber `Int`. Das ist genau die Modellwahl, die `messung/P6.md`:75 fuer die
         Pflichterzeugung getroffen hat ("Ganzzahlen sind `int`, unbeschraenkt") -- und
         sie ist hier tragend: der Satz `passt_dann_kein_ueberlauf` behauptet, dass die
         MATHEMATISCHE Summe im Zielbereich liegt. Dass die Maschine dann dasselbe
         rechnet, ist eine Aussage ueber den Erzeuger und steht NICHT hier.
    (A3) Stabilitaet einer Stelle (`stabil`) ist ein PRAEDIKAT, kein Beweis. Dass eine
         `device`-Registerstelle instabil ist, liest der Pass aus der Deklaration ab.
-/

namespace Passlogik.Bereich

/-! ## 0. Zwei Hilfsfunktionen, damit die Datei ohne `mathlib` steht -/

/-- Minimum ueber `Int`. Selbst definiert, weil diese Datei nichts importiert. -/
def imin (a b : Int) : Int := if a ≤ b then a else b
/-- Maximum ueber `Int`. -/
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imin_le_left (a b : Int) : imin a b ≤ a := by
  unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by
  unfold imin; split <;> omega
theorem le_imax_left (a b : Int) : a ≤ imax a b := by
  unfold imax; split <;> omega
theorem le_imax_right (a b : Int) : b ≤ imax a b := by
  unfold imax; split <;> omega
theorem le_imin {a b c : Int} (h1 : c ≤ a) (h2 : c ≤ b) : c ≤ imin a b := by
  unfold imin; split <;> omega
theorem imax_le {a b c : Int} (h1 : a ≤ c) (h2 : b ≤ c) : imax a b ≤ c := by
  unfold imax; split <;> omega

/-! ## 1. Der Traeger: ein Intervall -/

/-- Ein Intervall. `lo > hi` heisst LEER -- und leer ist eine echte Antwort des Passes,
    nicht ein Fehlerfall: sie sagt, dass der Zweig unerreichbar ist. -/
structure Iv where
  lo : Int
  hi : Int
deriving DecidableEq, Repr

namespace Iv

/-- Die KONKRETE Bedeutung eines abstrakten Werts: welche Zahlen er zulaesst. -/
def haelt (i : Iv) (x : Int) : Prop := i.lo ≤ x ∧ x ≤ i.hi

def leer (i : Iv) : Prop := i.hi < i.lo

theorem leer_haelt_nichts {i : Iv} (h : i.leer) (x : Int) : ¬ i.haelt x := by
  unfold leer at h; unfold haelt; omega

/-- Die Verbandsordnung, SEMANTISCH definiert: `a ⊑ b` heisst "a laesst nicht mehr zu". -/
def kleiner (a b : Iv) : Prop := ∀ x, a.haelt x → b.haelt x

theorem kleiner_refl (a : Iv) : kleiner a a := fun _ h => h
theorem kleiner_trans {a b c : Iv} (h1 : kleiner a b) (h2 : kleiner b c) : kleiner a c :=
  fun x h => h2 x (h1 x h)

/-- Die syntaktische Kennzeichnung der Ordnung -- gilt nur fuer ein NICHTLEERES `a`.
    *Fuer leeres `a` gilt `kleiner a b` immer, ohne dass die Ecken irgendetwas sagen;
    genau das ist der Grund, warum die Ordnung oben semantisch steht.* -/
theorem kleiner_syntaktisch {a b : Iv} (hne : a.lo ≤ a.hi) :
    kleiner a b ↔ (b.lo ≤ a.lo ∧ a.hi ≤ b.hi) := by
  constructor
  · intro h
    have h1 := h a.lo ⟨Int.le_refl _, hne⟩
    have h2 := h a.hi ⟨hne, Int.le_refl _⟩
    unfold haelt at h1 h2
    omega
  · intro h x hx
    unfold haelt at hx ⊢
    omega

end Iv

/-! ## 2. Die abstrakten Operationen, und ihre Korrektheit gegen die konkrete Semantik

    `SPRACHE.md`:647 -- jede Operation muss im Bereich ihres Ergebnistyps bleiben. Der
    Pass rechnet dafuer ein Intervall aus. Was hier bewiesen wird, ist die eine Richtung,
    auf die sich alles stuetzt: **das gerechnete Intervall UEBERDECKT die wahre Menge**.
-/

def add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩
def sub (a b : Iv) : Iv := ⟨a.lo - b.hi, a.hi - b.lo⟩

@[simp] theorem add_lo (a b : Iv) : (add a b).lo = a.lo + b.lo := rfl
@[simp] theorem add_hi (a b : Iv) : (add a b).hi = a.hi + b.hi := rfl
@[simp] theorem neg_lo (a : Iv) : (neg a).lo = -a.hi := rfl
@[simp] theorem neg_hi (a : Iv) : (neg a).hi = -a.lo := rfl
@[simp] theorem sub_lo (a b : Iv) : (sub a b).lo = a.lo - b.hi := rfl
@[simp] theorem sub_hi (a b : Iv) : (sub a b).hi = a.hi - b.lo := rfl

/-- Das Produkt ueber die VIER ECKEN. Das ist die uebliche Intervallarithmetik und
    zugleich die Form, die `beweise/Intervall_Aussen.thy` fuer die Summe schon fuehrt --
    dort steht ausdruecklich, dass der Satz fuer das Produkt "groesser ist und noch nicht
    dasteht" (`beweise/Intervall_Aussen.thy`:149). **Hier steht er.** -/
def mul (a b : Iv) : Iv :=
  let e1 := a.lo * b.lo
  let e2 := a.lo * b.hi
  let e3 := a.hi * b.lo
  let e4 := a.hi * b.hi
  ⟨imin (imin e1 e2) (imin e3 e4), imax (imax e1 e2) (imax e3 e4)⟩

/-- Der Schnitt -- das ist, was V1/V2/V3 mit einem Fakt tun. -/
def schnitt (a b : Iv) : Iv := ⟨imax a.lo b.lo, imin a.hi b.hi⟩

@[simp] theorem schnitt_lo (a b : Iv) : (schnitt a b).lo = imax a.lo b.lo := rfl
@[simp] theorem schnitt_hi (a b : Iv) : (schnitt a b).hi = imin a.hi b.hi := rfl

/-- Die Huelle -- das ist, was am Zusammenlauf zweier Zweige geschieht. -/
def huelle (a b : Iv) : Iv := ⟨imin a.lo b.lo, imax a.hi b.hi⟩

@[simp] theorem huelle_lo (a b : Iv) : (huelle a b).lo = imin a.lo b.lo := rfl
@[simp] theorem huelle_hi (a b : Iv) : (huelle a b).hi = imax a.hi b.hi := rfl

section Korrektheit
variable {a b : Iv} {x y : Int}

-- BEWEIST NICHT: dass die MASCHINE `x + y` rechnet. Der Satz spricht ueber die
-- unbeschraenkte Rechnung in `Int` (A2). Was die Absenkung daraus macht, ist
-- Sache des Erzeugers und steht in keiner Zeile dieser Datei.
theorem add_korrekt (hx : a.haelt x) (hy : b.haelt y) : (add a b).haelt (x + y) := by
  simp only [Iv.haelt, add_lo, add_hi] at *; omega


#print axioms Passlogik.Bereich.add_korrekt
-- BEWEIST NICHT: dass `-a` im Zielbereich liegt. Bei `i8` ist `-(-128)` genau der
-- Ueberlauf, den `passt` faengt -- dieser Satz sagt nur, wo die WAHRE Zahl liegt.
theorem neg_korrekt (hx : a.haelt x) : (neg a).haelt (-x) := by
  simp only [Iv.haelt, neg_lo, neg_hi] at *; omega

theorem sub_korrekt (hx : a.haelt x) (hy : b.haelt y) : (sub a b).haelt (x - y) := by
  simp only [Iv.haelt, sub_lo, sub_hi] at *; omega


#print axioms Passlogik.Bereich.sub_korrekt
-- BEWEIST NICHT: Schaerfe. Das Vier-Ecken-Intervall ist ueber ganzen Zahlen sogar
-- scharf, aber das ist ein zweiter Satz (er braucht die Fallunterscheidung nach
-- Vorzeichen) und er steht hier nicht -- nur die UEBERDECKUNG steht.
theorem mul_korrekt (hx : a.haelt x) (hy : b.haelt y) : (mul a b).haelt (x * y) := by
  obtain ⟨hxl, hxh⟩ := hx
  obtain ⟨hyl, hyh⟩ := hy
  -- Der Kern: `x*y` liegt zwischen zwei der vier Ecken. Ueber `Int` folgt das aus
  -- Monotonie der Multiplikation, aufgeteilt nach dem Vorzeichen von `y` bzw. `x`.
  have key : ∀ p q r s u v : Int, p ≤ u → u ≤ q → r ≤ v → v ≤ s →
      (imin (imin (p*r) (p*s)) (imin (q*r) (q*s)) ≤ u*v
       ∧ u*v ≤ imax (imax (p*r) (p*s)) (imax (q*r) (q*s))) := by
    intro p q r s u v hpu huq hrv hvs
    -- Beide Richtungen aus: u*v liegt zwischen p*v und q*v, und p*v bzw q*v
    -- zwischen den jeweiligen Ecken.
    have hpv_qv : (p*v ≤ u*v ∧ u*v ≤ q*v) ∨ (q*v ≤ u*v ∧ u*v ≤ p*v) := by
      rcases Int.lt_or_le v 0 with hv | hv
      · right
        constructor
        · exact Int.mul_le_mul_of_nonpos_right huq (Int.le_of_lt hv)
        · exact Int.mul_le_mul_of_nonpos_right hpu (Int.le_of_lt hv)
      · left
        constructor
        · exact Int.mul_le_mul_of_nonneg_right hpu hv
        · exact Int.mul_le_mul_of_nonneg_right huq hv
    have hp : (p*r ≤ p*v ∧ p*v ≤ p*s) ∨ (p*s ≤ p*v ∧ p*v ≤ p*r) := by
      rcases Int.lt_or_le p 0 with hp0 | hp0
      · right
        exact ⟨Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hp0) hvs,
               Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hp0) hrv⟩
      · left
        exact ⟨Int.mul_le_mul_of_nonneg_left hrv hp0,
               Int.mul_le_mul_of_nonneg_left hvs hp0⟩
    have hq : (q*r ≤ q*v ∧ q*v ≤ q*s) ∨ (q*s ≤ q*v ∧ q*v ≤ q*r) := by
      rcases Int.lt_or_le q 0 with hq0 | hq0
      · right
        exact ⟨Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hq0) hvs,
               Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hq0) hrv⟩
      · left
        exact ⟨Int.mul_le_mul_of_nonneg_left hrv hq0,
               Int.mul_le_mul_of_nonneg_left hvs hq0⟩
    have l1 := imin_le_left (imin (p*r) (p*s)) (imin (q*r) (q*s))
    have l2 := imin_le_right (imin (p*r) (p*s)) (imin (q*r) (q*s))
    have l3 := imin_le_left (p*r) (p*s)
    have l4 := imin_le_right (p*r) (p*s)
    have l5 := imin_le_left (q*r) (q*s)
    have l6 := imin_le_right (q*r) (q*s)
    have u1 := le_imax_left (imax (p*r) (p*s)) (imax (q*r) (q*s))
    have u2 := le_imax_right (imax (p*r) (p*s)) (imax (q*r) (q*s))
    have u3 := le_imax_left (p*r) (p*s)
    have u4 := le_imax_right (p*r) (p*s)
    have u5 := le_imax_left (q*r) (q*s)
    have u6 := le_imax_right (q*r) (q*s)
    rcases hpv_qv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hp with ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
      rcases hq with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> omega
  exact key a.lo a.hi b.lo b.hi x y hxl hxh hyl hyh


#print axioms Passlogik.Bereich.mul_korrekt
-- BEWEIST NICHT: dass der Schnitt die BESTE gemeinsame Verengung ist (das ist
-- `schnitt_ist_infimum` unten). Hier steht nur, dass er genau die Zahlen haelt,
-- die beide halten.
theorem schnitt_genau (a b : Iv) (x : Int) :
    (schnitt a b).haelt x ↔ (a.haelt x ∧ b.haelt x) := by
  simp only [Iv.haelt, schnitt_lo, schnitt_hi]
  constructor
  · intro ⟨h1, h2⟩
    have := le_imax_left a.lo b.lo
    have := le_imax_right a.lo b.lo
    have := imin_le_left a.hi b.hi
    have := imin_le_right a.hi b.hi
    omega
  · intro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨imax_le h1 h3, le_imin h2 h4⟩


#print axioms Passlogik.Bereich.schnitt_genau
theorem huelle_deckt_links (a b : Iv) (x : Int) (h : a.haelt x) : (huelle a b).haelt x := by
  simp only [Iv.haelt, huelle_lo, huelle_hi] at *
  have := imin_le_left a.lo b.lo
  have := le_imax_left a.hi b.hi
  omega

theorem huelle_deckt_rechts (a b : Iv) (x : Int) (h : b.haelt x) : (huelle a b).haelt x := by
  simp only [Iv.haelt, huelle_lo, huelle_hi] at *
  have := imin_le_right a.lo b.lo
  have := le_imax_right a.hi b.hi
  omega

end Korrektheit

/-! ## 3. Monotonie -- der Verband ist geordnet und die Operationen achten die Ordnung

    Warum das zaehlt: der Pass verengt (V1/V2/V3) und rechnet dann weiter. Ohne
    Monotonie koennte eine SCHAERFERE Eingabe ein SCHLECHTERES Ergebnis liefern, und
    dann waere jede Verengung ein Gluecksspiel.
-/

-- BEWEIST NICHT: Monotonie in der SYNTAKTISCHEN Ordnung. Die Aussage steht ueber
-- `Iv.kleiner`, also semantisch; fuer ein leeres Argument ist sie darum trivial wahr
-- und sagt nichts.
theorem add_monoton {a a' b b' : Iv}
    (ha : Iv.kleiner a a') (hb : Iv.kleiner b b')
    (hane : a.lo ≤ a.hi) (hbne : b.lo ≤ b.hi) :
    Iv.kleiner (add a b) (add a' b') := by
  rw [Iv.kleiner_syntaktisch hane] at ha
  rw [Iv.kleiner_syntaktisch hbne] at hb
  intro x hx
  simp only [Iv.haelt, add_lo, add_hi] at hx ⊢
  omega


#print axioms Passlogik.Bereich.add_monoton
theorem sub_monoton {a a' b b' : Iv}
    (ha : Iv.kleiner a a') (hb : Iv.kleiner b b')
    (hane : a.lo ≤ a.hi) (hbne : b.lo ≤ b.hi) :
    Iv.kleiner (sub a b) (sub a' b') := by
  rw [Iv.kleiner_syntaktisch hane] at ha
  rw [Iv.kleiner_syntaktisch hbne] at hb
  intro x hx
  simp only [Iv.haelt, sub_lo, sub_hi] at hx ⊢
  omega

-- BEWEIST NICHT: dass der Schnitt der GROESSTE untere Nachbar im syntaktischen Sinn
-- ist. Semantisch ist er es, und das steht hier.
theorem schnitt_ist_infimum {a b c : Iv} :
    (Iv.kleiner c a ∧ Iv.kleiner c b) ↔ Iv.kleiner c (schnitt a b) := by
  constructor
  · intro ⟨h1, h2⟩ x hx
    exact (schnitt_genau a b x).mpr ⟨h1 x hx, h2 x hx⟩
  · intro h
    exact ⟨fun x hx => ((schnitt_genau a b x).mp (h x hx)).1,
           fun x hx => ((schnitt_genau a b x).mp (h x hx)).2⟩

theorem schnitt_monoton {a a' b b' : Iv}
    (ha : Iv.kleiner a a') (hb : Iv.kleiner b b') :
    Iv.kleiner (schnitt a b) (schnitt a' b') := by
  intro x hx
  have := (schnitt_genau a b x).mp hx
  exact (schnitt_genau a' b' x).mpr ⟨ha x this.1, hb x this.2⟩

/-! ## 4. Terminierung der Verengung

    `SPRACHE.md`:651 sagt: **"syntax-directed, without fixpoint, without solver"**. Die
    Terminierung ist damit nicht die eines Fixpunkts, sondern die einer ABSTEIGENDEN
    KETTE: ein Fakt verengt, ein Schreiben loescht. Was zu zeigen ist: eine Kette echt
    verengender Schritte ist ENDLICH -- sonst koennte ein Block den Pass haengen lassen.
-/

/-- Das Mass: wie viele Zahlen das Intervall zulaesst. Fuer ein leeres Intervall `0`. -/
def weite (i : Iv) : Nat := (i.hi - i.lo + 1).toNat

/-- Ein ECHTER Verengungsschritt: kleiner, und nicht wieder dasselbe. -/
def echt_enger (a b : Iv) : Prop :=
  Iv.kleiner a b ∧ ¬ Iv.kleiner b a

-- BEWEIST NICHT: dass der Pass wirklich nur echt verengt. Ein Schritt, der nichts
-- aendert, ist erlaubt und kostet nur Zeit -- die Terminierung haengt daran, dass die
-- ANZAHL der Schritte syntaktisch beschraenkt ist (der Pass laeuft ueber den Baum).
-- Dieser Satz liefert die zweite, unabhaengige Schranke.
theorem echt_enger_faellt {a b : Iv} (hbne : b.lo ≤ b.hi) (h : echt_enger a b) :
    weite a < weite b := by
  obtain ⟨hle, hnle⟩ := h
  by_cases hane : a.lo ≤ a.hi
  · rw [Iv.kleiner_syntaktisch hane] at hle
    unfold weite
    -- `¬ kleiner b a` heisst: es gibt ein `x` in `b`, das nicht in `a` ist.
    have : ¬ (a.lo ≤ b.lo ∧ b.hi ≤ a.hi) := by
      intro hc
      exact hnle ((Iv.kleiner_syntaktisch hbne).mpr hc)
    omega
  · -- `a` ist leer: `weite a = 0`, und `b` ist nichtleer, also `weite b ≥ 1`.
    unfold weite
    omega

/-- Es gibt keine unendliche echt verengende Kette. **Das ist die Terminierung.** -/
-- BEWEIST NICHT: die Terminierung des GESAMTEN Passes. Der Pass steigt ueber den
-- Syntaxbaum ab, und dass dieser Abstieg endet, ist eine Aussage ueber den Baum, nicht
-- ueber den Verband. Was hier steht, ist die Terminierung der VERENGUNG -- die eine
-- Stelle, an der ein Verband ueberhaupt haengen koennte.
theorem keine_unendliche_verengung
    (f : Nat → Iv)
    (hne : ∀ n, (f n).lo ≤ (f n).hi)
    (hab : ∀ n, echt_enger (f (n+1)) (f n)) : False := by
  have schritt : ∀ n, weite (f (n+1)) < weite (f n) := fun n =>
    echt_enger_faellt (hne n) (hab n)
  have fall : ∀ n, weite (f n) + n ≤ weite (f 0) := by
    intro n
    induction n with
    | zero => omega
    | succ k ih => have := schritt k; omega
  have := fall (weite (f 0) + 1)
  omega


#print axioms Passlogik.Bereich.keine_unendliche_verengung
/-! ## 5. Das Ueberlauf-Kriterium -- `M104`

    `SPRACHE.md`:647: "if `a + b` does not fit the target, that is a **compile error, not
    a runtime check**." Der Pass prueft also eine Aussage ueber INTERVALLE und laesst
    daraus eine Aussage ueber WERTE folgen. Genau dieser Schluss steht hier.
-/

/-- Der erklaerte Bereich eines Ziels. `SPRACHE.md`:641 -- `u32 in 1..7` etc. -/
abbrev Ziel := Iv

/-- Was der Pass entscheidet: passt das gerechnete Intervall in den Zielbereich?
    **Entscheidbar, ohne Solver** -- zwei Vergleiche. -/
def passt (i : Iv) (z : Ziel) : Bool :=
  decide (z.lo ≤ i.lo) && decide (i.hi ≤ z.hi)

/-- **Der Satz zu `M104`.** Sagt der Pass "passt", so liegt jeder wirkliche Wert im
    erklaerten Bereich des Ziels -- es gibt keinen Ueberlauf und keine schneidende
    Breitenaenderung. -/
-- BEWEIST NICHT: die Umkehrung. `passt` ist HINREICHEND, nicht notwendig: ein Programm,
-- dessen Werte alle im Ziel liegen, dessen gerechnetes Intervall aber ueberschiesst,
-- wird abgesagt. Das ist die gewollte Richtung -- der Pass irrt laut, nicht still --
-- und es ist der Grund, warum `narrow` als Ausweg existiert (`SPRACHE.md`:735).
theorem passt_dann_kein_ueberlauf {i : Iv} {z : Ziel} {x : Int}
    (hp : passt i z = true) (hx : i.haelt x) : z.haelt x := by
  unfold passt at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  unfold Iv.haelt at hx ⊢
  omega


#print axioms Passlogik.Bereich.passt_dann_kein_ueberlauf
/-- **Die zusammengesetzte Form**, so wie der Pass sie an einer Zuweisung `z := a + b`
    wirklich fragt. -/
theorem summe_passt_dann_kein_ueberlauf {a b : Iv} {z : Ziel} {x y : Int}
    (hp : passt (add a b) z = true) (hx : a.haelt x) (hy : b.haelt y) :
    z.haelt (x + y) :=
  passt_dann_kein_ueberlauf hp (add_korrekt hx hy)

theorem produkt_passt_dann_kein_ueberlauf {a b : Iv} {z : Ziel} {x y : Int}
    (hp : passt (mul a b) z = true) (hx : a.haelt x) (hy : b.haelt y) :
    z.haelt (x * y) :=
  passt_dann_kein_ueberlauf hp (mul_korrekt hx hy)

/-! ### 5.1 Die Division -- die eine Operation mit einer eigenen Vorbedingung

    `SPRACHE.md`:647: "Division and remainder demand a denominator whose range excludes
    zero." Der Pass prueft das am INTERVALL des Nenners.
-/

/-- Der Pass laesst eine Division zu, wenn das Nennerintervall die Null nicht enthaelt. -/
def nenner_ok (b : Iv) : Bool := decide (0 < b.lo) || decide (b.hi < 0)

-- BEWEIST NICHT: irgendetwas ueber den WERT des Quotienten. Nur, dass die Division
-- ueberhaupt definiert ist. Das Ergebnisintervall einer Division ueber Ganzzahlen
-- braucht die Rundungsrichtung, und die ist in `messung/P6.md`:85 ausdruecklich ALS
-- ABGESAGT gebucht ("Isabelles `div` auf `int` rundet gegen minus unendlich, C
-- schneidet gegen null ab"). Dieselbe Absage gilt hier, und aus demselben Grund.
theorem nenner_ok_dann_nicht_null {b : Iv} {y : Int}
    (h : nenner_ok b = true) (hy : b.haelt y) : y ≠ 0 := by
  unfold nenner_ok at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  unfold Iv.haelt at hy
  omega


#print axioms Passlogik.Bereich.nenner_ok_dann_nicht_null
/-! ## 6. V1 -- die Bereichsverengung

    `SPRACHE.md`:684: "a checked **range condition** narrows the range of the checked
    place in the branch after it".

    **Und die zwei Vorbedingungen stehen im Modell, nicht in einer Fussnote:**
    * `stabil` -- eine Stelle durch ein `device`-Register bleibt zwischen Pruefung und
      Verwendung nicht dieselbe (`SPRACHE.md`:688, «B33»).
    * Trichotomie -- der `else`-Zweig setzt sie voraus (`SPRACHE.md`:717). Ueber `Int`
      gilt sie; §7 zeigt, wo sie bricht.
-/

/-- Eine Stelle im Programm, abstrakt. -/
structure Ort where
  id : Nat
deriving DecidableEq, Repr

/-- `stabil o` heisst: der Wert von `o` aendert sich zwischen zwei Lesungen nicht von
    selbst. Der Pass liest das aus der Deklaration ab -- eine `device`-Registerstelle
    ist NICHT stabil (`SPRACHE.md`:688). -/
abbrev Stabil := Ort → Prop

/-- Die Verengung nach oben: `if x >= k` -/
def verenge_ge (i : Iv) (k : Int) : Iv := schnitt i ⟨k, i.hi⟩
/-- Die Gegenrichtung im `else`: `x < k`, also `x <= k-1` -/
def verenge_lt (i : Iv) (k : Int) : Iv := schnitt i ⟨i.lo, k - 1⟩

/-- **V1, der Ja-Zweig.** Steht der Wert im Intervall und gilt die gepruefte Bedingung,
    so steht er im verengten Intervall. -/
-- BEWEIST NICHT: dass der Wert bei der VERWENDUNG noch derselbe ist. Das ist genau die
-- Vorbedingung `stabil`, und sie steht im Satz `v1_traegt_nur_stabil` unten. Fuer sich
-- genommen ist dieser Satz reine Intervallrechnung.
theorem v1_ja {i : Iv} {k x : Int} (hx : i.haelt x) (hb : k ≤ x) :
    (verenge_ge i k).haelt x := by
  unfold verenge_ge
  exact (schnitt_genau _ _ _).mpr ⟨hx, ⟨hb, hx.2⟩⟩


#print axioms Passlogik.Bereich.v1_ja
/-- **V1, der Nein-Zweig.** Er braucht die Trichotomie -- ueber `Int` ist sie da. -/
theorem v1_nein {i : Iv} {k x : Int} (hx : i.haelt x) (hb : ¬ (k ≤ x)) :
    (verenge_lt i k).haelt x := by
  unfold verenge_lt
  refine (schnitt_genau _ _ _).mpr ⟨hx, ?_⟩
  simp only [Iv.haelt] at hx ⊢
  omega


#print axioms Passlogik.Bereich.v1_nein
/-- **Beide Zweige zusammen verlieren nichts.** Das ist die Aussage, die eine Verengung
    von einer Verfaelschung unterscheidet: was vorher galt, gilt in einem der beiden
    Zweige weiter. -/
theorem v1_zweige_decken_ab {i : Iv} {k x : Int} (hx : i.haelt x) :
    (verenge_ge i k).haelt x ∨ (verenge_lt i k).haelt x := by
  by_cases h : k ≤ x
  · exact Or.inl (v1_ja hx h)
  · exact Or.inr (v1_nein hx h)


#print axioms Passlogik.Bereich.v1_zweige_decken_ab
/-- **Und die Verengung ist wirklich eine:** das verengte Intervall laesst nicht mehr
    zu als das alte. -/
theorem v1_verengt {i : Iv} {k : Int} : Iv.kleiner (verenge_ge i k) i := by
  intro x hx
  exact ((schnitt_genau _ _ _).mp hx).1

/-- **Die Vorbedingung, formuliert.** Ein Fakt traegt von der Pruefstelle zur
    Verwendungsstelle nur, wenn die Stelle DIESELBE bleibt.

    `SPRACHE.md`:688 -- und bis zum 2026-08-20 tat der Pruefer das Gegenteil: das
    erzeugte C indizierte ein Feld mit acht Plaetzen mit einem Wert, den die Hardware
    zwischen den beiden Zeilen frei setzen darf. -/
-- BEWEIST NICHT: dass `stabil` fuer irgendeine konkrete Stelle GILT. Das ist eine
-- Ablesung aus der Deklaration, kein Satz. Was hier steht, ist die Buchung: ohne
-- `stabil` ist `wert_bei_pruefung = wert_bei_verwendung` keine Praemisse, die man hat.
theorem v1_traegt_nur_stabil
    {i : Iv} {k : Int} {o : Ort} {stabil : Stabil}
    (wert_bei : Ort → Nat → Int)          -- der Wert der Stelle zum Zeitpunkt n
    (unveraenderlich : ∀ p, stabil p → ∀ m n, wert_bei p m = wert_bei p n)
    (hstab : stabil o)
    (hx : i.haelt (wert_bei o 0))         -- was bei der Pruefung galt
    (hb : k ≤ wert_bei o 0)               -- die geprueften Bedingung
    : (verenge_ge i k).haelt (wert_bei o 1) := by   -- was bei der Verwendung gilt
  have : wert_bei o 1 = wert_bei o 0 := unveraenderlich o hstab 1 0
  rw [this]
  exact v1_ja hx hb


#print axioms Passlogik.Bereich.v1_traegt_nur_stabil
/-! ## 7. Wo V1 BRICHT -- der `else`-Zweig ohne Trichotomie

    `SPRACHE.md`:717: "Die Verengung im `else`-Zweig setzt voraus, dass die Negation
    einer Vergleichsbedingung selbst eine Vergleichsbedingung ist -- also eine
    **totale Ordnung ohne unvergleichbare Elemente**. [...] Ist ein Operand NaN, sind
    *alle* Vergleiche falsch, und der `else`-Zweig gibt **nichts**. Vier Ausgaenge statt
    drei."

    Der Ordner nennt die Regel "sichtbar falsifizierbar". **Hier ist die Falsifikation
    als Satz**, an einem Traeger mit genau einem unvergleichbaren Element.
-/

/-- Ein Traeger mit einem unvergleichbaren Element -- das Modell von NaN, so klein wie
    es sein kann. -/
inductive PWert where
  | zahl : Int → PWert
  | nan  : PWert
deriving DecidableEq, Repr

/-- Der Vergleich, wie IEEE-754 ihn fuehrt: JEDER Vergleich mit NaN ist falsch. -/
def ple : PWert → PWert → Bool
  | .zahl a, .zahl b => decide (a ≤ b)
  | _, _ => false

/-- Ueber `Int` gilt Trichotomie -- das ist die Praemisse, unter der V1s `else` traegt. -/
theorem trichotomie_ueber_int (a b : Int) : a ≤ b ∨ b ≤ a := by omega

/-- **Und hier bricht sie.** Es gibt einen Wert, fuer den WEDER `x <= k` NOCH `k <= x`
    gilt -- der `else`-Zweig einer Pruefung `x <= k` gibt dann NICHT den Fakt `k <= x`.
    Ein Pass, der ihn dort setzte, waere unsound. -/
-- BEWEIST NICHT: dass Gabbros Gleitkommazweig HEUTE falsch rechnet. Der Pass verengt
-- ueber `f64` gar nicht in dieser Form -- `m1.endlichkeit` traegt nur den
-- Endlichkeitsfakt. Was hier steht, ist die Praezisierung dessen, was `SPRACHE.md`:717
-- als Bedingung nennt: die Regel ist an EINEM Punkt falsifizierbar, und der Punkt ist
-- konstruiert.
theorem trichotomie_bricht : ∃ x k : PWert, ple x k = false ∧ ple k x = false :=
  ⟨PWert.nan, PWert.zahl 0, rfl, rfl⟩


#print axioms Passlogik.Bereich.trichotomie_bricht
/-- **Die Folge, ausgeschrieben:** unter einem solchen Traeger gibt es vier Ausgaenge,
    nicht drei -- `<`, `=`, `>` und "unvergleichbar". -/
theorem vier_ausgaenge : ∃ x k : PWert, ¬ (ple x k = true ∨ ple k x = true) := by
  refine ⟨PWert.nan, PWert.zahl 0, ?_⟩
  simp [ple]

/-! ## 8. V2 -- die relationale Verengung

    `SPRACHE.md`:685: "under the fact `a >= b`, `a - b` has type `0 .. a.max - b.min`,
    under `a > b` type `1 .. a.max - b.min`."

    **Das ist der Satz des Passregisters mit der groessten Last und der geringsten
    Messung** -- `v2.relationale-verengung` steht auf `CONJECTURED`, weil die Regel
    ERWEITERT, was durchgeht, und darum keine eigene Absagekennung hat. *Er laesst sich
    nicht vergiften; beweisen laesst er sich.*
-/

/-- Was der Pass unter dem Fakt `a >= b` fuer `a - b` ausrechnet. -/
def sub_unter_ge (a b : Iv) : Iv := ⟨0, a.hi - b.lo⟩
/-- Und unter dem Fakt `a > b`. -/
def sub_unter_gt (a b : Iv) : Iv := ⟨1, a.hi - b.lo⟩

/-- **V2, Haelfte A.** -/
-- BEWEIST NICHT: die drei anderen Einschraenkungen aus dem Passregister. (1) Nur
-- DIREKT gepruefte Stellen -- `a >= b + 1` traegt nichts. (2) Ein Fakt stirbt an jedem
-- Schreiben auf eine beteiligte Stelle. (3) Ein Schreiben DURCH EINEN ZEIGER toetet
-- jeden nichtlokalen Fakt, weil es keine Aliasanalyse gibt. Punkt (3) ist der, den
-- `messung/V2.md` §4d als "explizit UNVERIFIZIERT" fuehrt, und er ist kein
-- Intervallsatz, sondern einer ueber Speicher -- er steht deshalb hier NICHT.
theorem v2_ge {a b : Iv} {x y : Int}
    (hx : a.haelt x) (hy : b.haelt y) (hf : y ≤ x) :
    (sub_unter_ge a b).haelt (x - y) := by
  simp only [Iv.haelt, sub_unter_ge] at *; omega


#print axioms Passlogik.Bereich.v2_ge
/-- **V2, Haelfte B.** -/
theorem v2_gt {a b : Iv} {x y : Int}
    (hx : a.haelt x) (hy : b.haelt y) (hf : y < x) :
    (sub_unter_gt a b).haelt (x - y) := by
  simp only [Iv.haelt, sub_unter_gt] at *; omega


#print axioms Passlogik.Bereich.v2_gt
/-- **Warum V2 ueberhaupt gebraucht wird, als Satz.** Ohne den relationalen Fakt liefert
    die gewoehnliche Intervallsubtraktion eine untere Schranke, die NEGATIV sein kann --
    und ueber einem vorzeichenlosen Ziel ist das die Absage `M104`. Mit dem Fakt ist die
    untere Schranke `0`. *Das ist "die Regel, die `narrow` davor bewahrt, ein Ritual zu
    werden" (`SPRACHE.md`:685), praezise gemacht.* -/
theorem v2_kauft_etwas :
    ∃ a b : Iv, (sub a b).lo < 0 ∧ (sub_unter_ge a b).lo = 0 := by
  refine ⟨⟨0, 10⟩, ⟨0, 10⟩, ?_, ?_⟩ <;> decide

/-! ### 8.1 FUND: "hat den Typ" oder "wird geschnitten mit"? -- eine Mehrdeutigkeit

    `SPRACHE.md`:685 schreibt: *unter dem Fakt `a >= b` **hat** `a - b` den Typ
    `0 .. a.max - b.min`*. Woertlich gelesen ERSETZT die Regel das gewoehnlich gerechnete
    Intervall. Das ist sound (§8 oben), aber es ist NICHT immer eine Verengung:
-/

/-- **Der Gegenfall.** Fuer `a = [10,10]`, `b = [0,0]` liefert die gewoehnliche
    Subtraktion die exakte Antwort `[10,10]`; die woertlich gelesene V2-Regel liefert
    `[0,10]` -- also WENIGER Wissen an einer Stelle, an der V2 helfen soll. -/
-- BEWEIST NICHT: dass der Pruefer die Regel woertlich liest. Diese Datei kennt den
-- Rust nicht. Was hier steht, ist eine Aussage ueber den TEXT der Spezifikation: der
-- Satz "hat den Typ" laesst beide Lesarten zu, und die beiden sind nicht gleich.
theorem v2_woertlich_ist_nicht_immer_enger :
    ∃ a b : Iv, ¬ Iv.kleiner (sub_unter_ge a b) (sub a b) := by
  refine ⟨⟨10, 10⟩, ⟨0, 0⟩, ?_⟩
  intro h
  have := h 0 (by simp only [Iv.haelt, sub_unter_ge]; omega)
  simp only [Iv.haelt, sub_lo, sub_hi] at this
  omega


#print axioms Passlogik.Bereich.v2_woertlich_ist_nicht_immer_enger
/-- **Die zweite Lesart, und sie ist die bessere:** V2 SCHNEIDET seinen Fakt in das
    gewoehnlich gerechnete Intervall. Dann ist das Ergebnis nie schlechter als beide. -/
def sub_v2 (a b : Iv) : Iv := schnitt (sub a b) (sub_unter_ge a b)

theorem sub_v2_korrekt {a b : Iv} {x y : Int}
    (hx : a.haelt x) (hy : b.haelt y) (hf : y ≤ x) : (sub_v2 a b).haelt (x - y) :=
  (schnitt_genau _ _ _).mpr ⟨sub_korrekt hx hy, v2_ge hx hy hf⟩


#print axioms Passlogik.Bereich.sub_v2_korrekt
theorem sub_v2_nie_schlechter (a b : Iv) :
    Iv.kleiner (sub_v2 a b) (sub a b) ∧ Iv.kleiner (sub_v2 a b) (sub_unter_ge a b) := by
  constructor
  · intro x hx; exact ((schnitt_genau _ _ _).mp hx).1
  · intro x hx; exact ((schnitt_genau _ _ _).mp hx).2

/-- Und die geschnittene Form kauft immer noch, was V2 kaufen soll: die untere Schranke
    `0`, wo die gewoehnliche Rechnung negativ wuerde. -/
theorem sub_v2_kauft_etwas :
    ∃ a b : Iv, (sub a b).lo < 0 ∧ Iv.kleiner (sub_v2 a b) ⟨0, 20⟩ := by
  refine ⟨⟨0, 10⟩, ⟨0, 10⟩, by decide, ?_⟩
  intro x hx
  have := (schnitt_genau _ _ _).mp hx
  simp only [Iv.haelt, sub_unter_ge] at this ⊢
  omega

/-! ## 9. V3 -- die Variantenverengung

    `SPRACHE.md`:686: "a `match` on a `tagged` type narrows in the branch to the variant
    including its payload -- exhaustive, no catch-all branch".

    V3 traegt NUR, weil `D005` den `match` erschoepfend macht. Das ist die Abhaengigkeit,
    die das Passregister nennt, und sie steht hier als Praemisse.
-/

/-- Ein `tagged`-Wert: eine Variantennummer mit einer Nutzlast. -/
structure TWert where
  variante : Nat
  nutzlast : Int
deriving DecidableEq, Repr

/-- Was ein Zweig eines `match` behauptet: "hier ist die Variante `v`". -/
def zweig_haelt (v : Nat) (w : TWert) : Prop := w.variante = v

/-- **V3.** Im Zweig zu `v` ist die Variante `v` -- also darf die Nutzlast GELESEN
    werden, ohne weitere Pruefung. -/
theorem v3_verengt {v : Nat} {w : TWert} (h : zweig_haelt v w) : w.variante = v := h

/-- **Die Praemisse, und sie ist `D005`.** Ein `match`, dessen Zweigliste alle Varianten
    nennt, trifft fuer jeden Wert genau einen Zweig. Ohne Erschoepfung gaebe es einen
    Wert ohne Zweig -- und der `_`-Zweig, den es nicht gibt, wuerde nichts verengen. -/
-- BEWEIST NICHT: dass `D005` seinerseits traegt. Das Passregister nennt drei
-- Schweigestellen von `D005` (nur bei einem blanken Ort, die lokale Typkarte haelt nur
-- PARAMETER, Varianten werden nach KURZNAMEN verglichen). Unter einer dieser drei ist
-- die Praemisse dieses Satzes nicht hergestellt.
theorem v3_braucht_erschoepfung
    (varianten : List Nat) (w : TWert)
    (erschoepfend : w.variante ∈ varianten) :
    ∃ v ∈ varianten, zweig_haelt v w :=
  ⟨w.variante, erschoepfend, rfl⟩


#print axioms Passlogik.Bereich.v3_braucht_erschoepfung
/-! ## 10. Der Fakt STIRBT beim Schreiben

    `SPRACHE.md`:651: "the checker keeps a fact set per block that grows only at the
    three named places and **dies on every write to a participating place**. Loops carry
    no facts inward."

    Das ist die Regel, ohne die alles oben nichts wert waere -- ein Fakt ueber einen
    ALTEN Wert, auf einen NEUEN angewandt, ist ein Fehlschluss.
-/

/-- Eine Faktenmenge: je Stelle hoechstens ein Intervall. -/
abbrev Fakten := Ort → Option Iv

def leere_fakten : Fakten := fun _ => none

/-- Ein Schreiben auf `o` loescht den Fakt zu `o`. -/
def nach_schreiben (F : Fakten) (o : Ort) : Fakten :=
  fun p => if p = o then none else F p

/-- Ein Fakt ist GUELTIG, wenn der wirkliche Wert der Stelle ihn erfuellt. -/
def gueltig (F : Fakten) (w : Ort → Int) : Prop :=
  ∀ o i, F o = some i → i.haelt (w o)

/-- **Die Loeschung traegt.** Nach einem Schreiben auf `o` sind die verbliebenen Fakten
    unter dem NEUEN Zustand noch gueltig -- weil der Fakt zu `o` weg ist und alle
    anderen Stellen unveraendert sind. -/
-- BEWEIST NICHT: dass ein Schreiben DURCH EINEN ZEIGER nur `o` trifft. Genau das ist
-- die Aliasfrage, und sie hat in diesem Pruefer keine Antwort -- `messung/RACE.md`
-- fuehrt sie als A2/A3, und das Passregister sagt zu V2: "ein Schreiben DURCH EINEN
-- ZEIGER toetet jeden nichtlokalen Fakt". Diese Haerte ist hier als Praemisse
-- `andere_unveraendert` sichtbar gemacht statt weggelassen.
theorem fakten_ueberleben_schreiben
    {F : Fakten} {w w' : Ort → Int} {o : Ort}
    (hg : gueltig F w)
    (andere_unveraendert : ∀ p, p ≠ o → w' p = w p) :
    gueltig (nach_schreiben F o) w' := by
  intro p i hp
  unfold nach_schreiben at hp
  by_cases h : p = o
  · simp [h] at hp
  · simp [h] at hp
    rw [andere_unveraendert p h]
    exact hg p i hp


#print axioms Passlogik.Bereich.fakten_ueberleben_schreiben
/-- **Und die Schleife traegt keinen Fakt hinein.** Modelliert als: vor der Schleife
    wird die Faktenmenge geleert. Der Satz ist trivial und steht hier, weil er die
    Entscheidung buchbar macht -- eine LEERE Menge ist unter JEDEM Zustand gueltig. -/
theorem leere_fakten_immer_gueltig (w : Ort → Int) : gueltig leere_fakten w := by
  intro o i h
  simp [leere_fakten] at h

end Passlogik.Bereich
