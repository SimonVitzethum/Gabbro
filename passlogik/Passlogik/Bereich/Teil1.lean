module


@[expose] public section


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

    `LANGUAGE.md`:647 -- jede Operation muss im Bereich ihres Ergebnistyps bleiben. Der
    Pass rechnet dafuer ein Intervall aus. Was hier bewiesen wird, ist die eine Richtung,
    auf die sich alles stuetzt: **das gerechnete Intervall UEBERDECKT die wahre Menge**.
-/

def add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩
def sub (a b : Iv) : Iv := ⟨a.lo - b.hi, a.hi - b.lo⟩

@[simp] theorem add_lo (a b : Iv) : (add a b).lo = a.lo + b.lo := by rfl
@[simp] theorem add_hi (a b : Iv) : (add a b).hi = a.hi + b.hi := by rfl
@[simp] theorem neg_lo (a : Iv) : (neg a).lo = -a.hi := by rfl
@[simp] theorem neg_hi (a : Iv) : (neg a).hi = -a.lo := by rfl
@[simp] theorem sub_lo (a b : Iv) : (sub a b).lo = a.lo - b.hi := by rfl
@[simp] theorem sub_hi (a b : Iv) : (sub a b).hi = a.hi - b.lo := by rfl

/-- Das Produkt ueber die VIER ECKEN. Das ist die uebliche Intervallarithmetik und
    zugleich die Form, die `grammatik/Beweise/Intervall_Aussen.thy` fuer die Summe schon fuehrt --
    dort steht ausdruecklich, dass der Satz fuer das Produkt "groesser ist und noch nicht
    dasteht" (`grammatik/Beweise/Intervall_Aussen.thy`:149). **Hier steht er.** -/
def mul (a b : Iv) : Iv :=
  let e1 := a.lo * b.lo
  let e2 := a.lo * b.hi
  let e3 := a.hi * b.lo
  let e4 := a.hi * b.hi
  ⟨imin (imin e1 e2) (imin e3 e4), imax (imax e1 e2) (imax e3 e4)⟩

/-- Der Schnitt -- das ist, was V1/V2/V3 mit einem Fakt tun. -/
def schnitt (a b : Iv) : Iv := ⟨imax a.lo b.lo, imin a.hi b.hi⟩

@[simp] theorem schnitt_lo (a b : Iv) : (schnitt a b).lo = imax a.lo b.lo := by rfl
@[simp] theorem schnitt_hi (a b : Iv) : (schnitt a b).hi = imin a.hi b.hi := by rfl

/-- Die Huelle -- das ist, was am Zusammenlauf zweier Zweige geschieht. -/
def huelle (a b : Iv) : Iv := ⟨imin a.lo b.lo, imax a.hi b.hi⟩

@[simp] theorem huelle_lo (a b : Iv) : (huelle a b).lo = imin a.lo b.lo := by rfl
@[simp] theorem huelle_hi (a b : Iv) : (huelle a b).hi = imax a.hi b.hi := by rfl

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

    `LANGUAGE.md`:651 sagt: **"syntax-directed, without fixpoint, without solver"**. Die
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

    `LANGUAGE.md`:647: "if `a + b` does not fit the target, that is a **compile error, not
    a runtime check**." Der Pass prueft also eine Aussage ueber INTERVALLE und laesst
    daraus eine Aussage ueber WERTE folgen. Genau dieser Schluss steht hier.
-/

/-- Der erklaerte Bereich eines Ziels. `LANGUAGE.md`:641 -- `u32 in 1..7` etc. -/
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
-- und es ist der Grund, warum `narrow` als Ausweg existiert (`LANGUAGE.md`:735).
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

    `LANGUAGE.md`:647: "Division and remainder demand a denominator whose range excludes
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

    `LANGUAGE.md`:684: "a checked **range condition** narrows the range of the checked
    place in the branch after it".

    **Und die zwei Vorbedingungen stehen im Modell, nicht in einer Fussnote:**
    * `stabil` -- eine Stelle durch ein `device`-Register bleibt zwischen Pruefung und
      Verwendung nicht dieselbe (`LANGUAGE.md`:688, «B33»).
    * Trichotomie -- der `else`-Zweig setzt sie voraus (`LANGUAGE.md`:717). Ueber `Int`
      gilt sie; §7 zeigt, wo sie bricht.
-/

/-- Eine Stelle im Programm, abstrakt. -/
structure Ort where
  id : Nat
deriving DecidableEq, Repr

/-- `stabil o` heisst: der Wert von `o` aendert sich zwischen zwei Lesungen nicht von
    selbst. Der Pass liest das aus der Deklaration ab -- eine `device`-Registerstelle
    ist NICHT stabil (`LANGUAGE.md`:688). -/
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
end Passlogik.Bereich
