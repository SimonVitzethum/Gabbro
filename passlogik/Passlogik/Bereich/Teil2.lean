module

public import Passlogik.Bereich.Teil1

@[expose] public section

namespace Passlogik.Bereich

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

    `LANGUAGE.md`:688 -- und bis zum 2026-08-20 tat der Pruefer das Gegenteil: das
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

    `LANGUAGE.md`:717: "Die Verengung im `else`-Zweig setzt voraus, dass die Negation
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
-- Endlichkeitsfakt. Was hier steht, ist die Praezisierung dessen, was `LANGUAGE.md`:717
-- als Bedingung nennt: die Regel ist an EINEM Punkt falsifizierbar, und der Punkt ist
-- konstruiert.
theorem trichotomie_bricht : ∃ x k : PWert, ple x k = false ∧ ple k x = false :=
  ⟨PWert.nan, PWert.zahl 0, rfl, rfl⟩


#print axioms Passlogik.Bereich.trichotomie_bricht
/-- **Die Folge, ausgeschrieben:** unter einem solchen Traeger gibt es vier Ausgaenge,
    nicht drei -- `<`, `=`, `>` und "unvergleichbar". -/
theorem vier_ausgaenge : ∃ x k : PWert, ¬ (ple x k = true ∨ ple k x = true) := by
  refine ⟨PWert.nan, PWert.zahl 0, ?_⟩
  simp only [ple, Bool.false_eq_true, or_self, not_false_eq_true]

/-! ## 8. V2 -- die relationale Verengung

    `LANGUAGE.md`:685: "under the fact `a >= b`, `a - b` has type `0 .. a.max - b.min`,
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
    werden" (`LANGUAGE.md`:685), praezise gemacht.* -/
theorem v2_kauft_etwas :
    ∃ a b : Iv, (sub a b).lo < 0 ∧ (sub_unter_ge a b).lo = 0 := by
  refine ⟨⟨0, 10⟩, ⟨0, 10⟩, ?_, ?_⟩ <;> decide

/-! ### 8.1 FUND: "hat den Typ" oder "wird geschnitten mit"? -- eine Mehrdeutigkeit

    `LANGUAGE.md`:685 schreibt: *unter dem Fakt `a >= b` **hat** `a - b` den Typ
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

    `LANGUAGE.md`:686: "a `match` on a `tagged` type narrows in the branch to the variant
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

    `LANGUAGE.md`:651: "the checker keeps a fact set per block that grows only at the
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
  · simp only [h, ↓reduceIte, reduceCtorEq] at hp
  · simp only [h, ↓reduceIte] at hp
    rw [andere_unveraendert p h]
    exact hg p i hp


#print axioms Passlogik.Bereich.fakten_ueberleben_schreiben
/-- **Und die Schleife traegt keinen Fakt hinein.** Modelliert als: vor der Schleife
    wird die Faktenmenge geleert. Der Satz ist trivial und steht hier, weil er die
    Entscheidung buchbar macht -- eine LEERE Menge ist unter JEDEM Zustand gueltig. -/
theorem leere_fakten_immer_gueltig (w : Ort → Int) : gueltig leere_fakten w := by
  intro o i h
  simp only [leere_fakten, reduceCtorEq] at h

end Passlogik.Bereich
