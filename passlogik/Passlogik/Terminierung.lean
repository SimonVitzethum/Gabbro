/-
  Datei:      Passlogik/Terminierung.lean
  Gegenstand: M4 -- die drei Schleifenformen und ihre Abstiegsmasse.

  MODELLIERT WIRD
    Der Kernsatz "kein unendlicher Abstieg", und je Schleifenform das Mass, das ihn
    traegt: `by unvisited` (die unbesuchte Restmenge einer endlichen Domaene), `by
    decreasing e` (das genannte Mass), `by consuming` (die Zahl der noch nicht
    verbrauchten Zeugen), `retry … bounded N ops` (das Restbudget). Und `forever`, das
    ausdruecklich NICHT endet.

  QUELLSAETZE
    dokumente/SYNTAX.md:855  -- "8. Loops -- **three forms, and infinite is one of them**.
                                The rule is not 'every loop ends' but: what a loop may do
                                stands beside it."
    dokumente/SYNTAX.md:862  -- `traverse = "traverse" ident [ "of" expr ] "over" domain
                                 "by" ( "unvisited" | "consuming" | "decreasing" expr )
                                 [ "touches" efflist ] block`
    dokumente/SYNTAX.md:888  -- die Tafel "was der Abstiegszeuge FUER DEN LAUF heisst"
                                 (Stufe 3, 2026-08-20)
    dokumente/SYNTAX.md:902  -- "`retry` | yes, through `bounded` | termination as a NUMBER"
    dokumente/SYNTAX.md:903  -- "`forever` | **no -- and that is permitted**"
    dokumente/SPRACHE.md:1121 -- §9.2 `by consuming`, die wohlfundierte Ordnung der Domaene
    gabbro paesse --je-satz  -- Satz `schleifen.fortschritt`:
        BUT NOT: "**Necessary, not sufficient, and the pass says so: it is NOT checked that
        the measure FALLS.** [...] `by unvisited` needs nothing here and that is not an
        omission -- it visits each element of a FINITE domain at most once, so it
        terminates by construction; the domain bound is `K003`'s business."

  ANGENOMMEN STATT BEWIESEN
    (T1) **Die Domaenenschranke.** Dass die Domaene wirklich `n` Elemente hat, ist
         `kosten.domaenenschranke` und steht auf `CONJECTURED`. Hier ist `n` gegeben.
    (T2) **DASS das Mass faellt, prueft kein Pass.** `S005` prueft, dass das Mass eine
         Groesse NENNT, die der Rumpf schreibt -- eine notwendige Bedingung. §3 und §4
         machen die Luecke als Satz sichtbar.
    (T3) Die wohlfundierte Ordnung, in der eine Domaene ihre Zeugen bei `by consuming`
         liefert (`SPRACHE.md`:1121), ist hier NICHT modelliert. Modelliert ist nur, dass
         die Zeugenmenge schrumpft.
-/

namespace Passlogik.Terminierung

/-! ## 1. Der Kernsatz: kein unendlicher Abstieg

    Alles unten ist eine Anwendung davon. **Das ist die ganze Mathematik der Terminierung
    in dieser Sprache** -- es gibt keinen Fixpunkt und keine Ordinalzahl, nur ein Mass
    nach `Nat`.
-/

/-- **Es gibt keine unendliche echt fallende Folge in `Nat`.** -/
-- BEWEIST NICHT: dass ein Programm ohne fallendes Mass NICHT endet. Die Umkehrung ist
-- falsch -- ein Mass ist eine hinreichende Bedingung, und `by unvisited` ist genau der
-- Fall, in dem der Pass keins verlangt, weil die Form selbst eins liefert.
theorem kein_unendlicher_abstieg {S : Type u} (m : S → Nat) (f : Nat → S)
    (fall : ∀ i, m (f (i+1)) < m (f i)) : False := by
  have schranke : ∀ i, m (f i) + i ≤ m (f 0) := by
    intro i
    induction i with
    | zero => omega
    | succ k ih => have := fall k; omega
  have := schranke (m (f 0) + 1)
  omega


#print axioms Passlogik.Terminierung.kein_unendlicher_abstieg
/-- Die gebrauchsfertige Form: ein Lauf ist eine Folge von Zustaenden mit einem Schritt
    dazwischen. Faellt das Mass bei jedem Schritt, so gibt es keinen unendlichen Lauf. -/
theorem schleife_endet {S : Type u} (schritt : S → S → Prop) (m : S → Nat)
    (faellt : ∀ a b, schritt a b → m b < m a)
    (lauf : Nat → S) (ist_lauf : ∀ i, schritt (lauf i) (lauf (i+1))) : False :=
  kein_unendlicher_abstieg m lauf (fun i => faellt _ _ (ist_lauf i))

/-! ## 2. `by unvisited` -- die Form liefert das Mass selbst

    `gabbro paesse --je-satz`, `schleifen.fortschritt`: *"`by unvisited` needs nothing here
    and that is not an omission -- it visits each element of a FINITE domain at most once,
    so it terminates by construction."*

    **Was "by construction" heisst, steht hier als Rechnung:** das Mass ist die Zahl der
    unbesuchten Elemente, und ein Schritt besucht ein bis dahin unbesuchtes.
-/

/-- Wie viele der Zahlen `0 … k-1` das Praedikat erfuellen. Selbstgebaut, weil diese
    Datei nichts importiert. -/
def zaehle : Nat → (Nat → Bool) → Nat
  | 0,   _ => 0
  | k+1, p => (if p k then 1 else 0) + zaehle k p

theorem zaehle_gleich {k : Nat} {p q : Nat → Bool}
    (h : ∀ j, j < k → p j = q j) : zaehle k p = zaehle k q := by
  induction k with
  | zero => rfl
  | succ n ih =>
      have hn : p n = q n := h n (by omega)
      have hr : zaehle n p = zaehle n q := ih (fun j hj => h j (by omega))
      simp only [zaehle, hn, hr]

/-- **Der Zaehlschritt:** wird genau eine Stelle unter `k` von `false` auf `true`
    gesetzt, so waechst die Zahl um genau eins. -/
theorem zaehle_ein_mehr {k i : Nat} {p q : Nat → Bool}
    (hik : i < k) (hp : p i = false) (hq : q i = true)
    (hrest : ∀ j, j ≠ i → q j = p j) : zaehle k q = zaehle k p + 1 := by
  induction k with
  | zero => omega
  | succ n ih =>
      by_cases hin : i = n
      · subst hin
        have : zaehle i q = zaehle i p := zaehle_gleich (fun j hj => hrest j (by omega))
        simp [zaehle, hp, hq, this]
        omega
      · have hne : q n = p n := hrest n (fun hc => hin hc.symm)
        have hr := ih (by omega)
        simp only [zaehle, hne, hr]
        omega

/-- Der Zustand einer `by unvisited`-Traversierung: welche Stellen schon besucht sind. -/
structure UZustand (n : Nat) where
  besucht : Nat → Bool

/-- Das Mass: die Zahl der noch unbesuchten Elemente der Domaene. -/
def unbesucht {n : Nat} (z : UZustand n) : Nat := zaehle n (fun i => ! z.besucht i)

/-- Ein Schritt: ein bisher UNbesuchtes Element wird besucht. Das ist die ganze
    Bedeutung von `by unvisited`. -/
def uschritt {n : Nat} (a b : UZustand n) : Prop :=
  ∃ i, i < n ∧ a.besucht i = false ∧ b.besucht i = true
       ∧ ∀ j, j ≠ i → b.besucht j = a.besucht j

/-- **`by unvisited` terminiert -- ohne dass irgendjemand ein Mass hinschreibt.** -/
-- BEWEIST NICHT (T1): dass `n` die Maechtigkeit der Domaene IST. Genau das ist
-- `kosten.domaenenschranke`, und dort lebte der `mappings of`-Fehler (2 048 statt 512^4).
-- BEWEIST AUCH NICHT: dass der ERZEUGER wirklich jedes Element hoechstens einmal
-- ausliefert. Das ist eine Aussage ueber die Absenkung der Domaene.
theorem unvisited_endet {n : Nat} (lauf : Nat → UZustand n)
    (ist_lauf : ∀ i, uschritt (lauf i) (lauf (i+1))) : False := by
  refine schleife_endet uschritt unbesucht ?_ lauf ist_lauf
  intro a b ⟨i, hin, ha, hb, hrest⟩
  unfold unbesucht
  have : zaehle n (fun j => ! a.besucht j) = zaehle n (fun j => ! b.besucht j) + 1 := by
    refine zaehle_ein_mehr hin (by simp [hb]) (by simp [ha]) ?_
    intro j hj; simp [hrest j hj]
  omega


#print axioms Passlogik.Terminierung.unvisited_endet
/-! ## 3. `by decreasing e` -- und die Luecke, die der Pass selbst nennt

    `S005` prueft: das Mass NENNT die Traversierungsvariable oder einen Namen, den der
    Rumpf schreibt. **Es prueft nicht, dass es FAELLT** -- und das Passregister sagt es
    ausdruecklich: *"Necessary, not sufficient, and the pass says so."*
-/

/-- Ein Zustand mit einem benannten Mass. -/
structure DZustand where
  mass : Nat
  /-- Ob der Rumpf den Namen ueberhaupt beschrieben hat -- das ist, was `S005` sieht. -/
  geschrieben : Bool

/-- Der Schritt, wie er sein SOLL: das Mass faellt. -/
def dschritt_gut (a b : DZustand) : Prop := b.mass < a.mass

/-- **Unter der starken Bedingung terminiert die Schleife.** -/
theorem decreasing_endet (lauf : Nat → DZustand)
    (ist_lauf : ∀ i, dschritt_gut (lauf i) (lauf (i+1))) : False :=
  schleife_endet dschritt_gut DZustand.mass (fun _ _ h => h) lauf ist_lauf

/-- Der Schritt, wie `S005` ihn PRUEFT: der Name wird geschrieben. -/
def dschritt_geprueft (_a b : DZustand) : Prop := b.geschrieben = true

/-- **Und das reicht nicht.** Es gibt einen unendlichen Lauf, in dem der Rumpf das Mass
    bei jedem Durchgang schreibt -- und es nie kleiner macht. -/
-- BEWEIST NICHT: dass ein solcher Rumpf im Korpus steht. Es ist eine Aussage ueber die
-- REGEL: `S005` ist notwendig, nicht hinreichend, und der Abstand zwischen beiden ist
-- genau dieser Lauf.
theorem s005_ist_nicht_hinreichend :
    ∃ lauf : Nat → DZustand, (∀ i, dschritt_geprueft (lauf i) (lauf (i+1)))
      ∧ ¬ (∀ i, dschritt_gut (lauf i) (lauf (i+1))) := by
  refine ⟨fun _ => ⟨7, true⟩, fun _ => rfl, ?_⟩
  intro h
  have := h 0
  simp [dschritt_gut] at this


#print axioms Passlogik.Terminierung.s005_ist_nicht_hinreichend
/-! ## 4. `by consuming` -- `S008`, und derselbe Abstand

    `S008` (gebaut 2026-08-24): `by consuming` muss ein `consumes` in seinem `touches`
    nennen -- *"die Zusage, dass die Domaene schrumpft, braucht einen Traeger."*

    Das Passregister sagt dazu: *"Necessary, not sufficient, as at `S005`: THAT it shrinks
    on every pass stays the prover's business."*
-/

/-- Der Zustand: wie viele Zeugen noch da sind, und ob `touches` ein `consumes` fuehrt. -/
structure CZustand where
  zeugen : Nat
  touches_nennt_consumes : Bool

/-- Was `S008` PRUEFT: `touches` nennt ein `consumes`. Eine Aussage ueber den TEXT. -/
def s008_haelt (z : CZustand) : Prop := z.touches_nennt_consumes = true

/-- Was der Satz BRAUCHT: die Zeugenmenge schrumpft wirklich. -/
def cschritt (a b : CZustand) : Prop := b.zeugen < a.zeugen

/-- **Unter der wirklichen Schrumpfung terminiert `by consuming`.** -/
theorem consuming_endet (lauf : Nat → CZustand)
    (ist_lauf : ∀ i, cschritt (lauf i) (lauf (i+1))) : False :=
  schleife_endet cschritt CZustand.zeugen (fun _ _ h => h) lauf ist_lauf

/-- **Und `S008` allein liefert sie nicht.** Ein `touches`, das ein `consumes` nennt,
    schliesst einen Durchgang ohne Verbrauch nicht aus. -/
-- BEWEIST NICHT: dass `S008` nutzlos ist. Es schliesst den Fall aus, in dem die Zusage
-- GAR KEINEN Traeger hat -- und vor dem 2026-08-24 ging genau der durch. Was hier steht,
-- ist der verbleibende Abstand, und er ist ausdruecklich der des Beweisers.
theorem s008_ist_nicht_hinreichend :
    ∃ lauf : Nat → CZustand, (∀ i, s008_haelt (lauf i))
      ∧ ¬ (∀ i, cschritt (lauf i) (lauf (i+1))) := by
  refine ⟨fun _ => ⟨3, true⟩, fun _ => rfl, ?_⟩
  intro h
  have := h 0
  simp [cschritt] at this


#print axioms Passlogik.Terminierung.s008_ist_nicht_hinreichend
/-! ## 5. `retry … bounded N ops` -- und ein FUND

    `SYNTAX.md`:902: *"`retry` | ends? **yes, through `bounded`** | termination as a
    NUMBER; the overrun is NAMED (`on_exceeded`), not interpreted."*

    Das Mass ist das RESTBUDGET: jeder Durchgang verbraucht seine Kosten, und bei
    Erschoepfung endet die Schleife ueber `on_exceeded`.
-/

/-- Der Zustand: wie viele Operationen noch im Budget sind. -/
structure RZustand where
  rest : Nat

/-- Ein Durchgang verbraucht `k` Operationen. -/
def rschritt (k : Nat) (a b : RZustand) : Prop := b.rest + k = a.rest

/-- **`retry` endet -- wenn jeder Durchgang MINDESTENS EINE Operation kostet.** -/
theorem retry_endet {k : Nat} (hk : 0 < k) (lauf : Nat → RZustand)
    (ist_lauf : ∀ i, rschritt k (lauf i) (lauf (i+1))) : False := by
  refine schleife_endet (rschritt k) RZustand.rest ?_ lauf ist_lauf
  intro a b h
  unfold rschritt at h
  omega


#print axioms Passlogik.Terminierung.retry_endet
/-- **FUND: ohne diese Bedingung endet `retry` nicht.** Kostet ein Durchgang null
    Operationen, so faellt das Budget nie, `on_exceeded` schlaegt nie an, und die
    Schleife laeuft ewig -- obwohl `SYNTAX.md`:902 sagt, sie ende "durch `bounded`".

    **Die Spezifikation stellt nirgends fest, dass ein `retry`-Durchgang mindestens eine
    Operation kostet.** `K006` haelt die Schranke gegen den Rumpf (`Ĉ(rumpf) <= N`) --
    das ist die OBERE Seite. Eine untere gibt es nicht, und `SPRACHE.md`:949 sagt
    ausdruecklich, dass `if`, `match`, `return` und `leave` **nichts** kosten. -/
-- BEWEIST NICHT: dass ein solcher Rumpf schreibbar ist. Ob die Grammatik einen Rumpf
-- zulaesst, dessen `Ĉ` null ist -- und ob der Pruefer die `until`-Bedingung ins Budget
-- rechnet --, entscheidet sich am Parser und am Kostenpass, nicht hier. **Was hier steht,
-- ist die Frage, die der Text offenlaesst.**
theorem retry_ohne_kosten_endet_nicht :
    ∃ lauf : Nat → RZustand, ∀ i, rschritt 0 (lauf i) (lauf (i+1)) := by
  refine ⟨fun _ => ⟨5⟩, ?_⟩
  intro i; simp [rschritt]


#print axioms Passlogik.Terminierung.retry_ohne_kosten_endet_nicht
/-! ## 6. `forever` -- endet ausdruecklich NICHT

    `SYNTAX.md`:903: *"`forever` | ends? **no -- and that is permitted** | every PASS is
    bounded, the FRAME stands in `effects`."*

    **Damit ist der Satz "jedes Programm terminiert" FALSCH**, und zwar nicht aus
    Versehen. Was gilt, ist der Satz mit der Voraussetzung -- und die steht hier.
-/

/-- `forever` hat kein Gesamtmass; es hat ein Mass JE DURCHGANG. -/
structure FZustand where
  /-- Was der laufende Durchgang bisher gekostet hat. -/
  pass_kosten : Nat

/-- `per_pass bounded N ops`: jeder Durchgang bleibt unter `N`. -/
def per_pass_haelt (N : Nat) (z : FZustand) : Prop := z.pass_kosten ≤ N

/-- **Ein `forever` hat einen unendlichen Lauf, und jeder Durchgang haelt seine
    Schranke.** Die beiden Aussagen widersprechen einander nicht -- das ist genau die
    Trennung, die `per_pass` einfuehrt. -/
theorem forever_laeuft_ewig (N : Nat) :
    ∃ lauf : Nat → FZustand, ∀ i, per_pass_haelt N (lauf i) := by
  refine ⟨fun _ => ⟨0⟩, ?_⟩
  intro i; simp [per_pass_haelt]


#print axioms Passlogik.Terminierung.forever_laeuft_ewig
/-! ## 7. Der zusammengesetzte Satz -- und was er voraussetzt

    Der Auftrag lautete: *"die drei Schleifenformen mit ihren Abstiegsmassen ⇒ jedes
    Programm terminiert."* **Dieser Satz ist so nicht wahr**, und §6 sagt warum. Was wahr
    ist, ist die Form mit der Voraussetzung.
-/

/-- Die vier Schleifenformen der Sprache, und ob sie ein Abstiegsmass tragen. -/
inductive Schleifenform where
  | unvisited
  | decreasing
  | consuming
  | retry
  | forever
deriving DecidableEq, Repr

/-- Welche Formen enden. -/
def endet : Schleifenform → Bool
  | .unvisited  => true
  | .decreasing => true
  | .consuming  => true
  | .retry      => true
  | .forever    => false

/-- **Der ehrliche Satz.** Ein Programm, dessen Schleifen alle eine der vier endenden
    Formen haben UND deren Abstiegsmasse wirklich fallen, hat keinen unendlichen Lauf.

    Die beiden Voraussetzungen sind verschieden stark, und der Unterschied ist der ganze
    Ertrag dieser Datei:
    * `by unvisited` liefert sein Mass aus der FORM (§2) -- da ist nichts vorauszusetzen
      ausser der Domaenenschranke (T1).
    * `by decreasing` und `by consuming` liefern es NICHT (§3, §4) -- der Pass prueft
      eine notwendige Bedingung, und `DASS` das Mass faellt, bleibt Beweisersache.
    * `retry` liefert es nur, wenn ein Durchgang etwas kostet (§5) -- **und das steht
      nirgends.** -/
-- BEWEIST NICHT: dass ein Programm nur diese Formen enthaelt. Rekursion ist eine zweite
-- Quelle der Nichttermination, und `K008`/`K009` verlangen dafuer `decreases` -- wieder
-- eine NOTWENDIGE Bedingung ("das Mass nennt eine Groesse, die der rekursive Ruf
-- aendert"), nicht die hinreichende. Der Satz oben deckt Schleifen, nicht Rekursion.
theorem programm_endet_unter_massen {S : Type u}
    (schritt : S → S → Prop) (m : S → Nat)
    (jede_schleife_faellt : ∀ a b, schritt a b → m b < m a)
    (lauf : Nat → S) (ist_lauf : ∀ i, schritt (lauf i) (lauf (i+1))) : False :=
  schleife_endet schritt m jede_schleife_faellt lauf ist_lauf


#print axioms Passlogik.Terminierung.programm_endet_unter_massen
/-- Und `forever` steht ausserhalb -- als Entscheidung, nicht als Luecke. -/
theorem forever_traegt_kein_mass : endet .forever = false := rfl

end Passlogik.Terminierung
