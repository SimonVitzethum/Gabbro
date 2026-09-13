/-
  Datei:      Grammatik/Interferenz.lean
  Gegenstand: **DAS GEMEINSAME MODELL ZWEIER FAEDEN** -- und der Satz, dass eine sequenziell
              gueltige Zusicherung ihre Verschraenkung ueberlebt (Stabilitaet, Owicki-Gries
              in einem Schritt).

  ## Das Modell

  Ein `ZweiFaden` sind zwei Schritte in Zeitfolge: Faden `f` von `σ₀` nach `σ₁`, Faden `g`
  von `σ₁` nach `σ₂`. Jede Seite traegt bei, was die angefuehrte Stelle liefert:

    * `hRahmenA/B` -- jeder Schritt bleibt in seinem Rahmen (`exec_rahmen` je Rumpf,
      `Satz.lean`; `rahmen_aus_exec` unten nennt die Herkunft beim Namen),
    * `hDisjunkt` -- die Rahmen sind paarweise disjunkt (Tabellen UND Globale),
    * `hGesittet` -- der Lauf ist sperrdiszipliniert (`Gesittet`, `Wettlauf.lean`),
    * `hHaeltA/B` -- jeder Faden haelt beim Eintritt genau seine erklaerten Sperren
      (die Form von `RufPasst.hh`, SG-20: die Sperrmenge steht in BEIDEN Richtungen),
    * `hNb` -- das Paar ist deklariert (`Nebeneinander`, `Wettlauf.lean` §6: die
      deklarierte Paarmenge, deren gemeinsames Modell in `Wettlauf.lean`:515
      als nirgends stehend gebucht war -- es steht hier).

  ## Der Satz

  `interferenz_erhaelt_vertraege`: ein Praedikat `Q` ueber dem Rahmen von `f`, gueltig am
  Ausgang von `f` (`hseq` -- die sequenzielle Gueltigkeit, `ensures`-Seite), gilt noch nach
  dem Schritt von `g`. `interferenz_erhaelt_vorbedingung` ist die Gegenrichtung: was nur
  vom Rahmen von `g` abhaengt, ueberlebt den Schritt von `f` (`requires`-Seite).

  Der Beweis: `Rahmen` sagt, wo `g` NICHT schreibt; Disjunktheit sagt, dass dort der
  Rahmen von `f` liegt (`rahmen_gleichAuf_of_disjunkt`); `HaengtAb` sagt, dass `Q` nur
  dort liest (`stabil`).

  Daneben: `inv_schreiber_sperren` (wer eine Invariante schuldet, haelt die Sperren ALLER
  ihrer Traeger -- `invarianten_gehalten`, U003, am Rumpf `f`), `schuldet_hat_schreibtraeger`
  (eine geschuldete Invariante hat einen Traeger im Rahmen -- sonst stuende `schuldet`
  am `return` ueber nichts), `paar_inv_haelt` (die Invariantensicht liest unter gehaltenen
  Sperren -- `hHaeltA` ueber `heldIn_invarianten`).

  ## Was dieser Satz NICHT sagt -- jeder Schnitt gebucht

  (S1) Vertraege als Praedikate. `requires`/`ensures` stehen hier als abstraktes `Q` mit
       sequenzieller Gueltigkeit als Praemisse (`hseq`). Dass die Auswertung eines
       Vertragsausdrucks nur seinen Rahmen liest (ein `eval`-Fussabdruck-Lemma: `eval`
       liest nur `orte`), steht nirgends -- darum wird es ANGENOMMEN (`hQ`), nicht
       abgeleitet. Wer es beweist, ersetzt `hQ` durch die Einsetzung; der Stabilitaetsschluss
       bleibt derselbe.
  (S2) `Gesittet` wird getragen, nicht verbraucht. Stabilitaet braucht nur Rahmen plus
       Disjunktheit; W3-W5 (fremde Sperrprimitive, disjunkte Marken, `shared`) sprechen ueber
       das Verhaeltnis der Faeden zueinander, und kein Satz ueber Rahmen kann sie schliessen
       (`Wettlauf.lean` §5 sagt es). `hGesittet` haelt den Lauf rennfrei ueber `kein_wettlauf`;
       die Stabilitaet daneben ist der zweite, unverbundene Satz -- jetzt wenigstens im
       selben Modell.
  (S3) Geteilte Traeger unter gemeinsamer Sperre sind AUSGESCHLOSSEN. Disjunktheit verbietet
       gemeinsames Schreiben; ein Paar, das denselben Traeger unter derselben Sperre
       schreibt, ordnet HB (`kein_wettlauf`), nicht Stabilitaet. Wer es hier will, beweist
       erst die HB-Ordnung der zwei Schritte und faehrt dann sequenziell.
  (S4) Zwei Faeden, je ein Schritt (`σ₀ → σ₁ → σ₂`). Keine n-Faden-Verallgemeinerung, keine
       beliebige Verschraenkung -- die Schrittfolge IST das Modell. Wer mehr Faeden will,
       faltet `stabil` ueber die Folge.
  (S5) `hHaeltA/B` beweisen nicht die Stabilitaet; sie tragen nur `paar_inv_haelt`
       (die Invariantenseite am Eintritt). Die Sperr-Richtung der Stabilitaet ist (S2).
  (S6) `Q` spricht nur ueber die Welt, nicht ueber Belegungen (`Env`): lokale Bindungen
       teilt kein Faden, also steht nichts ueber sie im Satz.
-/
import Grammatik.Satz
import Grammatik.Wettlauf

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Rahmenlesung: woran ein Praedikat haengt -/

/-- Zwei Welten stimmen auf dem Rahmen `(W, G)` ueberein. -/
def RahmenGleichAuf (W : D.Tab → Bool) (G : D.Glob → Bool) (σ σ' : World D) : Prop :=
  (∀ t, W t = true → ∀ k f, σ'.slots t k f = σ.slots t k f) ∧
  (∀ g, G g = true → σ'.globs g = σ.globs g)

/-- `Q` haengt nur am Rahmen `(W, G)`: gleiche Rahmenbelegung, gleiche Antwort. -/
def HaengtAb (W : D.Tab → Bool) (G : D.Glob → Bool) (Q : World D → Prop) : Prop :=
  ∀ σ σ', RahmenGleichAuf W G σ σ' → (Q σ ↔ Q σ')

/-- Paarweise-disjunkte Rahmen: kein Traeger, kein Global in beiden. -/
def Disjunkt (W₁ : D.Tab → Bool) (G₁ : D.Glob → Bool) (W₂ : D.Tab → Bool)
    (G₂ : D.Glob → Bool) : Prop :=
  (∀ t, W₁ t = true → W₂ t = false) ∧ (∀ g, G₁ g = true → G₂ g = false)

theorem Disjunkt.symm {W₁ W₂ : D.Tab → Bool} {G₁ G₂ : D.Glob → Bool}
    (hd : Disjunkt W₁ G₁ W₂ G₂) : Disjunkt W₂ G₂ W₁ G₁ := by
  constructor
  · intro t ht
    cases hw : W₁ t with
    | true => rw [hd.1 t hw] at ht; cases ht
    | false => rfl
  · intro g hg
    cases hw : G₁ g with
    | true => rw [hd.2 g hw] at hg; cases hg
    | false => rfl

/-- Ein Schritt im fremden Rahmen laesst den eigenen unberuehrt: `Rahmen` nennt, wo NICHT
    geschrieben wurde, und die Disjunktheit legt den eigenen Rahmen dorthin. -/
theorem rahmen_gleichAuf_of_disjunkt {W₁ W₂ : D.Tab → Bool} {G₁ G₂ : D.Glob → Bool}
    {σ σ' : World D} (hR : Rahmen W₂ G₂ σ σ') (hd : Disjunkt W₁ G₁ W₂ G₂) :
    RahmenGleichAuf W₁ G₁ σ σ' := by
  constructor
  · intro t ht k f
    exact hR.1 t (hd.1 t ht) k f
  · intro g hg
    exact hR.2 g (hd.2 g hg)

/-- **Stabilitaet in einem Schritt** (Owicki-Gries, nicht-interferierend): was nur am
    eigenen Rahmen haengt, ueberlebt einen Schritt im dazu disjunkten Rahmen. -/
theorem stabil {W₁ W₂ : D.Tab → Bool} {G₁ G₂ : D.Glob → Bool} {Q : World D → Prop}
    {σ σ' : World D} (hQ : HaengtAb W₁ G₁ Q) (hR : Rahmen W₂ G₂ σ σ')
    (hd : Disjunkt W₁ G₁ W₂ G₂) : Q σ ↔ Q σ' :=
  hQ σ σ' (rahmen_gleichAuf_of_disjunkt hR hd)

/-! ## 2. Das gemeinsame Modell: zwei Faeden, zwei Schritte -/

/-- Zwei Faeden in Zeitfolge: `f` von `σ₀` nach `σ₁`, `g` von `σ₁` nach `σ₂` -- je im
    eigenen Rahmen, die Rahmen disjunkt, der Lauf gesittet, die Eintrittssperren erklaert,
    das Paar deklariert. -/
structure ZweiFaden (Nb : Nebeneinander) where
  f : D.Fn
  g : D.Fn
  σ₀ : World D
  σ₁ : World D
  σ₂ : World D
  l : Lauf D
  /-- Das Paar teilt sich den Lauf nur als deklariertes (`Wettlauf.lean` §6). -/
  hNb : Nb 0 1
  /-- Jeder Schritt bleibt in seinem Rahmen (das liefert `exec_rahmen` je Rumpf). -/
  hRahmenA : Rahmen (D.schreibt f) (D.gschreibt f) σ₀ σ₁
  hRahmenB : Rahmen (D.schreibt g) (D.gschreibt g) σ₁ σ₂
  /-- Die Rahmen sind paarweise disjunkt (Tabellen UND Globale). -/
  hDisjunkt : Disjunkt (D.schreibt f) (D.gschreibt f) (D.schreibt g) (D.gschreibt g)
  /-- Der Lauf ist sperrdiszipliniert. -/
  hGesittet : Gesittet l
  /-- Jeder Faden haelt beim Eintritt genau seine erklaerten Sperren (die Form von
      `RufPasst.hh`, SG-20, in beiden Richtungen je Faden). -/
  hHaeltA : HeldGenau (Signatur.anfang D (D.signatur f)) σ₀.haelt
  hHaeltB : HeldGenau (Signatur.anfang D (D.signatur g)) σ₁.haelt

/-! ## 3. Woher der Rahmen kommt -- `exec_rahmen`, beim Namen genannt -/

/-- Die Rahmenpraemisse ist genau das, was `exec_rahmen` je Rumpf liefert: ein Rumpf unter
    Vertrag `V`, gestartet mit den genannten Zeugnissen, schreibt nur, was `V` nennt. -/
theorem rahmen_aus_exec (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (hP : StufenOk P) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt)
    (σ' : World D) (h : (exec P O passes fuel V b σ ρ).welt = some σ') :
    Rahmen V.schreibt V.gschreibt σ σ' :=
  exec_rahmen P O passes fuel hO hP b σ ρ hh σ' h

/-! ## 4. Invarianten am Paar: U003 und `schuldet` -/

/-- **U003 am Rumpf**: wer eine Invariante schuldet, haelt die Sperren ALLER ihrer Traeger --
    `invarianten_gehalten`, eingeloest an `f`. -/
theorem inv_schreiber_sperren (f : D.Fn) (i : D.Inv) (hs : schuldet f i = true)
    (t : D.Tab) (ht : t ∈ D.traeger i) (L : D.Lock) (hL : Sum.inl L ∈ D.braucht t) :
    L ∈ D.haelt f :=
  D.invarianten_gehalten (D.sig f) i hs t ht L hL

/-- Eine geschuldete Invariante hat einen Traeger im Rahmen: `schuldet` am `return` steht
    sonst ueber nichts. -/
theorem schuldet_hat_schreibtraeger (f : D.Fn) (i : D.Inv) (hs : schuldet f i = true) :
    ∃ t ∈ D.traeger i, D.schreibt f t = true := by
  unfold schuldet at hs
  have key : ∀ (ts : List D.Tab), ts.any (D.schreibt f) = true →
      ∃ t ∈ ts, D.schreibt f t = true := by
    intro ts
    induction ts with
    | nil => intro h; simp at h
    | cons x xs ih =>
        intro h
        simp only [List.any_cons] at h
        by_cases hx : D.schreibt f x = true
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨t, ht, hwt⟩ := ih (by simpa [hx] using h)
          exact ⟨t, List.mem_cons_of_mem _ ht, hwt⟩
  exact key _ hs

/-- Die Invariantensicht liest unter gehaltenen Sperren: am Eintritt von `f` haelt `f` die
    Waechter jeder geschuldeten Invariante (`hHaeltA` ueber `heldIn_invarianten`). -/
theorem paar_inv_haelt (P : Programm D) (Nb : Nebeneinander) (J : ZweiFaden (D := D) Nb)
    (i : D.Inv) (hs : schuldet J.f i = true) : HeldIn (invSicht D i) J.σ₀.haelt :=
  heldIn_invarianten P J.f J.hHaeltA.heldIn i hs

/-! ## 5. Der Satz: sequenzielle Gueltigkeit ueberlebt Verschraenkung -/

/-- **Interferenz erhaelt Vertraege (`ensures`-Seite).** Was nur am Rahmen von `f` haengt
    und am Ausgang von `f` gilt (die sequenzielle Gueltigkeit), gilt noch nach dem Schritt
    von `g`: die Rahmen sind disjunkt, also schreibt `g` daran vorbei. -/
theorem interferenz_erhaelt_vertraege (Nb : Nebeneinander) (J : ZweiFaden (D := D) Nb)
    (Q : World D → Prop) (hQ : HaengtAb (D.schreibt J.f) (D.gschreibt J.f) Q)
    (hseq : Q J.σ₁) : Q J.σ₂ :=
  (stabil hQ J.hRahmenB J.hDisjunkt).mp hseq

/-- **Interferenz erhaelt Vertraege (`requires`-Seite).** Was nur am Rahmen von `g` haengt,
    ueberlebt den Schritt von `f` -- darum darf die sequenzielle `requires`-Pruefung von `g`
    vor dem Schritt von `f` stehen. -/
theorem interferenz_erhaelt_vorbedingung (Nb : Nebeneinander) (J : ZweiFaden (D := D) Nb)
    (Q : World D → Prop) (hQ : HaengtAb (D.schreibt J.g) (D.gschreibt J.g) Q)
    (hseq : Q J.σ₀) : Q J.σ₁ :=
  (stabil hQ J.hRahmenA J.hDisjunkt.symm).mp hseq

#print axioms Gabbro.Grammatik.stabil
#print axioms Gabbro.Grammatik.interferenz_erhaelt_vertraege
#print axioms Gabbro.Grammatik.interferenz_erhaelt_vorbedingung
#print axioms Gabbro.Grammatik.inv_schreiber_sperren
#print axioms Gabbro.Grammatik.paar_inv_haelt

end Gabbro.Grammatik
