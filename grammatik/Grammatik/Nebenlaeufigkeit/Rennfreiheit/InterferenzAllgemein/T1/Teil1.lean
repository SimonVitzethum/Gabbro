module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.Interferenz

@[expose] public section



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
  /-- The guard lock bounding step `k`: the take-to-release interval this chain
      step resolves. `none` marks a lock-free section. One body execution with
      several lock phases contributes one chain step PER section (see
      `MehrphasenKoerper` below), not one step per body. -/
  abschnittWache : Nat → Option D.Lock := fun _ => none
  /-- Forever-thread residents (dispatcher, idle): chain inhabitants that never
      return, hence never close a chain step. They stay members (`EwigBewohner`)
      and hold the invariant at every section boundary they cross
      (`EwigGrenzeHaelt`), without any return premise. -/
  ewig : List Faden := []

/-- One chain step is one lock-bounded section (take-to-release interval): where
    the step's writer touches a carrier, the step names the guard of that
    section -- a lock in the carrier's watch list, declared held by the writer
    (the dynamic take at entry and release at return are the body's own
    critical-section discipline, as in §21). This is the corrected grain: the
    old "one body = one critical section" reading fits no body with several
    lock phases (L1 take, release, L2 take, ...), which contributes one step per
    phase (`MehrphasenKoerper`). -/
def AbschnittGedeckt (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) : Prop :=
  ∀ (k : Nat) (g : Faden) (vor nach : World D),
    J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
      ∀ (c : D.Tab ⊕ D.Glob), TraegerSchreibt (J.code g) c = true →
        ∃ L : D.Lock, J.abschnittWache k = some L ∧ WaechterGehalten (J.code g) c ∧
          (match c with
          | .inl t => Sum.inl L ∈ D.braucht t
          | .inr x => Sum.inl L ∈ D.gbraucht x) ∧
          L ∈ D.haelt (J.code g)

/-- A body with several lock phases: two chain steps by the same thread under
    different guards. The chain resolves sections, not bodies. -/
def MehrphasenKoerper (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (f : Faden) : Prop :=
  ∃ (k1 k2 : Nat) (L1 L2 : D.Lock),
    L1 ≠ L2 ∧ J.schrittFaden[k1]? = some f ∧ J.schrittFaden[k2]? = some f ∧
      J.abschnittWache k1 = some L1 ∧ J.abschnittWache k2 = some L2

/-- Forever-thread membership: every resident is a chain inhabitant, so
    interference reasoning covers it even though it never closes a step. -/
def EwigBewohner (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) : Prop :=
  ∀ (f : Faden), f ∈ J.ewig → f ∈ J.faeden

/-- The non-terminating resident, explicitly: a forever-thread holds the
    invariant at every section boundary it crosses -- both worlds of each of
    its steps -- with no return premise owed (contrast the writer's
    return-under-guard in §21 `hReturn`: residents never return, so there is
    nothing to re-establish at an end that never comes). -/
def EwigGrenzeHaelt (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) : Prop :=
  ∀ (f : Faden), f ∈ J.ewig → ∀ (k : Nat) (vor nach : World D),
    J.schrittFaden[k]? = some f → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
      ∀ (c : D.Tab ⊕ D.Glob), I.inv c vor ∧ I.inv c nach

/-- **Each section step stays in its writer's frame.** The `hSchritt` engine
    read at section grain: one take-to-release interval contributes its
    writer's frame, indivisible at chain level. Later sections consume this
    the way §21 consumes `schritt_rahmen_aus_korn`. -/
theorem abschnitt_schritt_rahmen (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    g ∈ J.faeden ∧ Rahmen (D.schreibt (J.code g)) (D.gschreibt (J.code g)) vor nach :=
  J.hSchritt k g vor nach hkg hkv hkn

/-- **Phases are distinct steps.** A body under two different guards occupies
    two chain positions: the grain is one step per lock-bounded section. -/
theorem mehrphasen_schritte_verschieden (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (f : Faden) (hM : MehrphasenKoerper Nb J f) :
    ∃ (k1 k2 : Nat), k1 ≠ k2 ∧ J.schrittFaden[k1]? = some f ∧
      J.schrittFaden[k2]? = some f := by
  obtain ⟨k1, k2, L1, L2, hne, h1, h2, hw1, hw2⟩ := hM
  refine ⟨k1, k2, ?_, h1, h2⟩
  intro heq
  subst heq
  exact hne (Option.some_inj.mp (hw1.symm.trans hw2))

/-- **Residents stay inhabitants.** A forever-thread never closes a step, but
    it never leaves the chain either. -/
theorem ewig_bleibt_faden (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hE : EwigBewohner Nb J) (f : Faden) (hf : f ∈ J.ewig) : f ∈ J.faeden :=
  hE f hf

#print axioms Gabbro.Grammatik.abschnitt_schritt_rahmen
#print axioms Gabbro.Grammatik.mehrphasen_schritte_verschieden
#print axioms Gabbro.Grammatik.ewig_bleibt_faden

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
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hk
  | cons a as ih =>
    cases k with
    | zero => exact ⟨a, by simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero]⟩
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
  | nil => simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h
  | cons a as ih =>
    cases k with
    | zero => simp only [List.length_cons, Nat.zero_lt_succ]
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
end Gabbro.Grammatik
