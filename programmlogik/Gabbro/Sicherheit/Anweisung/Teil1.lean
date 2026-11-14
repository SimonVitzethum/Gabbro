/-
  Datei:      Gabbro/Sicherheit/Anweisung.lean
  Gegenstand: **Der Sicherheitssatz fuer ANWEISUNGEN** -- ein Rumpf, den der Pruefer annimmt,
              bleibt in `Body.lean`s Semantik nur an zwei Stellen stecken, und beide heissen
              beim Namen: an einem `requires`, das nicht gilt, und an einer `invariant`, die
              beim Eintritt nicht gilt. **Das ist die Logik des Schreibers -- und sonst nichts.**

  Angelegt 2026-09-09. Zweite Haelfte zu `Ausdruck.lean`.

  WAS MODELLIERT WIRD
    `pruefe` ist der Pruefer ueber Anweisungen, als Algorithmus: er traegt den Sichtbereich
    (`Umgebung`, eine Liste von Namen mit Gestalt) durch den Rumpf, haelt jeden Wert gegen
    die Gestalt seines Ziels (`passt` -- das ist `M104` an der Zuweisung), verlangt am `match`
    jeden Fall (`D005`/`M123`), am Ruf die Signatur (`N`-Paesse), und sagt ab, wo etwas nicht
    passt. `none` ist die Absage.

    `Logik` ist das inductive Praedikat der STELLEN, an denen das Modell aus einem Grund
    stecken bleibt, den KEIN Pass tragen kann: die Vorbedingung eines Gerufenen (`requires`)
    oder die Invariante einer Schleife beim Eintritt. Beide sind Klauseln, die der Mensch
    schrieb -- `Coverage.lean` nennt sie `ownRequires`/`ownInvariant`.

    Der Satz `exec_sicher` sagt: **ist `exec` steckengeblieben, dann an einer `Logik`-Stelle.**
    Und laeuft es weiter, dann bleibt die Welt in ihrer Typisierung -- damit die naechste
    Anweisung dieselbe Praemisse hat.

  QUELLSAETZE
    dokumente/LANGUAGE.md:615   -- "Gabbro proves everything except logic."
    dokumente/PROOF.md:18     -- "Whoever proves a Gabbro program proves the LOGIC of their
                                  program -- and nothing else. Everything else falls out by
                                  construction."
    dokumente/SYNTAX.md:1027   -- "`match` is exhaustive"; `let … else` "the `else` branch
                                  must diverge or return"
    programmlogik/Gabbro/Body.lean, `step`  -- "a call whose PRECONDITION does not hold gets
                                  STUCK", "a loop entered with its invariant FALSE gets stuck",
                                  "A callee that returns nothing cannot fill a binding"
    programmlogik/Gabbro/Coverage.lean §4 -- `IsOwnLogic`: `ensures`, `invariant`,
                                  `requires`, `reaches`

  ANGENOMMEN STATT BEWIESEN
    (U1) **Die Umgebung haelt die Welt.** `UmgebungOK`: jeder Gerufene, der eine wohlgeformte
         Welt bekommt, gibt eine wohlgeformte zurueck und antwortet mit einem Wert seiner
         erklaerten Gestalt (oder einem Grund seines `or R`). Das ist der Satz ueber den
         RUMPF des Gerufenen -- genau dieser Satz, eine Ebene tiefer. Ihn aus `Runs` und
         diesem Satz zu SCHLIESSEN ist der Programmsatz (`Sicherheit.lean`, Schritt 2) und
         steht hier nicht: hier ist er Praemisse, sichtbar am Satz.
    (U2) **Die Schleife haelt den Sichtbereich.** `SchleifenOK`: der Sichtbereich, unter
         dem die Schleife geprueft wurde, gilt nach ihr weiter. Dasselbe wie (U1) ueber
         `RunsLoop`/`iterate`.
    (U3) Namen werden nicht mit ANDERER Gestalt neu gebunden. `let x = 1; … let x = true;`
         sagt der Pruefer ab; `n = n + 1` (dieselbe Gestalt) nicht. So sind die Namen eines
         Zweigs nach dem Zweig noch von derselben Gestalt, wo ein spaeterer Leser sie sieht.
    (U4) Die Faelle eines `tagged`-Typs tragen VERSCHIEDENE Namen (`D005` sagt das ab, hier
         ist es `namenEindeutig` als Bedingung des Pruefers).
    (U5) Kein erklaerter Gerufener divergiert (`DivergenzOK` ueber `Signatur.divergiert`).
         Der Fehlerzweig haelt einen Ruf, der nicht zurueckkehrt, nur ueber
         `endetMitAusgang` (F1) -- `step` aber kehrt von jedem Ruf zurueck. Ohne diese
         Klausel liefe die Fortsetzung im Modell mit ungebundener Bindung weiter; mit
         ihr ist der Satz fuer Programme, die einen divergierenden Gerufenen erklaeren,
         leer. Was faellig ist, steht daneben: ein `step`, das einen divergierenden Ruf
         nicht zurueckkehren laesst (`Body.lean`), und der Erzeuger, der `divergiert`
         aus `Typ::Nie` setzt (`lean.rs`).
-/
module
public import Gabbro.Sicherheit.Ausdruck
@[expose] public section


namespace Gabbro.Sicherheit

open Gabbro.Body

/-! ## 1. Der Sichtbereich, und die Signaturen -/

/-- Was ein lokaler Name traegt: eine Gestalt, oder -- nach `let … else (e)` -- einen GRUND
    aus einer erklaerten Liste von Faellen. -/
inductive Ge where
  | form (sh : Shape)
  | why (faelle : List String)
  deriving DecidableEq, Repr

/-- Der Sichtbereich: eine LISTE, kein Funktionsraum -- so ist er vergleichbar, und die
    Schleife kann den ihren registrieren. Der juengste Eintrag steht vorn. -/
abbrev Umgebung := List (String × Ge)

def such : Umgebung → String → Option Ge
  | [], _ => none
  | (m, g) :: rest, n => if m = n then some g else such rest n

/-- Die Gestalten allein -- das, was `schluss` liest. -/
def formen (Δ : Umgebung) : Lokal := fun n =>
  match such Δ n with
  | some (.form sh) => some sh
  | _ => none

/-- Ein Wert traegt, was der Sichtbereich ueber ihn sagt. -/
def Ge.haelt : Ge → Value → Prop
  | .form sh, v => v.hasShape sh = true
  | .why cs, v => ∃ r, r ∈ cs ∧ v = .reason r

/-- Die Lokalen liegen in ihrem Sichtbereich. -/
def WFU (Δ : Umgebung) (β : Binding) : Prop :=
  ∀ n g, such Δ n = some g → g.haelt (β n)

theorem WFU_formen {Δ : Umgebung} {β : Binding} (h : WFU Δ β) : WFL (formen Δ) β := by
  intro n sh hn
  unfold formen at hn
  split at hn
  · rename_i g hs; cases hn; exact h n _ hs
  · cases hn

/-- Neu binden: mit derselben Gestalt ein Ueberschreiben (Zuweisung), sonst nur, wenn der
    Name noch keine traegt (U3). `none`: der Pruefer sagt ab. -/
def binde (Δ : Umgebung) (n : String) (g : Ge) : Option Umgebung :=
  match such Δ n with
  | none => some ((n, g) :: Δ)
  | some g' => if g = g' then some Δ else none

/-- `Δ ⊆ Δ'` -- jeder Name behaelt seine Gestalt. -/
def erweitert (Δ Δ' : Umgebung) : Prop := ∀ n g, such Δ n = some g → such Δ' n = some g

theorem erweitert_refl (Δ : Umgebung) : erweitert Δ Δ := fun _ _ h => h
theorem erweitert_trans {a b c : Umgebung} (h1 : erweitert a b) (h2 : erweitert b c) :
    erweitert a c := fun n g h => h2 n g (h1 n g h)

theorem WFU_erweitert {Δ Δ' : Umgebung} {β : Binding} (he : erweitert Δ Δ') (h : WFU Δ' β) :
    WFU Δ β := fun n g hn => h n g (he n g hn)

theorem binde_erweitert {Δ Δ' : Umgebung} {n : String} {g : Ge} (h : binde Δ n g = some Δ') :
    erweitert Δ Δ' := by
  unfold binde at h
  split at h
  · rename_i hn; cases h
    intro m g' hm
    simp only [such]
    split
    · rename_i hmn; subst hmn; rw [hn] at hm; cases hm
    · exact hm
  · rename_i g' hn
    split at h
    · cases h; exact erweitert_refl _
    · cases h

theorem WFU_binde {Δ Δ' : Umgebung} {β : Binding} {n : String} {g : Ge} {v : Value}
    (h : binde Δ n g = some Δ') (hw : WFU Δ β) (hv : g.haelt v) :
    WFU Δ' (bindLocal β n v) := by
  unfold binde at h
  split at h
  · rename_i hn; cases h
    intro m g' hm
    simp only [such] at hm
    split at hm
    · rename_i hmn; subst hmn; cases hm; simpa [bindLocal] using hv
    · rename_i hmn
      have hmn' : m ≠ n := fun h => hmn h.symm
      simpa [bindLocal, hmn'] using hw m g' hm
  · rename_i g' hn
    split at h
    · rename_i hg; subst hg; cases h
      intro m g' hm
      by_cases hmn : m = n
      · subst hmn; rw [hn] at hm; cases hm; simpa [bindLocal] using hv
      · simpa [bindLocal, hmn] using hw m g' hm
    · cases h

mutual
/-- Passt ein gerechneter Wert in die Gestalt des Ziels? Das ist `M104` an der Zuweisung:
    ein Bereich in einen weiteren, eine Zahl ohne Bereich nur in `.int`. -/
def passt : Shape → Shape → Bool
  | .intIn lo hi, .intIn lo' hi' => decide (lo' ≤ lo ∧ hi ≤ hi')
  | .intIn _ _, .int => true
  | .int, .int => true
  | .bool, .bool => true
  | .opt, .opt => true
  | .sum a, .sum b => decide (a = b)
  | .record a, .record b => passtFelder a b
  | _, _ => false
termination_by structural a _ => a

/-- Record assignment checks every position and refuses different arities. -/
def passtFelder : List Shape → List Shape → Bool
  | [], [] => true
  | a :: as, b :: bs => passt a b && passtFelder as bs
  | _, _ => false
termination_by structural as _ => as
end

mutual
theorem passt_hasShape {a b : Shape} {v : Value} (hp : passt a b = true) (hv : v.hasShape a = true) :
    v.hasShape b = true := by
  cases a <;> cases b <;> simp only [passt, Bool.false_eq_true, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hp
  · exact hv
  · obtain ⟨n, rfl⟩ := Value.hasShape_bool_true v hv; simp only [Value.hasShape]
  · exact hv
  · obtain ⟨n, rfl, h1, h2⟩ := Value.hasShape_intIn_true v _ _ hv; simp only [Value.hasShape]
  · obtain ⟨n, rfl, h1, h2⟩ := Value.hasShape_intIn_true v _ _ hv; simp only [Value.hasShape, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]; omega
  · subst hp; exact hv
  · rename_i as bs
    obtain ⟨vs, rfl, hlen, hf⟩ := Value.hasShape_rec_true v as hv
    obtain ⟨hlen', hf'⟩ := passtFelder_hasShape hp hf
    simp [hlen, hlen', hf']
termination_by structural a

theorem passtFelder_hasShape {as bs : List Shape} {vs : List Value}
    (hp : passtFelder as bs = true) (hv : Value.fieldsHaveShape vs as = true) :
    as.length = bs.length ∧ Value.fieldsHaveShape vs bs = true := by
  cases as with
  | nil =>
      cases bs with
      | nil => exact ⟨rfl, hv⟩
      | cons b bs => simp only [passtFelder, Bool.false_eq_true] at hp
  | cons a as =>
      cases bs with
      | nil => simp only [passtFelder, Bool.false_eq_true] at hp
      | cons b bs =>
          have hh := Bool.and_eq_true_iff.mp hp
          cases vs with
          | nil => simp only [Value.fieldsHaveShape_nil_cons, Bool.false_eq_true] at hv
          | cons v vs =>
              have hvs := Bool.and_eq_true_iff.mp hv
              obtain ⟨hlen, hf⟩ := passtFelder_hasShape hh.2 hvs.2
              exact ⟨by simp only [List.length_cons, hlen], by
                simp only [Value.fieldsHaveShape_cons_cons,
                  passt_hasShape hh.1 hvs.1, hf, Bool.true_and]⟩
termination_by structural as
end

/-- Ein Wert in ein ZIEL, das eine Gestalt tragen kann oder nicht: traegt es keine, ist
    jeder Wert recht (die Stelle ist untypisiert, `WF` fragt sie nicht). -/
def passtIn (sh : Shape) : Option Shape → Bool
  | none => true
  | some ziel => passt sh ziel

/-- Die Signatur eines Gerufenen -- was `fndecl` erklaert. -/
structure Signatur where
  /-- Die Parameter, in Reihenfolge, je mit Gestalt (`none`: ein Wert ohne Gestalt, etwa
      eine lineare Marke). -/
  params   : List (String × Option Shape)
  /-- `-> T`: die Gestalt der Antwort; `none`: keine Antwort. -/
  ergebnis : Option Shape
  /-- `or R`: die Faelle des Fehlerkanals; `[]`: kein Fehlerkanal. -/
  gruende  : List String
  /-- `-> never`: der Gerufene kehrt nicht zurueck (F1). Voreinstellung `false`, damit jedes
      bestehende Literal weitergeht; der Erzeuger setzt es aus `Typ::Nie`. -/
  divergiert : Bool := false

/-- Das Programm, wie der Pruefer es sieht: Deklarationen, Signaturen, und je Schleife der
    Sichtbereich, unter dem sie steht (U2). `ruferR` ist der Fehlerkanal der Funktion, in
    der geprueft wird -- ein `return f(a);` reicht einen Grund nur dorthin durch (F6).
    Voreinstellung `[]`, also das bisherige Verhalten. -/
structure Programm where
  D        : Deklaration
  sig      : String → Option Signatur
  schleife : String → Option Umgebung
  ruferR   : List String := []

/-- Der Sichtbereich beim EINTRITT in einen Gerufenen: seine Parameter. -/
def paramUmgebung : List (String × Option Shape) → Umgebung
  | [] => []
  | (n, some sh) :: rest => (n, .form sh) :: paramUmgebung rest
  | (_, none) :: rest => paramUmgebung rest

/-- Die Argumente gegen die Parameter: gleich viele, und jedes passt. -/
def argumentePassen (P : Programm) (Δ : Lokal) : List (String × Option Shape) → List Expr → Bool
  | [], [] => true
  | (_, ziel) :: ps, e :: es =>
      match schluss P.D Δ e with
      | some sh => passtIn sh ziel && argumentePassen P Δ ps es
      | none => false
  | _, _ => false

/-! ## 2. Der Pruefer ueber Anweisungen -/

/-- Die Gestalt des Binders eines `match`-Arms, aus der Nutzlast seines Falls. -/
def nutzlastGestalt : Option (Option (Int × Int)) → Option Shape
  | none => none
  | some none => some .int
  | some (some (lo, hi)) => some (.intIn lo hi)

/-- Der Fall eines `tagged`-Typs mit diesem Namen -- der erste. -/
def suchFall : List (String × Option (Option (Int × Int))) → String → Option (Option (Option (Int × Int)))
  | [], _ => none
  | (t, pl) :: rest, x => if t = x then some pl else suchFall rest x

/-- Jeder Fall hat einen Arm (`D005`: kein Fall bleibt ohne Zweig). -/
def alleFaelleHabenArm (arms : List (String × Option String × List Stmt)) :
    List (String × Option (Option (Int × Int))) → Bool
  | [] => true
  | (t, _) :: rest => arms.any (fun a => a.1 == t) && alleFaelleHabenArm arms rest

def alleGruendeHabenArm (arms : List (String × List Stmt)) : List String → Bool
  | [] => true
  | r :: rest => arms.any (fun a => a.1 == r) && alleGruendeHabenArm arms rest

/-- (U4): keine zwei Faelle mit demselben Namen. -/
def namenEindeutig : List (String × Option (Option (Int × Int))) → Bool
  | [] => true
  | (t, _) :: rest => !(rest.any (fun c => c.1 == t)) && namenEindeutig rest

/-- Namen, die keiner zweimal traegt (U3 an den Parametern). -/
def namenFrei : List String → Bool
  | [] => true
  | n :: rest => !(rest.contains n) && namenFrei rest

theorem bindAll_fremd (names : List String) : ∀ (vs : List Value) (β : Binding) (m : String),
    m ∉ names → bindAll names vs β m = β m := by
  induction names with
  | nil => intro vs β m _; cases vs <;> rfl
  | cons n ns ih =>
      intro vs β m hm
      cases vs with
      | nil => rfl
      | cons v vs =>
          simp only [bindAll]
          have hmn : m ≠ n := fun h => hm (h ▸ List.mem_cons_self)
          have hmns : m ∉ ns := fun h => hm (List.mem_cons_of_mem _ h)
          rw [ih vs _ m hmns]
          simp only [bindLocal, hmn, ↓reduceIte]

/-- Die Antwort eines Gerufenen in die Antwort des Rufers (`return f(a);`). -/
def antwortGestaltPasst : Option Shape → Option Shape → Bool
  | some z, some sh => passt sh z
  | none, none => true
  | _, _ => false

/-- Haelt `rs` jeden Grund von `cs`? Die Boolesche Haelfte von `⊆` (F6). -/
def grundEnthalten : List String → String → Bool
  | [], _ => false
  | c :: rest, r => (r == c) || grundEnthalten rest r

theorem grundEnthalten_mem {rs : List String} {r : String}
    (h : grundEnthalten rs r = true) : r ∈ rs := by
  induction rs with
  | nil => simp only [grundEnthalten, Bool.false_eq_true] at h
  | cons c rest ih =>
      simp only [grundEnthalten, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · simp only [List.mem_cons, true_or]
      · exact List.mem_cons_of_mem _ (ih h)

/-- Der Fehlerkanal des Gerufenen gegen den des Rufers (F6). -/
def gruendePassen : List String → List String → Bool
  | [], _ => true
  | r :: rest, rs => grundEnthalten rs r && gruendePassen rest rs

theorem gruendePassen_mem {cs rs : List String} {r : String}
    (h : gruendePassen cs rs = true) (hm : r ∈ cs) : r ∈ rs := by
  induction cs with
  | nil => simp only [List.not_mem_nil] at hm
  | cons c rest ih =>
      simp only [gruendePassen, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rcases List.mem_cons.mp hm with rfl | hm
      · exact grundEnthalten_mem h1
      · exact ih h2 hm

/-- Der Fehlerzweig eines `let … else` endet mit `return`, `leave`, `next` -- oder mit
    einem Ruf, der nicht zurueckkehrt (F1) -- `M1` verlangt es (`SYNTAX.md`:1029: "the
    `else` branch must diverge or return"). Ohne das liefe der Rumpf mit einer Bindung
    weiter, die keinen Wert bekam. -/
def istAusgang (sig : String → Option Signatur) : Stmt → Bool
  | .ret _ => true
  | .retCall _ _ _ _ => true
  | .leave => true
  | .exit => true
  | .call f _ _ _ =>
      match sig f with
      | some S => S.divergiert
      | none => false
  | _ => false

def endetMitAusgang (sig : String → Option Signatur) : List Stmt → Bool
  | [] => false
  | [a] => istAusgang sig a
  | _ :: rest => endetMitAusgang sig rest

/-- Der Sichtbereich unter der Bedingung -- heute die Identitaet (F5). `Ge` traegt keine
    Wertfakten (`M1`s Fakten -- Vergleiche, Bereiche -- leben nicht in `Umgebung`), also
    verfeinert keine Quellbedingung ihn; die Stelle steht, damit die Polaritaet getragen
    ist, wenn sie es einmal tut. -/
def verfeinere (Δ : Umgebung) (_c : Expr) (_b : Bool) : Umgebung := Δ

theorem verfeinere_erweitert (Δ : Umgebung) (c : Expr) (b : Bool) :
    erweitert Δ (verfeinere Δ c b) :=
  erweitert_refl _

/-- Die Vereinigung zweier Zweigbereiche (F5): stimmt beides ueberein, gilt es danach --
    sonst faellt die Stelle auf den Eintrittsbereich zurueck, wie bisher. Der Vergleich
    ist listenfoermig (reihenfolgeempfindlich); ein Stellungswechsel kostet Praezision,
    nie Lauterkeit. -/
def vereinige (Δ Δt Δe : Umgebung) : Umgebung :=
  if Δt = Δe then Δt else Δ

/-- Der Ruf: die Signatur steht, die Namen der Parameter stimmen, die Argumente passen, und
    die VORBEDINGUNG ist unter den Parametern ein `bool` -- ein `requires`, das steckenbleibt,
    weil es keine Gestalt hat, waere ein Pruefer-Fehler, keiner des Schreibers. -/
def rufPasst (P : Programm) (Δ : Lokal) (f : String) (ps : List String) (as : List Expr)
    (pre : Expr) : Option Signatur :=
  match P.sig f with
  | some S =>
      if ps = S.params.map (·.1) && namenFrei ps && argumentePassen P Δ S.params as
         && (schluss P.D (formen (paramUmgebung S.params)) pre == some .bool)
      then some S else none
  | none => none

end Gabbro.Sicherheit
