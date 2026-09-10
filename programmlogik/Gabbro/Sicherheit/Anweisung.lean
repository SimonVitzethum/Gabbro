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
    dokumente/SPRACHE.md:615   -- "Gabbro proves everything except logic."
    dokumente/BEWEIS.md:18     -- "Whoever proves a Gabbro program proves the LOGIC of their
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
-/
import Gabbro.Sicherheit.Ausdruck

namespace Gabbro.Sicherheit

open Gabbro.Body

/-! ## 1. Der Sichtbereich, und die Signaturen -/

/-- Was ein lokaler Name traegt: eine Gestalt, oder -- nach `let … else (e)` -- einen GRUND
    aus einer erklaerten Liste von Faellen. -/
inductive Ge where
  | form (sh : Shape)
  | grund (faelle : List String)
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
  | .grund cs, v => ∃ r, r ∈ cs ∧ v = .reason r

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

/-- Passt ein gerechneter Wert in die Gestalt des Ziels? Das ist `M104` an der Zuweisung:
    ein Bereich in einen weiteren, eine Zahl ohne Bereich nur in `.int`. -/
def passt : Shape → Shape → Bool
  | .intIn lo hi, .intIn lo' hi' => decide (lo' ≤ lo ∧ hi ≤ hi')
  | .intIn _ _, .int => true
  | .int, .int => true
  | .bool, .bool => true
  | .opt, .opt => true
  | .sum a, .sum b => decide (a = b)
  | _, _ => false

theorem passt_hasShape {a b : Shape} {v : Value} (hp : passt a b = true) (hv : v.hasShape a = true) :
    v.hasShape b = true := by
  cases a <;> cases b <;> simp [passt] at hp
  · exact hv
  · obtain ⟨n, rfl⟩ := Value.hasShape_bool_true v hv; simp [Value.hasShape]
  · exact hv
  · obtain ⟨n, rfl, h1, h2⟩ := Value.hasShape_intIn_true v _ _ hv; simp [Value.hasShape]
  · obtain ⟨n, rfl, h1, h2⟩ := Value.hasShape_intIn_true v _ _ hv; simp [Value.hasShape]; omega
  · subst hp; exact hv

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

/-- Das Programm, wie der Pruefer es sieht: Deklarationen, Signaturen, und je Schleife der
    Sichtbereich, unter dem sie steht (U2). -/
structure Programm where
  D        : Deklaration
  sig      : String → Option Signatur
  schleife : String → Option Umgebung

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
          simp [bindLocal, hmn]

/-- Die Antwort eines Gerufenen in die Antwort des Rufers (`return f(a);`). -/
def antwortGestaltPasst : Option Shape → Option Shape → Bool
  | some z, some sh => passt sh z
  | none, none => true
  | _, _ => false

/-- Der Fehlerzweig eines `let … else` endet mit `return`, `leave` oder `next` -- `M1`
    verlangt es (`SYNTAX.md`:1029: "the `else` branch must diverge or return"). Ohne das
    liefe der Rumpf mit einer Bindung weiter, die keinen Wert bekam. -/
def istAusgang : Stmt → Bool
  | .ret _ => true
  | .retCall _ _ _ _ => true
  | .leave => true
  | .exit => true
  | _ => false

def endetMitAusgang : List Stmt → Bool
  | [] => false
  | [a] => istAusgang a
  | _ :: rest => endetMitAusgang rest

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

mutual

/-- **Der Pruefer.** `erg` ist die erklaerte Antwortgestalt der Funktion, in der die
    Anweisung steht -- ein `return e` muss sie treffen. -/
def pruefe (P : Programm) (erg : Option Shape) : Umgebung → Stmt → Option Umgebung
  | Δ, .assign c i f e =>
      match schluss P.D (formen Δ) i, schluss P.D (formen Δ) e with
      | some (.intIn lo hi), some sh =>
          if 0 ≤ lo ∧ hi < P.D.count c ∧ passtIn sh (P.D.slot c f) then some Δ else none
      | _, _ => none
  | Δ, .assignField c f e =>
      match schluss P.D (formen Δ) e with
      | some sh => if passtIn sh (P.D.feld c f) then some Δ else none
      | none => none
  | Δ, .assignGlobal g e =>
      match schluss P.D (formen Δ) e with
      | some sh => if passtIn sh (P.D.global g) then some Δ else none
      | none => none
  | Δ, .bindName n e =>
      match schluss P.D (formen Δ) e with
      | some sh => binde Δ n (.form sh)
      | none => none
  | Δ, .ite c t e =>
      match schluss P.D (formen Δ) c, pruefeBlock P erg Δ t, pruefeBlock P erg Δ e with
      | some .bool, some _, some _ => some Δ
      | _, _, _ => none
  | Δ, .onOption g bn onP onA =>
      match schluss P.D (formen Δ) g, binde Δ bn (.form .int) with
      | some .opt, some ΔP =>
          match pruefeBlock P erg ΔP onP, pruefeBlock P erg Δ onA with
          | some _, some _ => some Δ
          | _, _ => none
      | _, _ => none
  | Δ, .call f ps as pre =>
      match rufPasst P (formen Δ) f ps as pre with
      | some S => if S.gruende = [] then some Δ else none
      | none => none
  | Δ, .bindCall n f ps as pre =>
      match rufPasst P (formen Δ) f ps as pre with
      | some S =>
          match S.ergebnis with
          | some sh => if S.gruende = [] then binde Δ n (.form sh) else none
          | none => none
      | none => none
  | Δ, .bindCallElse n f ps as pre err onErr =>
      match rufPasst P (formen Δ) f ps as pre with
      | some S =>
          if S.gruende = [] then none else
          if !endetMitAusgang onErr then none else
          match binde Δ err (.grund S.gruende) with
          | some ΔE =>
              match pruefeBlock P erg ΔE onErr with
              | some _ =>
                  match S.ergebnis with
                  | some sh => binde Δ n (.form sh)
                  -- `fn f() or R` ohne Wert: die Bindung bekommt `absent`, also `.opt`.
                  | none => binde Δ n (.form .opt)
              | none => none
          | none => none
      | none => none
  | Δ, .onReason (.name g) arms =>
      match such Δ g with
      | some (.grund cs) =>
          if alleGruendeHabenArm arms cs then pruefeArme P erg Δ arms else none
      | _ => none
  | _, .onReason _ _ => none
  | Δ, .onTag g arms =>
      match schluss P.D (formen Δ) g with
      | some (.sum cs) =>
          if namenEindeutig cs && alleFaelleHabenArm arms cs then pruefeTags P erg Δ cs arms
          else none
      | _ => none
  | Δ, .retCall f ps as pre =>
      match rufPasst P (formen Δ) f ps as pre with
      | some S => if S.gruende = [] && antwortGestaltPasst erg S.ergebnis then some Δ else none
      | none => none
  | Δ, .loop id inv body =>
      match P.schleife id, schluss P.D (formen Δ) inv with
      | some ΔS, some .bool =>
          -- Der registrierte Sichtbereich ist genau der hier gueltige (U2).
          if ΔS = Δ then
            match pruefeBlock P erg Δ body with
            | some _ => some Δ
            | none => none
          else none
      | _, _ => none
  | Δ, .locked _ b => match pruefeBlock P erg Δ b with | some _ => some Δ | none => none
  | Δ, .breaking _ b => match pruefeBlock P erg Δ b with | some _ => some Δ | none => none
  | Δ, .publish a e _ =>
      match schluss P.D (formen Δ) e with
      | some sh => if passtIn sh (P.D.global a) then some Δ else none
      | none => none
  | Δ, .awaitLoad n a _ =>
      -- Ein `atomic` ohne erklaerte Gestalt kennt das Modell nicht: Absage.
      match P.D.global a with
      | some sh => binde Δ n (.form sh)
      | none => none
  | Δ, .exchangeWith n a e =>
      match schluss P.D (formen Δ) e, P.D.global a with
      | some sh, some za => if passt sh za then binde Δ n (.form za) else none
      | _, _ => none
  | Δ, .ret none => if erg = none then some Δ else none
  | Δ, .ret (some e) =>
      match schluss P.D (formen Δ) e, erg with
      | some sh, some z => if passt sh z then some Δ else none
      | _, _ => none
  | Δ, .exit => some Δ
  | Δ, .leave => some Δ

def pruefeBlock (P : Programm) (erg : Option Shape) : Umgebung → List Stmt → Option Umgebung
  | Δ, [] => some Δ
  | Δ, a :: rest =>
      match pruefe P erg Δ a with
      | some Δ' => pruefeBlock P erg Δ' rest
      | none => none

def pruefeArme (P : Programm) (erg : Option Shape) (Δ : Umgebung) :
    List (String × List Stmt) → Option Umgebung
  | [] => some Δ
  | (_, b) :: rest =>
      match pruefeBlock P erg Δ b with
      | some _ => pruefeArme P erg Δ rest
      | none => none

/-- Jeder Arm nennt einen Fall des Typs, sein Binder passt zur Nutzlast des Falls, und sein
    Rumpf geht unter dem Binder durch. -/
def pruefeTags (P : Programm) (erg : Option Shape) (Δ : Umgebung)
    (cs : List (String × Option (Option (Int × Int)))) :
    List (String × Option String × List Stmt) → Option Umgebung
  | [] => some Δ
  | (t, bd, b) :: rest =>
      match suchFall cs t with
      | some pl =>
          match nutzlastGestalt pl with
          | some sh =>
              match bd with
              | some v =>
                  match binde Δ v (.form sh) with
                  | some Δ' =>
                      match pruefeBlock P erg Δ' b with
                      | some _ => pruefeTags P erg Δ cs rest
                      | none => none
                  | none => none
              | none => none
          | none =>
              match bd with
              | none =>
                  match pruefeBlock P erg Δ b with
                  | some _ => pruefeTags P erg Δ cs rest
                  | none => none
              | some _ => none
      | none => none

end

/-! ## 3. Die LOGIK-Stellen -- wo das Modell aus einem Grund stecken bleibt, den kein Pass
    tragen kann. Jeder Konstruktor ohne Rekursion nennt eine Klausel des Schreibers. -/

/-- Der Eintrittszustand eines Gerufenen. -/
def eintritt (s : State) (ps : List String) (vs : List Value) : State :=
  { world := s.world, local' := bindAll ps vs (fun _ => .absent) }

mutual

inductive LogikS (ρ : Env) : Stmt → State → Prop
  /-- `requires` des Gerufenen gilt nicht an der Rufstelle -- `ownRequires`. -/
  | ruf {f ps as pre s vs} :
      evalAll s as = some vs → eval (eintritt s ps vs) pre ≠ some (.bool true) →
      LogikS ρ (.call f ps as pre) s
  | rufGebunden {n f ps as pre s vs} :
      evalAll s as = some vs → eval (eintritt s ps vs) pre ≠ some (.bool true) →
      LogikS ρ (.bindCall n f ps as pre) s
  | rufSonst {n f ps as pre err onErr s vs} :
      evalAll s as = some vs → eval (eintritt s ps vs) pre ≠ some (.bool true) →
      LogikS ρ (.bindCallElse n f ps as pre err onErr) s
  | rufZurueck {f ps as pre s vs} :
      evalAll s as = some vs → eval (eintritt s ps vs) pre ≠ some (.bool true) →
      LogikS ρ (.retCall f ps as pre) s
  /-- Die `invariant` gilt beim Eintritt in die Schleife nicht -- `ownInvariant`. -/
  | invariante {id inv body s} :
      eval s inv ≠ some (.bool true) → LogikS ρ (.loop id inv body) s
  -- Die Weitergabe: die Stelle liegt in einem Unterblock.
  | dann {c t e s} : eval s c = some (.bool true) → LogikB ρ t s → LogikS ρ (.ite c t e) s
  | sonst {c t e s} : eval s c = some (.bool false) → LogikB ρ e s → LogikS ρ (.ite c t e) s
  | vorhanden {g bn onP onA s k} : eval s g = some (.present k) →
      LogikB ρ onP { s with local' := bindLocal s.local' bn (.int k) } →
      LogikS ρ (.onOption g bn onP onA) s
  | abwesend {g bn onP onA s} : eval s g = some .absent → LogikB ρ onA s →
      LogikS ρ (.onOption g bn onP onA) s
  | fehlerzweig {n f ps as pre err onErr s vs x} :
      evalAll s as = some vs → (ρ f (eintritt s ps vs)).2 = some (.reason x) →
      LogikB ρ onErr { world := (ρ f (eintritt s ps vs)).1.world,
                       local' := bindLocal s.local' err (.reason x) } →
      LogikS ρ (.bindCallElse n f ps as pre err onErr) s
  | grundArm {g arms s x} : eval s g = some (.reason x) → LogikA ρ arms x s →
      LogikS ρ (.onReason g arms) s
  | fallArm {g arms s x p} : eval s g = some (.tagged x p) → LogikT ρ arms x p s →
      LogikS ρ (.onTag g arms) s
  | gesperrt {l b s} : LogikB ρ b s → LogikS ρ (.locked l b) s
  | ausgesetzt {i b s} : LogikB ρ b s → LogikS ρ (.breaking i b) s

inductive LogikB (ρ : Env) : List Stmt → State → Prop
  | kopf {a rest s} : LogikS ρ a s → LogikB ρ (a :: rest) s
  | weiter {a rest s s'} : step ρ a s = .running s' → LogikB ρ rest s' → LogikB ρ (a :: rest) s

inductive LogikA (ρ : Env) : List (String × List Stmt) → String → State → Prop
  | hier {n b rest x s} : n = x → LogikB ρ b s → LogikA ρ ((n, b) :: rest) x s
  | dort {n b rest x s} : n ≠ x → LogikA ρ rest x s → LogikA ρ ((n, b) :: rest) x s

inductive LogikT (ρ : Env) : List (String × Option String × List Stmt) → String → Option Int →
    State → Prop
  | hierMit {n v b rest x k s} : n = x →
      LogikB ρ b { s with local' := bindLocal s.local' v (.int k) } →
      LogikT ρ ((n, some v, b) :: rest) x (some k) s
  | hierOhne {n b rest x p s} : n = x → LogikB ρ b s → LogikT ρ ((n, none, b) :: rest) x p s
  | dort {n bd b rest x p s} : n ≠ x → LogikT ρ rest x p s → LogikT ρ ((n, bd, b) :: rest) x p s

end

/-! ## 4. Die Praemissen ueber die UMGEBUNG -- (U1) und (U2) -/

/-- Die Welt, wie beide Haelften sie brauchen. -/
def Welt (D : Deklaration) (Γ : Typing) (σ : World) : Prop :=
  WF Γ σ ∧ KettenWohlgeformt D σ

/-- **(U1)** Jeder erklaerte Gerufene haelt die Welt und antwortet gemaess Signatur. -/
def UmgebungOK (P : Programm) (Γ : Typing) (ρ : Env) : Prop :=
  ∀ f S, P.sig f = some S → ∀ t, Welt P.D Γ t.world →
    Welt P.D Γ (ρ f t).1.world ∧
    (match S.ergebnis with
     | some sh => ∃ v, (ρ f t).2 = some v ∧ (v.hasShape sh = true ∨ ∃ r, r ∈ S.gruende ∧ v = .reason r)
     | none => (ρ f t).2 = none ∨ ∃ r, r ∈ S.gruende ∧ (ρ f t).2 = some (.reason r))

/-- **(U2)** Jede registrierte Schleife haelt die Welt und ihren Sichtbereich. -/
def SchleifenOK (P : Programm) (Γ : Typing) (ρ : Env) : Prop :=
  ∀ id Δ, P.schleife id = some Δ → ∀ t, Welt P.D Γ t.world → WFU Δ t.local' →
    Welt P.D Γ (ρ id t).1.world ∧ WFU Δ (ρ id t).1.local'

/-! ## 5. Hilfssaetze -/

theorem Welt_store {D : Deklaration} {Γ : Typing} {σ : World} (_hD : Deklariert D Γ)
    (hw : Welt D Γ σ) (p : Place) (v : Value)
    (hv : ∀ sh, Γ p = some sh → v.hasShape sh = true)
    (hk : ∀ c k via, p = .slot c k via → D.slot c via = some .opt → v.hasShape .opt = true) :
    Welt D Γ (store σ p v) := by
  refine ⟨WF_store Γ σ p v hw.1 hv, ?_⟩
  intro c via k hvia
  simp only [store]
  split
  · rename_i h; exact hk c k via h.symm hvia
  · exact hw.2 c via k hvia

/-- Ein Wert, der in eine Slotstelle passt, haelt beide Haelften der Welt. -/
theorem Welt_store_slot {D : Deklaration} {Γ : Typing} {σ : World} (hD : Deklariert D Γ)
    (hw : Welt D Γ σ) (c : String) (k : Int) (f : String) (v : Value) (sh : Shape)
    (hk0 : 0 ≤ k) (hk1 : k < D.count c) (hvs : v.hasShape sh = true)
    (hp : passtIn sh (D.slot c f) = true) :
    Welt D Γ (store σ (.slot c k f) v) := by
  apply Welt_store hD hw
  · intro sh' hΓ
    rw [hD.1 c k f hk0 hk1] at hΓ
    unfold passtIn at hp; rw [hΓ] at hp
    exact passt_hasShape hp hvs
  · intro c' k' via heq hvia
    cases heq
    unfold passtIn at hp; rw [hvia] at hp
    exact passt_hasShape hp hvs

theorem Welt_store_field {D : Deklaration} {Γ : Typing} {σ : World} (hD : Deklariert D Γ)
    (hw : Welt D Γ σ) (c f : String) (v : Value) (sh : Shape)
    (hvs : v.hasShape sh = true) (hp : passtIn sh (D.feld c f) = true) :
    Welt D Γ (store σ (.field c f) v) := by
  apply Welt_store hD hw
  · intro sh' hΓ
    rw [hD.2.1 c f] at hΓ
    unfold passtIn at hp; rw [hΓ] at hp
    exact passt_hasShape hp hvs
  · intro _ _ _ heq; cases heq

theorem Welt_store_global {D : Deklaration} {Γ : Typing} {σ : World} (hD : Deklariert D Γ)
    (hw : Welt D Γ σ) (g : String) (v : Value) (sh : Shape)
    (hvs : v.hasShape sh = true) (hp : passtIn sh (D.global g) = true) :
    Welt D Γ (store σ (.global g) v) := by
  apply Welt_store hD hw
  · intro sh' hΓ
    rw [hD.2.2 g] at hΓ
    unfold passtIn at hp; rw [hΓ] at hp
    exact passt_hasShape hp hvs
  · intro _ _ _ heq; cases heq

/-- Ein angenommener Ausdruck unter dem Sichtbereich: die Form, die unten gebraucht wird. -/
theorem schluss_sicher' {P : Programm} {Γ : Typing} (hD : Deklariert P.D Γ) {Δ : Umgebung}
    {s : State} {e : Expr} {sh : Shape} (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local')
    (h : schluss P.D (formen Δ) e = some sh) :
    ∃ v, eval s e = some v ∧ v.hasShape sh = true :=
  schluss_sicher P.D Γ hD e (formen Δ) s sh hw.1 (WFU_formen hl) hw.2 h

/-- Die Argumente werten aus, und die Parameter liegen danach in ihrem Sichtbereich. -/
theorem argumente_sicher {P : Programm} {Γ : Typing} (hD : Deklariert P.D Γ) {Δ : Umgebung}
    {s : State} (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local') :
    ∀ (params : List (String × Option Shape)) (as : List Expr) (β : Binding),
      namenFrei (params.map (·.1)) = true →
      argumentePassen P (formen Δ) params as = true →
      ∃ vs, evalAll s as = some vs ∧
        WFU (paramUmgebung params) (bindAll (params.map (·.1)) vs β) := by
  intro params
  induction params with
  | nil =>
      intro as β _ h
      cases as with
      | nil => exact ⟨[], rfl, fun n g hn => by simp [paramUmgebung, such] at hn⟩
      | cons _ _ => simp [argumentePassen] at h
  | cons p ps ih =>
      intro as β hfrei h
      cases as with
      | nil => simp [argumentePassen] at h
      | cons e es =>
          obtain ⟨n, ziel⟩ := p
          simp only [argumentePassen] at h
          split at h
          · rename_i sh hsh
            simp only [Bool.and_eq_true] at h
            obtain ⟨hp, hrest⟩ := h
            simp only [List.map, namenFrei, Bool.and_eq_true, Bool.not_eq_true'] at hfrei
            obtain ⟨hnin, hfrei'⟩ := hfrei
            have hnin' : n ∉ ps.map (·.1) := fun hmem => by
              have h := List.contains_iff_mem.mpr hmem
              rw [h] at hnin; cases hnin
            obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hsh
            obtain ⟨vs, hvs', hrec⟩ := ih es (bindLocal β n v) hfrei' hrest
            refine ⟨v :: vs, by simp [evalAll, hv, hvs'], ?_⟩
            intro m g hm
            cases ziel with
            | none =>
                simp only [paramUmgebung] at hm
                simpa [List.map, bindAll] using hrec m g hm
            | some z =>
                simp only [paramUmgebung, such] at hm
                split at hm
                · rename_i hmn; subst hmn; cases hm
                  simp only [List.map, bindAll]
                  rw [bindAll_fremd _ vs _ n hnin']
                  simp only [bindLocal_here]
                  show Value.hasShape _ _ = true
                  exact passt_hasShape (by unfold passtIn at hp; simpa using hp) hvs
                · rename_i hmn
                  simpa [List.map, bindAll] using hrec m g hm
          · cases h



/-! ## 6. Der Sicherheitssatz fuer Anweisungen -/

/-- Passt die Antwort zur erklaerten Antwortgestalt? -/
def AntwortPasst : Option Shape → Option Value → Prop
  | some sh, some v => v.hasShape sh = true
  | none, none => True
  | _, _ => False

/-- **Was nach einem Schritt gilt** -- je Ausgang. `Δ0` ist der Sichtbereich beim Eintritt,
    `Δ'` der nach der Anweisung; ein Ausgang aus einem Block (`return`, `next`, `leave`)
    traegt den beim Eintritt, weil ein Block Namen nur HINZUFUEGT (U3). `stuck` ist FALSCH:
    das ist die Aussage. -/
def Ergebnis (P : Programm) (Γ : Typing) (erg : Option Shape) (Δ0 Δ' : Umgebung) :
    Outcome → Prop
  | .running s' => Welt P.D Γ s'.world ∧ WFU Δ' s'.local'
  | .returned s' v => Welt P.D Γ s'.world ∧ WFU Δ0 s'.local' ∧ AntwortPasst erg v
  | .exited s' => Welt P.D Γ s'.world ∧ WFU Δ0 s'.local'
  | .left s' => Welt P.D Γ s'.world ∧ WFU Δ0 s'.local'
  | .stuck => False

theorem Ergebnis_schwaecher {P : Programm} {Γ : Typing} {erg : Option Shape}
    {Δ0 Δ1 Δ' Δ'' : Umgebung} {o : Outcome} (h0 : erweitert Δ0 Δ1) (h1 : erweitert Δ' Δ'')
    (h : Ergebnis P Γ erg Δ1 Δ'' o) : Ergebnis P Γ erg Δ0 Δ' o := by
  cases o <;> simp only [Ergebnis] at h ⊢
  · exact ⟨h.1, WFU_erweitert h1 h.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2.1, h.2.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2⟩

mutual

theorem pruefe_erweitert (P : Programm) (erg : Option Shape) :
    ∀ (st : Stmt) (Δ Δ' : Umgebung), pruefe P erg Δ st = some Δ' → erweitert Δ Δ'
  | .assign c i f e, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .assignField c f e, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .assignGlobal g e, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .bindName n e, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · exact binde_erweitert h
      · cases h
  | .ite c t e, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · cases h; exact erweitert_refl _
      · cases h
  | .onOption g bn onP onA, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .call f ps as pre, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .bindCall n f ps as pre, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · split at h
          · exact binde_erweitert h
          · cases h
        · cases h
      · cases h
  | .bindCallElse n f ps as pre err onErr, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · split at h
              · split at h
                · exact binde_erweitert h
                · exact binde_erweitert h
              · cases h
            · cases h
      · cases h
  | .onReason (.name g) arms, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · exact pruefeArme_erweitert P erg Δ arms Δ' h
        · cases h
      · cases h
  | .onReason (.lit _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.global _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.place _ _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.un _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.bin _ _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.someOf _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.fieldOf _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.forallSlots _ _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.existsSlots _ _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.reaches _ _ _ _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.chainFrom _ _ _ _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.hasShape _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.wrapTo _ _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onReason (.tagOf _ _) _, Δ, Δ', h => by simp [pruefe] at h
  | .onTag g arms, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · exact pruefeTags_erweitert P erg Δ _ arms Δ' h
        · cases h
      · cases h
  | .retCall f ps as pre, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .loop id inv body, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · split at h
          · cases h; exact erweitert_refl _
          · cases h
        · cases h
      · cases h
  | .locked l b, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · cases h; exact erweitert_refl _
      · cases h
  | .breaking i b, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · cases h; exact erweitert_refl _
      · cases h
  | .publish a e pl, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .awaitLoad n a pl, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · exact binde_erweitert h
      · cases h
  | .exchangeWith n a e, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · exact binde_erweitert h
        · cases h
      · cases h
  | .ret none, Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · cases h; exact erweitert_refl _
      · cases h
  | .ret (some e), Δ, Δ', h => by
      simp only [pruefe] at h; split at h
      · split at h
        · cases h; exact erweitert_refl _
        · cases h
      · cases h
  | .exit, Δ, Δ', h => by simp only [pruefe] at h; cases h; exact erweitert_refl _
  | .leave, Δ, Δ', h => by simp only [pruefe] at h; cases h; exact erweitert_refl _

theorem pruefeBlock_erweitert (P : Programm) (erg : Option Shape) :
    ∀ (b : List Stmt) (Δ Δ' : Umgebung), pruefeBlock P erg Δ b = some Δ' → erweitert Δ Δ'
  | [], Δ, Δ', h => by simp only [pruefeBlock] at h; cases h; exact erweitert_refl _
  | a :: rest, Δ, Δ', h => by
      simp only [pruefeBlock] at h; split at h
      · rename_i Δ1 h1
        exact erweitert_trans (pruefe_erweitert P erg a Δ Δ1 h1)
          (pruefeBlock_erweitert P erg rest Δ1 Δ' h)
      · cases h

theorem pruefeArme_erweitert (P : Programm) (erg : Option Shape) (Δ : Umgebung) :
    ∀ (arms : List (String × List Stmt)) (Δ' : Umgebung),
      pruefeArme P erg Δ arms = some Δ' → erweitert Δ Δ'
  | [], Δ', h => by simp only [pruefeArme] at h; cases h; exact erweitert_refl _
  | (n, b) :: rest, Δ', h => by
      simp only [pruefeArme] at h; split at h
      · exact pruefeArme_erweitert P erg Δ rest Δ' h
      · cases h

theorem pruefeTags_erweitert (P : Programm) (erg : Option Shape) (Δ : Umgebung)
    (cs : List (String × Option (Option (Int × Int)))) :
    ∀ (arms : List (String × Option String × List Stmt)) (Δ' : Umgebung),
      pruefeTags P erg Δ cs arms = some Δ' → erweitert Δ Δ'
  | [], Δ', h => by simp only [pruefeTags] at h; cases h; exact erweitert_refl _
  | (t, bd, b) :: rest, Δ', h => by
      simp only [pruefeTags] at h; split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · exact pruefeTags_erweitert P erg Δ cs rest Δ' h
              · cases h
            · cases h
          · cases h
        · split at h
          · split at h
            · exact pruefeTags_erweitert P erg Δ cs rest Δ' h
            · cases h
          · cases h
      · cases h

end


/-! ### 6.1 Was ein angenommener Ruf beim Eintritt hat -/

theorem rufPasst_eq {P : Programm} {Δ : Lokal} {f : String} {ps : List String} {as : List Expr}
    {pre : Expr} {S : Signatur} (h : rufPasst P Δ f ps as pre = some S) :
    P.sig f = some S ∧ ps = S.params.map (·.1) ∧ namenFrei ps = true ∧
    argumentePassen P Δ S.params as = true ∧
    schluss P.D (formen (paramUmgebung S.params)) pre = some .bool := by
  unfold rufPasst at h
  split at h
  · rename_i S' hS
    split at h
    · rename_i hc; cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact ⟨hS, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
    · cases h
  · cases h

/-- Beim Eintritt: die Argumente werten aus, die Parameter liegen in ihrem Sichtbereich, und
    die Vorbedingung ist ein Wahrheitswert -- WELCHER, sagt die Logik. -/
theorem ruf_eintritt {P : Programm} {Γ : Typing} (hD : Deklariert P.D Γ) {Δ : Umgebung}
    {s : State} (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local') {f : String}
    {ps : List String} {as : List Expr} {pre : Expr} {S : Signatur}
    (h : rufPasst P (formen Δ) f ps as pre = some S) :
    ∃ vs, evalAll s as = some vs ∧ ∃ b, eval (eintritt s ps vs) pre = some (.bool b) := by
  obtain ⟨_, hps, hfrei, hargs, hpre⟩ := rufPasst_eq h
  subst hps
  obtain ⟨vs, hvs, hwfu⟩ := argumente_sicher hD hw hl S.params as (fun _ => .absent) hfrei hargs
  refine ⟨vs, hvs, ?_⟩
  have hw' : Welt P.D Γ (eintritt s (S.params.map (·.1)) vs).world := hw
  obtain ⟨v, hv, hvs'⟩ := schluss_sicher' hD hw' hwfu hpre
  obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs'
  exact ⟨b, hv⟩

/-! ### 6.2 `match` -- der Fall ist da, und der Arm passt zu ihm -/

theorem fall_gefunden : ∀ (cs : List (String × Option (Option (Int × Int)))) (x : String)
    (p : Option Int), namenEindeutig cs = true → Shape.caseOk cs x p = true →
    ∃ pl, suchFall cs x = some pl ∧ Shape.payloadOk pl p = true := by
  intro cs
  induction cs with
  | nil => intro x p _ h; simp at h
  | cons c rest ih =>
      intro x p hu h
      obtain ⟨t, pl⟩ := c
      simp only [namenEindeutig, Bool.and_eq_true, Bool.not_eq_true'] at hu
      obtain ⟨hnot, hu'⟩ := hu
      simp only [Shape.caseOk_cons, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      simp only [suchFall]
      rcases h with ⟨rfl, hpl⟩ | h
      · exact ⟨pl, by simp, hpl⟩
      · have hne : t ≠ x := by
          intro heq; subst heq
          -- `x` haette dann einen Fall in `rest`, gegen `hnot`
          have : rest.any (fun c => c.1 == t) = true := by
            unfold Shape.caseOk at h
            simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
            obtain ⟨c, hc, hct, _⟩ := h
            exact ⟨c, hc, hct⟩
          rw [this] at hnot; cases hnot
        simp only [hne, ↓reduceIte]
        exact ih x p hu' h

theorem grund_hat_arm : ∀ (arms : List (String × List Stmt)) (cs : List String) (r : String),
    alleGruendeHabenArm arms cs = true → r ∈ cs → arms.any (fun a => a.1 == r) = true := by
  intro arms cs
  induction cs with
  | nil => intro r _ h; simp at h
  | cons c rest ih =>
      intro r h hr
      simp only [alleGruendeHabenArm, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hr with rfl | hr
      · exact h.1
      · exact ih r h.2 hr

theorem fall_hat_arm : ∀ (arms : List (String × Option String × List Stmt))
    (cs : List (String × Option (Option (Int × Int)))) (x : String) (pl : Option (Option (Int × Int))),
    alleFaelleHabenArm arms cs = true → suchFall cs x = some pl →
    arms.any (fun a => a.1 == x) = true := by
  intro arms cs
  induction cs with
  | nil => intro x pl _ h; simp [suchFall] at h
  | cons c rest ih =>
      intro x pl h hs
      obtain ⟨t, pl'⟩ := c
      simp only [alleFaelleHabenArm, Bool.and_eq_true] at h
      simp only [suchFall] at hs
      split at hs
      · rename_i heq; subst heq; exact h.1
      · exact ih x pl h.2 hs

/-! ### 6.3 Der Satz -/

/-- Die Antwort eines Gerufenen ohne Fehlerkanal, wie (U1) sie zusagt. -/
theorem antwort_ohne_kanal {P : Programm} {Γ : Typing} {ρ : Env} (hU : UmgebungOK P Γ ρ)
    {f : String} {S : Signatur} (hS : P.sig f = some S) (hg : S.gruende = [])
    {t : State} (hw : Welt P.D Γ t.world) :
    Welt P.D Γ (ρ f t).1.world ∧ AntwortPasst S.ergebnis (ρ f t).2 := by
  obtain ⟨hw', hr⟩ := hU f S hS t hw
  refine ⟨hw', ?_⟩
  cases he : S.ergebnis with
  | none =>
      rw [he] at hr
      rcases hr with hr | ⟨r, hr, _⟩
      · rw [hr]; trivial
      · rw [hg] at hr; simp at hr
  | some sh =>
      rw [he] at hr
      obtain ⟨v, hv, hvs⟩ := hr
      rw [hv]
      rcases hvs with hvs | ⟨r, hr, _⟩
      · exact hvs
      · rw [hg] at hr; simp at hr


theorem ausgang_nicht_running (ρ : Env) (a : Stmt) (s s' : State) (h : istAusgang a = true) :
    step ρ a s ≠ .running s' := by
  intro hx
  cases a <;> simp [istAusgang] at h
  case retCall f ps as pre =>
    simp only [step] at hx
    split at hx
    · split at hx <;> simp at hx
    · simp at hx
  case ret v =>
    cases v
    · simp [step] at hx
    · simp only [step] at hx; split at hx <;> simp at hx
  case exit => simp [step] at hx
  case leave => simp [step] at hx

theorem endet_nicht_running (ρ : Env) :
    ∀ (b : List Stmt) (s s' : State), endetMitAusgang b = true → exec ρ b s ≠ .running s'
  | [], s, s', h, _ => by simp [endetMitAusgang] at h
  | [a], s, s', h, hx => by
      simp only [endetMitAusgang] at h
      simp only [exec] at hx
      split at hx
      · rename_i t ht; exact ausgang_nicht_running ρ a s t h ht
      · rename_i o ho; exact ho _ hx
  | a :: b :: rest, s, s', h, hx => by
      have h' : endetMitAusgang (b :: rest) = true := h
      simp only [exec] at hx
      split at hx
      · exact endet_nicht_running ρ (b :: rest) _ s' h' hx
      · rename_i o ho; exact ho _ hx

/-- Ein Ausgang, der KEIN `running` ist, braucht nur den Eintritts-Sichtbereich. -/
theorem Ergebnis_ausgang {P : Programm} {Γ : Typing} {erg : Option Shape}
    {Δ0 Δ1 Δ' Δ'' : Umgebung} {o : Outcome} (h0 : erweitert Δ0 Δ1)
    (hnr : ∀ s', o ≠ .running s') (h : Ergebnis P Γ erg Δ1 Δ'' o) : Ergebnis P Γ erg Δ0 Δ' o := by
  cases o <;> simp only [Ergebnis] at h ⊢
  · exact absurd rfl (hnr _)
  · exact ⟨h.1, WFU_erweitert h0 h.2.1, h.2.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2⟩
  · exact ⟨h.1, WFU_erweitert h0 h.2⟩

theorem antwort_uebertragen {erg z : Option Shape} {v : Option Value}
    (h : antwortGestaltPasst erg z = true) (hv : AntwortPasst z v) : AntwortPasst erg v := by
  cases erg <;> cases z <;> simp [antwortGestaltPasst] at h
  · cases v with
    | none => trivial
    | some _ => exact hv.elim
  · cases v with
    | none => exact hv.elim
    | some w => exact passt_hasShape h hv

theorem pruefeArme_gibt_Δ (P : Programm) (erg : Option Shape) (Δ : Umgebung) :
    ∀ (arms : List (String × List Stmt)) (Δ' : Umgebung),
      pruefeArme P erg Δ arms = some Δ' → Δ' = Δ
  | [], Δ', h => by simp only [pruefeArme] at h; cases h; rfl
  | (n, b) :: rest, Δ', h => by
      simp only [pruefeArme] at h; split at h
      · exact pruefeArme_gibt_Δ P erg Δ rest Δ' h
      · cases h

theorem pruefeTags_gibt_Δ (P : Programm) (erg : Option Shape) (Δ : Umgebung)
    (cs : List (String × Option (Option (Int × Int)))) :
    ∀ (arms : List (String × Option String × List Stmt)) (Δ' : Umgebung),
      pruefeTags P erg Δ cs arms = some Δ' → Δ' = Δ
  | [], Δ', h => by simp only [pruefeTags] at h; cases h; rfl
  | (t, bd, b) :: rest, Δ', h => by
      simp only [pruefeTags] at h; split at h
      · split at h
        · split at h
          · split at h
            · split at h
              · exact pruefeTags_gibt_Δ P erg Δ cs rest Δ' h
              · cases h
            · cases h
          · cases h
        · split at h
          · split at h
            · exact pruefeTags_gibt_Δ P erg Δ cs rest Δ' h
            · cases h
          · cases h
      · cases h

/-- `let n = f() else (e) { … }`, und der Gerufene antwortet mit einem WERT: die Bindung
    bekommt ihn, und er hat die Gestalt der Signatur. -/
theorem bindCallElse_wert {P : Programm} {Γ : Typing} {ρ : Env} {erg : Option Shape}
    {Δ Δ' : Umgebung} {n f err : String} {ps : List String} {as : List Expr} {pre : Expr}
    {onErr : List Stmt} {S : Signatur} {s : State} {vs : List Value} {v : Value}
    (h : (match S.ergebnis with
          | some sh => binde Δ n (.form sh)
          | none => binde Δ n (.form .opt)) = some Δ')
    (hres : match S.ergebnis with
            | some sh => ∃ w, (ρ f (eintritt s ps vs)).2 = some w ∧
                (w.hasShape sh = true ∨ ∃ r, r ∈ S.gruende ∧ w = .reason r)
            | none => (ρ f (eintritt s ps vs)).2 = none ∨
                ∃ r, r ∈ S.gruende ∧ (ρ f (eintritt s ps vs)).2 = some (.reason r))
    (hr2 : (ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).2 = some v)
    (hnr : ∀ x, v ≠ .reason x)
    (hw' : Welt P.D Γ (ρ f (eintritt s ps vs)).1.world) (hl : WFU Δ s.local') :
    Ergebnis P Γ erg Δ Δ'
      (.running { world := (ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).1.world,
                  local' := bindLocal s.local' n v })
    ∨ LogikS ρ (.bindCallElse n f ps as pre err onErr) s := by
  left
  simp only [Ergebnis]
  refine ⟨hw', ?_⟩
  cases he : S.ergebnis with
  | none =>
      rw [he] at h hres
      simp only [eintritt, hr2] at hres
      rcases hres with hres | ⟨r, _, hres⟩
      · cases hres
      · cases hres; exact absurd rfl (hnr r)
  | some sh =>
      rw [he] at h hres
      simp only [eintritt, hr2] at hres
      obtain ⟨w, hw2, hws⟩ := hres
      cases hw2
      rcases hws with hws | ⟨r, _, rfl⟩
      · exact WFU_binde h hl hws
      · exact absurd rfl (hnr r)


mutual

/-- **Der Sicherheitssatz fuer eine Anweisung.** Nimmt der Pruefer sie an, so ist nach dem
    Schritt die Welt wohlgeformt und der Sichtbereich gehalten -- ODER der Schritt steht an
    einer `Logik`-Stelle. `stuck` ohne `Logik` gibt es nicht. -/
theorem pruefe_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) :
    ∀ (st : Stmt) (Δ Δ' : Umgebung) (s : State),
      pruefe P erg Δ st = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' →
      Ergebnis P Γ erg Δ Δ' (step ρ st s) ∨ LogikS ρ st s
  | .assign c i f e, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i lo hi sh hi' he
        split at h
        · rename_i hc; cases h
          obtain ⟨hlo, hhi, hp⟩ := hc
          obtain ⟨vi, hvi, hvis⟩ := schluss_sicher' hD hw hl hi'
          obtain ⟨k, rfl, hk0, hk1⟩ := Value.hasShape_intIn_true vi lo hi hvis
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
          left
          simp only [step, hvi, hv, Ergebnis]
          exact ⟨Welt_store_slot hD hw c k f v sh (by omega) (by omega) hvs hp, hl⟩
        · cases h
      · cases h
  | .assignField c f e, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i sh he
        split at h
        · rename_i hp; cases h
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
          left
          simp only [step, hv, Ergebnis]
          exact ⟨Welt_store_field hD hw c f v sh hvs hp, hl⟩
        · cases h
      · cases h
  | .assignGlobal g e, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i sh he
        split at h
        · rename_i hp; cases h
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
          left
          simp only [step, hv, Ergebnis]
          exact ⟨Welt_store_global hD hw g v sh hvs hp, hl⟩
        · cases h
      · cases h
  | .bindName n e, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i sh he
        obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
        left
        simp only [step, hv, Ergebnis]
        exact ⟨hw, WFU_binde h hl hvs⟩
      · cases h
  | .ite c t e, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i Δt Δe hc ht he; cases h
        obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hc
        obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs
        cases b
        · simp only [step, hv]
          rcases pruefeBlock_sicher P Γ ρ hD hU hS erg e Δ Δe s he hw hl with hr | hlog
          · left; exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg e Δ Δe he) hr
          · right; exact LogikS.sonst hv hlog
        · simp only [step, hv]
          rcases pruefeBlock_sicher P Γ ρ hD hU hS erg t Δ Δt s ht hw hl with hr | hlog
          · left; exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg t Δ Δt ht) hr
          · right; exact LogikS.dann hv hlog
      · cases h
  | .onOption g bn onP onA, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i ΔP hg hb
        split at h
        · rename_i ΔP' ΔA hP hA; cases h
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hg
          rcases Value.hasShape_opt_true v hvs with rfl | ⟨k, rfl⟩
          · simp only [step, hv]
            rcases pruefeBlock_sicher P Γ ρ hD hU hS erg onA Δ ΔA s hA hw hl with hr | hlog
            · left; exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg onA Δ ΔA hA) hr
            · right; exact LogikS.abwesend hv hlog
          · simp only [step, hv]
            have hl' : WFU ΔP (bindLocal s.local' bn (.int k)) :=
              WFU_binde hb hl (by simp [Ge.haelt, Value.hasShape])
            rcases pruefeBlock_sicher P Γ ρ hD hU hS erg onP ΔP ΔP'
                ⟨s.world, bindLocal s.local' bn (.int k)⟩ hP hw hl' with hr | hlog
            · left
              exact Ergebnis_schwaecher (binde_erweitert hb)
                (erweitert_trans (binde_erweitert hb) (pruefeBlock_erweitert P erg onP ΔP ΔP' hP)) hr
            · right; exact LogikS.vorhanden hv hlog
        · cases h
      · cases h
  | .call f ps as pre, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i S hr
        split at h
        · rename_i hg; cases h
          obtain ⟨vs, hvs, b, hb⟩ := ruf_eintritt hD hw hl hr
          obtain ⟨hsig, _⟩ := rufPasst_eq hr
          cases b
          · right; exact LogikS.ruf hvs (by rw [hb]; simp)
          · left
            simp only [step, hvs, eintritt] at hb ⊢
            simp only [hb, Ergebnis]
            exact ⟨(antwort_ohne_kanal hU hsig hg (t := eintritt s ps vs) hw).1, hl⟩
        · cases h
      · cases h
  | .bindCall n f ps as pre, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i S hr
        split at h
        · rename_i sh he
          split at h
          · rename_i hg
            obtain ⟨vs, hvs, b, hb⟩ := ruf_eintritt hD hw hl hr
            obtain ⟨hsig, _⟩ := rufPasst_eq hr
            cases b
            · right; exact LogikS.rufGebunden hvs (by rw [hb]; simp)
            · left
              obtain ⟨hw', ha⟩ := antwort_ohne_kanal hU hsig hg (t := eintritt s ps vs) hw
              rw [he] at ha
              simp only [step, hvs, eintritt] at hb ⊢
              simp only [hb]
              cases hres : (ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).2 with
              | none => simp only [eintritt, hres, AntwortPasst] at ha
              | some v =>
                  simp only [eintritt, hres, AntwortPasst] at ha
                  simp only [Ergebnis]
                  exact ⟨hw', WFU_binde h hl ha⟩
          · cases h
        · cases h
      · cases h
  | .bindCallElse n f ps as pre err onErr, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i S hr
        split at h
        · cases h
        · rename_i hg
          split at h
          · cases h
          · rename_i hEnd'
            have hEnd : endetMitAusgang onErr = true := by simpa using hEnd'
            split at h
            · rename_i ΔE hE
              split at h
              · rename_i ΔE' hErr
                obtain ⟨vs, hvs, b, hb⟩ := ruf_eintritt hD hw hl hr
                obtain ⟨hsig, _⟩ := rufPasst_eq hr
                cases b
                · right; exact LogikS.rufSonst hvs (by rw [hb]; simp)
                · obtain ⟨hw', hres⟩ := hU f S hsig (eintritt s ps vs) hw
                  simp only [step, hvs, eintritt] at hb ⊢
                  simp only [hb]
                  -- Drei Antworten: ein Grund, ein Wert, keine.
                  cases hr2 : (ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).2 with
                  | none =>
                      simp only
                      split at h
                      · rename_i sh he
                        -- Signatur verspricht einen Wert; (U1) widerspricht `none`.
                        rw [he] at hres; simp only [eintritt, hr2] at hres
                        obtain ⟨v, hv, _⟩ := hres; cases hv
                      · rename_i he
                        left
                        simp only [Ergebnis]
                        exact ⟨hw', WFU_binde h hl (by simp [Ge.haelt, Value.hasShape])⟩
                  | some v =>
                      cases v with
                      | reason x =>
                          simp only
                          have hx : x ∈ S.gruende := by
                            cases he : S.ergebnis with
                            | none =>
                                rw [he] at hres; simp only [eintritt, hr2] at hres
                                rcases hres with hres | ⟨r, hr', hr''⟩
                                · cases hres
                                · cases hr''; exact hr'
                            | some sh =>
                                rw [he] at hres; simp only [eintritt, hr2] at hres
                                obtain ⟨w, hw2, hws⟩ := hres
                                cases hw2
                                rcases hws with hws | ⟨r, hr', hr''⟩
                                · cases sh <;> simp [Value.hasShape] at hws
                                · cases hr''; exact hr'
                          have hlE : WFU ΔE (bindLocal s.local' err (.reason x)) :=
                            WFU_binde hE hl ⟨x, hx, rfl⟩
                          rcases pruefeBlock_sicher P Γ ρ hD hU hS erg onErr ΔE ΔE'
                              ⟨(ρ f { world := s.world, local' := bindAll ps vs fun _ => Value.absent }).1.world,
                               bindLocal s.local' err (.reason x)⟩ hErr hw' hlE with hr3 | hlog
                          · left
                            exact Ergebnis_ausgang (binde_erweitert hE)
                              (fun s' => endet_nicht_running ρ onErr _ s' hEnd) hr3
                          · right; exact LogikS.fehlerzweig hvs hr2 hlog
                      | int k => exact bindCallElse_wert h hres hr2 (by simp) hw' hl
                      | bool t => exact bindCallElse_wert h hres hr2 (by simp) hw' hl
                      | absent => exact bindCallElse_wert h hres hr2 (by simp) hw' hl
                      | present k => exact bindCallElse_wert h hres hr2 (by simp) hw' hl
                      | tagged t q => exact bindCallElse_wert h hres hr2 (by simp) hw' hl
              · cases h
            · cases h
      · cases h
  | .onReason (.name g) arms, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i cs hg
        split at h
        · rename_i hall
          obtain ⟨r, hr, hgr⟩ := hl g _ hg
          simp only [step, eval, hgr]
          rcases pruefeArme_sicher P Γ ρ hD hU hS erg Δ arms Δ' r s h
              (grund_hat_arm arms cs r hall hr) hw hl with hres | hlog
          · left; exact hres
          · right; exact LogikS.grundArm (by simp [eval, hgr]) hlog
        · cases h
      · cases h
  | .onReason (.lit _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.global _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.place _ _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.un _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.bin _ _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.someOf _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.fieldOf _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.forallSlots _ _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.existsSlots _ _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.reaches _ _ _ _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.chainFrom _ _ _ _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.hasShape _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.wrapTo _ _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onReason (.tagOf _ _) _, Δ, Δ', s, h, hw, hl => by simp [pruefe] at h
  | .onTag g arms, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i cs hg
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hg
          obtain ⟨x, p, rfl, hok⟩ := Value.hasShape_sum_true v cs hvs
          obtain ⟨pl, hpl, hpok⟩ := fall_gefunden cs x p hc.1 hok
          simp only [step, hv]
          rcases pruefeTags_sicher P Γ ρ hD hU hS erg Δ cs arms Δ' x p s h hc.1
              (fall_hat_arm arms cs x pl hc.2 hpl) hok hw hl with hres | hlog
          · left; exact hres
          · right; exact LogikS.fallArm hv hlog
        · cases h
      · cases h
  | .retCall f ps as pre, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i S hr
        split at h
        · rename_i hc; cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨vs, hvs, b, hb⟩ := ruf_eintritt hD hw hl hr
          obtain ⟨hsig, _⟩ := rufPasst_eq hr
          cases b
          · right; exact LogikS.rufZurueck hvs (by rw [hb]; simp)
          · left
            obtain ⟨hw', ha⟩ := antwort_ohne_kanal hU hsig hc.1 (t := eintritt s ps vs) hw
            simp only [step, hvs, eintritt] at hb ⊢
            simp only [hb, Ergebnis]
            refine ⟨hw', hl, ?_⟩
            exact antwort_uebertragen hc.2 ha
        · cases h
      · cases h
  | .loop id inv body, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i ΔS hreg hinv
        split at h
        · rename_i heq; subst heq
          split at h
          · cases h
            obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl hinv
            obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs
            cases b
            · right; exact LogikS.invariante (by rw [hv]; simp)
            · left
              simp only [step, hv, Ergebnis]
              exact hS id _ hreg s hw hl
          · cases h
        · cases h
      · cases h
  | .locked l b, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i Δb hb; cases h
        simp only [step]
        rcases pruefeBlock_sicher P Γ ρ hD hU hS erg b Δ Δb s hb hw hl with hr | hlog
        · left; exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg b Δ Δb hb) hr
        · right; exact LogikS.gesperrt hlog
      · cases h
  | .breaking i b, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i Δb hb; cases h
        simp only [step]
        rcases pruefeBlock_sicher P Γ ρ hD hU hS erg b Δ Δb s hb hw hl with hr | hlog
        · left; exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg b Δ Δb hb) hr
        · right; exact LogikS.ausgesetzt hlog
      · cases h
  | .publish a e pl, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i sh he
        split at h
        · rename_i hp; cases h
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
          left
          simp only [step, hv, Ergebnis]
          exact ⟨Welt_store_global hD hw a v sh hvs hp, hl⟩
        · cases h
      · cases h
  | .awaitLoad n a pl, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i sh ha
        left
        simp only [step, Ergebnis]
        refine ⟨hw, WFU_binde h hl ?_⟩
        show Value.hasShape _ _ = true
        apply hw.1 (.global a) sh
        rw [hD.2.2 a]; exact ha
      · cases h
  | .exchangeWith n a e, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i sh za he ha
        split at h
        · rename_i hp
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
          left
          simp only [step, hv, Ergebnis]
          refine ⟨Welt_store_global hD hw a v sh hvs (by unfold passtIn; rw [ha]; exact hp),
                  WFU_binde h hl ?_⟩
          show Value.hasShape _ _ = true
          apply hw.1 (.global a) za
          rw [hD.2.2 a]; exact ha
        · cases h
      · cases h
  | .ret none, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i he; cases h; subst he
        left; simp only [step, Ergebnis]; exact ⟨hw, hl, trivial⟩
      · cases h
  | .ret (some e), Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h
      split at h
      · rename_i sh z he
        split at h
        · rename_i hp; cases h
          obtain ⟨v, hv, hvs⟩ := schluss_sicher' hD hw hl he
          left
          simp only [step, hv, Ergebnis, AntwortPasst]
          exact ⟨hw, hl, passt_hasShape hp hvs⟩
        · cases h
      · cases h
  | .exit, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h; cases h
      left; simp only [step, Ergebnis]; exact ⟨hw, hl⟩
  | .leave, Δ, Δ', s, h, hw, hl => by
      simp only [pruefe] at h; cases h
      left; simp only [step, Ergebnis]; exact ⟨hw, hl⟩

theorem pruefeBlock_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) :
    ∀ (b : List Stmt) (Δ Δ' : Umgebung) (s : State),
      pruefeBlock P erg Δ b = some Δ' → Welt P.D Γ s.world → WFU Δ s.local' →
      Ergebnis P Γ erg Δ Δ' (exec ρ b s) ∨ LogikB ρ b s
  | [], Δ, Δ', s, h, hw, hl => by
      simp only [pruefeBlock] at h; cases h
      left; simp only [exec, Ergebnis]; exact ⟨hw, hl⟩
  | a :: rest, Δ, Δ', s, h, hw, hl => by
      simp only [pruefeBlock] at h
      split at h
      · rename_i Δ1 h1
        rcases pruefe_sicher P Γ ρ hD hU hS erg a Δ Δ1 s h1 hw hl with hr | hlog
        · simp only [exec]
          cases ho : step ρ a s with
          | running s' =>
              rw [ho] at hr; simp only [Ergebnis] at hr
              rcases pruefeBlock_sicher P Γ ρ hD hU hS erg rest Δ1 Δ' s' h hr.1 hr.2 with hr2 | hlog2
              · left; exact Ergebnis_schwaecher (pruefe_erweitert P erg a Δ Δ1 h1) (erweitert_refl _) hr2
              · right; exact LogikB.weiter ho hlog2
          | returned s' v => rw [ho] at hr; left; exact hr
          | exited s' => rw [ho] at hr; left; exact hr
          | left s' => rw [ho] at hr; left; exact hr
          | stuck => rw [ho] at hr; exact hr.elim
        · right; exact LogikB.kopf hlog
      · cases h

theorem pruefeArme_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung) :
    ∀ (arms : List (String × List Stmt)) (Δ' : Umgebung) (x : String) (s : State),
      pruefeArme P erg Δ arms = some Δ' → arms.any (fun a => a.1 == x) = true →
      Welt P.D Γ s.world → WFU Δ s.local' →
      Ergebnis P Γ erg Δ Δ' (pickArm ρ arms x s) ∨ LogikA ρ arms x s
  | [], Δ', x, s, h, hx, hw, hl => by simp at hx
  | (n, b) :: rest, Δ', x, s, h, hx, hw, hl => by
      simp only [pruefeArme] at h
      split at h
      · rename_i Δb hb
        simp only [pickArm]
        by_cases hnx : n = x
        · subst hnx
          simp only [↓reduceIte]
          rw [pruefeArme_gibt_Δ P erg Δ rest Δ' h]
          rcases pruefeBlock_sicher P Γ ρ hD hU hS erg b Δ Δb s hb hw hl with hr | hlog
          · left
            exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg b Δ Δb hb) hr
          · right; exact LogikA.hier rfl hlog
        · simp only [hnx, ↓reduceIte]
          have hx' : rest.any (fun a => a.1 == x) = true := by
            simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at hx
            rcases hx with hx | hx
            · exact absurd hx hnx
            · exact hx
          rcases pruefeArme_sicher P Γ ρ hD hU hS erg Δ rest Δ' x s h hx' hw hl with hr | hlog
          · left; exact hr
          · right; exact LogikA.dort hnx hlog
      · cases h

theorem pruefeTags_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape) (Δ : Umgebung)
    (cs : List (String × Option (Option (Int × Int)))) :
    ∀ (arms : List (String × Option String × List Stmt)) (Δ' : Umgebung) (x : String)
      (p : Option Int) (s : State),
      pruefeTags P erg Δ cs arms = some Δ' → namenEindeutig cs = true →
      arms.any (fun a => a.1 == x) = true → Shape.caseOk cs x p = true →
      Welt P.D Γ s.world → WFU Δ s.local' →
      Ergebnis P Γ erg Δ Δ' (pickTag ρ arms x p s) ∨ LogikT ρ arms x p s
  | [], Δ', x, p, s, h, hu, hx, hok, hw, hl => by simp at hx
  | (t, bd, b) :: rest, Δ', x, p, s, h, hu, hx, hok, hw, hl => by
      simp only [pruefeTags] at h
      split at h
      · rename_i pl hpl
        by_cases htx : t = x
        · subst htx
          obtain ⟨pl', hpl', hpok⟩ := fall_gefunden cs t p hu hok
          rw [hpl] at hpl'; cases hpl'
          simp only [pickTag, ↓reduceIte]
          split at h
          · -- eine Nutzlast: der Arm muss binden
            rename_i sh hsh
            split at h
            · rename_i v
              split at h
              · rename_i Δv hv
                split at h
                · rename_i Δb hb
                  rw [pruefeTags_gibt_Δ P erg Δ cs rest Δ' h]
                  obtain ⟨k, rfl⟩ : ∃ k, p = some k := by
                    cases pl with
                    | none => simp [nutzlastGestalt] at hsh
                    | some q => cases p with
                      | none => cases q with
                        | none => simp at hpok
                        | some r => obtain ⟨lo, hi⟩ := r; simp at hpok
                      | some k => exact ⟨k, rfl⟩
                  simp only
                  have hk : (Value.int k).hasShape sh = true := by
                    cases pl with
                    | none => simp [nutzlastGestalt] at hsh
                    | some q => cases q with
                      | none => simp only [nutzlastGestalt, Option.some.injEq] at hsh; subst hsh; simp [Value.hasShape]
                      | some r =>
                          obtain ⟨lo, hi⟩ := r
                          simp only [nutzlastGestalt, Option.some.injEq] at hsh; subst hsh
                          simp only [Shape.payloadOk_range_some, decide_eq_true_eq] at hpok
                          simp [Value.hasShape]; omega
                  have hl' : WFU Δv (bindLocal s.local' v (.int k)) := WFU_binde hv hl hk
                  rcases pruefeBlock_sicher P Γ ρ hD hU hS erg b Δv Δb
                      ⟨s.world, bindLocal s.local' v (.int k)⟩ hb hw hl' with hr | hlog
                  · left
                    exact Ergebnis_schwaecher (binde_erweitert hv)
                      (erweitert_trans (binde_erweitert hv) (pruefeBlock_erweitert P erg b Δv Δb hb)) hr
                  · right; exact LogikT.hierMit rfl hlog
                · cases h
              · cases h
            · cases h
          · -- keine Nutzlast: der Arm bindet nicht
            rename_i hsh
            split at h
            · split at h
              · rename_i Δb hb
                rw [pruefeTags_gibt_Δ P erg Δ cs rest Δ' h]
                have hp : p = none := by
                  cases pl with
                  | none => simpa using hpok
                  | some q => cases q with
                    | none => simp [nutzlastGestalt] at hsh
                    | some r => obtain ⟨lo, hi⟩ := r; simp [nutzlastGestalt] at hsh
                subst hp
                simp only
                rcases pruefeBlock_sicher P Γ ρ hD hU hS erg b Δ Δb s hb hw hl with hr | hlog
                · left
                  exact Ergebnis_schwaecher (erweitert_refl _) (pruefeBlock_erweitert P erg b Δ Δb hb) hr
                · right; exact LogikT.hierOhne rfl hlog
              · cases h
            · cases h
        · simp only [pickTag, htx, ↓reduceIte]
          have hx' : rest.any (fun a => a.1 == x) = true := by
            simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at hx
            rcases hx with hx | hx
            · exact absurd hx htx
            · exact hx
          have hrest : pruefeTags P erg Δ cs rest = some Δ' := by
            split at h
            · split at h
              · split at h
                · split at h
                  · exact h
                  · cases h
                · cases h
              · cases h
            · split at h
              · split at h
                · exact h
                · cases h
              · cases h
          rcases pruefeTags_sicher P Γ ρ hD hU hS erg Δ cs rest Δ' x p s hrest hu hx' hok hw hl with hr | hlog
          · left; exact hr
          · right; exact LogikT.dort htx hlog
      · cases h

end

end Gabbro.Sicherheit
