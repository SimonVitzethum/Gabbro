/-
  Datei:      Grammatik/Semantik.lean
  Gegenstand: **Was ein Satz der Grammatik BEDEUTET** -- und der Typ, in dem die Bedeutung
              steht, hat genau zwei Fehlerausgaenge.

    `eval`  -- ein Ausdruck liefert IMMER einen Wert seines Typs. Kein `Option`, kein
               `stuck`: es gibt keinen Fall, in dem die Rechnung nicht weiter weiss, weil die
               Grammatik jeden solchen Fall nicht ableitet (Nenner null, Index ausserhalb,
               Bitoperator auf negativer Zahl, falsche Gestalt).
    `exec`  -- eine Anweisung endet in einem `Ausgang`, und `Ausgang` hat sieben
               Konstruktoren: fuenf Kontrollfluss (`ok`, `zurueck`, `grund`, `leave`, `next`)
               und ZWEI Fehler -- `logik` (eine Klausel des Schreibers gilt nicht) und
               `hardware` (eine Annahme ueber die Maschine gilt nicht). **Einen dritten gibt
               es nicht, weil der Typ keinen hat.** Das ist der Satz; `Satz.lean` schreibt
               ihn hin.

  DIE ZWEI FEHLER, und woher jeder kommt
    `Logik.vorbedingung f`  -- `requires` von `f` gilt an der Rufstelle nicht
    `Logik.nachbedingung f` -- `ensures` von `f` gilt am `return` nicht
    `Logik.invariante i`    -- eine Tabellen- oder Gruppeninvariante gilt am Ende eines Rumpfs
                               nicht, der ihren Traeger schreibt (`maintains`)
    `Logik.schleife`        -- die `invariant` einer Schleife gilt an einer Durchgangsgrenze
                               nicht
    `Logik.abstieg f`       -- die Rekursion kommt nicht zum Ende: das `decreases`-Mass faellt
                               nicht (K009: "DASS es faellt, bleibt Beweisersache")
    `Logik.vorzustand`    -- ein `state`-Uebergang `von -> nach`, aber das Feld stand nicht auf `von`
    `Hardware.annahme a`    -- ein `axiom` (jeder fremde Rumpf) antwortet ausserhalb seines Typs
    `Hardware.fortschritt a`-- ein `forever … progress a` wird von der Umgebung nicht beendet
    `Hardware.ieee`         -- eine Gleitkommarechnung verliess ihren erklaerten Bereich
    `Hardware.register r`   -- ein Register antwortete ausserhalb seines erklaerten Typs
    `Hardware.geraet r`     -- ein Register antwortete gegen seine erklaerte Zusage (`requires`)
    `Hardware.sichtbarkeit` -- ein `awaits` sah die Veroeffentlichung nicht: das Speichermodell
                               (A10) hat nicht gehalten

  DIE SPUR -- was die Welt ausserdem mitfuehrt (seit 2026-09-09 abends)
    Jeder Zugriff auf einen Traeger schreibt ein EREIGNIS in die Welt: Traeger, Lesen oder
    Schreiben, das statische Λ der Stelle und die dynamisch GEHALTENEN Sperren. `locks L`
    schreibt `nimmt L` und `gibt L`. `Satz.lean` beweist, dass jedes Ereignis seine Waechter
    traegt (`spur_bewacht`); `Wettlauf.lean` schliesst daraus ueber JEDER Verschraenkung
    solcher Spuren, dass zwei Faeden einen bewachten Traeger nie im Wettlauf beruehren.

  WAS DIE SEMANTIK ANNIMMT -- benannt, als Parameter
    (H1) das `Orakel`: was ein `axiom` tut, kommt von aussen. Sein Ergebnis wird gegen den
         erklaerten Typ gehalten (`annahme`); seine WIRKUNG auf die Welt nicht -- dass es nur
         schreibt, was sein `effects` sagt, ist Annahme A_n, wie `SYNTAX.md`:1646 sie bucht.
    (H2) `forever` bekommt seine Durchgaenge von aussen (`fuel`); sind sie verbraucht, ist
         der Ausgang `fortschritt a` -- die Annahme, die der Schreiber am `progress` nannte.
-/
import Grammatik.Syntax

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Welt und Sichtbereich -/

/-- Ein Ereignis der Spur: ein Zugriff mit dem statischen `Λ` seiner Stelle und den
    dynamisch gehaltenen Sperren, oder das Nehmen und Geben einer Sperre. -/
inductive Ereignis (D : Deklaration) where
  | zugriff (t : D.Tab) (schreibt : Bool) (Λ : List (Res D)) (haelt : List D.Lock)
  | gzugriff (g : D.Glob) (schreibt : Bool) (Λ : List (Res D)) (haelt : List D.Lock)
  /-- Nehmen einer Sperre, mit den zu diesem Zeitpunkt gehaltenen (die Sperre ist nicht darunter:
      der Rang steigt strikt, also nimmt kein Faden eine Sperre zweimal). -/
  | nimmt (L : D.Lock) (haelt : List D.Lock)
  | gibt (L : D.Lock)

/-- Die OFFENEN Sperren einer Spur: was genommen und nicht gegeben ist (neuestes zuerst). -/
def offen : List (Ereignis D) → List D.Lock
  | [] => []
  | .nimmt L _ :: s => L :: offen s
  | .gibt L :: s => (offen s).erase L
  | .zugriff .. :: s => offen s
  | .gzugriff .. :: s => offen s

/-- Die Welt: je Tabelle, Index und Feld ein Wert des erklaerten Typs; je Global einer; dazu
    die Spur dieses Fadens (neuestes zuerst). Die gehaltenen Sperren sind die offenen der Spur. -/
structure World (D : Deklaration) where
  slots : ∀ t : D.Tab, Int → ∀ f : D.Feld t, Wert D (D.typ t f)
  globs : ∀ g : D.Glob, Wert D (D.gtyp g)
  spur : List (Ereignis D)

def World.haelt (σ : World D) : List D.Lock := offen σ.spur

def World.merke (σ : World D) (es : List (Ereignis D)) : World D := { σ with spur := es ++ σ.spur }

/-- Die Lesungen eines Ausdrucks, als Ereignisse mit dem Stand der Sperren. -/
def World.lese (σ : World D) (Λ : List (Res D)) (orte : List (D.Tab ⊕ D.Glob)) : World D :=
  σ.merke (orte.map fun o => match o with
    | .inl t => Ereignis.zugriff t false Λ σ.haelt
    | .inr g => Ereignis.gzugriff g false Λ σ.haelt)

def World.nimmt (σ : World D) (L : D.Lock) : World D := { σ with spur := .nimmt L σ.haelt :: σ.spur }

def World.gibt (σ : World D) (L : D.Lock) : World D := { σ with spur := .gibt L :: σ.spur }

/-- Ein Schreiben in einen Slot: alle anderen Orte bleiben -- der RAHMEN faellt hier aus. -/
def World.storeSlot (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    World D :=
  { σ with slots := fun t' k' f' =>
      if ht : t' = t then
        (by subst ht
            exact if k' = k then (if hf : f' = f then (by subst hf; exact v) else σ.slots t' k' f')
                  else σ.slots t' k' f')
      else σ.slots t' k' f' }

def World.storeGlob (σ : World D) (g : D.Glob) (v : Wert D (D.gtyp g)) : World D :=
  { σ with globs := fun g' =>
      if hg : g' = g then (by subst hg; exact v) else σ.globs g' }

/-- Ein Schreiben MIT seinem Ereignis. -/
def World.schreibSlot (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) : World D :=
  (σ.storeSlot t k f v).merke [.zugriff t true Λ σ.haelt]

def World.schreibGlob (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g)) : World D :=
  (σ.storeGlob g v).merke [.gzugriff g true Λ σ.haelt]

/-- Die Bytes ab `k`, `n` Stueck, aus einem Bytefeld. -/
def World.bytesAb (σ : World D) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) :
    Nat → Int → List Byte
  | 0, _ => []
  | n + 1, k => (cast (congrArg (Wert D) hf) (σ.slots t k f) : Wert D (.int 0 255)) :: σ.bytesAb t f hf n (k + 1)

theorem World.bytesAb_length (σ : World D) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (n : Nat) (k : Int) : (σ.bytesAb t f hf n k).length = n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => exact congrArg (· + 1) (ih (k + 1))

/-- Die Bytes ab `k` schreiben, eines nach dem anderen, jedes mit seinem Ereignis. -/
def World.schreibBytes (σ : World D) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) : Int → List Byte → World D
  | _, [] => σ
  | k, b :: bs => (σ.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes t f hf Λ (k + 1) bs

/-- Die Belegung des Sichtbereichs. -/
inductive Env (D : Deklaration) : Ctx → Type where
  | nil : Env D []
  | cons (v : Wert D τ) (ρ : Env D Γ) : Env D (τ :: Γ)

def Env.get : Env D Γ → Var Γ τ → Wert D τ
  | .cons v _, .hier => v
  | .cons _ ρ, .dort x => ρ.get x

def Env.set : Env D Γ → Var Γ τ → Wert D τ → Env D Γ
  | .cons _ ρ, .hier, v => .cons v ρ
  | .cons w ρ, .dort x, v => .cons w (ρ.set x v)

def Env.tail : Env D (τ :: Γ) → Env D Γ
  | .cons _ ρ => ρ

/-! ## 2. Die Orte eines Ausdrucks -- was er liest -/

mutual

/-- Die Traeger und Globale, die ein Ausdruck liest (statisch; eine Ueberdeckung, denn
    `&&` liest den rechten Operanden nicht immer -- mehr Ereignisse, alle bewacht). -/
def Expr.orte : Expr D Γ Λ τ → List (D.Tab ⊕ D.Glob)
  | .lit _ | .wahr | .falsch | .var _ | .ptrOf _ _ _ _ | .fnref _ _ _ | .none _ | .grund _ _ => []
  | .glob g _ => [.inr g]
  | .slot t _ i _ => .inl t :: i.orte
  | .durch p t _ _ i _ => p.orte ++ .inl t :: i.orte
  | .altGlob g _ => [.inr g]
  | .altSlot t _ i _ => .inl t :: i.orte
  | .leseBytes t _ _ _ i _ _ _ => .inl t :: i.orte
  | .weiter _ _ e => e.orte
  | .add a b | .sub a b | .mul a b | .div _ _ a b | .rem _ _ a b | .sdiv _ a b | .srem _ a b
  | .band _ _ a b | .bor _ _ _ _ _ a b | .bxor _ _ _ _ _ a b | .shl _ _ _ _ _ a b | .shr _ _ _ _ _ a b
  | .lt a b | .le a b | .eq a b | .fllt a b | .flle a b | .und a b | .oder a b => a.orte ++ b.orte
  | .neg a | .nicht a | .some a | .istSome a => a.orte
  | .fall _ _ nutz => nutz.orte
  | .forallSlots t body _ | .existsSlots t body _ => .inl t :: body.orte
  | .reaches t _ _ a b _ => .inl t :: a.orte ++ b.orte

def NutzlastExpr.orte : NutzlastExpr D Γ Λ c → List (D.Tab ⊕ D.Glob)
  | .keine => []
  | .zahl e => e.orte

end

def Args.orte : Args D Γ Λ τs → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons e rest => e.orte ++ rest.orte

def ErgExpr.orte : ErgExpr D Γ Λ e → List (D.Tab ⊕ D.Glob)
  | .keine => []
  | .wert e => e.orte

/-! ## 3. Die Bedeutung eines Ausdrucks -- total -/

/-- Ein Wahrheitswert, als `Bool` gelesen. -/
def wahr? {D : Deklaration} (v : Wert D .bool) : Bool := v

/-- Alle Indizes `0 ..< n`, als Werte des Indextyps. -/
def alleIndizes (n : Int) : List (Zahl 0 (n - 1)) :=
  (List.range n.toNat).filterMap fun (k : Nat) =>
    if h : ((k : Nat) : Int) ≤ n - 1 then some ⟨((k : Nat) : Int), by omega, h⟩ else none

/-- Die Kette ueber ein `option index`-Feld, mit Treibstoff: `k` erreicht `ziel`, wenn eine
    Folge von hoechstens `fuel` Schritten dort ankommt. Total, weil der Treibstoff endlich ist. -/
def kette (weiter : Int → Option (Zahl 0 (n - 1))) : Nat → Int → Int → Bool
  | 0, k, ziel => decide (k = ziel)
  | fuel + 1, k, ziel =>
      if k = ziel then true else
      match weiter k with
      | Option.none => false
      | Option.some m => kette weiter fuel m.n ziel

mutual

/-- `σ₀` ist die Welt beim EINTRITT (fuer `old(…)` in `ensures`); im Rumpf ist sie `σ`. -/
def eval (σ₀ : World D) : Expr D Γ Λ τ → World D → Env D Γ → Wert D τ
  | .lit n, _, _ => ⟨n, Int.le_refl _, Int.le_refl _⟩
  | .wahr, _, _ => true
  | .falsch, _, _ => false
  | .var x, _, ρ => ρ.get x
  | .glob g _, σ, _ => σ.globs g
  | .slot t f i _, σ, ρ => σ.slots t (eval σ₀ i σ ρ).n f
  | .durch _ t _ f i _, σ, ρ => σ.slots t (eval σ₀ i σ ρ).n f
  | .ptrOf _ _ _ _, _, _ => ()
  | .fnref f _ h, _, _ => ⟨f, h⟩
  | .altGlob g _, _, _ => σ₀.globs g
  | .altSlot t f i _, σ, ρ => σ₀.slots t (eval σ₀ i σ ρ).n f
  | .weiter h1 h2 e, σ, ρ => Zahl.weiter h1 h2 (eval σ₀ e σ ρ)
  | .add a b, σ, ρ => Zahl.add (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .sub a b, σ, ρ => Zahl.sub (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .neg a, σ, ρ => Zahl.neg (eval σ₀ a σ ρ)
  | .mul a b, σ, ρ => Zahl.mul (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .div h0 h1 a b, σ, ρ => Zahl.div h0 h1 (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .rem h0 h1 a b, σ, ρ => Zahl.rem h0 h1 (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .sdiv hb a b, σ, ρ => Zahl.sdiv hb (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .srem hb a b, σ, ρ => Zahl.srem hb (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .leseBytes t f hf n i _ _ _, σ, ρ =>
      let bs := σ.bytesAb t f hf n (eval σ₀ i σ ρ).n
      ⟨bytesZuZahl bs, (bytesZuZahl_bereich bs).1, by
        have := (bytesZuZahl_bereich bs).2; rw [World.bytesAb_length] at this; exact this⟩
  | .band h0 h0' a b, σ, ρ => Zahl.band h0 h0' (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .bor w h0 h0' hw1 hw2 a b, σ, ρ => Zahl.bor w h0 h0' hw1 hw2 (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .bxor w h0 h0' hw1 hw2 a b, σ, ρ => Zahl.bxor w h0 h0' hw1 hw2 (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .shl w hw1 hw2 h0 h0' a b, σ, ρ => Zahl.shl w hw1 hw2 h0 h0' (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .shr w hw1 hw2 h0 h0' a b, σ, ρ => Zahl.shr w hw1 hw2 h0 h0' (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .lt a b, σ, ρ => decide ((eval σ₀ a σ ρ).n < (eval σ₀ b σ ρ).n)
  | .le a b, σ, ρ => decide ((eval σ₀ a σ ρ).n ≤ (eval σ₀ b σ ρ).n)
  | .eq a b, σ, ρ => decide ((eval σ₀ a σ ρ).n = (eval σ₀ b σ ρ).n)
  | .fllt a b, σ, ρ => decide ((eval σ₀ a σ ρ).x < (eval σ₀ b σ ρ).x)
  | .flle a b, σ, ρ => decide ((eval σ₀ a σ ρ).x ≤ (eval σ₀ b σ ρ).x)
  | .und a b, σ, ρ => (wahr? (eval σ₀ a σ ρ) && wahr? (eval σ₀ b σ ρ) : Bool)
  | .oder a b, σ, ρ => (wahr? (eval σ₀ a σ ρ) || wahr? (eval σ₀ b σ ρ) : Bool)
  | .nicht a, σ, ρ => (!wahr? (eval σ₀ a σ ρ) : Bool)
  | .none _, _, _ => Option.none
  | .some e, σ, ρ => Option.some (eval σ₀ e σ ρ)
  | .istSome e, σ, ρ => (eval σ₀ e σ ρ).isSome
  | .fall cs i nutz, σ, ρ => ⟨i, evalNutz σ₀ nutz σ ρ⟩
  | .grund _ r, _, _ => r
  | .forallSlots t body _, σ, ρ =>
      (alleIndizes (D.count t)).all fun k => wahr? (eval σ₀ body σ (.cons k ρ))
  | .existsSlots t body _, σ, ρ =>
      (alleIndizes (D.count t)).any fun k => wahr? (eval σ₀ body σ (.cons k ρ))
  | .reaches t f hf a b _, σ, ρ =>
      kette (fun k => hf ▸ σ.slots t k f) (D.count t).toNat (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n

def evalNutz (σ₀ : World D) : NutzlastExpr D Γ Λ c → World D → Env D Γ → Nutzlast c
  | .keine, _, _ => ()
  | .zahl e, σ, ρ => eval σ₀ e σ ρ

end

def evalArgs (σ₀ : World D) : Args D Γ Λ τs → World D → Env D Γ → Env D τs
  | .nil, _, _ => .nil
  | .cons e rest, σ, ρ => .cons (eval σ₀ e σ ρ) (evalArgs σ₀ rest σ ρ)

/-! ## 3. Die Ausgaenge -- genau zwei davon sind Fehler -/

/-- Die Logik des Schreibers: eine Klausel, die er schrieb, gilt nicht. -/
inductive Logik (D : Deklaration) where
  | vorbedingung (f : D.Fn)
  | nachbedingung (f : D.Fn)
  | invariante (i : D.Inv)
  | schleife
  | abstieg (f : D.Fn)
  /-- Ein `state`-Uebergang `von -> nach`, aber das Feld stand nicht auf `von`.
      `Vorzustand`, nicht `Uebergang`: das alte Schlüsselwort ist abgelegt, und der
      Ausgang heisst nach dem, was nicht stimmte (PFLICHTEN.md «B26»). -/
  | vorzustand

/-- Die Hardware: eine Annahme ueber die Maschine gilt nicht. -/
inductive Hardware (D : Deklaration) where
  | annahme (a : D.Ax)
  | fortschritt (a : D.Annahme)
  /-- Eine Gleitkommarechnung verliess ihren erklaerten Bereich, oder wurde NaN/unendlich:
      IEEE 754 ist die Maschine, und ihr Rundungsverhalten ist die Annahme («F»). -/
  | ieee
  /-- Ein Register antwortete ausserhalb seines erklaerten Typs. -/
  | register (r : D.Reg)
  /-- Ein Register antwortete gegen seine erklaerte Zusage (`requires` ohne `else`): die
      Annahme ueber das Geraet, am Register benannt. -/
  | geraet (r : D.Reg)
  /-- Ein `awaits` sah die Veroeffentlichung nicht, die es erwartet: das Speichermodell (A10). -/
  | sichtbarkeit (a : D.Annahme)

/-- Der Wert einer Antwort. -/
def ErgVal (D : Deklaration) : Option Ty → Type
  | Option.none => Unit
  | Option.some τ => Wert D τ

/-- **Der Ausgangstyp.** `l` sagt, ob `leave`/`next` moeglich sind (nur in einer Schleife). -/
inductive Ausgang (V : Vertrag D) : Bool → Ctx → Type where
  | ok (σ : World D) (ρ : Env D Γ) : Ausgang V l Γ
  | zurueck (σ : World D) (v : ErgVal D V.erg) : Ausgang V l Γ
  | grund (σ : World D) (r : Fin V.gruende) : Ausgang V l Γ
  | leave (h : l = true) (σ : World D) (ρ : Env D Γ) : Ausgang V l Γ
  | next (h : l = true) (σ : World D) (ρ : Env D Γ) : Ausgang V l Γ
  | logik (e : Logik D) : Ausgang V l Γ
  | hardware (e : Hardware D) : Ausgang V l Γ

variable {V : Vertrag D}

/-- Ein Ausgang, der nicht `ok` ist -- was ein `Endblock` liefert. -/
inductive EndAusgang (V : Vertrag D) : Bool → Ctx → Type where
  | zurueck (σ : World D) (v : ErgVal D V.erg) : EndAusgang V l Γ
  | grund (σ : World D) (r : Fin V.gruende) : EndAusgang V l Γ
  | leave (h : l = true) (σ : World D) (ρ : Env D Γ) : EndAusgang V l Γ
  | next (h : l = true) (σ : World D) (ρ : Env D Γ) : EndAusgang V l Γ
  | logik (e : Logik D) : EndAusgang V l Γ
  | hardware (e : Hardware D) : EndAusgang V l Γ

/-- Was ein Ruf liefert -- im Vertrag des GERUFENEN. -/
inductive RufAusgang {D : Deklaration} (f : D.Fn) : Type where
  | ok (σ : World D) (v : ErgVal D (D.erg f))
  | grund (σ : World D) (r : Fin (D.gruende f))
  | logik (e : Logik D)
  | hardware (e : Hardware D)

/-! ## 4. Das Orakel -- die Hardware, als Parameter -/

/-- Ein rohes Ergebnis der Maschine, gegen einen Typ gehalten: passt es nicht, ist die
    Annahme widerlegt. -/
def einpassen : (τ : Ty) → Int → Option (Wert D τ)
  | .int lo hi, n => if h : lo ≤ n ∧ n ≤ hi then some ⟨n, h.1, h.2⟩ else Option.none
  | .bool, n => some (decide (n ≠ 0))
  | .opt m, n => if h : 0 ≤ n ∧ n ≤ m - 1 then some (some ⟨n, h.1, h.2⟩)
                 else if n < 0 then some Option.none else Option.none
  | .sum _, _ => Option.none
  | .grund m, n => if h : 0 ≤ n ∧ n < m then some ⟨n.toNat, by omega⟩ else Option.none
  | .never, _ => Option.none
  | .fl _ _, _ => Option.none
  | .fnptr _, _ => Option.none
  | .ptr _ _, _ => some ()

def einpassenErg : (τ : Option Ty) → Int → Option (ErgVal D τ)
  | Option.none, _ => some ()
  | Option.some τ, n => einpassen τ n

/-- (H1) Was ein Axiom tut: eine neue Welt und eine rohe Antwort. -/
structure Orakel (D : Deklaration) where
  wirkt : ∀ a : D.Ax, World D → Env D (D.aparams a) → World D × Int
  /-- Eine Registerlesung: die Maschine antwortet roh. -/
  regLies : D.Reg → World D → Int
  /-- Ein Registerschreiben: das Geraet ist nicht Teil der Welt; die Welt bleibt. -/
  regSchreib : D.Reg → Int → Unit
  /-- (A10) Ob ein `awaits` auf `g` die letzte Veroeffentlichung SIEHT -- das Speichermodell
      der Maschine, als Antwort. -/
  sichtbar : D.Glob → World D → Bool

/-! ## 5. Die Bedeutung einer Anweisung -/

/-- Der Sichtbereich von `ensures`: die Antwort vor den Parametern. -/
def ergEnv : (e : Option Ty) → ErgVal D e → Env D Γ → Env D (ErgCtx Γ e)
  | Option.none, _, ρ => ρ
  | Option.some _, v, ρ => .cons v ρ

/-- Die Invarianten, die ein Rumpf von `f` am Ende schuldet: alle ueber Traegern, die er
    schreibt (`maintains`, aus `effects` abgeleitet -- «SG-I»). -/
def schuldet (f : D.Fn) (i : D.Inv) : Bool :=
  (D.traeger i).any fun t => D.schreibt f t

/-- Ein Ausgang aus einem Unterblock mit erweitertem Sichtbereich, zurueck in den aeusseren. -/
def Ausgang.schrumpf : Ausgang V l (τ :: Γ) → Ausgang V l Γ
  | .ok σ ρ => .ok σ ρ.tail
  | .zurueck σ v => .zurueck σ v
  | .grund σ r => .grund σ r
  | .leave h σ ρ => .leave h σ ρ.tail
  | .next h σ ρ => .next h σ ρ.tail
  | .logik e => .logik e
  | .hardware e => .hardware e

def Ausgang.schrumpfArm : (c : Option (Int × Int)) → Ausgang V l (ArmCtx Γ c) → Ausgang V l Γ
  | Option.none, a => a
  | Option.some (_, _), a => a.schrumpf

def EndAusgang.schrumpf : EndAusgang V l (τ :: Γ) → EndAusgang V l Γ
  | .zurueck σ v => .zurueck σ v
  | .grund σ r => .grund σ r
  | .leave h σ ρ => .leave h σ ρ.tail
  | .next h σ ρ => .next h σ ρ.tail
  | .logik e => .logik e
  | .hardware e => .hardware e

def EndAusgang.zuAusgang : EndAusgang V l Γ → Ausgang V l Γ
  | .zurueck σ v => .zurueck σ v
  | .grund σ r => .grund σ r
  | .leave h σ ρ => .leave h σ ρ
  | .next h σ ρ => .next h σ ρ
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- Die Welt eines Ausgangs umbauen (Sperre geben). -/
def Ausgang.mapWelt (f : World D → World D) : Ausgang V l Γ → Ausgang V l Γ
  | .ok σ ρ => .ok (f σ) ρ
  | .zurueck σ v => .zurueck (f σ) v
  | .grund σ r => .grund (f σ) r
  | .leave h σ ρ => .leave h (f σ) ρ
  | .next h σ ρ => .next h (f σ) ρ
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- Ein Ausgang, der im Rumpf einer Schleife entstand, gesehen von der Anweisung, in der
    die Schleife steht: `leave` und `next` sind dort verbraucht. -/
def Ausgang.ausSchleife : Ausgang V true Γ → Ausgang V l Γ
  | .ok σ ρ => .ok σ ρ
  | .zurueck σ v => .zurueck σ v
  | .grund σ r => .grund σ r
  | .leave _ σ ρ => .ok σ ρ
  | .next _ σ ρ => .ok σ ρ
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- **Ein Durchlauf ueber die Indizes** (`traverse … by unvisited`): jeder Index einmal, die
    `invariant` an jeder Grenze, `next` beendet den Durchgang, `leave` die Schleife. -/
def traverseLauf (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) :
    List (Wert D τ) → World D → Env D Γ → Ausgang V l Γ
  | [], σ, ρ => if (inv σ ρ).2 = true then .ok (inv σ ρ).1 ρ else .logik .schleife
  | k :: ks, σ, ρ =>
      if (inv σ ρ).2 = false then .logik .schleife else
      match schritt (inv σ ρ).1 (.cons k ρ) with
      | .ok σ' ρ' => traverseLauf schritt inv ks σ' ρ'.tail
      | .next _ σ' ρ' => traverseLauf schritt inv ks σ' ρ'.tail
      | .leave _ σ' ρ' => if (inv σ' ρ'.tail).2 = true then .ok (inv σ' ρ'.tail).1 ρ'.tail else .logik .schleife
      | .zurueck σ' v => .zurueck σ' v
      | .grund σ' r => .grund σ' r
      | .logik e => .logik e
      | .hardware e => .hardware e

/-- `retry until p bounded n … on_exceeded { … }`: hoechstens `n` Durchgaenge. -/
def retryLauf (schritt : World D → Env D Γ → Ausgang V true Γ) (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) :
    Nat → World D → Env D Γ → Ausgang V l Γ
  | 0, σ, ρ => ueberlauf σ ρ
  | n + 1, σ, ρ =>
      if (bis σ ρ).2 = true then .ok (bis σ ρ).1 ρ else
      match schritt (bis σ ρ).1 ρ with
      | .ok σ' ρ' => retryLauf schritt bis ueberlauf n σ' ρ'
      | .next _ σ' ρ' => retryLauf schritt bis ueberlauf n σ' ρ'
      | .leave _ σ' ρ' => .ok σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .grund σ' r => .grund σ' r
      | .logik e => .logik e
      | .hardware e => .hardware e

/-- `forever … progress a { … }` (H2): `passes` Durchgaenge von aussen; danach steht der
    Ausgang bei der Annahme `a`. -/
def foreverLauf (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    Nat → World D → Env D Γ → Ausgang V l Γ
  | 0, _, _ => .hardware (.fortschritt a)
  | n + 1, σ, ρ =>
      if (inv σ ρ).2 = false then .logik .schleife else
      match schritt (inv σ ρ).1 ρ with
      | .ok σ' ρ' => foreverLauf a schritt inv n σ' ρ'
      | .next _ σ' ρ' => foreverLauf a schritt inv n σ' ρ'
      | .leave _ σ' ρ' => .ok σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .grund σ' r => .grund σ' r
      | .logik e => .logik e
      | .hardware e => .hardware e

variable (P : Programm D) (O : Orakel D)

-- (H2) Wie viele Durchgaenge die Umgebung einem `forever` gibt.
variable (passes : Nat)

/-- Die Antwort eines Rufs, in den Typ der Bindung uebersetzt (`D.erg f = some τ`). -/
def ergWert {τ : Ty} {e : Option Ty} (he : e = some τ) (v : ErgVal D e) : Wert D τ := by
  subst he; exact v

/-- Die Nutzlast eines Falls in den Sichtbereich seines Arms. -/
def armEnv {c : Option (Int × Int)} (nutz : Nutzlast c) (ρ : Env D Γ) : Env D (ArmCtx Γ c) :=
  match c, nutz with
  | Option.none, _ => ρ
  | Option.some (_, _), v => .cons v ρ

def evalErg (σ₀ : World D) : ErgExpr D Γ Λ e → World D → Env D Γ → ErgVal D e
  | .keine, _, _ => ()
  | .wert e, σ, ρ => eval σ₀ e σ ρ

/-- Die Argumente eines indirekten Rufs, in die Parameter der GERUFENEN Funktion: dieselbe
    Signatur, per `sig f = n`. -/
def umsig {f : D.Fn} {n : Nat} (hf : D.sig f = n) (ρ : Env D (D.sigNr n).params) :
    Env D (D.params f) := by
  unfold Deklaration.params Deklaration.signatur; rw [hf]; exact ρ

def keinGrundSig {f : D.Fn} {n : Nat} (hf : D.sig f = n) (hr : (D.sigNr n).gruende = 0)
    (r : Fin (D.gruende f)) : α := by
  unfold Deklaration.gruende Deklaration.signatur at r; rw [hf, hr] at r; exact r.elim0

theorem ergSig {f : D.Fn} {n : Nat} {τ : Ty} (hf : D.sig f = n) (he : (D.sigNr n).erg = some τ) :
    D.erg f = some τ := by
  unfold Deklaration.erg Deklaration.signatur; rw [hf]; exact he

/-- Ein Wert als rohe Zahl, fuer die Maschine. -/
def roh : {τ : Ty} → Wert D τ → Int
  | .int _ _, v => v.n
  | .bool, b => if wahr? b then 1 else 0
  | .opt _, Option.none => -1
  | .opt _, Option.some k => k.n
  | .sum _, ⟨i, _⟩ => i.val
  | .grund _, r => r.val
  | .never, v => v.elim
  | .fl _ _, v => v.x.toInt64.toInt
  | .fnptr _, _ => 0
  | .ptr _ _, _ => 0

/-- Die Gleitkommarechnung der Maschine. -/
def gleitRechne : GleitOp → Float → Float → Float
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

/-- Ein Maschinenergebnis gegen den erklaerten Bereich: endlich und drin, oder nichts. -/
def gleitPasst (lo hi : Int × Int) (x : Float) : Option (Gleit lo hi) :=
  if h : x.isFinite = true ∧ bruch lo ≤ x ∧ x ≤ bruch hi then some ⟨x, h.1, h.2.1, h.2.2⟩
  else Option.none

section Rumpf
-- Die Bedeutung eines Rufs auf dieser Rekursionstiefe -- von aussen gegeben, und in
-- `rufAt` aus dem Rumpf des Gerufenen gebaut.
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- Ein Ruf, dessen Signatur keinen Fehlerkanal hat, liefert keinen Grund. -/
def keinGrund {f : D.Fn} (hr : D.gruende f = 0) (r : Fin (D.gruende f)) : α :=
  (Fin.cast hr r).elim0

/-- Das Ergebnis eines Axioms, gegen seinen Typ gehalten. -/
def axiomAntwort (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    World D × Option (ErgVal D (D.aerg a)) :=
  let (σ', roh) := O.wirkt a σ ρ
  (σ', einpassenErg (D.aerg a) roh)

mutual

def execStmt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .assignSlot t f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignDurch p t _ f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignGlob g e _ _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .schreibBytes t f hf n i _ _ e _ _, σ, ρ =>
      let σ := σ.lese Λ (i.orte ++ e.orte)
      .ok (σ.schreibBytes t f hf Λ (eval σ i σ ρ).n (zahlZuBytes n (eval σ e σ ρ).n)) ρ
  | .assignVar x e, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok σ (ρ.set x (eval σ e σ ρ))
  | .uebergang t f hτ i von nach hn _ _ _, σ, ρ =>
      let σ := σ.lese Λ (.inl t :: i.orte)
      let k := (eval σ i σ ρ).n
      if (hτ ▸ σ.slots t k f : Zahl _ _).n = von
      then .ok (σ.schreibSlot t Λ k f (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ
      else .logik .vorzustand
  | .ite c t e, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlock t σ ρ else execBlock e σ ρ
  | .onOption o p a, σ, ρ =>
      let σ := σ.lese Λ o.orte
      match eval σ o σ ρ with
      | Option.some k => (execBlock p σ (.cons k ρ)).schrumpf
      | Option.none => execBlock a σ ρ
  | .onTag v arms, σ, ρ =>
      let σ := σ.lese Λ v.orte
      execArms arms (eval σ v σ ρ) σ ρ
  | .onGrund r arms, σ, ρ =>
      let σ := σ.lese Λ r.orte
      execGrund arms (eval σ r σ ρ) σ ρ
  | .call f args _ hr, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' _ => .ok σ' ρ
      | .grund _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .callInd p args _ hr, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' _ => .ok σ' ρ
      | .grund _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .locks L _ body, σ, ρ => (execBlock body (σ.nimmt L) ρ).mapWelt (·.gibt L)
  | .breaking _ body, σ, ρ => execBlock body σ ρ
  | .traverse t inv body, σ, ρ =>
      traverseLauf (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (alleIndizes (D.count t)) σ ρ
  | .retry n bis body ueberlauf, σ, ρ =>
      retryLauf (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
        (fun σ ρ => execBlock ueberlauf σ ρ) n σ ρ
  | .forever a inv body, σ, ρ =>
      foreverLauf a (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) passes σ ρ
  | .axiomCall a args _ _ _ _ _, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some _) => .ok σ' ρ
      | (_, Option.none) => .hardware (.annahme a)
  | .regSchreib r _ e, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let _ := O.regSchreib r (roh (eval σ e σ ρ))
      .ok σ ρ
  | .transition r _ m _ _ maske bits, σ, ρ =>
      let alt := O.regLies m σ
      let _ := O.regSchreib r (((alt.toNat &&& (Nat.xor maske.toNat (2 ^ 64 - 1))) ||| bits.toNat : Nat) : Int)
      .ok σ ρ
  | .publish g e _ _ _ _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .advances _ _ _ _, σ, ρ => .ok σ ρ
  | .retires _ _ _ _, σ, ρ => .ok σ ρ
  | .ret e _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retGrund r _, σ, _ => .grund σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ

def execBlock {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .nil, σ, ρ => .ok σ ρ
  | .cons s rest, σ, ρ =>
      match execStmt s σ ρ with
      | .ok σ' ρ' => execBlock rest σ' ρ'
      | o => o
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execBlock rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .grund _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .grund _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .grund σ' r => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .regLies r _ rest, σ, ρ =>
      match einpassen (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execBlock rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regLiesElse r _ zusage sonst rest, σ, ρ =>
      match einpassen (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := σ.lese Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execBlock rest σ (.cons v ρ)).schrumpf
          else (execEnd sonst σ ρ).zuAusgang
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ rest, σ, ρ =>
      if O.sichtbar g σ then
        let σ := σ.lese Λ [.inr g]
        (execBlock rest σ (.cons (σ.globs g) ρ)).schrumpf
      else .hardware (.sichtbarkeit D.a10)
  | .exchange g neu _ _ rest, σ, ρ =>
      let σ := σ.lese Λ (.inr g :: neu.orte)
      let alt := σ.globs g
      (execBlock rest (σ.schreibGlob g Λ (eval σ neu σ (.cons alt ρ))) (.cons alt ρ)).schrumpf
  | .narrow e lo' hi' sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execBlock rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else (execEnd sonst σ ρ).zuAusgang
  | .pruefung c sonst rest, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlock rest σ ρ else (execEnd sonst σ ρ).zuAusgang
  | .gleit op a b lo hi rest, σ, ρ =>
      let σ := σ.lese Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ a σ ρ).x (eval σ b σ ρ).x) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .hardware .ieee
  | .gleitLit q lo hi rest, σ, ρ =>
      match gleitPasst lo hi (bruch q) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .hardware .ieee
  | .gleitVon e lo hi rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (Float.ofInt (eval σ e σ ρ).n) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .hardware .ieee
  | .gleitNarrow e lo hi sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (eval σ e σ ρ).x with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => (execEnd sonst σ ρ).zuAusgang

def execEnd {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → World D → Env D Γ → EndAusgang V l Γ
  | .ret e _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retGrund r _, σ, _ => .grund σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ
  | .cons s rest, σ, ρ =>
      match execStmt s σ ρ with
      | .ok σ' ρ' => execEnd rest σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .grund σ' r => .grund σ' r
      | .leave h σ' ρ' => .leave h σ' ρ'
      | .next h σ' ρ' => .next h σ' ρ'
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execEnd rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf

def execArms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → Wert D (.sum cs) → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨⟨0, _⟩, nutz⟩, σ, ρ => (execBlock b σ (armEnv nutz ρ)).schrumpfArm _
  | .cons _ rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

def execGrund {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Fin n → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨0, _⟩, σ, ρ => execBlock b σ ρ
  | .cons _ rest, ⟨i + 1, h⟩, σ, ρ => execGrund rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Rumpf

/-! ## 6. Der Ruf -- `requires`, der Rumpf, `ensures`, die Invarianten; und die Tiefe -/

/-- Die Bedeutung eines Rufs auf Tiefe `fuel`: die Vorbedingung, der Rumpf, die
    Nachbedingung, die geschuldeten Invarianten. Ist die Tiefe erschoepft, ist das Mass
    nicht gefallen -- `abstieg`, eine Logikstelle. -/
def rufAt : Nat → ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f
  | 0, f, _, _ => .logik (.abstieg f)
  | n + 1, f, σ, ρ =>
      let σ := σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
      if wahr? (eval σ (P.requires f) σ ρ) = false then .logik (.vorbedingung f) else
      match execEnd (V := vertragVon D f) O passes (rufAt n) (P.rumpf f) σ ρ with
      | EndAusgang.zurueck σ' v =>
          let σ' := σ'.lese (vertragVon D f).ende (P.ensures f).orte
          if wahr? (eval σ (P.ensures f) σ' (ergEnv (D.erg f) v ρ)) = false then .logik (.nachbedingung f)
          else
            let σ' := (D.invs.filter (schuldet f)).foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ'
            match D.invs.find? (fun i => schuldet f i && !wahr? (eval σ' (P.invariante i) σ' .nil)) with
            | Option.some i => .logik (.invariante i)
            | Option.none => .ok σ' v
      | .grund σ' r => .grund σ' r
      | .leave h _ _ => absurd h (by decide)
      | .next h _ _ => absurd h (by decide)
      | .logik e => .logik e
      | .hardware e => .hardware e

/-- **Die Bedeutung eines Rumpfs** in einem Programm, auf Rekursionstiefe `fuel`. -/
def exec (fuel : Nat) (V : Vertrag D) (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    Ausgang V l Γ :=
  execBlock O passes (rufAt P O passes fuel) b σ ρ

/-! ## 7. User partition and async device step -- shapes beside the run, no discharge -/

/-! ### 7.1 The two sides of one boundary, over the flat key space -/

/-- The two sides of one boundary: kernel memory and user memory. The world stays
    one flat mapping (`slots`/`globs`/`spur` above); the partition is a side per key,
    not a second world -- so every existing theorem reads the same `World`. -/
inductive Seite where
  | kern
  | user
  deriving DecidableEq, Repr

/-- A side assignment over the flat key space: each table slot has one side. -/
def SeitenWahl (D : Deklaration) : Type :=
  D.Tab → Int → Seite

/-- The user side, as a boolean test. -/
def istUserSeite : Seite → Bool
  | .user => true
  | .kern => false

/-- The kernel side, as a boolean test. -/
def istKernSeite : Seite → Bool
  | .kern => true
  | .user => false

/-- A world key on the user side: the assignment says `user`. -/
def benutzerSchluessel (w : SeitenWahl D) (t : D.Tab) (k : Int) : Prop :=
  w t k = .user

/-- A world key on the kernel side: the assignment says `kern`. -/
def kernSchluessel (w : SeitenWahl D) (t : D.Tab) (k : Int) : Prop :=
  w t k = .kern

/-- The partition covers and separates: every key is on exactly one side. -/
theorem seite_zerlegt (w : SeitenWahl D) (t : D.Tab) (k : Int) :
    (benutzerSchluessel w t k ∨ kernSchluessel w t k) ∧
    ¬ (benutzerSchluessel w t k ∧ kernSchluessel w t k) := by
  constructor
  · cases h : w t k <;> simp_all [benutzerSchluessel, kernSchluessel]
  · cases h : w t k <;> simp_all [benutzerSchluessel, kernSchluessel]

/-- The flat mapping is preserved across the partition: a store to one carrier
    leaves every slot of another carrier untouched -- the frame the partition
    checks against, still stated on `World.slots`. -/
theorem seite_rahmen_fremd (σ : World D) {t t' : D.Tab} (h : t' ≠ t)
    (k k' : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) (f' : D.Feld t') :
    (σ.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f' := by
  simp [World.storeSlot, h]

/-! ### 7.2 The async device write beside `Orakel.wirkt` -/

/-- An async device write to carrier `t`, world to world -- beside `Orakel.wirkt`,
    which acts AT a call site (`D.Ax` plus its `Env`). This shape takes neither:
    no axiom, no call site, no argument environment. What it may change is the
    DMA-visible buffer carrier `t` alone: every other carrier, every global, and
    the trace stay -- the frame half. What the write OBSERVES (content) is not
    stated here: events carry no values, so no run fact implies it. -/
structure GeraetSchreibt (t : D.Tab) (σ σ' : World D) : Prop where
  sichtbar : D.geteilt t = true
  rahmen : ∀ t' : D.Tab, t' ≠ t → ∀ k' : Int, ∀ f' : D.Feld t', σ'.slots t' k' f' = σ.slots t' k' f'
  globale : ∀ g : D.Glob, σ'.globs g = σ.globs g
  spur : σ'.spur = σ.spur

/-- The window around an async device write: handoff before, take-back after --
    the `vor`/`nach` premise shape of `GeraetWache` (Geraet.lean), stated over
    worlds instead of run indices. At the handoff the guard is released (not held
    in `σ`); at the take-back it is held again (held in `σ'`). The CPU-side
    ordering against these endpoints stays driver duty, as `haussen` there. -/
structure GeraetFensterWelt (W : D.Lock) (t : D.Tab) (σ σ' : World D) : Prop where
  schritt : GeraetSchreibt t σ σ'
  vor : W ∉ σ.haelt
  nach : W ∈ σ'.haelt

/-- A windowed device write leaves every foreign carrier untouched. -/
theorem asyncFenster_rahmen {W : D.Lock} {t : D.Tab} {σ σ' : World D}
    (w : GeraetFensterWelt W t σ σ') {t' : D.Tab} (h : t' ≠ t)
    (k' : Int) (f' : D.Feld t') :
    σ'.slots t' k' f' = σ.slots t' k' f' :=
  w.schritt.rahmen t' h k' f'

/-- A windowed device write leaves the trace untouched -- locks held stay held. -/
theorem asyncFenster_spur {W : D.Lock} {t : D.Tab} {σ σ' : World D}
    (w : GeraetFensterWelt W t σ σ') :
    σ'.spur = σ.spur :=
  w.schritt.spur

/-! ### Cuts (booked, not hidden)

    (S1) The partition is a shape over the flat key space; no `Stmt`/`Block`
         transition discharges it -- a range check inside `exec` stays future work.
    (S2) The async step is a shape beside `Orakel.wirkt`; there is no interleaving
         with `exec` runs here and no content invariant -- order without content
         leaves the content half open, content without order the race half open.
-/

end Gabbro.Grammatik
