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
    `Logik.bereich`         -- a float result left its declared range (was `Hardware.ieee`
                               until 2026-09-15: the kernel IEEE model decides it, no oracle)
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
import Grammatik.Kern.Syntax.Syntax
import Grammatik.Bausteine.Gleitkomma.GleitkommaBits

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
  /-- **An answer from outside the program** (2026-10-25): a foreign body is called (`inl a`), a device register is
      read (`inr (inl r)`), or the visibility of an `awaits` on `g` is asked (`inr (inr g)`). Recorded BEFORE the
      machine answers, so the answer may depend on the whole history of the thread: two calls of the same foreign
      body in the same memory are two events, and an oracle can answer them differently, as a real system does
      (a `read` that returns the next bytes, a provider that gives a fresh cell, a register that moves). It
      touches no cell and records no lock. -/
  | fremd (q : D.Ax ⊕ D.Reg ⊕ D.Glob)

/-- Die OFFENEN Sperren einer Spur: was genommen und nicht gegeben ist (neuestes zuerst). -/
def offen : List (Ereignis D) → List D.Lock
  | [] => []
  | .nimmt L _ :: s => L :: offen s
  | .gibt L :: s => (offen s).erase L
  | .zugriff .. :: s => offen s
  | .gzugriff .. :: s => offen s
  | .fremd _ :: s => offen s

/-- Die Welt: je Tabelle, Index und Feld ein Wert des erklaerten Typs; je Global einer; dazu
    die Spur dieses Fadens (neuestes zuerst). Die gehaltenen Sperren sind die offenen der Spur. -/
structure World (D : Deklaration) where
  slots : ∀ t : D.Tab, Int → ∀ f : D.Feld t, Wert D (D.typ t f)
  globs : ∀ g : D.Glob, Wert D (D.gtyp g)
  spur : List (Ereignis D)

def World.haelt (σ : World D) : List D.Lock := offen σ.spur

def World.merke (σ : World D) (es : List (Ereignis D)) : World D := { σ with spur := es ++ σ.spur }

/-- **Asking outside the program** records the question first (`Ereignis.fremd`): the world the machine answers in. -/
def World.fragt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : World D := σ.merke [.fremd q]

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
  | .cons v _, .here => v
  | .cons _ ρ, .there x => ρ.get x

def Env.set : Env D Γ → Var Γ τ → Wert D τ → Env D Γ
  | .cons _ ρ, .here, v => .cons v ρ
  | .cons w ρ, .there x, v => .cons w (ρ.set x v)

def Env.tail : Env D (τ :: Γ) → Env D Γ
  | .cons _ ρ => ρ

/-! ## 2. Die Orte eines Ausdrucks -- was er liest -/

mutual

/-- Die Traeger und Globale, die ein Ausdruck liest (statisch; eine Ueberdeckung, denn
    `&&` liest den rechten Operanden nicht immer -- mehr Ereignisse, alle bewacht). -/
def Expr.orte : Expr D Γ Λ τ → List (D.Tab ⊕ D.Glob)
  | .lit _ | .tru | .fls | .var _ | .ptrOf _ _ _ _ | .fnref _ _ _ | .none _ | .why _ _ => []
  | .refEq a b => a.orte ++ b.orte
  | .slotRef r t _ _ _ _ => .inl t :: r.orte
  | .glob g _ => [.inr g]
  | .slot t _ i _ => .inl t :: i.orte
  | .thru p t _ _ i _ => p.orte ++ .inl t :: i.orte
  | .oldG g _ => [.inr g]
  | .oldS t _ i _ => .inl t :: i.orte
  | .getBytes t _ _ _ i _ _ _ => .inl t :: i.orte
  | .widen _ _ e => e.orte
  | .add a b | .sub a b | .mul a b | .div _ _ a b | .rem _ _ a b | .sdiv _ a b | .srem _ a b
  | .band _ _ a b | .bor _ _ _ _ _ a b | .bxor _ _ _ _ _ a b | .shl _ _ _ _ _ a b | .shr _ _ _ _ _ a b
  | .lt a b | .le a b | .eq a b | .fllt a b | .flle a b | .and a b | .or a b => a.orte ++ b.orte
  | .neg a | .not a | .some a | .istSome a => a.orte
  | .case _ _ nutz => nutz.orte
  | .forallSlots t body _ | .existsSlots t body _ => .inl t :: body.orte
  | .reaches t _ _ a b _ => .inl t :: a.orte ++ b.orte
  | .arrNil | .strLit _ _ => []
  | .arrCons a rest => a.orte ++ rest.orte
  | .arrGet a i => a.orte ++ i.orte
  | .arrSet a i v => a.orte ++ i.orte ++ v.orte
  | .strLen s => s.orte
  | .strCat s t => s.orte ++ t.orte
  | .strGet s i => s.orte ++ i.orte
  | .strEq s t => s.orte ++ t.orte
  | .strLt s t => s.orte ++ t.orte
  | .strWeit _ s => s.orte

def NutzlastExpr.orte : NutzlastExpr D Γ Λ c → List (D.Tab ⊕ D.Glob)
  | .empty => []
  | .num e => e.orte

end
def Args.orte : Args D Γ Λ τs → List (D.Tab ⊕ D.Glob)
  | .nil => []
  | .cons e rest => e.orte ++ rest.orte

def ErgExpr.orte : ErgExpr D Γ Λ e → List (D.Tab ⊕ D.Glob)
  | .empty => []
  | .val e => e.orte

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
  | .tru, _, _ => true
  | .fls, _, _ => false
  | .var x, _, ρ => ρ.get x
  | .glob g _, σ, _ => σ.globs g
  | .slot t f i _, σ, ρ => σ.slots t (eval σ₀ i σ ρ).n f
  | .thru _ t _ f i _, σ, ρ => σ.slots t (eval σ₀ i σ ρ).n f
  | .ptrOf _ _ _ _, _, _ => ()
  | .fnref f _ h, _, _ => ⟨f, h⟩
  | .refEq a b, σ, ρ => decide ((eval σ₀ a σ ρ).zelle = (eval σ₀ b σ ρ).zelle)
  | .slotRef r t _ _ f _, σ, ρ => σ.slots t ((eval σ₀ r σ ρ).zelle : Int) f
  | .oldG g _, _, _ => σ₀.globs g
  | .oldS t f i _, σ, ρ => σ₀.slots t (eval σ₀ i σ ρ).n f
  | .widen h1 h2 e, σ, ρ => Zahl.weiter h1 h2 (eval σ₀ e σ ρ)
  | .add a b, σ, ρ => Zahl.add (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .sub a b, σ, ρ => Zahl.sub (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .neg a, σ, ρ => Zahl.neg (eval σ₀ a σ ρ)
  | .mul a b, σ, ρ => Zahl.mul (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .div h0 h1 a b, σ, ρ => Zahl.div h0 h1 (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .rem h0 h1 a b, σ, ρ => Zahl.rem h0 h1 (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .sdiv hb a b, σ, ρ => Zahl.sdiv hb (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .srem hb a b, σ, ρ => Zahl.srem hb (eval σ₀ a σ ρ) (eval σ₀ b σ ρ)
  | .getBytes t f hf n i _ _ _, σ, ρ =>
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
  | .fllt a b, σ, ρ => gleitLt (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x
  | .flle a b, σ, ρ => gleitLe (eval σ₀ a σ ρ).x (eval σ₀ b σ ρ).x
  | .and a b, σ, ρ => (wahr? (eval σ₀ a σ ρ) && wahr? (eval σ₀ b σ ρ) : Bool)
  | .or a b, σ, ρ => (wahr? (eval σ₀ a σ ρ) || wahr? (eval σ₀ b σ ρ) : Bool)
  | .not a, σ, ρ => (!wahr? (eval σ₀ a σ ρ) : Bool)
  | .none _, _, _ => Option.none
  | .some e, σ, ρ => Option.some (eval σ₀ e σ ρ)
  | .istSome e, σ, ρ => (eval σ₀ e σ ρ).isSome
  | .case cs i nutz, σ, ρ => ⟨i, evalNutz σ₀ nutz σ ρ⟩
  | .why _ r, _, _ => r
  | .forallSlots t body _, σ, ρ =>
      (alleIndizes (D.count t)).all fun k => wahr? (eval σ₀ body σ (.cons k ρ))
  | .existsSlots t body _, σ, ρ =>
      (alleIndizes (D.count t)).any fun k => wahr? (eval σ₀ body σ (.cons k ρ))
  | .reaches t f hf a b _, σ, ρ =>
      kette (fun k => hf ▸ σ.slots t k f) (D.count t).toNat (eval σ₀ a σ ρ).n (eval σ₀ b σ ρ).n
  | .arrNil, _, _ => fun i => i.elim0
  | .arrCons a rest, σ, ρ => arrConsW (eval σ₀ a σ ρ) (eval σ₀ rest σ ρ)
  | .arrGet a i, σ, ρ => (eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin
  | .arrSet a i v, σ, ρ => arrSetW (eval σ₀ a σ ρ) (eval σ₀ i σ ρ).fin (eval σ₀ v σ ρ)
  | .strLit bs h, _, _ => ⟨bs, h⟩
  | .strLen s, σ, ρ => strLenW (eval σ₀ s σ ρ)
  | .strCat s t, σ, ρ => strCatW (eval σ₀ s σ ρ) (eval σ₀ t σ ρ)
  | .strGet s i, σ, ρ => strGetW (eval σ₀ s σ ρ) (eval σ₀ i σ ρ).n
  | .strEq s t, σ, ρ => strEqW (eval σ₀ s σ ρ) (eval σ₀ t σ ρ)
  | .strLt s t, σ, ρ => strLtW (eval σ₀ s σ ρ) (eval σ₀ t σ ρ)
  | .strWeit m s, σ, ρ => strWeitW m (eval σ₀ s σ ρ)

def evalNutz (σ₀ : World D) : NutzlastExpr D Γ Λ c → World D → Env D Γ → Nutzlast c
  | .empty, _, _ => ()
  | .num e, σ, ρ => eval σ₀ e σ ρ

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
  /-- A float result (`gleit`, a float literal, `gleitVon`) outside its declared range, or NaN
      or infinite, where the form has no `else`. The kernel IEEE model (`gleitRechne`, Annex F)
      decides it from the program's own values, for EVERY oracle: it is the program's logic,
      as a `state` pre-state is (verdict F1, URTEIL-OPUS-2026-09-15b; until 2026-09-15 it was
      `Hardware.ieee`). That the FPU computes the kernel model is `gleitkomma_ieee`, on the C
      side. -/
  | bereich

/-- Die Hardware: eine Annahme ueber die Maschine gilt nicht. -/
inductive Hardware (D : Deklaration) where
  | annahme (a : D.Ax)
  | fortschritt (a : D.Annahme)
  /-- Eine Gleitkommarechnung verliess ihren erklaerten Bereich, oder wurde NaN/unendlich:
      IEEE 754 ist die Maschine, und ihr Rundungsverhalten ist die Annahme («F»).
      NO LONGER PRODUCED by the semantics since 2026-09-15 (verdict F1): an out-of-range float
      result is `Logik.bereich`. The constructor stays for the C-side vocabulary. -/
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
  | why (σ : World D) (r : Fin V.gruende) : Ausgang V l Γ
  | leave (h : l = true) (σ : World D) (ρ : Env D Γ) : Ausgang V l Γ
  | next (h : l = true) (σ : World D) (ρ : Env D Γ) : Ausgang V l Γ
  | logik (e : Logik D) : Ausgang V l Γ
  | hardware (e : Hardware D) : Ausgang V l Γ

variable {V : Vertrag D}

/-- Ein Ausgang, der nicht `ok` ist -- was ein `Endblock` liefert. -/
inductive EndAusgang (V : Vertrag D) : Bool → Ctx → Type where
  | zurueck (σ : World D) (v : ErgVal D V.erg) : EndAusgang V l Γ
  | why (σ : World D) (r : Fin V.gruende) : EndAusgang V l Γ
  | leave (h : l = true) (σ : World D) (ρ : Env D Γ) : EndAusgang V l Γ
  | next (h : l = true) (σ : World D) (ρ : Env D Γ) : EndAusgang V l Γ
  | logik (e : Logik D) : EndAusgang V l Γ
  | hardware (e : Hardware D) : EndAusgang V l Γ

/-- Was ein Ruf liefert -- im Vertrag des GERUFENEN. -/
inductive RufAusgang {D : Deklaration} (f : D.Fn) : Type where
  | ok (σ : World D) (v : ErgVal D (D.erg f))
  | why (σ : World D) (r : Fin (D.gruende f))
  | logik (e : Logik D)
  | hardware (e : Hardware D)

/-! ## 4. Das Orakel -- die Hardware, als Parameter -/

/-- A float result against its declared range: finite and inside, or nothing. NaN and the
    infinities fail `gleitEndlich` and fall into the `none` branch -- the `logik bereich`
    outcome of a computed float (or a `narrow`'s `else`), and a refused register or axiom
    answer (`einpassen`). -/
def gleitPasst (lo hi : Int × Int) (x : GFloat) : Option (Gleit lo hi) :=
  if h : gleitEndlich x = true ∧ gleitLe (bruch lo) x = true ∧ gleitLe x (bruch hi) = true then
    some ⟨x, h.1, h.2.1, h.2.2⟩
  else Option.none

/-- The payload of a `tagged` case against its declared payload: a bare case carries `0`
    (the C struct has no `last` member for it), a payload case a number in its range. -/
def nutzPasst : (c : Option (Int × Int)) → Int → Option (Nutzlast c)
  | Option.none, p => if p = 0 then some () else Option.none
  | Option.some (lo, hi), p => if h : lo ≤ p ∧ p ≤ hi then some ⟨p, h.1, h.2⟩ else Option.none

/-- The number of `tagged` cases, as an `Int`. -/
abbrev fallZahl (cs : List (Option (Int × Int))) : Int := (cs.length : Int)

theorem fall_marke_lt (cs : List (Option (Int × Int))) (n : Int) (hk : 0 < cs.length) :
    (n % fallZahl cs).toNat < cs.length := by
  have h0 : (0 : Int) < fallZahl cs := by unfold fallZahl; omega
  have h1 := Int.emod_nonneg n (Int.ne_of_gt h0)
  have h2 := Int.emod_lt_of_pos n h0
  unfold fallZahl at h1 h2 ⊢
  omega

/-- **A raw word as a `tagged` value** (G1 repair, 2026-09-15). The emitter lays a `tagged`
    value out as `struct { T_marke marke; union { … } last; }` (`emit.rs`, `markiert`): the
    case number `marke` (a C `enum`, the cases numbered `0, 1, …` in declaration order) and
    the payload `last` of that case (none for a bare case). The machine's ONE raw word is that
    pair, PACKED MIXED-RADIX with the case number in the low digit:
    `roh = marke + |cases| * last` -- so `marke = roh % |cases|` and `last = roh / |cases|`
    (Euclidean). The packing is a bijection between `Int` and the pairs
    `(marke < |cases|, last : Int)`, so every value of the `tagged` type has exactly one raw
    word -- a bare case with `last = 0`, whatever the C union holds there
    (`einpassen_voll`, EinpassenVoll.lean); `nutzPasst` then holds the payload against its
    range. A syscall's `ok value | reason r` is such a sum; its generated errno decoding
    (`dekodiere`, Syscall.lean) is the emitted C that forms the pair. -/
def summePasst (cs : List (Option (Int × Int))) (n : Int) :
    Option (Σ i : Fin cs.length, Nutzlast (cs.get i)) :=
  if hk : 0 < cs.length then
    let i : Fin cs.length := ⟨(n % fallZahl cs).toNat, fall_marke_lt cs n hk⟩
    (nutzPasst (cs.get i) (n / fallZahl cs)).map fun x => ⟨i, x⟩
  else Option.none

/-- The width of the raw float word: the IEEE-754 binary64 bit pattern is an unsigned
    64-bit integer. -/
abbrev gleitWortGrenze : Int := 18446744073709551616

/-- **A raw word as a float** (G1 repair): the word is the IEEE-754 binary64 bit pattern
    (sign, exponent, significand; `Gleitkomma.ausBits`, the inverse of `zuBits` on
    well-formed triples), held against the declared range like a computed float
    (`gleitPasst`: finite and inside). `Ty.fl` carries no width and the model computes in
    binary64 (FLOATING-POINT.md section 7), so an `f32` register's answer is read as its binary64
    value -- the same named cut. -/
def gleitWortPasst (lo hi : Int × Int) (n : Int) : Option (Gleit lo hi) :=
  if 0 ≤ n ∧ n < gleitWortGrenze then
    gleitPasst lo hi (Gleitkomma.ausBits Gleitkomma.f64 n.toNat)
  else Option.none

/-- **A raw word as a function pointer** (G1 repair): the word is a code address; the loaded
    image `z` (`Orakel.zeiger`) names the function at it, and its conformance to the declared
    `fnptr n` is held (`Deklaration.passt`). -/
def zeigerPasst (z : Int → Option D.Fn) (m : Nat) (n : Int) : Option {f : D.Fn // D.passt f m = true} :=
  match z n with
  | Option.some f => if h : D.passt f m = true then some ⟨f, h⟩ else Option.none
  | Option.none => Option.none

/-- Ein rohes Ergebnis der Maschine, gegen einen Typ gehalten: passt es nicht, ist die
    Annahme widerlegt. **Every type has a real decoding** since 2026-09-15 (round-5 finding
    G1: `sum`, `fl` and `fnptr` answered `none` for EVERY raw word, so every call of an axiom
    with such a result, and every read of such a register, stopped at `hardware` for every
    oracle -- a stop the MODEL decided and filed as hardware). Every value of every type is
    the decoding of some raw word under some image (`einpassen_voll`, EinpassenVoll.lean; for
    floats: every well-formed one). What is left without an answer is exactly the EMPTY
    types -- `never`, `.why 0`, an empty range, a sum without a value -- and among them the
    checker admits only an axiom `-> never` (round-6 finding W1, `AkzeptiertSpec.antworten`),
    whose call does not return (`HaltArt.nieZurueck`, Zielsatz/Spec.lean).
    `z` is the loaded image (`Orakel.zeiger`), read only by `fnptr`. -/
def einpassen (z : Int → Option D.Fn) : (τ : Ty) → Int → Option (Wert D τ)
  | .int lo hi, n => if h : lo ≤ n ∧ n ≤ hi then some ⟨n, h.1, h.2⟩ else Option.none
  | .bool, n => some (decide (n ≠ 0))
  | .opt m, n => if h : 0 ≤ n ∧ n ≤ m - 1 then some (some ⟨n, h.1, h.2⟩)
                 else if n < 0 then some Option.none else Option.none
  | .sum cs, n => summePasst cs n
  | .why m, n => if h : 0 ≤ n ∧ n < m then some ⟨n.toNat, by omega⟩ else Option.none
  | .never, _ => Option.none
  | .fl lo hi, n => gleitWortPasst lo hi n
  | .fnptr m, n => zeigerPasst z m n
  | .ptr _ _, _ => some ()
  | .ref _, n => if 0 ≤ n then some (Val.vonZelle n.toNat) else Option.none
  -- An aggregate is not one raw word: the checker admits no foreign or register answer of such a type.
  | .arr _ _, _ => Option.none
  | .str _, _ => Option.none

def einpassenErg (z : Int → Option D.Fn) : (τ : Option Ty) → Int → Option (ErgVal D τ)
  | Option.none, _ => some ()
  | Option.some τ, n => einpassen z τ n

/-- **An empty answer class** (G1 repair, 2026-09-15): no raw word decodes under any image --
    the declared answer type has no value (`never`, `.why 0`, an empty range, a sum
    without a value, a pointer type no function has; `einpassen_voll`, EinpassenVoll.lean,
    shows that every value IS some answer). A call whose answer class is empty cannot
    return, and the machine cannot fail to answer it "outside its type": there is no inside.
    That stop is `HaltArt.nieZurueck` (Zielsatz/Spec.lean), not a hardware stop -- and since
    W1 the checker admits it only for an axiom `-> never` (whose C prototype is `_Noreturn`);
    every other empty answer type is refused (`AkzeptiertSpec.antworten`). -/
def AntwortLeer (D : Deklaration) (e : Option Ty) : Prop :=
  ∀ (z : Int → Option D.Fn) (n : Int), einpassenErg z e n = Option.none

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
  /-- **The loaded image** (G1 repair, 2026-09-15): the function at a code address, for a
      raw answer of `fnptr` type (`zeigerPasst`). Which address a function has is the
      linker's and loader's, not the program's, so it is the machine's answer like every
      other: `einpassen` checks the signature number, and every function of a signature is
      some image's answer. Default: no function at any address (a witness oracle that
      answers no pointer). -/
  zeiger : Int → Option D.Fn := fun _ => Option.none

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
  | .why σ r => .why σ r
  | .leave h σ ρ => .leave h σ ρ.tail
  | .next h σ ρ => .next h σ ρ.tail
  | .logik e => .logik e
  | .hardware e => .hardware e

def Ausgang.schrumpfArm : (c : Option (Int × Int)) → Ausgang V l (ArmCtx Γ c) → Ausgang V l Γ
  | Option.none, a => a
  | Option.some (_, _), a => a.schrumpf

def EndAusgang.schrumpf : EndAusgang V l (τ :: Γ) → EndAusgang V l Γ
  | .zurueck σ v => .zurueck σ v
  | .why σ r => .why σ r
  | .leave h σ ρ => .leave h σ ρ.tail
  | .next h σ ρ => .next h σ ρ.tail
  | .logik e => .logik e
  | .hardware e => .hardware e

def EndAusgang.zuAusgang : EndAusgang V l Γ → Ausgang V l Γ
  | .zurueck σ v => .zurueck σ v
  | .why σ r => .why σ r
  | .leave h σ ρ => .leave h σ ρ
  | .next h σ ρ => .next h σ ρ
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- Die Welt eines Ausgangs umbauen (Sperre geben). -/
def Ausgang.mapWelt (f : World D → World D) : Ausgang V l Γ → Ausgang V l Γ
  | .ok σ ρ => .ok (f σ) ρ
  | .zurueck σ v => .zurueck (f σ) v
  | .why σ r => .why (f σ) r
  | .leave h σ ρ => .leave h (f σ) ρ
  | .next h σ ρ => .next h (f σ) ρ
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- Ein Ausgang, der im Rumpf einer Schleife entstand, gesehen von der Anweisung, in der
    die Schleife steht: `leave` und `next` sind dort verbraucht. -/
def Ausgang.ausSchleife : Ausgang V true Γ → Ausgang V l Γ
  | .ok σ ρ => .ok σ ρ
  | .zurueck σ v => .zurueck σ v
  | .why σ r => .why σ r
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
      | .why σ' r => .why σ' r
      | .logik e => .logik e
      | .hardware e => .hardware e


end Gabbro.Grammatik
