module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Grammatik.Kern.Semantik.Semantik.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
variable {V : Vertrag D}

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
    schreibt (`maintains`, aus `effects` abgeleitet -- «SG-I»): Tabellen ueber `D.schreibt f`,
    Globale ueber `D.gschreibt f` (C05). -/
def schuldet (f : D.Fn) (i : D.Inv) : Bool :=
  (D.traeger i).any (Sum.elim (D.schreibt f) (D.gschreibt f))

/-- Ein Ausgang aus einem Unterblock mit erweitertem Sichtbereich, zurueck in den aeusseren. -/
def Ausgang.schrumpf : Ausgang V l (τ :: Γ) → Ausgang V l Γ
  | .ok σ ρ => .ok σ ρ.tail
  | .zurueck σ v => .zurueck σ v
  | .why σ r => .why σ r
  | .leave h σ ρ => .leave h σ ρ.tail
  | .next h σ ρ => .next h σ ρ.tail
  | .logik e => .logik e
  | .hardware e => .hardware e

def Ausgang.schrumpfArm : (c : Option Ty) → Ausgang V l (ArmCtx Γ c) → Ausgang V l Γ
  | Option.none, a => a
  | Option.some _, a => a.schrumpf

def EndAusgang.schrumpf : EndAusgang V l (τ :: Γ) → EndAusgang V l Γ
  | .zurueck σ v => .zurueck σ v
  | .why σ r => .why σ r
  | .leave h σ ρ => .leave h σ ρ.tail
  | .next h σ ρ => .next h σ ρ.tail
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- **The outcome of a generalized foreign binder** («C08»): void adds no local,
    a value shrinks -- the uniform continuation behind `ErgCtx`. -/
def Ausgang.weiterOpt : (e : Option Ty) → Ausgang V l (ErgCtx Γ e) → Ausgang V l Γ
  | none, x => x
  | some _, x => x.schrumpf

/-- **The outcome of a generalized foreign binder at the top level** («C08»):
    void adds no local, a value shrinks. -/
def EndAusgang.weiterOpt : (e : Option Ty) → EndAusgang V l (ErgCtx Γ e) → EndAusgang V l Γ
  | none, x => x
  | some _, x => x.schrumpf

def EndAusgang.zuAusgang : EndAusgang V l Γ → Ausgang V l Γ
  | .zurueck σ v => .zurueck σ v
  | .why σ r => .why σ r
  | .leave h σ ρ => .leave h σ ρ
  | .next h σ ρ => .next h σ ρ
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- Both outcome transformers agree through `zuAusgang`. -/
theorem weiterOpt_zuAusgang (e : Option Ty) (x : EndAusgang V l (ErgCtx Γ e)) :
    (EndAusgang.weiterOpt e x).zuAusgang = Ausgang.weiterOpt e x.zuAusgang := by
  cases e with
  | none => cases x <;> rfl
  | some τ => cases x <;> rfl

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



/-- The narrowing of `Expr.eng` is a function of the narrowed value. -/
theorem eng_kongr {lo hi lo' hi' : Int} {x y : Zahl lo hi} (h : x = y) (f : Zahl lo' hi') :
    (if h : lo' ≤ x.n ∧ x.n ≤ hi' then (⟨x.n, h.1, h.2⟩ : Zahl lo' hi') else f) =
      (if h : lo' ≤ y.n ∧ y.n ≤ hi' then (⟨y.n, h.1, h.2⟩ : Zahl lo' hi') else f) := by
  subst h; rfl

end Gabbro.Grammatik
