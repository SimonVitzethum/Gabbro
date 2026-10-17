/- Part 5 of 5 of `Satz` (split by instrumente/teile/lean-teilen.py; the umbrella `Satz.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Satz.T4

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- Der RAHMEN, fuer sich. -/
theorem exec_rahmen (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O) (hP : StufenOk P)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    ∀ σ', (exec P O passes fuel V b σ ρ).welt = some σ' → Rahmen V.schreibt V.gschreibt σ σ' :=
  fun σ' h => (exec_gut P O passes fuel hO hP b σ ρ hh σ' h).1

/-- Die SPUR, fuer sich: jedes Ereignis, das ein Rumpf hinterlaesst, traegt die Waechter seines
    Traegers und haelt jede Sperre, die sein `Λ` nennt -- und am Ende sind die Sperren, was sie
    am Anfang waren. Das ist der Anschluss an `Wettlauf.lean`. -/
theorem exec_spur (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O) (hP : StufenOk P)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    ∀ σ', (exec P O passes fuel V b σ ρ).welt = some σ' →
      σ'.haelt = σ.haelt ∧ (∀ e ∈ σ'.spur, e ∈ σ.spur ∨ e.gut) ∧
      (Konsistent σ.spur → Konsistent σ'.spur) :=
  fun σ' h => (exec_gut P O passes fuel hO hP b σ ρ hh σ' h).2

/-! ## 4. Sprechproben -- Saetze der Grammatik, ausgewertet -/

/-- Eine Deklaration ohne Tabellen, Globale, Sperren, Register: nur Rechnung. -/
def leer : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun t => t.elim
  ggeteilt := fun g => g.elim
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun g => g.elim
  eigner := fun t => t.elim
  Fn := Empty
  sig := fun f => f.elim
  sigNr := fun _ => ⟨[], none, 0, [], fun t => t.elim, fun g => g.elim, [], [], none⟩
  eigner_nie_erzeugt := fun _ t => t.elim
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Empty
  aparams := fun a => a.elim
  aerg := fun a => a.elim
  aschreibt := fun a => a.elim
  agschreibt := fun a => a.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => t.elim
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g => g.elim

def leereWelt : World leer := ⟨fun t => Empty.elim t, fun g => Empty.elim g, []⟩

/-- `x : u8 in 0 .. 5`; `x + x` hat den Bereich `0 .. 10`, und `(x + x) / (x + 1)` ist
    schreibbar, weil der Nenner in `1 .. 6` liegt -- Bereich `0 .. 10`. -/
def probe : Expr leer [.int 0 5] [] (.int 0 10) :=
  .div (by decide) (by decide) (.add (.var .here) (.var .here)) (.add (.var .here) (.lit 1))

example : (eval leereWelt probe leereWelt (.cons ⟨3, by decide, by decide⟩ .nil)).n = 1 := by rfl
example : (eval leereWelt probe leereWelt (.cons ⟨0, by decide, by decide⟩ .nil)).n = 0 := by rfl

/-- `x : i8 in -5 .. 5`, `y : i8 in -3 .. -1`: `x / y` ist schreibbar (der Nenner ist nie
    null), Bereich `-5 .. 5`; bei `x = -5, y = -2` ist es `2` (abschneidend, wie C). -/
def sprobe : Expr leer [.int (-3) (-1), .int (-5) 5] [] (.int (-(betragMax (-5) 5)) (betragMax (-5) 5)) :=
  .sdiv (.inr (by decide)) (.var (.there .here)) (.var .here)

example : (eval leereWelt sprobe leereWelt
    (.cons ⟨-2, by decide, by decide⟩ (.cons ⟨-5, by decide, by decide⟩ .nil))).n = 2 := by rfl

/-- `x / x` ist NICHT schreibbar: `.div` verlangt `1 ≤ 0`, und `.sdiv` verlangt einen Bereich
    ohne die Null -- `0 .. 5` hat sie. -/
example : ¬ (1 ≤ (0 : Int)) := by decide
example : ¬ (1 ≤ (0 : Int) ∨ (5 : Int) ≤ -1) := by decide

/-- `forall k in slots of T : …` ueber der leeren Tabelle -- immer wahr. -/
example : wahr? (eval (D := leer) (Γ := []) (Λ := []) leereWelt (.and .tru (.not .fls)) leereWelt .nil) = true := by
  rfl

def leerV : Vertrag leer := ⟨fun t => t.elim, fun g => g.elim, none, 0, [], [], none⟩

def leerO : Orakel leer :=
  ⟨fun a => a.elim, fun r => r.elim, fun r => r.elim, fun g => g.elim, fun _ => Option.none⟩

def gleitProbe : Block leer leerV false [] [] [] :=
  .floatLit (3, 2) (0, 1) (10, 1) .nil

example : ∃ o, execBlock (D := leer) leerO 0 (fun f => f.elim) gleitProbe leereWelt .nil = o :=
  ⟨_, rfl⟩

/-! ## 5. Die Axiome -- abgeleitet -/

#print axioms Gabbro.Grammatik.zwei_fehler
#print axioms Gabbro.Grammatik.bedeutung_total
#print axioms Gabbro.Grammatik.exec_gut
#print axioms Gabbro.Grammatik.exec_rahmen
#print axioms Gabbro.Grammatik.exec_spur
#print axioms Gabbro.Grammatik.rufAt_gut
#print axioms Gabbro.Grammatik.keine_verklemmung


end Gabbro.Grammatik
