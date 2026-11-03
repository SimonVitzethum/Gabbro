module
public import Grammatik.Kern.Semantik.Semantik

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Scalar

/-- A const call uses its declared parameter/result types and the ordinary G call rule.
    This closed declaration introduces no hardware assumption or source interpreter. -/
def declaration (params : List Ty) (result : Ty) : Deklaration where
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
  rang := fun l => l.elim
  maskiert := fun l => l.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun g => g.elim
  eigner := fun t => t.elim
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => ⟨params, some result, 0, [], fun t => t.elim,
    fun g => g.elim, [], [], none, {}⟩
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

/-- A canonical empty world; arbitrary worlds may carry their own trace. -/
def world (params : List Ty) (result : Ty) : World (declaration params result) where
  slots := fun t => t.elim
  globs := fun g => g.elim
  spur := []

/-- Every expression in this closed declaration has an empty memory footprint. -/
theorem footprint {Γ : Ctx} {τ : Ty} (e : Expr (declaration ps result) Γ [] τ) :
    e.orte = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro place _
  cases place with
  | inl t => exact t.elim
  | inr g => exact g.elim

/-- A typed expression with a generic denotation independent of both worlds.
    The proof is built compositionally with the source expression, not by testing a program. -/
structure Code (D : Deklaration) (Γ : Ctx) (τ : Ty) where
  expr : Expr D Γ [] τ
  denote : Env D Γ → Wert D τ
  equation : ∀ before after env, eval before expr after env = denote env

/-- Existential type inferred by G's exact integer interval constructors. -/
abbrev SomeCode (D : Deklaration) (Γ : Ctx) := Sigma (Code D Γ)

namespace Code
variable {D : Deklaration} {Γ : Ctx}

def literal (n : Int) : Code D Γ (.int n n) :=
  ⟨.lit n, fun _ => ⟨n, Int.le_refl _, Int.le_refl _⟩, by intros; rfl⟩

def «variable» (x : Var Γ τ) : Code D Γ τ :=
  ⟨.var x, fun env => env.get x, by intros; rfl⟩

def truth (b : Bool) : Code D Γ .bool :=
  if b then ⟨.tru, fun _ => true, by intros; rfl⟩
  else ⟨.fls, fun _ => false, by intros; rfl⟩

def negate (a : Code D Γ (.int lo hi)) : Code D Γ (.int (-hi) (-lo)) :=
  ⟨.neg a.expr, fun env => Zahl.neg (a.denote env), by
    intros; simp only [eval, a.equation, wahr?] <;> rfl⟩

def add (a : Code D Γ (.int l h)) (b : Code D Γ (.int l' h')) :
    Code D Γ (.int (l + l') (h + h')) :=
  ⟨.add a.expr b.expr, fun env => Zahl.add (a.denote env) (b.denote env), by
    intros; simp only [eval, a.equation, b.equation, wahr?] <;> rfl⟩

def sub (a : Code D Γ (.int l h)) (b : Code D Γ (.int l' h')) :
    Code D Γ (.int (l - h') (h - l')) :=
  ⟨.sub a.expr b.expr, fun env => Zahl.sub (a.denote env) (b.denote env), by
    intros; simp only [eval, a.equation, b.equation, wahr?] <;> rfl⟩

def mul (a : Code D Γ (.int l h)) (b : Code D Γ (.int l' h')) :
    Code D Γ (.int (imin (imin (l*l') (l*h')) (imin (h*l') (h*h')))
      (imax (imax (l*l') (l*h')) (imax (h*l') (h*h')))) :=
  ⟨.mul a.expr b.expr, fun env => Zahl.mul (a.denote env) (b.denote env), by
    intros; simp only [eval, a.equation, b.equation, wahr?] <;> rfl⟩

def boolNot (a : Code D Γ .bool) : Code D Γ .bool :=
  ⟨.not a.expr, fun env => !(a.denote env), by intros; simp only [eval, a.equation, wahr?] <;> rfl⟩

def boolAnd (a b : Code D Γ .bool) : Code D Γ .bool :=
  ⟨.and a.expr b.expr, fun env => a.denote env && b.denote env, by
    intros; simp only [eval, a.equation, b.equation, wahr?] <;> rfl⟩

def boolOr (a b : Code D Γ .bool) : Code D Γ .bool :=
  ⟨.or a.expr b.expr, fun env => a.denote env || b.denote env, by
    intros; simp only [eval, a.equation, b.equation, wahr?] <;> rfl⟩

/-- Comparisons preserve operands of different exact integer intervals. -/
def less (a : Code D Γ (.int l h)) (b : Code D Γ (.int l' h')) : Code D Γ .bool :=
  ⟨.lt a.expr b.expr, fun env => decide ((a.denote env).n < (b.denote env).n), by
    intros; simp only [eval, a.equation, b.equation, wahr?] <;> rfl⟩

def lessEqual (a : Code D Γ (.int l h)) (b : Code D Γ (.int l' h')) : Code D Γ .bool :=
  ⟨.le a.expr b.expr, fun env => decide ((a.denote env).n ≤ (b.denote env).n), by
    intros; simp only [eval, a.equation, b.equation, wahr?] <;> rfl⟩

def equal (a : Code D Γ (.int l h)) (b : Code D Γ (.int l' h')) : Code D Γ .bool :=
  ⟨.eq a.expr b.expr, fun env => decide ((a.denote env).n = (b.denote env).n), by
    intros; simp only [eval, a.equation, b.equation, wahr?] <;> rfl⟩

end Code
end Gabbro.Grammatik.Parser.Konst.Scalar
