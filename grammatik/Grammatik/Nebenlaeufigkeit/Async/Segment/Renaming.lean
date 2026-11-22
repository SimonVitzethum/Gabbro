module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil1a

namespace Gabbro.Grammatik

variable {D : Deklaration} {Γ Γ' : Ctx} {Λ : List (Res D)}

/-- The environments agree on the source variables selected by the renaming. -/
@[expose] public def Env.AgreesUnder (original : Env D Γ) (renamed : Env D Γ')
    (rename : ∀ {τ : Ty}, Var Γ τ → Var Γ' τ) : Prop :=
  ∀ {τ : Ty} (x : Var Γ τ), renamed.get (rename x) = original.get x

private theorem Env.AgreesUnder.binder {original : Env D Γ} {renamed : Env D Γ'}
    {rename : ∀ {τ : Ty}, Var Γ τ → Var Γ' τ} (agrees : original.AgreesUnder renamed rename)
    {σ : Ty} (value : Wert D σ) :
    (Env.cons value original).AgreesUnder (.cons value renamed) (Var.hoch rename) := by
  intro τ x
  cases x with
  | here => rfl
  | there x => exact agrees x

mutual
/-- Renaming preserves ordinary G evaluation, the complete read trace,
    and the static cost used for poll admission. -/
public theorem Expr.ren_sound {Γ Γ' : Ctx} {τ : Ty}
    (expression : Expr D Γ Λ τ) (rename : ∀ {ν : Ty}, Var Γ ν → Var Γ' ν) :
    (expression.ren rename).orte = expression.orte ∧
    kostenExpr (expression.ren rename) = kostenExpr expression ∧
    ∀ (entry world : World D) (original : Env D Γ) (renamed : Env D Γ'),
      original.AgreesUnder renamed rename →
      eval entry (expression.ren rename) world renamed = eval entry expression world original :=
  match expression with
  | .lit _
  | .tru
  | .fls
  | .glob _ _
  | .ptrOf _ _ _ _
  | .fnref _ _ _
  | .oldG _ _
  | .none _
  | .why _ _
  | .arrNil
  | .strLit _ _ => ⟨rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | .var x => ⟨rfl, rfl, fun _ _ _ _ agrees => agrees x⟩
  | .slot _ _ a _
  | .slotRef a _ _ _ _ _
  | .oldS _ _ a _
  | .getBytes _ _ _ _ a _ _ _
  | .widen _ _ a
  | .neg a
  | .not a
  | .some a
  | .istSome a
  | .strLen a
  | .strWeit _ a
  | .intBuiltin1 _ a
  | .prodGet a _ => by
    have aSound := Expr.ren_sound a rename
    refine ⟨?_, ?_, ?_⟩
    · simp only [Expr.ren, Expr.orte, aSound.1]
    · simp only [Expr.ren, kostenExpr, aSound.2.1]
    · intro entry world original renamed agrees
      simp only [Expr.ren, eval, aSound.2.2 entry world original renamed agrees] <;> rfl
  | .thru a _ _ _ b _
  | .thruOwn a _ _ _ b _ _ _ _ _ _
  | .refEq a b
  | .add a b
  | .sub a b
  | .mul a b
  | .div _ _ a b
  | .rem _ _ a b
  | .sdiv _ a b
  | .srem _ a b
  | .band _ _ a b
  | .bor _ _ _ _ _ a b
  | .bxor _ _ _ _ _ a b
  | .shl _ _ _ _ _ a b
  | .shr _ _ _ _ _ a b
  | .lt a b
  | .le a b
  | .eq a b
  | .fllt a b
  | .flle a b
  | .and a b
  | .or a b
  | .reaches _ _ _ a b _
  | .arrCons a b
  | .arrGet a b
  | .strCat a b
  | .strGet a b
  | .strEq a b
  | .strLt a b
  | .intBuiltin2 _ a b
  | .prodSet a _ b => by
    have aSound := Expr.ren_sound a rename
    have bSound := Expr.ren_sound b rename
    refine ⟨?_, ?_, ?_⟩
    · simp only [Expr.ren, Expr.orte, aSound.1, bSound.1]
    · simp only [Expr.ren, kostenExpr, aSound.2.1, bSound.2.1]
    · intro entry world original renamed agrees
      simp only [Expr.ren, eval, aSound.2.2 entry world original renamed agrees,
        bSound.2.2 entry world original renamed agrees] <;> rfl
  | .eng a lower upper fallback => by
    have argument := Expr.ren_sound a rename
    have alternative := Expr.ren_sound fallback rename
    refine ⟨?_, ?_, ?_⟩
    · simp only [Expr.ren, Expr.orte, argument.1, alternative.1]
    · simp only [Expr.ren, kostenExpr, argument.2.1, alternative.2.1]
    · intro entry world original renamed agrees
      simp only [Expr.ren, eval]
      exact congrArg₂ (fun selected otherwise =>
        if within : lower ≤ selected.n ∧ selected.n ≤ upper then ⟨selected.n, within.1, within.2⟩ else otherwise)
        (argument.2.2 entry world original renamed agrees) (alternative.2.2 entry world original renamed agrees)
  | .arrSet a b c
  | .wenn a b c => by
    have aSound := Expr.ren_sound a rename
    have bSound := Expr.ren_sound b rename
    have cSound := Expr.ren_sound c rename
    refine ⟨?_, ?_, ?_⟩
    · simp only [Expr.ren, Expr.orte, aSound.1, bSound.1, cSound.1]
    · simp only [Expr.ren, kostenExpr, aSound.2.1, bSound.2.1, cSound.2.1]
    · intro entry world original renamed agrees
      simp only [Expr.ren, eval, aSound.2.2 entry world original renamed agrees,
        bSound.2.2 entry world original renamed agrees, cSound.2.2 entry world original renamed agrees] <;> rfl
  | .case _ _ payload => by
    have payloadSound := NutzlastExpr.ren_sound payload rename
    refine ⟨?_, ?_, ?_⟩
    · simp only [Expr.ren, Expr.orte, payloadSound.1]
    · simp only [Expr.ren, kostenExpr, payloadSound.2.1]
    · intro entry world original renamed agrees
      simp only [Expr.ren, eval, payloadSound.2.2 entry world original renamed agrees] <;> rfl
  | .prod _ arguments => by
    have argumentsSound := Args.ren_sound arguments rename
    refine ⟨?_, ?_, ?_⟩
    · simp only [Expr.ren, Expr.orte, argumentsSound.1]
    · simp only [Expr.ren, kostenExpr, argumentsSound.2.1]
    · intro entry world original renamed agrees
      simp only [Expr.ren, eval, argumentsSound.2.2 entry world original renamed agrees] <;> rfl
  | .forallSlots _ body _ | .existsSlots _ body _ | .count _ body => by
    have sound := Expr.ren_sound body (Var.hoch rename)
    refine ⟨?_, ?_, ?_⟩
    · simp only [Expr.ren, Expr.orte, sound.1]
    · simp only [Expr.ren, kostenExpr, sound.2.1]
    · intro entry world original renamed agrees
      simp only [Expr.ren, eval]
      congr 1
      funext value
      exact congrArg wahr? (sound.2.2 entry world (.cons value original) (.cons value renamed)
        (Env.AgreesUnder.binder agrees value))
termination_by structural expression

public theorem NutzlastExpr.ren_sound {Γ Γ' : Ctx} {c : Option Ty}
    (expression : NutzlastExpr D Γ Λ c) (rename : ∀ {ν : Ty}, Var Γ ν → Var Γ' ν) :
    (expression.ren rename).orte = expression.orte ∧
    kostenNutz (expression.ren rename) = kostenNutz expression ∧
    ∀ (entry world : World D) (original : Env D Γ) (renamed : Env D Γ'),
      original.AgreesUnder renamed rename →
      evalNutz entry (expression.ren rename) world renamed = evalNutz entry expression world original :=
  match expression with
  | .empty => ⟨rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | .val expression => Expr.ren_sound expression rename
termination_by structural expression

public theorem Args.ren_sound {Γ Γ' : Ctx} {fields : List Ty}
    (expressions : Args D Γ Λ fields) (rename : ∀ {ν : Ty}, Var Γ ν → Var Γ' ν) :
    (expressions.ren rename).orte = expressions.orte ∧
    kostenArgs (expressions.ren rename) = kostenArgs expressions ∧
    ∀ (entry world : World D) (original : Env D Γ) (renamed : Env D Γ'),
      original.AgreesUnder renamed rename →
      evalProd entry (expressions.ren rename) world renamed = evalProd entry expressions world original :=
  match expressions with
  | .nil => ⟨rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | .cons expression rest => by
    have expressionSound := Expr.ren_sound expression rename
    have restSound := Args.ren_sound rest rename
    refine ⟨?_, ?_, ?_⟩
    · simp only [Args.ren, Args.orte, expressionSound.1, restSound.1]
    · simp only [Args.ren, kostenArgs, expressionSound.2.1, restSound.2.1]
    · intro entry world original renamed agrees
      simp only [Args.ren, evalProd, expressionSound.2.2 entry world original renamed agrees,
        restSound.2.2 entry world original renamed agrees] <;> rfl
termination_by structural expressions
end

end Gabbro.Grammatik
