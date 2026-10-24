import Grammatik.Bausteine.Arena.Ownership.Body.Check.Context

/-! Recognisers for the expression shapes of the executed allocator forms,
with what they mean. They match on G's expression constructors at any type
index, so a cast along a type equation (`Expr.umTyp`) is transparent on
every concrete declaration; the meaning lemmas hold for every expression. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- A read of a global. -/
def exprGlob : {τ : Ty} → Expr D Γ Λ τ → Option D.Glob
  | _, .glob g _ => some g
  | _, _ => none

/-- A variable, possibly widened: its bottom position. -/
def exprVarPos : {τ : Ty} → Expr D Γ Λ τ → Option Nat
  | _, .var x => some x.unten
  | _, .widen _ _ e => exprVarPos e
  | _, _ => none

/-- A literal. -/
def exprLit : {τ : Ty} → Expr D Γ Λ τ → Option Int
  | _, .lit n => some n
  | _, _ => none

/-- A variable plus one, possibly widened: the variable's bottom position. -/
def exprSucc : {τ : Ty} → Expr D Γ Λ τ → Option Nat
  | _, .add a b => if exprLit b = some 1 then exprVarPos a else none
  | _, .widen _ _ e => exprSucc e
  | _, _ => none

/-- A field read at a variable: table, field and the variable's bottom position. -/
def exprSlotRead : {τ : Ty} → Expr D Γ Λ τ → Option ((t : D.Tab) × D.Feld t × Nat)
  | _, .slot t f i _ => (exprVarPos i).map fun p => ⟨t, f, p⟩
  | _, _ => none

theorem intVon_umTyp {τ : Ty} {a b : Int} (h : τ = .int a b) (v : Wert D τ) :
    intVon τ v = some (Wert.umTyp h v).n := by
  subst h; rfl

theorem exprGlob_eval : ∀ {τ : Ty} (e : Expr D Γ Λ τ) {g : D.Glob}, exprGlob e = some g →
    ∀ (σa σb : World D) (ρ : Env D Γ), intVon τ (eval σa e σb ρ) = intVon (D.gtyp g) (σb.globs g) := by
  intro τ e g h σa σb ρ
  cases e <;> simp only [exprGlob, reduceCtorEq] at h
  cases h
  rfl

theorem exprVarPos_eval : ∀ {τ : Ty} (e : Expr D Γ Λ τ) {p : Nat}, exprVarPos e = some p →
    ∀ (σa σb : World D) (ρ : Env D Γ), intVon τ (eval σa e σb ρ) = ρ.unten p := by
  intro τ e
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True) with
  | var x =>
    intro p h σa σb ρ
    simp only [exprVarPos, Option.some.injEq] at h
    subst h
    exact (Env.unten_get ρ x).symm
  | widen h1 h2 e ih =>
    intro p h σa σb ρ
    rw [← ih h σa σb ρ]
    rfl
  | empty => trivial
  | num _ _ => trivial
  | _ => intro p h; simp [exprVarPos] at h

theorem exprLit_eval : ∀ {τ : Ty} (e : Expr D Γ Λ τ) {n : Int}, exprLit e = some n →
    ∀ (σa σb : World D) (ρ : Env D Γ), intVon τ (eval σa e σb ρ) = some n := by
  intro τ e n h σa σb ρ
  cases e <;> simp only [exprLit, reduceCtorEq, Option.some.injEq] at h
  subst h
  rfl

theorem exprSucc_eval : ∀ {τ : Ty} (e : Expr D Γ Λ τ) {p : Nat}, exprSucc e = some p →
    ∀ (σa σb : World D) (ρ : Env D Γ) (n : Int), ρ.unten p = some n →
      intVon τ (eval σa e σb ρ) = some (n + 1) := by
  intro τ e
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True) with
  | add a b iha ihb =>
    intro p h σa σb ρ n hn
    simp only [exprSucc] at h
    split at h
    · rename_i hb
      have ha := exprVarPos_eval a h σa σb ρ
      have hb' := exprLit_eval b hb σa σb ρ
      rw [hn] at ha
      simp only [intVon, Option.some.injEq] at ha hb'
      simp only [intVon, eval, Zahl.add]
      rw [ha, hb']
    · cases h
  | widen h1 h2 e ih =>
    intro p h σa σb ρ n hn
    rw [← ih h σa σb ρ n hn]
    rfl
  | empty => trivial
  | num _ _ => trivial
  | _ => intro p h; simp [exprSucc] at h

theorem exprSlotRead_eval : ∀ {τ : Ty} (e : Expr D Γ Λ τ) {t : D.Tab} {f : D.Feld t} {p : Nat},
    exprSlotRead e = some ⟨t, f, p⟩ → ∀ (σa σb : World D) (ρ : Env D Γ) (n : Int), ρ.unten p = some n →
      intVon τ (eval σa e σb ρ) = intVon (D.typ t f) (σb.slots t n f) := by
  intro τ e t f p h σa σb ρ n hn
  unfold exprSlotRead at h
  split at h
  · rename_i t' f' i hL
    cases hp : exprVarPos i with
    | none => rw [hp] at h; cases h
    | some q =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, hf⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have hi := exprVarPos_eval i hp σa σb ρ
      rw [hn] at hi
      simp only [intVon, Option.some.injEq] at hi
      simp only [eval, hi]
  · cases h

#print axioms exprSucc_eval
#print axioms exprSlotRead_eval

end Gabbro.Grammatik.ArenaOwnership.Body
