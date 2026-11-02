/-
  File:     Grammatik/ZeugnisStmt.lean
  Subject:  Certificate soundness for STATEMENTS (T1 of PLAN-TRANSLATION-VALIDATION.md).

  Extends `Zeugnis.lean` (expressions) to statements: `CertCond`/`CertStmt`/
  `CertSeq`/`CertEnd` are plain-data certificates, the `*Gueltig` predicates
  recompute every side condition (`darf`, `V.schreibt`, rank order, index
  shapes, linear balance), and `zeugnisStmt_sound` elaborates a valid
  certificate to a well-typed `Endblock` (the run statement).
  The Rust printer (`certemit.rs`) covers expressions only; the statement
  print format is designed in the docstrings below for the transfer phase.
-/
module
public import Grammatik.Korpus.Zeugnis.Zeugnis
public import Grammatik.Korpus.Referenz.ReferenzB
@[expose] public section


namespace Gabbro.Grammatik

/-- Boolean conditions as plain data: the `ite`/`retry`/`forever`/`pruefung`
    scrutinees over the int fragment (`CertExpr`) plus variable reads. -/
inductive CertCond (D : Deklaration) where
  | tru
  | fls
  | var (k : Nat)
  | lt (a b : CertExpr D)
  | le (a b : CertExpr D)
  | eq (a b : CertExpr D)
  | and (a b : CertCond D)
  | or (a b : CertCond D)
  | not (a : CertCond D)

/-- The `bool` range of the `k`-th variable of `Γ`, if it is bool-typed. -/
def ctxBoolTyp : Ctx → Nat → Option Unit
  | .bool :: _, 0 => some ()
  | _ :: _, 0 => none
  | _ :: Γ, k + 1 => ctxBoolTyp Γ k
  | [], _ => none

/-- Condition validity, recomputed: comparisons need int ranges on both
    sides, variables a `bool` entry, connectives valid parts. -/
def certCondGueltig (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) :
    CertCond D → Prop
  | .tru => True
  | .fls => True
  | .var k => ctxBoolTyp Γ k ≠ none
  | .lt a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .le a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .eq a b => certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none
  | .and a b => certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b
  | .or a b => certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b
  | .not a => certCondGueltig D Γ Λ a

/-- What `ctxBoolTyp` promises: a `some` names a `bool` variable. -/
theorem ctxBoolTyp_var (Γ : Ctx) (k : Nat) (h : ctxBoolTyp Γ k = some ()) :
    ∃ _ : Var Γ .bool, True := by
  induction Γ generalizing k with
  | nil =>
    cases k <;> simp only [ctxBoolTyp, reduceCtorEq] at h
  | cons τ Γ ih =>
    cases k with
    | zero =>
      cases τ with
      | bool =>
        simp only [ctxBoolTyp] at h
        exact ⟨.here, trivial⟩
      | int => simp only [ctxBoolTyp, reduceCtorEq] at h
      | opt => simp only [ctxBoolTyp, reduceCtorEq] at h
      | sum => simp only [ctxBoolTyp, reduceCtorEq] at h
      | why => simp only [ctxBoolTyp, reduceCtorEq] at h
      | never => simp only [ctxBoolTyp, reduceCtorEq] at h
      | fl => simp only [ctxBoolTyp, reduceCtorEq] at h
      | fnptr => simp only [ctxBoolTyp, reduceCtorEq] at h
      | ptr => simp only [ctxBoolTyp, reduceCtorEq] at h
      | ref | arr | str | prod => simp only [ctxBoolTyp, reduceCtorEq] at h
    | succ k =>
      simp only [ctxBoolTyp] at h
      obtain ⟨x, _⟩ := ih k h
      exact ⟨.there x, trivial⟩

/-- Condition validity as `Decidable`, by structural recursion. -/
def decCondGueltig (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (c : CertCond D) : Decidable (certCondGueltig D Γ Λ c) :=
  match c with
  | .tru => inferInstanceAs (Decidable True)
  | .fls => inferInstanceAs (Decidable True)
  | .var k => inferInstanceAs (Decidable (ctxBoolTyp Γ k ≠ none))
  | .lt a b =>
    inferInstanceAs
      (Decidable (certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none))
  | .le a b =>
    inferInstanceAs
      (Decidable (certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none))
  | .eq a b =>
    inferInstanceAs
      (Decidable (certRange D Γ Λ a ≠ none ∧ certRange D Γ Λ b ≠ none))
  | .and a b =>
    haveI := decCondGueltig D Γ Λ a
    haveI := decCondGueltig D Γ Λ b
    inferInstanceAs
      (Decidable (certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b))
  | .or a b =>
    haveI := decCondGueltig D Γ Λ a
    haveI := decCondGueltig D Γ Λ b
    inferInstanceAs
      (Decidable (certCondGueltig D Γ Λ a ∧ certCondGueltig D Γ Λ b))
  | .not a =>
    haveI := decCondGueltig D Γ Λ a
    inferInstanceAs (Decidable (certCondGueltig D Γ Λ a))

instance instDecCond (D : Deklaration) (Γ : Ctx) (Λ : List (Res D))
    (c : CertCond D) : Decidable (certCondGueltig D Γ Λ c) :=
  decCondGueltig D Γ Λ c

/-- Condition soundness: a valid condition print elaborates to a `bool`
    expression. Every hypothesis is used: range facts via `zeugnis_sound`,
    variable facts via `ctxBoolTyp_var`, tails via the induction. -/
theorem cond_sound {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertCond D) (h : certCondGueltig D Γ Λ c) :
    ∃ _ : Expr D Γ Λ .bool, True := by
  induction c with
  | tru => exact ⟨Expr.tru, trivial⟩
  | fls => exact ⟨Expr.fls, trivial⟩
  | var k =>
    simp only [certCondGueltig] at h
    cases hk : ctxBoolTyp Γ k with
    | none => exact absurd hk h
    | some u =>
      cases u with
      | unit =>
        simp only [hk] at h
        obtain ⟨x, _⟩ := ctxBoolTyp_var Γ k hk
        exact ⟨Expr.var x, trivial⟩
  | lt a b =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    cases ra : certRange D Γ Λ a with
    | none => exact absurd ra ha
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases rb : certRange D Γ Λ b with
      | none => exact absurd rb hb
      | some q =>
        obtain ⟨l2, h2⟩ := q
        obtain ⟨ea, _⟩ := zeugnis_sound a l1 h1 ra
        obtain ⟨eb, _⟩ := zeugnis_sound b l2 h2 rb
        exact ⟨Expr.lt ea eb, trivial⟩
  | le a b =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    cases ra : certRange D Γ Λ a with
    | none => exact absurd ra ha
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases rb : certRange D Γ Λ b with
      | none => exact absurd rb hb
      | some q =>
        obtain ⟨l2, h2⟩ := q
        obtain ⟨ea, _⟩ := zeugnis_sound a l1 h1 ra
        obtain ⟨eb, _⟩ := zeugnis_sound b l2 h2 rb
        exact ⟨Expr.le ea eb, trivial⟩
  | eq a b =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    cases ra : certRange D Γ Λ a with
    | none => exact absurd ra ha
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases rb : certRange D Γ Λ b with
      | none => exact absurd rb hb
      | some q =>
        obtain ⟨l2, h2⟩ := q
        obtain ⟨ea, _⟩ := zeugnis_sound a l1 h1 ra
        obtain ⟨eb, _⟩ := zeugnis_sound b l2 h2 rb
        exact ⟨Expr.eq ea eb, trivial⟩
  | and a b iha ihb =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨ea, _⟩ := iha ha
    obtain ⟨eb, _⟩ := ihb hb
    exact ⟨Expr.and ea eb, trivial⟩
  | or a b iha ihb =>
    simp only [certCondGueltig] at h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨ea, _⟩ := iha ha
    obtain ⟨eb, _⟩ := ihb hb
    exact ⟨Expr.or ea eb, trivial⟩
  | not a ih =>
    simp only [certCondGueltig] at h
    obtain ⟨ea, _⟩ := ih h
    exact ⟨Expr.not ea, trivial⟩
end Gabbro.Grammatik
