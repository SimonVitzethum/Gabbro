module
public import Grammatik.Kern.Syntax.Konst.ReinBKlangAnweisungBasis
import all Grammatik.Kern.Syntax.Konst.ReinBKlangAnweisungBasis
public section
namespace Gabbro.Grammatik

/-- Accepted `constEndB` cases, as equations proved once. -/
private theorem constEndB_eq_ret (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (v : ErgExpr c.D Γ Λ V.erg) (h : Λ.Perm V.ende) :
    constEndB c (V := V) (l := l) (.ret v h) = constResultB c v := by simp only [constEndB]

private theorem constEndB_eq_cons (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λmid : List (Res c.D)} (s : Stmt c.D V l Γ Λ Λmid) (r : Endblock c.D V l Γ Λmid) :
    constEndB c (V := V) (l := l) (.cons s r) = (constStmtB c s && constEndB c r) := by simp only [constEndB]

private theorem constEndB_eq_bind (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (v : Expr c.D Γ Λ τ) (r : Endblock c.D V l (τ :: Γ) Λ) :
    constEndB c (V := V) (l := l) (.bind v r) = (constExprB c v && constEndB c r) := by simp only [constEndB]

private theorem constEndB_eq_ite (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (co : Expr c.D Γ Λ .bool) (yes no : Endblock c.D V l Γ Λ) :
    constEndB c (V := V) (l := l) (.ite co yes no) = (constExprB c co && constEndB c yes && constEndB c no) := by
  simp only [constEndB]

private theorem constEndB_eq_bindCall (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (f : c.D.Fn) (args : Args c.D Γ Λ (c.D.params f))
    (he : c.D.erg f = some τ) (hp : RufPasst c.D V (c.D.signatur f) Λ) (hr : c.D.gruende f = 0)
    (r : Endblock c.D V l (τ :: Γ) (nach c.D f Λ)) :
    constEndB c (V := V) (l := l) (.bindCall f args he hp hr r) = (constArgsB c args && constEndB c r) := by
  simp only [constEndB]

theorem constEndB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (e : Endblock c.D V l Γ Λ) (hΛ : Λ = [])
    (hacc : constEndB c e = true) : ConstEnd c (hΛ ▸ e) :=
  match e with
  | .ret value hperm => by
      try subst hΛ
      simp only [constEndB_eq_ret] at hacc
      exact .ret (constResultB_sound c value hacc)
  | .cons (Λ' := Λm) stmt rest => by
      try subst hΛ
      have hmid : Λm = [] := emptyResources c Λm
      simp only [constEndB_eq_cons, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      have hs := constStmtB_soundGen c stmt rfl hmid h0
      have hr := constEndB_soundGen c rest hmid h1
      cases hmid
      exact .cons hs hr
  | .bind value rest => by
      try subst hΛ
      simp only [constEndB_eq_bind, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .bind (constExprB_sound c value h0) (constEndB_soundGen c rest rfl h1)
  | .ite condition yes no => by
      try subst hΛ
      simp only [constEndB_eq_ite, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .ite (constExprB_sound c condition h0)
        (constEndB_soundGen c yes rfl h1) (constEndB_soundGen c no rfl h2)
  | .bindCall f args he hp hr rest => by
      try subst hΛ
      have hcall : nach c.D f [] = [] := emptyResources c _
      simp only [constEndB_eq_bindCall, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact ConstEnd.bindCall f args he hp hr hcall rest
        (constArgsB_sound c args h0) (constEndB_soundGen c rest hcall h1)
  | .retWhy .. => by
      try subst hΛ
      rw [constEndB_absage_retWhy] at hacc; exact absurd hacc Bool.false_ne_true
  | .leave .. => by
      try subst hΛ
      rw [constEndB_absage_leave] at hacc; exact absurd hacc Bool.false_ne_true
  | .next .. => by
      try subst hΛ
      rw [constEndB_absage_next] at hacc; exact absurd hacc Bool.false_ne_true
  | .narrowRequired .. => by
      try subst hΛ
      rw [constEndB_absage_narrowRequired] at hacc; exact absurd hacc Bool.false_ne_true
  | .retScoped .. => by
      try subst hΛ
      rw [constEndB_absage_retScoped] at hacc; exact absurd hacc Bool.false_ne_true
  | .retWhyScoped .. => by
      try subst hΛ
      rw [constEndB_absage_retWhyScoped] at hacc; exact absurd hacc Bool.false_ne_true
  | .bindCallElse .. => by
      try subst hΛ
      rw [constEndB_absage_bindCallElse] at hacc; exact absurd hacc Bool.false_ne_true
  | .bindAxiom .. => by
      try subst hΛ
      rw [constEndB_absage_bindAxiom] at hacc; exact absurd hacc Bool.false_ne_true
  | .bindAxiomElse .. => by
      try subst hΛ
      rw [constEndB_absage_bindAxiomElse] at hacc; exact absurd hacc Bool.false_ne_true
  | .bindAxiomOpt .. => by
      try subst hΛ
      rw [constEndB_absage_bindAxiomOpt] at hacc; exact absurd hacc Bool.false_ne_true
  | .bindAxiomOptElse .. => by
      try subst hΛ
      rw [constEndB_absage_bindAxiomOptElse] at hacc; exact absurd hacc Bool.false_ne_true
  | .regRead .. => by
      try subst hΛ
      rw [constEndB_absage_regRead] at hacc; exact absurd hacc Bool.false_ne_true
  | .regReadElse .. => by
      try subst hΛ
      rw [constEndB_absage_regReadElse] at hacc; exact absurd hacc Bool.false_ne_true
  | .awaits .. => by
      try subst hΛ
      rw [constEndB_absage_awaits] at hacc; exact absurd hacc Bool.false_ne_true
  | .bindCallInd .. => by
      try subst hΛ
      rw [constEndB_absage_bindCallInd] at hacc; exact absurd hacc Bool.false_ne_true
  | .bindCallIndElse .. => by
      try subst hΛ
      rw [constEndB_absage_bindCallIndElse] at hacc; exact absurd hacc Bool.false_ne_true
  | .narrow .. => by
      try subst hΛ
      rw [constEndB_absage_narrow] at hacc; exact absurd hacc Bool.false_ne_true
  | .exchange .. => by
      try subst hΛ
      rw [constEndB_absage_exchange] at hacc; exact absurd hacc Bool.false_ne_true
  | .float .. => by
      try subst hΛ
      rw [constEndB_absage_float] at hacc; exact absurd hacc Bool.false_ne_true
  | .floatLit .. => by
      try subst hΛ
      rw [constEndB_absage_floatLit] at hacc; exact absurd hacc Bool.false_ne_true
  | .floatOf .. => by
      try subst hΛ
      rw [constEndB_absage_floatOf] at hacc; exact absurd hacc Bool.false_ne_true
  | .floatNarrow .. => by
      try subst hΛ
      rw [constEndB_absage_floatNarrow] at hacc; exact absurd hacc Bool.false_ne_true
termination_by structural e

theorem constStmtB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    (e : Stmt c.D V l Γ [] []) :
    constStmtB c e = true → ConstStmt c e :=
  fun h => constStmtB_soundGen c e rfl rfl h

theorem constBlockB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    (e : Block c.D V l Γ [] []) :
    constBlockB c e = true → ConstBlock c e :=
  fun h => constBlockB_soundGen c e rfl rfl h

theorem constEndB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    (e : Endblock c.D V l Γ []) :
    constEndB c e = true → ConstEnd c e :=
  fun h => constEndB_soundGen c e rfl h

theorem constArmsB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {cs : List (Option Ty)} (e : Arms c.D V l Γ [] [] cs) :
    constArmsB c e = true → ConstArms c e :=
  fun h => constArmsB_soundGen c e rfl rfl h

theorem constReasonArmsB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {n : Nat} (e : GrundArms c.D V l Γ [] [] n) :
    constReasonArmsB c e = true → ConstReasonArms c e :=
  fun h => constReasonArmsB_soundGen c e rfl rfl h

end Gabbro.Grammatik
