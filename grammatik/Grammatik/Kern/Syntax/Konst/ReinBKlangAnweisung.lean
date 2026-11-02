module
public import Grammatik.Kern.Syntax.Konst.ReinBKlangAusdruck
public section
namespace Gabbro.Grammatik
private theorem emptyResources (c : ConstProgram) (rs : List (Res c.D)) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rest =>
    cases r with
    | held lock => exact (c.noLocks lock).elim
    | marke mark stage => exact (c.noMarks mark).elim
mutual
theorem constStmtB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (e : Stmt c.D V l Γ Λ Λout) (hΛ : Λ = []) (hΛout : Λout = [])
    (hacc : constStmtB c e = true) : ConstStmt c (hΛout ▸ hΛ ▸ e) := by
  match e with
  | .assignVar x e => by
      cases hΛ; cases hΛout
      simp only [constStmtB] at hacc
      exact .assignVar (constExprB_sound c e hacc)
  | .ite condition yes no => by
      cases hΛ; cases hΛout
      simp only [constStmtB, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .ite (constExprB_sound c condition h0)
        (constBlockB_soundGen c yes rfl rfl h1) (constBlockB_soundGen c no rfl rfl h2)
  | .onOption value present absent => by
      cases hΛ; cases hΛout
      simp only [constStmtB, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .onOption (constExprB_sound c value h0)
        (constBlockB_soundGen c present rfl rfl h1) (constBlockB_soundGen c absent rfl rfl h2)
  | .onTag value arms => by
      cases hΛ; cases hΛout
      simp only [constStmtB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .onTag (constExprB_sound c value h0) (constArmsB_soundGen c arms rfl rfl h1)
  | .onWhy reason arms => by
      cases hΛ; cases hΛout
      simp only [constStmtB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .onWhy (constExprB_sound c reason h0) (constReasonArmsB_soundGen c arms rfl rfl h1)
  | .ret value hperm => by
      cases hΛ; cases hΛout
      simp only [constStmtB] at hacc
      exact .ret (constResultB_sound c value hacc)
  | .call f args hp hr => by
      cases hΛ
      simp only [constStmtB] at hacc
      exact ConstStmt.call f args hp hr hΛout (constArgsB_sound c args hacc)
  | .assignSlot .. => by
      simp [constStmtB] at hacc
  | .assignThru .. => by
      simp [constStmtB] at hacc
  | .assignGlob .. => by
      simp [constStmtB] at hacc
  | .putBytes .. => by
      simp [constStmtB] at hacc
  | .shift .. => by
      simp [constStmtB] at hacc
  | .callInd .. => by
      simp [constStmtB] at hacc
  | .locks .. => by
      simp [constStmtB] at hacc
  | .breaking .. => by
      simp [constStmtB] at hacc
  | .traverse .. => by
      simp [constStmtB] at hacc
  | .retry .. => by
      simp [constStmtB] at hacc
  | .forever .. => by
      simp [constStmtB] at hacc
  | .axiomCall .. => by
      simp [constStmtB] at hacc
  | .regWrite .. => by
      simp [constStmtB] at hacc
  | .transition .. => by
      simp [constStmtB] at hacc
  | .publish .. => by
      simp [constStmtB] at hacc
  | .advances .. => by
      simp [constStmtB] at hacc
  | .retires .. => by
      simp [constStmtB] at hacc
  | .retWhy .. => by
      simp [constStmtB] at hacc
  | .leave .. => by
      simp [constStmtB] at hacc
  | .next .. => by
      simp [constStmtB] at hacc
  | .assignSlotRef .. => by
      simp [constStmtB] at hacc
  | .consumeTraverse .. => by
      simp [constStmtB] at hacc
  | .retScoped .. => by
      simp [constStmtB] at hacc
  | .retWhyScoped .. => by
      simp [constStmtB] at hacc
theorem constBlockB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (e : Block c.D V l Γ Λ Λout) (hΛ : Λ = []) (hΛout : Λout = [])
    (hacc : constBlockB c e = true) : ConstBlock c (hΛout ▸ hΛ ▸ e) := by
  match e with
  | .nil => by
      cases hΛ; cases hΛout
      exact .nil
  | .cons stmt rest => by
      rename_i mid
      have hmid : mid = [] := emptyResources c mid
      cases hΛ; cases hmid; cases hΛout
      simp only [constBlockB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .cons (constStmtB_soundGen c stmt rfl rfl h0) (constBlockB_soundGen c rest rfl rfl h1)
  | .bind value rest => by
      cases hΛ; cases hΛout
      simp only [constBlockB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .bind (constExprB_sound c value h0) (constBlockB_soundGen c rest rfl rfl h1)
  | .bindCall f args he hp hr rest => by
      cases hΛ; cases hΛout
      have hcall : nach c.D f [] = [] := emptyResources c _
      simp only [constBlockB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact ConstBlock.bindCall f args he hp hr hcall rest
        (constArgsB_sound c args h0) (constBlockB_soundGen c rest hcall rfl h1)
  | .bindCallInd .. => by
      simp [constBlockB] at hacc
  | .bindCallElse .. => by
      simp [constBlockB] at hacc
  | .bindAxiom .. => by
      simp [constBlockB] at hacc
  | .bindAxiomElse .. => by
      simp [constBlockB] at hacc
  | .regRead .. => by
      simp [constBlockB] at hacc
  | .regReadElse .. => by
      simp [constBlockB] at hacc
  | .awaits .. => by
      simp [constBlockB] at hacc
  | .exchange .. => by
      simp [constBlockB] at hacc
  | .narrow .. => by
      simp [constBlockB] at hacc
  | .narrowRequired .. => by
      simp [constBlockB] at hacc
  | .check .. => by
      simp [constBlockB] at hacc
  | .float .. => by
      simp [constBlockB] at hacc
  | .floatLit .. => by
      simp [constBlockB] at hacc
  | .floatOf .. => by
      simp [constBlockB] at hacc
  | .floatNarrow .. => by
      simp [constBlockB] at hacc
theorem constEndB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (e : Endblock c.D V l Γ Λ) (hΛ : Λ = [])
    (hacc : constEndB c e = true) : ConstEnd c (hΛ ▸ e) := by
  match e with
  | .ret value hperm => by
      cases hΛ
      simp only [constEndB] at hacc
      exact .ret (constResultB_sound c value hacc)
  | .cons stmt rest => by
      rename_i mid
      have hmid : mid = [] := emptyResources c mid
      cases hΛ; cases hmid
      simp only [constEndB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .cons (constStmtB_soundGen c stmt rfl rfl h0) (constEndB_soundGen c rest rfl h1)
  | .bind value rest => by
      cases hΛ
      simp only [constEndB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .bind (constExprB_sound c value h0) (constEndB_soundGen c rest rfl h1)
  | .ite condition yes no => by
      cases hΛ
      simp only [constEndB, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .ite (constExprB_sound c condition h0)
        (constEndB_soundGen c yes rfl h1) (constEndB_soundGen c no rfl h2)
  | .bindCall f args he hp hr rest => by
      cases hΛ
      have hcall : nach c.D f [] = [] := emptyResources c _
      simp only [constEndB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact ConstEnd.bindCall f args he hp hr hcall rest
        (constArgsB_sound c args h0) (constEndB_soundGen c rest hcall h1)
  | .retWhy .. => by
      simp [constEndB] at hacc
  | .leave .. => by
      simp [constEndB] at hacc
  | .next .. => by
      simp [constEndB] at hacc
  | .narrowRequired .. => by
      simp [constEndB] at hacc
  | .retScoped .. => by
      simp [constEndB] at hacc
  | .retWhyScoped .. => by
      simp [constEndB] at hacc
  | .bindCallElse .. => by
      simp [constEndB] at hacc
  | .bindAxiom .. => by
      simp [constEndB] at hacc
  | .bindAxiomElse .. => by
      simp [constEndB] at hacc
  | .regRead .. => by
      simp [constEndB] at hacc
  | .regReadElse .. => by
      simp [constEndB] at hacc
  | .awaits .. => by
      simp [constEndB] at hacc
  | .bindCallInd .. => by
      simp [constEndB] at hacc
  | .narrow .. => by
      simp [constEndB] at hacc
  | .exchange .. => by
      simp [constEndB] at hacc
theorem constArmsB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} {cs : List (Option Ty)} (e : Arms c.D V l Γ Λ Λout cs)
    (hΛ : Λ = []) (hΛout : Λout = []) (hacc : constArmsB c e = true) :
    ConstArms c (hΛout ▸ hΛ ▸ e) := by
  match e with
  | .nil => by
      cases hΛ; cases hΛout
      exact .nil
  | .cons body rest => by
      rename_i mid
      have hmid : mid = [] := emptyResources c mid
      cases hΛ; cases hmid; cases hΛout
      simp only [constArmsB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .cons (constBlockB_soundGen c body rfl rfl h0) (constArmsB_soundGen c rest rfl rfl h1)
theorem constReasonArmsB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} {n : Nat} (e : GrundArms c.D V l Γ Λ Λout n)
    (hΛ : Λ = []) (hΛout : Λout = []) (hacc : constReasonArmsB c e = true) :
    ConstReasonArms c (hΛout ▸ hΛ ▸ e) := by
  match e with
  | .nil => by
      cases hΛ; cases hΛout
      exact .nil
  | .cons body rest => by
      rename_i mid
      have hmid : mid = [] := emptyResources c mid
      cases hΛ; cases hmid; cases hΛout
      simp only [constReasonArmsB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .cons (constBlockB_soundGen c body rfl rfl h0) (constReasonArmsB_soundGen c rest rfl rfl h1)
end

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
