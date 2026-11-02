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
set_option maxHeartbeats 4000000 in
mutual
theorem constStmtB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (e : Stmt c.D V l Γ Λ Λout) (hΛ : Λ = []) (hΛout : Λout = [])
    (hacc : constStmtB c e = true) : ConstStmt c (hΛout ▸ hΛ ▸ e) :=
  match Λ, Λout, e, hΛ, hΛout, hacc with
  | _, _, .assignVar x e, rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
      exact .assignVar (constExprB_sound c e hacc)
  | _, _, .ite condition yes no, rfl, rfl, hacc => by
      simp only [constStmtB, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .ite (constExprB_sound c condition h0)
        (constBlockB_soundGen c yes rfl rfl h1) (constBlockB_soundGen c no rfl rfl h2)
  | _, _, .onOption value present absent, rfl, rfl, hacc => by
      simp only [constStmtB, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .onOption (constExprB_sound c value h0)
        (constBlockB_soundGen c present rfl rfl h1) (constBlockB_soundGen c absent rfl rfl h2)
  | _, _, .onTag value arms, rfl, rfl, hacc => by
      simp only [constStmtB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .onTag (constExprB_sound c value h0) (constArmsB_soundGen c arms rfl rfl h1)
  | _, _, .onWhy reason arms, rfl, rfl, hacc => by
      simp only [constStmtB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .onWhy (constExprB_sound c reason h0) (constReasonArmsB_soundGen c arms rfl rfl h1)
  | _, _, .ret value hperm, rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
      exact .ret (constResultB_sound c value hacc)
  | _, _, .call f args hp hr, rfl, heq, hacc => by
      simp only [constStmtB] at hacc
      exact ConstStmt.call f args hp hr heq (constArgsB_sound c args hacc)
  | _, _, .assignSlot .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .assignThru .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .assignGlob .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .putBytes .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .shift .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .callInd .., rfl, _, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .locks .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .breaking .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .traverse .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .retry .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .forever .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .axiomCall .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .axiomCallElse .., rfl, _, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .regWrite .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .transition .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .publish .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .advances .., rfl, _, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .retires .., rfl, _, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .retWhy .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .leave .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .next .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .assignSlotRef .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .consumeTraverse .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .retScoped .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
  | _, _, .retWhyScoped .., rfl, rfl, hacc => by
      simp only [constStmtB] at hacc
theorem constBlockB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (e : Block c.D V l Γ Λ Λout) (hΛ : Λ = []) (hΛout : Λout = [])
    (hacc : constBlockB c e = true) : ConstBlock c (hΛout ▸ hΛ ▸ e) :=
  match Λ, Λout, e, hΛ, hΛout, hacc with
  | _, _, .nil, rfl, rfl, hacc => by
      exact .nil
  | _, _, .cons stmt rest, rfl, rfl, hacc => by
      have hmid : _ = (_ : List (Res c.D)) := emptyResources c _
      simp only [constBlockB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      have hs := constStmtB_soundGen c stmt rfl hmid h0
      have hr := constBlockB_soundGen c rest hmid rfl h1
      cases hmid
      exact .cons hs hr
  | _, _, .bind value rest, rfl, rfl, hacc => by
      simp only [constBlockB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .bind (constExprB_sound c value h0) (constBlockB_soundGen c rest rfl rfl h1)
  | _, _, .bindCall f args he hp hr rest, rfl, rfl, hacc => by
      have hcall : nach c.D f [] = [] := emptyResources c _
      simp only [constBlockB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact ConstBlock.bindCall f args he hp hr hcall rest
        (constArgsB_sound c args h0) (constBlockB_soundGen c rest hcall rfl h1)
  | _, _, .bindCallInd .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .bindCallElse .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .bindAxiom .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .bindAxiomElse .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .bindAxiomOpt .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .bindAxiomOptElse .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .regRead .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .regReadElse .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .awaits .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .exchange .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .narrow .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .narrowRequired .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .check .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .float .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .floatLit .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .floatOf .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
  | _, _, .floatNarrow .., rfl, rfl, hacc => by
      simp only [constBlockB] at hacc
theorem constEndB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (e : Endblock c.D V l Γ Λ) (hΛ : Λ = [])
    (hacc : constEndB c e = true) : ConstEnd c (hΛ ▸ e) :=
  match Λ, e, hΛ, hacc with
  | _, .ret value hperm, rfl, hacc => by
      simp only [constEndB] at hacc
      exact .ret (constResultB_sound c value hacc)
  | _, .cons stmt rest, rfl, hacc => by
      have hmid : _ = (_ : List (Res c.D)) := emptyResources c _
      simp only [constEndB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      have hs := constStmtB_soundGen c stmt rfl hmid h0
      have hr := constEndB_soundGen c rest hmid h1
      cases hmid
      exact .cons hs hr
  | _, .bind value rest, rfl, hacc => by
      simp only [constEndB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .bind (constExprB_sound c value h0) (constEndB_soundGen c rest rfl h1)
  | _, .ite condition yes no, rfl, hacc => by
      simp only [constEndB, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .ite (constExprB_sound c condition h0)
        (constEndB_soundGen c yes rfl h1) (constEndB_soundGen c no rfl h2)
  | _, .bindCall f args he hp hr rest, rfl, hacc => by
      have hcall : nach c.D f [] = [] := emptyResources c _
      simp only [constEndB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact ConstEnd.bindCall f args he hp hr hcall rest
        (constArgsB_sound c args h0) (constEndB_soundGen c rest hcall h1)
  | _, .retWhy .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .leave .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .next .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .narrowRequired .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .retScoped .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .retWhyScoped .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .bindCallElse .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .bindAxiom .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .bindAxiomElse .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .bindAxiomOpt .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .bindAxiomOptElse .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .regRead .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .regReadElse .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .awaits .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .bindCallInd .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .narrow .., rfl, hacc => by
      simp only [constEndB] at hacc
  | _, .exchange .., rfl, hacc => by
      simp only [constEndB] at hacc
theorem constArmsB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} {cs : List (Option Ty)} (e : Arms c.D V l Γ Λ Λout cs)
    (hΛ : Λ = []) (hΛout : Λout = []) (hacc : constArmsB c e = true) :
    ConstArms c (hΛout ▸ hΛ ▸ e) :=
  match Λ, Λout, cs, e, hΛ, hΛout, hacc with
  | _, _, _, .nil, rfl, rfl, hacc => by
      exact .nil
  | _, _, _, .cons body rest, rfl, rfl, hacc => by
      simp only [constArmsB, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .cons (constBlockB_soundGen c body rfl rfl h0) (constArmsB_soundGen c rest rfl rfl h1)
theorem constReasonArmsB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} {n : Nat} (e : GrundArms c.D V l Γ Λ Λout n)
    (hΛ : Λ = []) (hΛout : Λout = []) (hacc : constReasonArmsB c e = true) :
    ConstReasonArms c (hΛout ▸ hΛ ▸ e) :=
  match Λ, Λout, n, e, hΛ, hΛout, hacc with
  | _, _, _, .nil, rfl, rfl, hacc => by
      exact .nil
  | _, _, _, .cons body rest, rfl, rfl, hacc => by
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
