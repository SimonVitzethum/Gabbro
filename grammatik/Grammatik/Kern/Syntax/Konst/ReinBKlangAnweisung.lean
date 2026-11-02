module
public import Grammatik.Kern.Syntax.Konst.ReinBKlangAusdruck
public import Grammatik.Kern.Syntax.Konst.ReinBKlangAnweisungAbsage
public section
namespace Gabbro.Grammatik
private theorem emptyResources (c : ConstProgram) (rs : List (Res c.D)) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rest =>
    cases r with
    | held lock => exact (c.noLocks lock).elim
    | marke mark stage => exact (c.noMarks mark).elim
/-- Accepted `constStmtB` cases, as equations proved once (no unfolding at use sites). -/
private theorem constStmtB_eq_assignVar (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (x : Var Γ τ) (e : Expr c.D Γ Λ τ) :
    constStmtB c (.assignVar x e) = constExprB c e := by simp only [constStmtB]

private theorem constStmtB_eq_ite (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (co : Expr c.D Γ Λ .bool) (yes no : Block c.D V l Γ Λ Λout) :
    constStmtB c (.ite co yes no) = (constExprB c co && constBlockB c yes && constBlockB c no) := by
  simp only [constStmtB]

private theorem constStmtB_eq_onOption (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (v : Expr c.D Γ Λ (.opt n)) (p : Block c.D V l (.index n :: Γ) Λ Λout)
    (a : Block c.D V l Γ Λ Λout) :
    constStmtB c (.onOption v p a) = (constExprB c v && constBlockB c p && constBlockB c a) := by
  simp only [constStmtB]

private theorem constStmtB_eq_onTag (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} {cs : List (Option Ty)} (v : Expr c.D Γ Λ (.sum cs))
    (arms : Arms c.D V l Γ Λ Λout cs) :
    constStmtB c (.onTag v arms) = (constExprB c v && constArmsB c arms) := by simp only [constStmtB]

private theorem constStmtB_eq_onWhy (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} {n : Nat} (r : Expr c.D Γ Λ (.why n))
    (arms : GrundArms c.D V l Γ Λ Λout n) :
    constStmtB c (.onWhy r arms) = (constExprB c r && constReasonArmsB c arms) := by simp only [constStmtB]

private theorem constStmtB_eq_ret (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (v : ErgExpr c.D Γ Λ V.erg) (h : Λ.Perm V.ende) :
    constStmtB c (.ret v h) = constResultB c v := by simp only [constStmtB]

private theorem constStmtB_eq_call (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (f : c.D.Fn) (args : Args c.D Γ Λ (c.D.params f))
    (hp : RufPasst c.D V (c.D.signatur f) Λ) (hr : c.D.gruende f = 0) :
    constStmtB c (.call f args hp hr) = constArgsB c args := by simp only [constStmtB]

/-- Accepted `constBlockB` cases, as equations proved once. -/
private theorem constBlockB_eq_cons (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λmid Λout : List (Res c.D)} (s : Stmt c.D V l Γ Λ Λmid) (r : Block c.D V l Γ Λmid Λout) :
    constBlockB c (.cons s r) = (constStmtB c s && constBlockB c r) := by simp only [constBlockB]

private theorem constBlockB_eq_bind (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (v : Expr c.D Γ Λ τ) (r : Block c.D V l (τ :: Γ) Λ Λout) :
    constBlockB c (.bind v r) = (constExprB c v && constBlockB c r) := by simp only [constBlockB]

private theorem constBlockB_eq_bindCall (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (f : c.D.Fn) (args : Args c.D Γ Λ (c.D.params f))
    (he : c.D.erg f = some τ) (hp : RufPasst c.D V (c.D.signatur f) Λ) (hr : c.D.gruende f = 0)
    (r : Block c.D V l (τ :: Γ) (nach c.D f Λ) Λout) :
    constBlockB c (.bindCall f args he hp hr r) = (constArgsB c args && constBlockB c r) := by
  simp only [constBlockB]

/-- Accepted `constEndB` cases, as equations proved once. -/
private theorem constEndB_eq_ret (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (v : ErgExpr c.D Γ Λ V.erg) (h : Λ.Perm V.ende) :
    constEndB c (.ret v h) = constResultB c v := by simp only [constEndB]

private theorem constEndB_eq_cons (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λmid : List (Res c.D)} (s : Stmt c.D V l Γ Λ Λmid) (r : Endblock c.D V l Γ Λmid) :
    constEndB c (.cons s r) = (constStmtB c s && constEndB c r) := by simp only [constEndB]

private theorem constEndB_eq_bind (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (v : Expr c.D Γ Λ τ) (r : Endblock c.D V l (τ :: Γ) Λ) :
    constEndB c (.bind v r) = (constExprB c v && constEndB c r) := by simp only [constEndB]

private theorem constEndB_eq_ite (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (co : Expr c.D Γ Λ .bool) (yes no : Endblock c.D V l Γ Λ) :
    constEndB c (.ite co yes no) = (constExprB c co && constEndB c yes && constEndB c no) := by
  simp only [constEndB]

private theorem constEndB_eq_bindCall (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (f : c.D.Fn) (args : Args c.D Γ Λ (c.D.params f))
    (he : c.D.erg f = some τ) (hp : RufPasst c.D V (c.D.signatur f) Λ) (hr : c.D.gruende f = 0)
    (r : Endblock c.D V l (τ :: Γ) (nach c.D f Λ)) :
    constEndB c (.bindCall f args he hp hr r) = (constArgsB c args && constEndB c r) := by
  simp only [constEndB]

set_option maxHeartbeats 6000000 in
mutual
theorem constStmtB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (e : Stmt c.D V l Γ Λ Λout) (hΛ : Λ = []) (hΛout : Λout = [])
    (hacc : constStmtB c e = true) : ConstStmt c (hΛout ▸ hΛ ▸ e) :=
  match Λ, Λout, e, hΛ, hΛout, hacc with
  | _, _, .assignVar x e, rfl, rfl, hacc => by
      simp only [constStmtB_eq_assignVar] at hacc
      exact .assignVar (constExprB_sound c e hacc)
  | _, _, .ite condition yes no, rfl, rfl, hacc => by
      simp only [constStmtB_eq_ite, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .ite (constExprB_sound c condition h0)
        (constBlockB_soundGen c yes rfl rfl h1) (constBlockB_soundGen c no rfl rfl h2)
  | _, _, .onOption value present absent, rfl, rfl, hacc => by
      simp only [constStmtB_eq_onOption, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .onOption (constExprB_sound c value h0)
        (constBlockB_soundGen c present rfl rfl h1) (constBlockB_soundGen c absent rfl rfl h2)
  | _, _, .onTag value arms, rfl, rfl, hacc => by
      simp only [constStmtB_eq_onTag, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .onTag (constExprB_sound c value h0) (constArmsB_soundGen c arms rfl rfl h1)
  | _, _, .onWhy reason arms, rfl, rfl, hacc => by
      simp only [constStmtB_eq_onWhy, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .onWhy (constExprB_sound c reason h0) (constReasonArmsB_soundGen c arms rfl rfl h1)
  | _, _, .ret value hperm, rfl, rfl, hacc => by
      simp only [constStmtB_eq_ret] at hacc
      exact .ret (constResultB_sound c value hacc)
  | _, _, .call f args hp hr, rfl, heq, hacc => by
      simp only [constStmtB_eq_call] at hacc
      exact ConstStmt.call f args hp hr heq (constArgsB_sound c args hacc)
  | _, _, .assignSlot .., rfl, rfl, hacc => by
      rw [constStmtB_absage_assignSlot] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .assignThru .., rfl, rfl, hacc => by
      rw [constStmtB_absage_assignThru] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .assignGlob .., rfl, rfl, hacc => by
      rw [constStmtB_absage_assignGlob] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .putBytes .., rfl, rfl, hacc => by
      rw [constStmtB_absage_putBytes] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .shift .., rfl, rfl, hacc => by
      rw [constStmtB_absage_shift] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .callInd .., rfl, _, hacc => by
      rw [constStmtB_absage_callInd] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .callIndElse .., rfl, _, hacc => by
      rw [constStmtB_absage_callIndElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .locks .., rfl, rfl, hacc => by
      rw [constStmtB_absage_locks] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .breaking .., rfl, rfl, hacc => by
      rw [constStmtB_absage_breaking] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .traverse .., rfl, rfl, hacc => by
      rw [constStmtB_absage_traverse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .retry .., rfl, rfl, hacc => by
      rw [constStmtB_absage_retry] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .forever .., rfl, rfl, hacc => by
      rw [constStmtB_absage_forever] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .axiomCall .., rfl, rfl, hacc => by
      rw [constStmtB_absage_axiomCall] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .axiomCallElse .., rfl, _, hacc => by
      rw [constStmtB_absage_axiomCallElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .regWrite .., rfl, rfl, hacc => by
      rw [constStmtB_absage_regWrite] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .transition .., rfl, rfl, hacc => by
      rw [constStmtB_absage_transition] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .publish .., rfl, rfl, hacc => by
      rw [constStmtB_absage_publish] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .advances .., rfl, _, hacc => by
      rw [constStmtB_absage_advances] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .retires .., rfl, _, hacc => by
      rw [constStmtB_absage_retires] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .retWhy .., rfl, rfl, hacc => by
      rw [constStmtB_absage_retWhy] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .leave .., rfl, rfl, hacc => by
      rw [constStmtB_absage_leave] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .next .., rfl, rfl, hacc => by
      rw [constStmtB_absage_next] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .assignSlotRef .., rfl, rfl, hacc => by
      rw [constStmtB_absage_assignSlotRef] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .consumeTraverse .., rfl, rfl, hacc => by
      rw [constStmtB_absage_consumeTraverse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .retScoped .., rfl, rfl, hacc => by
      rw [constStmtB_absage_retScoped] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .retWhyScoped .., rfl, rfl, hacc => by
      rw [constStmtB_absage_retWhyScoped] at hacc; exact absurd hacc Bool.false_ne_true
theorem constBlockB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ Λout : List (Res c.D)} (e : Block c.D V l Γ Λ Λout) (hΛ : Λ = []) (hΛout : Λout = [])
    (hacc : constBlockB c e = true) : ConstBlock c (hΛout ▸ hΛ ▸ e) :=
  match Λ, Λout, e, hΛ, hΛout, hacc with
  | _, _, .nil, rfl, rfl, hacc => by
      exact .nil
  | _, _, .cons stmt rest, rfl, rfl, hacc => by
      have hmid : _ = (_ : List (Res c.D)) := emptyResources c _
      simp only [constBlockB_eq_cons, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      have hs := constStmtB_soundGen c stmt rfl hmid h0
      have hr := constBlockB_soundGen c rest hmid rfl h1
      cases hmid
      exact .cons hs hr
  | _, _, .bind value rest, rfl, rfl, hacc => by
      simp only [constBlockB_eq_bind, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .bind (constExprB_sound c value h0) (constBlockB_soundGen c rest rfl rfl h1)
  | _, _, .bindCall f args he hp hr rest, rfl, rfl, hacc => by
      have hcall : nach c.D f [] = [] := emptyResources c _
      simp only [constBlockB_eq_bindCall, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact ConstBlock.bindCall f args he hp hr hcall rest
        (constArgsB_sound c args h0) (constBlockB_soundGen c rest hcall rfl h1)
  | _, _, .bindCallInd .., rfl, rfl, hacc => by
      rw [constBlockB_absage_bindCallInd] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .bindCallIndElse .., rfl, rfl, hacc => by
      rw [constBlockB_absage_bindCallIndElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .bindCallElse .., rfl, rfl, hacc => by
      rw [constBlockB_absage_bindCallElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .bindAxiom .., rfl, rfl, hacc => by
      rw [constBlockB_absage_bindAxiom] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .bindAxiomElse .., rfl, rfl, hacc => by
      rw [constBlockB_absage_bindAxiomElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .bindAxiomOpt .., rfl, rfl, hacc => by
      rw [constBlockB_absage_bindAxiomOpt] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .bindAxiomOptElse .., rfl, rfl, hacc => by
      rw [constBlockB_absage_bindAxiomOptElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .regRead .., rfl, rfl, hacc => by
      rw [constBlockB_absage_regRead] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .regReadElse .., rfl, rfl, hacc => by
      rw [constBlockB_absage_regReadElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .awaits .., rfl, rfl, hacc => by
      rw [constBlockB_absage_awaits] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .exchange .., rfl, rfl, hacc => by
      rw [constBlockB_absage_exchange] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .narrow .., rfl, rfl, hacc => by
      rw [constBlockB_absage_narrow] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .narrowRequired .., rfl, rfl, hacc => by
      rw [constBlockB_absage_narrowRequired] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .check .., rfl, rfl, hacc => by
      rw [constBlockB_absage_check] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .float .., rfl, rfl, hacc => by
      rw [constBlockB_absage_float] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .floatLit .., rfl, rfl, hacc => by
      rw [constBlockB_absage_floatLit] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .floatOf .., rfl, rfl, hacc => by
      rw [constBlockB_absage_floatOf] at hacc; exact absurd hacc Bool.false_ne_true
  | _, _, .floatNarrow .., rfl, rfl, hacc => by
      rw [constBlockB_absage_floatNarrow] at hacc; exact absurd hacc Bool.false_ne_true
theorem constEndB_soundGen (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res c.D)} (e : Endblock c.D V l Γ Λ) (hΛ : Λ = [])
    (hacc : constEndB c e = true) : ConstEnd c (hΛ ▸ e) :=
  match Λ, e, hΛ, hacc with
  | _, .ret value hperm, rfl, hacc => by
      simp only [constEndB_eq_ret] at hacc
      exact .ret (constResultB_sound c value hacc)
  | _, .cons stmt rest, rfl, hacc => by
      have hmid : _ = (_ : List (Res c.D)) := emptyResources c _
      simp only [constEndB_eq_cons, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      have hs := constStmtB_soundGen c stmt rfl hmid h0
      have hr := constEndB_soundGen c rest hmid h1
      cases hmid
      exact .cons hs hr
  | _, .bind value rest, rfl, hacc => by
      simp only [constEndB_eq_bind, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact .bind (constExprB_sound c value h0) (constEndB_soundGen c rest rfl h1)
  | _, .ite condition yes no, rfl, hacc => by
      simp only [constEndB_eq_ite, Bool.and_eq_true] at hacc
      obtain ⟨⟨h0, h1⟩, h2⟩ := hacc
      exact .ite (constExprB_sound c condition h0)
        (constEndB_soundGen c yes rfl h1) (constEndB_soundGen c no rfl h2)
  | _, .bindCall f args he hp hr rest, rfl, hacc => by
      have hcall : nach c.D f [] = [] := emptyResources c _
      simp only [constEndB_eq_bindCall, Bool.and_eq_true] at hacc
      obtain ⟨h0, h1⟩ := hacc
      exact ConstEnd.bindCall f args he hp hr hcall rest
        (constArgsB_sound c args h0) (constEndB_soundGen c rest hcall h1)
  | _, .retWhy .., rfl, hacc => by
      rw [constEndB_absage_retWhy] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .leave .., rfl, hacc => by
      rw [constEndB_absage_leave] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .next .., rfl, hacc => by
      rw [constEndB_absage_next] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .narrowRequired .., rfl, hacc => by
      rw [constEndB_absage_narrowRequired] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .retScoped .., rfl, hacc => by
      rw [constEndB_absage_retScoped] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .retWhyScoped .., rfl, hacc => by
      rw [constEndB_absage_retWhyScoped] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .bindCallElse .., rfl, hacc => by
      rw [constEndB_absage_bindCallElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .bindAxiom .., rfl, hacc => by
      rw [constEndB_absage_bindAxiom] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .bindAxiomElse .., rfl, hacc => by
      rw [constEndB_absage_bindAxiomElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .bindAxiomOpt .., rfl, hacc => by
      rw [constEndB_absage_bindAxiomOpt] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .bindAxiomOptElse .., rfl, hacc => by
      rw [constEndB_absage_bindAxiomOptElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .regRead .., rfl, hacc => by
      rw [constEndB_absage_regRead] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .regReadElse .., rfl, hacc => by
      rw [constEndB_absage_regReadElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .awaits .., rfl, hacc => by
      rw [constEndB_absage_awaits] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .bindCallInd .., rfl, hacc => by
      rw [constEndB_absage_bindCallInd] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .bindCallIndElse .., rfl, hacc => by
      rw [constEndB_absage_bindCallIndElse] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .narrow .., rfl, hacc => by
      rw [constEndB_absage_narrow] at hacc; exact absurd hacc Bool.false_ne_true
  | _, .exchange .., rfl, hacc => by
      rw [constEndB_absage_exchange] at hacc; exact absurd hacc Bool.false_ne_true
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
