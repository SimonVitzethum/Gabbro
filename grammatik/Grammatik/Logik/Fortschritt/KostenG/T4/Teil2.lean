module

public import Grammatik.Logik.Fortschritt.KostenG.T3
public import Grammatik.Logik.Fortschritt.KostenG.T4.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

mutual
def fremdStmt (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Nat
  | .ite _ t e => max (fremdBlock fa pa t) (fremdBlock fa pa e)
  | .onOption _ p a => max (fremdBlock fa pa p) (fremdBlock fa pa a)
  | .onTag _ arms => fremdArms fa pa arms
  | .onWhy _ arms => fremdGArms fa pa arms
  | .locks _ _ body => fremdBlock fa pa body
  | .breaking _ body => fremdBlock fa pa body
  | .traverse t _ body => (D.count t).toNat * fremdBlock fa pa body
  | .consumeTraverse t _ _ _ _ _ body => (D.count t).toNat * fremdBlock fa pa body
  | .retry n _ body ueber => n * fremdBlock fa pa body + fremdBlock fa pa ueber
  | .forever _ _ body => pa * fremdBlock fa pa body
  | .axiomCall a _ _ _ _ _ _ => fa a
  | _ => 0

def fremdBlock (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Nat
  | .nil => 0
  | .cons s rest => fremdStmt fa pa s + fremdBlock fa pa rest
  | .bind _ rest => fremdBlock fa pa rest
  | .bindCall _ _ _ _ _ rest => fremdBlock fa pa rest
  | .bindCallInd _ _ _ _ _ rest => fremdBlock fa pa rest
  | .bindCallElse _ _ _ _ _ err rest => fremdEnd fa pa err + fremdBlock fa pa rest
  | .bindAxiom a _ _ _ _ _ _ rest => fa a + fremdBlock fa pa rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => fa a + fremdEnd fa pa err + fremdBlock fa pa rest
  | .regRead _ _ rest => fremdBlock fa pa rest
  | .regReadElse _ _ _ sonst rest => fremdEnd fa pa sonst + fremdBlock fa pa rest
  | .awaits _ _ _ _ _ rest => fremdBlock fa pa rest
  | .exchange _ _ _ _ rest => fremdBlock fa pa rest
  | .narrow _ _ _ sonst rest => fremdEnd fa pa sonst + fremdBlock fa pa rest
  | .narrowRequired _ _ _ rest => fremdBlock fa pa rest
  | .check _ sonst rest => fremdEnd fa pa sonst + fremdBlock fa pa rest
  | .float _ _ _ _ _ rest => fremdBlock fa pa rest
  | .floatLit _ _ _ rest => fremdBlock fa pa rest
  | .floatOf _ _ _ rest => fremdBlock fa pa rest
  | .floatNarrow _ _ _ sonst rest => fremdEnd fa pa sonst + fremdBlock fa pa rest

def fremdArms (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Nat
  | .nil => 0
  | .cons b rest => max (fremdBlock fa pa b) (fremdArms fa pa rest)

def fremdGArms (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Nat
  | .nil => 0
  | .cons b rest => max (fremdBlock fa pa b) (fremdGArms fa pa rest)

def fremdEnd (fa : D.Ax → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret .. => 0
  | .retWhy .. => 0
  | .retScoped .. => 0
  | .retWhyScoped .. => 0
  | .leave _ => 0
  | .next _ => 0
  | .cons s rest => fremdStmt fa pa s + fremdEnd fa pa rest
  | .bind _ rest => fremdEnd fa pa rest
  | .bindCall _ _ _ _ _ rest => fremdEnd fa pa rest
  | .bindCallElse _ _ _ _ _ err rest => fremdEnd fa pa err + fremdEnd fa pa rest
  | .bindAxiom a _ _ _ _ _ _ rest => fa a + fremdEnd fa pa rest
  | .bindAxiomElse a _ _ _ _ _ _ _ err rest => fa a + fremdEnd fa pa err + fremdEnd fa pa rest
  | .regRead _ _ rest => fremdEnd fa pa rest
  | .regReadElse _ _ _ sonst rest => fremdEnd fa pa sonst + fremdEnd fa pa rest
  | .awaits _ _ _ _ _ rest => fremdEnd fa pa rest
  | .bindCallInd _ _ _ _ _ rest => fremdEnd fa pa rest
  | .narrow _ _ _ sonst rest => fremdEnd fa pa sonst + fremdEnd fa pa rest
  | .narrowRequired _ _ _ rest => fremdEnd fa pa rest
  | .exchange _ _ _ _ rest => fremdEnd fa pa rest
  -- as `Block.check` (`Endblock.alsBlock`)
  | .ite _ t e => fremdEnd fa pa e + fremdEnd fa pa t
end
/-- The §1 cost plus the declared foreign cost, per statement form. -/
def kostenStmtF (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : Nat :=
  kostenStmt c pa s + fremdStmt fa pa s

/-- The §1 cost plus the declared foreign cost, per block. -/
def kostenBlockF (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Nat :=
  kostenBlock c pa b + fremdBlock fa pa b

/-- The §1 cost plus the declared foreign cost, per end block. -/
def kostenEndF (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) : Nat :=
  kostenEnd c pa e + fremdEnd fa pa e

/-- The §1 cost plus the declared foreign cost, per `else` branch. -/
def kostenSonstF (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) : Nat :=
  kostenSonst c pa e + fremdEnd fa pa e

theorem kostenStmtF_ge (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') :
    kostenStmt c pa s ≤ kostenStmtF fa c pa s := by
  simp only [kostenStmtF]; omega

theorem kostenBlockF_ge (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    kostenBlock c pa b ≤ kostenBlockF fa c pa b := by
  simp only [kostenBlockF]; omega

theorem kostenEndF_ge (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    kostenEnd c pa e ≤ kostenEndF fa c pa e := by
  simp only [kostenEndF]; omega

theorem kostenSonstF_ge (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    kostenSonst c pa e ≤ kostenSonstF fa c pa e := by
  simp only [kostenSonstF]; omega

/-- A foreign statement site counts exactly its declared cost. -/
theorem fremd_axiomCall (fa : D.Ax → Nat) (pa : Nat) (V : Vertrag D) {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) :
    fremdStmt (V := V) fa pa (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) = fa a := by rfl

/-- A foreign bind site counts exactly its declared cost plus its continuation. -/
theorem fremd_bindAxiom (fa : D.Ax → Nat) (pa : Nat) (V : Vertrag D) {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') :
    fremdBlock (V := V) fa pa (Block.bindAxiom (V := V) (l := l) a args he hw hg hd hgd rest)
      = fa a + fremdBlock fa pa rest := by rfl

/-- No zero slip, statement site: a foreign call costs at least one step even
    at declared `0` (the §1 dispatch step). -/
theorem fremd_kein_null_stmt (fa : D.Ax → Nat) (c : D.Fn → Nat) (pa : Nat)
    (V : Vertrag D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) :
    1 ≤ kostenStmtF (V := V) fa c pa (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) := by
  simp only [kostenStmtF, kostenStmt]; omega
