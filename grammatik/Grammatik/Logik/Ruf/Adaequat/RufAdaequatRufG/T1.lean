/-
  File:      Grammatik/RufAdaequatRufG.lean
  Subject:   ADEQUACY OF THE CALL MACHINE G FOR BODIES WITH CALLS (Target 4) --
             the sequential semantics, run with the handler `rufRumpf` that
             executes the callee's BODY, is realised by steps of one thread of
             the repaired machine, by induction on the nesting depth.

  Why: `RufAdaequatG.lean` proves adequacy for CALL-FREE bodies. A call is
  where the machine differs structurally from `execStmt` (a frame push, the
  callee's steps, a pop), and where G was wrong (`ruf` repeated the call
  after `rueck`; a verbatim pop could restore a WAITING caller and
  deadlock; the error channel of `let x = g(…) else { … }` had no rule;
  all repaired in `RufMaschineG.lean`). This file extends the covered
  fragment by direct calls in block position (`call` in `dann`), at `ende`
  position and bind-calls (`let x = g(…)`, with or without an else block,
  both paths), by callees answering a reason (`retGrund`), by the loops
  `traverse`, bounded `retry` and `forever` (with its budget), and by
  `leave`/`next` (the machine peels the scaffolding the loop body built and
  fires the loop shim), and proves: a body in the extended fragment whose
  callees' bodies are themselves in the fragment one level down
  (`Tief P A n`), started at the thread's world, returns in the machine
  exactly what `execEnd O passes (rufRumpf P O passes n)` returns
  (`rufG_adaequat_ruf`), for every nesting depth `n`.

  The handler: `rufRumpf n f σ ρ` runs `P.rumpf f` with `execEnd` and handler
  `rufRumpf (n - 1)`; depth `0` is `logik (abstieg f)` like `rufAt`. It is
  NOT `rufAt`: `rufAt` also checks `requires`/`ensures`/invariants and READS
  their places (trace events); the machine checks no contract, so the
  handler that the machine realises is the bare body run.
-/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The body-running call handler -/

/-- **The call handler that runs the callee's body.** At depth `n + 1` a call
    of `f` runs `P.rumpf f` sequentially with the handler of depth `n`; a
    return is the call's normal outcome. Depth `0` is exhausted
    (`logik (abstieg f)`, as in `rufAt`). No contract is checked -- the
    machine checks none either. -/
def rufRumpf (P : Programm D) (O : Orakel D) (passes : Nat) :
    Nat → ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f
  | 0, f, _, _ => .logik (.abstieg f)
  | n + 1, f, σ, ρ =>
      match execEnd (V := vertragVon D f) O passes (rufRumpf P O passes n) (P.rumpf f) σ ρ with
      | .zurueck σ' v => .ok σ' v
      | .why σ' r => .why σ' r
      | .leave h _ _ => absurd h (by decide)
      | .next h _ _ => absurd h (by decide)
      | .logik e => .logik e
      | .hardware e => .hardware e

/-- A normal call outcome at depth `n + 1` is a return of the callee's body. -/
theorem rufRumpf_ok {P : Programm D} {O : Orakel D} {passes : Nat} {n : Nat} {g : D.Fn}
    {σ σ' : World D} {ρ : Env D (D.params g)} {v : ErgVal D (D.erg g)}
    (h : rufRumpf P O passes (n + 1) g σ ρ = .ok σ' v) :
    execEnd (V := vertragVon D g) O passes (rufRumpf P O passes n) (P.rumpf g) σ ρ =
      .zurueck σ' v := by
  revert h
  simp only [rufRumpf]
  generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes n) (P.rumpf g) σ ρ = o
  cases o with
  | zurueck σ2 w => intro h; cases h; rfl
  | why => intro h; cases h
  | leave h' => exact absurd h' (by decide)
  | next h' => exact absurd h' (by decide)
  | logik => intro h; cases h
  | hardware => intro h; cases h

/-- A reason at depth `n + 1` is a reason of the callee's body. -/
theorem rufRumpf_grund {P : Programm D} {O : Orakel D} {passes : Nat} {n : Nat} {g : D.Fn}
    {σ σ' : World D} {ρ : Env D (D.params g)} {r : Fin (D.gruende g)}
    (h : rufRumpf P O passes (n + 1) g σ ρ = .why σ' r) :
    execEnd (V := vertragVon D g) O passes (rufRumpf P O passes n) (P.rumpf g) σ ρ =
      .why σ' r := by
  revert h
  simp only [rufRumpf]
  generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes n) (P.rumpf g) σ ρ = o
  cases o with
  | zurueck => intro h; cases h
  | why σ2 w => intro h; cases h; rfl
  | leave h' => exact absurd h' (by decide)
  | next h' => exact absurd h' (by decide)
  | logik => intro h; cases h
  | hardware => intro h; cases h

/-- Depth `0` never ends normally. -/
theorem rufRumpf_null {P : Programm D} {O : Orakel D} {passes : Nat} {g : D.Fn}
    {σ σ' : World D} {ρ : Env D (D.params g)} {v : ErgVal D (D.erg g)} :
    rufRumpf P O passes 0 g σ ρ ≠ .ok σ' v := by
  simp [rufRumpf]

/-! ## 2. The covered fragment, extended by calls, loops and exits

    As `StmtG`/`BlockG`/`EndG` (`RufAdaequatG.lean`), plus `call` (any
    position), `bindCall` and `bindCallElse`, each admitted for callees `g`
    with `C g`, plus `traverse`, `retry`, `forever`, `leave`, `next` and
    `retGrund`. -/

/-- The callee of a direct `call` statement. -/
def Stmt.rufZiel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Option D.Fn
  | .call g .. => some g
  | _ => none

mutual

/- The covered fragment, extended by calls. A call is admitted by a GENERIC
   constructor with the classifier `rufZiel` (like `blatt` with `BlattG`), so
   that inversions on other statement forms need not unify the holdings
   `nach D g Λ` of a call with anything. -/
inductive StmtR {V : Vertrag D} (A : D.Lock → Prop) (C : D.Fn → Prop) :
    Bool → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → Prop where
  | blatt {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (s : Stmt D V l Γ Λ Λ') (h : BlattG s) : StmtR A C mr s
  | ite {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ')
      (ht : BlockR A C mr t) (he : BlockR A C mr e) : StmtR A C mr (.ite c t e)
  | onOption {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Int}
      (o : Expr D Γ Λ (.opt n)) (p : Block D V l (.index n :: Γ) Λ Λ')
      (a : Block D V l Γ Λ Λ') (hp : BlockR A C mr p) (ha : BlockR A C mr a) :
      StmtR A C mr (.onOption o p a)
  | onTag {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      {cs : List (Option (Int × Int))} (v : Expr D Γ Λ (.sum cs))
      (arms : Arms D V l Γ Λ Λ' cs) (ha : ArmsR A C mr arms) :
      StmtR A C mr (.onTag v arms)
  | onWhy {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (r : Expr D Γ Λ (.why n)) (arms : GrundArms D V l Γ Λ Λ' n)
      (ha : GrundArmsR A C mr arms) : StmtR A C mr (.onWhy r arms)
  | breaking {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (i : D.Inv) (body : Block D V l Γ Λ Λ') (hb : BlockR A C mr body) :
      StmtR A C mr (.breaking i body)
  | locks {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ))
      (hbo : ∀ c, V.boden = some c → c ≤ D.rang L)
      (hA : A L) (hb : BlockR A C false body) : StmtR A C mr (.locks L hr body)
  | ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) :
      StmtR A C true (l := l) (.ret e hΛ)
  | call {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (s : Stmt D V l Γ Λ Λ') (g : D.Fn) (hg : s.rufZiel = some g) (hC : C g) :
      StmtR A C mr s
  | traverse {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (t : D.Tab) (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (hb : BlockR A C mr body) :
      StmtR A C mr (l := l) (.traverse t inv body)
  | retry {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) (hb : BlockR A C mr body) (hu : BlockR A C mr ueber) :
      StmtR A C mr (.retry n bis body ueber)
  | forever {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (hb : BlockR A C mr body) :
      StmtR A C mr (l := l) (.forever a inv body)
  | leave {mr : Bool} {Γ : Ctx} {Λ : List (Res D)} (h : true = true) :
      StmtR A C mr (.leave h : Stmt D V true Γ Λ Λ)
  | next {mr : Bool} {Γ : Ctx} {Λ : List (Res D)} (h : true = true) :
      StmtR A C mr (.next h : Stmt D V true Γ Λ Λ)
  | retWhy {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) :
      StmtR A C true (l := l) (.retWhy r hΛ)

inductive BlockR {V : Vertrag D} (A : D.Lock → Prop) (C : D.Fn → Prop) :
    Bool → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Prop where
  | nil {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      BlockR A C mr (.nil : Block D V l Γ Λ Λ)
  | cons {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
      (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
      (hs : StmtR A C mr s) (hr : BlockR A C mr rest) : BlockR A C mr (.cons s rest)
  | bind {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (e : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
      (hr : BlockR A C mr rest) : BlockR A C mr (.bind e rest)
  | bindCall {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
      (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
      (rest : Block D V l (τ :: Γ) (nach D g Λ) Λ') (hC : C g) (hrest : BlockR A C mr rest) :
      BlockR A C mr (.bindCall g args he hp hr rest)
  | regRead {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (hr : BlockR A C mr rest) :
      BlockR A C mr (.regRead r hk rest)
  | regReadElse {Γ : Ctx} {Λ Λ' : List (Res D)}
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (D.rtyp r :: Γ) Λ Λ')
      (hs : EndR A C sonst) (hr : BlockR A C true rest) :
      BlockR A C true (.regReadElse r hk zusage sonst rest)
  | awaits {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
      (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
      (hr : BlockR A C mr rest) : BlockR A C mr (.awaits g payload hp hL rest)
  | exchange {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g))
      (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
      (rest : Block D V l (D.gtyp g :: Γ) Λ Λ') (hr : BlockR A C mr rest) :
      BlockR A C mr (.exchange g neu hw hL rest)
  | narrow {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
      (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (.int lo' hi' :: Γ) Λ Λ')
      (hs : EndR A C sonst) (hr : BlockR A C true rest) :
      BlockR A C true (.narrow e lo' hi' sonst rest)
  | check {Γ : Ctx} {Λ Λ' : List (Res D)}
      (c : Expr D Γ Λ .bool) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false Γ Λ Λ')
      (hs : EndR A C sonst) (hr : BlockR A C true rest) :
      BlockR A C true (.check c sonst rest)
  | float {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int}
      (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
      (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hr : BlockR A C mr rest) : BlockR A C mr (.float op a b lo hi rest)
  | floatLit {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (q lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hr : BlockR A C mr rest) : BlockR A C mr (.floatLit q lo hi rest)
  | floatOf {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int}
      (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockR A C mr rest) :
      BlockR A C mr (.floatOf e lo hi rest)
  | floatNarrow {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
      (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (.fl lo hi :: Γ) Λ Λ')
      (hs : EndR A C sonst) (hr : BlockR A C true rest) :
      BlockR A C true (.floatNarrow e lo hi sonst rest)
  | bindCallElse {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
      (hp : RufPasst D V (D.signatur g) Λ) (hr : 0 < D.gruende g)
      (err : Endblock D V false (.why (D.gruende g) :: Γ) (nach D g Λ))
      (rest : Block D V false (τ :: Γ) (nach D g Λ) Λ') (hC : C g)
      (herr : EndR A C err) (hrest : BlockR A C true rest) :
      BlockR A C true (.bindCallElse g args he hp hr err rest)

/-- Covered end blocks: at loop level `false` (a function body), ending in
    `ret`, with covered statements (a `ret` allowed) and `let` bindings. -/
inductive EndR {V : Vertrag D} (A : D.Lock → Prop) (C : D.Fn → Prop) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → Prop where
  | ret {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) :
      EndR A C (.ret (l := false) e hΛ)
  | cons {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V false Γ Λ Λ')
      (rest : Endblock D V false Γ Λ') (hs : StmtR A C true s) (hr : EndR A C rest) :
      EndR A C (.cons s rest)
  | bind {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
      (rest : Endblock D V false (τ :: Γ) Λ) (hr : EndR A C rest) :
      EndR A C (.bind e rest)
  | retWhy {Γ : Ctx} {Λ : List (Res D)} (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) :
      EndR A C (.retWhy (l := false) r hΛ)

inductive ArmsR {V : Vertrag D} (A : D.Lock → Prop) (C : D.Fn → Prop) :
    Bool → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs → Prop where
  | nil {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      ArmsR A C mr (.nil : Arms D V l Γ Λ Λ [])
  | cons {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      {c : Option (Int × Int)} {cs : List (Option (Int × Int))}
      (b : Block D V l (ArmCtx Γ c) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs)
      (hb : BlockR A C mr b) (hr : ArmsR A C mr rest) : ArmsR A C mr (.cons b rest)

inductive GrundArmsR {V : Vertrag D} (A : D.Lock → Prop) (C : D.Fn → Prop) :
    Bool → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {n : Nat} → GrundArms D V l Γ Λ Λ' n → Prop where
  | nil {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      GrundArmsR A C mr (.nil : GrundArms D V l Γ Λ Λ 0)
  | cons {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (b : Block D V l Γ Λ Λ') (rest : GrundArms D V l Γ Λ Λ' n)
      (hb : BlockR A C mr b) (hr : GrundArmsR A C mr rest) : GrundArmsR A C mr (.cons b rest)

end
/-- The statement forms of `StmtR`, as a decidable classifier. -/
def Stmt.rArt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') : Bool :=
  match s with
  | .ite .. | .onOption .. | .onTag .. | .onWhy .. | .breaking .. | .locks ..
  | .ret .. | .call .. | .traverse .. | .retry .. | .forever .. | .leave .. | .next ..
  | .retWhy .. => true
  | s => s.blattArt

theorem StmtR.art {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (h : StmtR A C mr s) :
    s.rArt = true := by
  cases h with
  | blatt _ hb => cases hb <;> rfl
  | call s g hg _ => cases s <;> simp_all [Stmt.rufZiel, Stmt.rArt]
  | _ => rfl

/-! Inversion lemmas: the simulation recurses on the SYNTAX, so it must not
    `cases` the coverage proof (that would rename the recursive subterms). -/


end Gabbro.Grammatik
