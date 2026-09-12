/-
  File:      Grammatik/RufAdaequatRufG.lean
  Subject:   ADEQUACY OF THE CALL MACHINE G FOR BODIES WITH CALLS (Target 4) --
             the sequential semantics, run with the handler `rufRumpf` that
             executes the callee's BODY, is realised by steps of one thread of
             the repaired machine, by induction on the nesting depth.

  Why: `RufAdaequatG.lean` proves adequacy for CALL-FREE bodies. A call is
  where the machine differs structurally from `execStmt` (a frame push, the
  callee's steps, a pop), and where G was wrong (`ruf` repeated the call
  after `rueck`; repaired in `RufMaschineG.lean`). This file extends the
  covered fragment by direct calls in block position (`call` in `dann`),
  at `ende` position (`call` before the rest of an end block) and bind-calls
  (`let x = g(…)`), and proves: a body in the extended fragment whose
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
import Grammatik.RufAdaequatG

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
      | .grund σ' r => .grund σ' r
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
  | grund => intro h; cases h
  | leave h' => exact absurd h' (by decide)
  | next h' => exact absurd h' (by decide)
  | logik => intro h; cases h
  | hardware => intro h; cases h

/-- Depth `0` never ends normally. -/
theorem rufRumpf_null {P : Programm D} {O : Orakel D} {passes : Nat} {g : D.Fn}
    {σ σ' : World D} {ρ : Env D (D.params g)} {v : ErgVal D (D.erg g)} :
    rufRumpf P O passes 0 g σ ρ ≠ .ok σ' v := by
  simp [rufRumpf]

/-! ## 2. The covered fragment, extended by calls

    As `StmtG`/`BlockG`/`EndG` (`RufAdaequatG.lean`), plus `call` (any
    position) and `bindCall`, each admitted for callees `g` with `C g`. -/

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
  | onGrund {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (r : Expr D Γ Λ (.grund n)) (arms : GrundArms D V l Γ Λ Λ' n)
      (ha : GrundArmsR A C mr arms) : StmtR A C mr (.onGrund r arms)
  | breaking {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (i : D.Inv) (body : Block D V l Γ Λ Λ') (hb : BlockR A C mr body) :
      StmtR A C mr (.breaking i body)
  | locks {mr : Bool} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ))
      (hA : A L) (hb : BlockR A C false body) : StmtR A C mr (.locks L hr body)
  | ret {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
      (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) :
      StmtR A C true (l := l) (.ret e hΛ)
  | call {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (s : Stmt D V l Γ Λ Λ') (g : D.Fn) (hg : s.rufZiel = some g) (hC : C g) :
      StmtR A C mr s

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
  | regLies {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (hr : BlockR A C mr rest) :
      BlockR A C mr (.regLies r hk rest)
  | regLiesElse {Γ : Ctx} {Λ Λ' : List (Res D)}
      (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (D.rtyp r :: Γ) Λ Λ')
      (hs : EndR A C sonst) (hr : BlockR A C true rest) :
      BlockR A C true (.regLiesElse r hk zusage sonst rest)
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
  | pruefung {Γ : Ctx} {Λ Λ' : List (Res D)}
      (c : Expr D Γ Λ .bool) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false Γ Λ Λ')
      (hs : EndR A C sonst) (hr : BlockR A C true rest) :
      BlockR A C true (.pruefung c sonst rest)
  | gleit {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int}
      (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
      (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hr : BlockR A C mr rest) : BlockR A C mr (.gleit op a b lo hi rest)
  | gleitLit {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
      (q lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ')
      (hr : BlockR A C mr rest) : BlockR A C mr (.gleitLit q lo hi rest)
  | gleitVon {mr : Bool} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int}
      (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (hr : BlockR A C mr rest) :
      BlockR A C mr (.gleitVon e lo hi rest)
  | gleitNarrow {Γ : Ctx} {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
      (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int) (sonst : Endblock D V false Γ Λ)
      (rest : Block D V false (.fl lo hi :: Γ) Λ Λ')
      (hs : EndR A C sonst) (hr : BlockR A C true rest) :
      BlockR A C true (.gleitNarrow e lo hi sonst rest)

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
  | .ite .. | .onOption .. | .onTag .. | .onGrund .. | .breaking .. | .locks ..
  | .ret .. | .call .. => true
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

section Inv

variable {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} {mr l : Bool} {Γ : Ctx}

theorem StmtR.ite_inv {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool}
    {t e : Block D V l Γ Λ Λ'} (h : StmtR A C mr (.ite c t e)) :
    BlockR A C mr t ∧ BlockR A C mr e := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | call _ _ hg _ => simp [Stmt.rufZiel] at hg
  | ite _ _ _ ht he => exact ⟨ht, he⟩

theorem StmtR.onOption_inv {Λ Λ' : List (Res D)} {n : Int} {o : Expr D Γ Λ (.opt n)}
    {p : Block D V l (.index n :: Γ) Λ Λ'} {a : Block D V l Γ Λ Λ'}
    (h : StmtR A C mr (.onOption o p a)) : BlockR A C mr p ∧ BlockR A C mr a := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | call _ _ hg _ => simp [Stmt.rufZiel] at hg
  | onOption _ _ _ hp ha => exact ⟨hp, ha⟩

theorem StmtR.onTag_inv {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {v : Expr D Γ Λ (.sum cs)} {arms : Arms D V l Γ Λ Λ' cs}
    (h : StmtR A C mr (.onTag v arms)) : ArmsR A C mr arms := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | call _ _ hg _ => simp [Stmt.rufZiel] at hg
  | onTag _ _ ha => exact ha

theorem StmtR.onGrund_inv {Λ Λ' : List (Res D)} {n : Nat}
    {r : Expr D Γ Λ (.grund n)} {arms : GrundArms D V l Γ Λ Λ' n}
    (h : StmtR A C mr (.onGrund r arms)) : GrundArmsR A C mr arms := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | call _ _ hg _ => simp [Stmt.rufZiel] at hg
  | onGrund _ _ ha => exact ha

theorem StmtR.breaking_inv {Λ Λ' : List (Res D)} {i : D.Inv}
    {body : Block D V l Γ Λ Λ'} (h : StmtR A C mr (.breaking i body)) : BlockR A C mr body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | call _ _ hg _ => simp [Stmt.rufZiel] at hg
  | breaking _ _ hb => exact hb

theorem StmtR.locks_inv {Λ : List (Res D)} {L : D.Lock}
    {hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L}
    {body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)}
    (h : StmtR A C mr (.locks L hr body)) : A L ∧ BlockR A C false body := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | call _ _ hg _ => simp [Stmt.rufZiel] at hg
  | locks _ _ _ hA hb => exact ⟨hA, hb⟩

theorem StmtR.ret_inv {Λ : List (Res D)} {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (h : StmtR A C mr (.ret (l := l) e hΛ)) : mr = true := by
  cases h with
  | blatt _ hb => exact absurd hb.art (by simp [Stmt.blattArt])
  | call _ _ hg _ => simp [Stmt.rufZiel] at hg
  | ret _ _ => rfl

theorem BlockR.cons_inv {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} (h : BlockR A C mr (.cons s rest)) :
    StmtR A C mr s ∧ BlockR A C mr rest := by
  cases h with
  | cons _ _ hs hr => exact ⟨hs, hr⟩

theorem BlockR.bind_inv {Λ Λ' : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Block D V l (τ :: Γ) Λ Λ'} (h : BlockR A C mr (.bind e rest)) : BlockR A C mr rest := by
  cases h with
  | bind _ _ hr => exact hr

theorem BlockR.regLies_inv {Λ Λ' : List (Res D)} {r : D.Reg}
    {hk : (D.rklasse r).lesbar = true} {rest : Block D V l (D.rtyp r :: Γ) Λ Λ'}
    (h : BlockR A C mr (.regLies r hk rest)) : BlockR A C mr rest := by
  cases h with
  | regLies _ _ _ hr => exact hr

theorem BlockR.awaits_inv {Λ Λ' : List (Res D)} {g : D.Glob} {payload : List D.Glob}
    {hp : payload = D.nutzlast g} {hL : gdarf D g Λ}
    {rest : Block D V l (D.gtyp g :: Γ) Λ Λ'}
    (h : BlockR A C mr (.awaits g payload hp hL rest)) : BlockR A C mr rest := by
  cases h with
  | awaits _ _ _ _ _ hr => exact hr

theorem BlockR.exchange_inv {Λ Λ' : List (Res D)} {g : D.Glob}
    {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)} {hw : V.gschreibt g = true}
    {hL : gdarf D g Λ} {rest : Block D V l (D.gtyp g :: Γ) Λ Λ'}
    (h : BlockR A C mr (.exchange g neu hw hL rest)) : BlockR A C mr rest := by
  cases h with
  | exchange _ _ _ _ _ hr => exact hr

theorem BlockR.gleit_inv {Λ Λ' : List (Res D)} {l1 h1 l2 h2 : Int × Int} {op : GleitOp}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)} {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockR A C mr (.gleit op a b lo hi rest)) : BlockR A C mr rest := by
  cases h with
  | gleit _ _ _ _ _ _ hr => exact hr

theorem BlockR.gleitLit_inv {Λ Λ' : List (Res D)} {q lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockR A C mr (.gleitLit q lo hi rest)) : BlockR A C mr rest := by
  cases h with
  | gleitLit _ _ _ _ hr => exact hr

theorem BlockR.gleitVon_inv {Λ Λ' : List (Res D)} {l1 h1 : Int}
    {e : Expr D Γ Λ (.int l1 h1)} {lo hi : Int × Int}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockR A C mr (.gleitVon e lo hi rest)) : BlockR A C mr rest := by
  cases h with
  | gleitVon _ _ _ _ hr => exact hr

theorem BlockR.regLiesElse_inv {Λ Λ' : List (Res D)} {r : D.Reg}
    {hk : (D.rklasse r).lesbar = true} {zusage : Expr D (D.rtyp r :: Γ) Λ .bool}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l (D.rtyp r :: Γ) Λ Λ'}
    (h : BlockR A C mr (.regLiesElse r hk zusage sonst rest)) :
    mr = true ∧ BlockR A C true rest ∧ EndR A C sonst ∧ l = false := by
  cases h with
  | regLiesElse _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockR.narrow_inv {Λ Λ' : List (Res D)} {lo hi : Int}
    {e : Expr D Γ Λ (.int lo hi)} {lo' hi' : Int} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.int lo' hi' :: Γ) Λ Λ'}
    (h : BlockR A C mr (.narrow e lo' hi' sonst rest)) :
    mr = true ∧ BlockR A C true rest ∧ EndR A C sonst ∧ l = false := by
  cases h with
  | narrow _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockR.pruefung_inv {Λ Λ' : List (Res D)} {c : Expr D Γ Λ .bool}
    {sonst : Endblock D V l Γ Λ} {rest : Block D V l Γ Λ Λ'}
    (h : BlockR A C mr (.pruefung c sonst rest)) :
    mr = true ∧ BlockR A C true rest ∧ EndR A C sonst ∧ l = false := by
  cases h with
  | pruefung _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem BlockR.gleitNarrow_inv {Λ Λ' : List (Res D)} {l1 h1 : Int × Int}
    {e : Expr D Γ Λ (.fl l1 h1)} {lo hi : Int × Int} {sonst : Endblock D V l Γ Λ}
    {rest : Block D V l (.fl lo hi :: Γ) Λ Λ'}
    (h : BlockR A C mr (.gleitNarrow e lo hi sonst rest)) :
    mr = true ∧ BlockR A C true rest ∧ EndR A C sonst ∧ l = false := by
  cases h with
  | gleitNarrow _ _ _ _ _ hs hr => exact ⟨rfl, hr, hs, rfl⟩

theorem ArmsR.cons_inv {Λ Λ' : List (Res D)} {c : Option (Int × Int)}
    {cs : List (Option (Int × Int))} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {rest : Arms D V l Γ Λ Λ' cs} (h : ArmsR A C mr (.cons b rest)) :
    BlockR A C mr b ∧ ArmsR A C mr rest := by
  cases h with
  | cons _ _ hb hr => exact ⟨hb, hr⟩

theorem GrundArmsR.cons_inv {Λ Λ' : List (Res D)} {n : Nat}
    {b : Block D V l Γ Λ Λ'} {rest : GrundArms D V l Γ Λ Λ' n}
    (h : GrundArmsR A C mr (.cons b rest)) : BlockR A C mr b ∧ GrundArmsR A C mr rest := by
  cases h with
  | cons _ _ hb hr => exact ⟨hb, hr⟩

theorem EndR.ret_inv {Λ : List (Res D)} {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (h : EndR A C (.ret (l := l) e hΛ)) : l = false := by
  cases h with
  | ret _ _ => rfl

theorem EndR.cons_inv {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : EndR A C (.cons s rest)) :
    StmtR A C true s ∧ EndR A C rest ∧ l = false := by
  cases h with
  | cons _ _ hs hr => exact ⟨hs, hr, rfl⟩

theorem EndR.bind_inv {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D V l (τ :: Γ) Λ} (h : EndR A C (.bind e rest)) : EndR A C rest := by
  cases h with
  | bind _ _ hr => exact hr

/-- A covered statement that is a call admits its callee. -/
theorem StmtR.call_inv' {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (h : StmtR A C mr s)
    (g : D.Fn) (hg : s.rufZiel = some g) : C g := by
  cases h with
  | blatt _ hb => cases hb <;> simp [Stmt.rufZiel] at hg
  | call s g' hg' hC =>
    rw [hg'] at hg
    cases hg
    exact hC
  | _ => simp [Stmt.rufZiel] at hg

theorem StmtR.call_inv {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D V (D.signatur g) Λ} {hr : D.gruende g = 0}
    (h : StmtR A C mr (.call (l := l) g args hp hr)) : C g :=
  h.call_inv' g rfl

theorem BlockR.bindCall_inv {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ}
    {hp : RufPasst D V (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Block D V l (τ :: Γ) (nach D g Λ) Λ'}
    (h : BlockR A C mr (.bindCall g args he hp hr rest)) : C g ∧ BlockR A C mr rest := by
  generalize hb : Block.bindCall g args he hp hr rest = b at h
  cases h with
  | bindCall g' args' he' hp' hr' rest' hC hrest =>
    cases hb
    exact ⟨hC, hrest⟩
  | _ => cases hb

end Inv



/-! ## 3. How a caller resumes, and the call steps over a thread state -/

/-- How the caller frame resumes when the callee `fn` pops: UNCHANGED (a
    plain call; `rueck`, `rueckCons`, `dannRet`), or with the returned value
    bound into its waiting residue (a bind-call; `rueckBind`,
    `rueckConsBind`, `dannRetBind`). `ziel v` is the resumed frame. -/
inductive PopArt (fn : D.Fn) (caller : RufRahmenG D) :
    (ErgVal D (D.erg fn) → RufRahmenG D) → Prop where
  | wie : PopArt fn caller (fun _ => caller)
  | bind {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
      (hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) (he : D.erg fn = some τ) :
      PopArt fn caller (fun v => ⟨caller.f, caller.rho, caller.s0,
        ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩)

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem w_rueckP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {ziel : ErgVal D (D.erg z.kopf.f) → RufRahmenG D} (hart : PopArt z.kopf.f caller ziel)
    {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.ret e hperm)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f (ziel (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ))
        rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  cases hart with
  | wie =>
    exact ⟨_, RufSchrittG.rueck M f caller rst hpop Γ Λ e hperm ρ hhead _ rfl
      (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl, gepopptG_neu rfl rfl⟩
  | bind restb k ρc hc he =>
    exact ⟨_, RufSchrittG.rueckBind M f caller rst hpop _ _ _ _ _ restb k ρc hc Γ Λ e hperm ρ
      hhead _ rfl (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl he _ rfl, gepopptG_neu rfl rfl⟩

theorem w_rueckConsP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {ziel : ErgVal D (D.erg z.kopf.f) → RufRahmenG D} (hart : PopArt z.kopf.f caller ziel)
    {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Endblock D (vertragVon D z.kopf.f) lr Γ Λ) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨lr, Γ, Λ, ρ, .ende (.cons (.ret e hperm) rest)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f (ziel (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ))
        rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  cases hart with
  | wie =>
    exact ⟨_, RufSchrittG.rueckCons M f caller rst hpop Γ Λ e hperm rest ρ hhead _ rfl
      (M.faeden f).kopf.rho rfl _ rfl hΛ _ rfl _ rfl _ rfl, gepopptG_neu rfl rfl⟩
  | bind restb k ρc hc he =>
    exact ⟨_, RufSchrittG.rueckConsBind M f _ Γ Λ e hperm rest ρ hhead caller rst hpop _ _ _ _ _
      restb k ρc hc hΛ _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl he _ rfl,
      gepopptG_neu rfl rfl⟩

theorem w_dannRetP {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (hpop : z.stapel = caller :: rst)
    {ziel : ErgVal D (D.erg z.kopf.f) → RufRahmenG D} (hart : PopArt z.kopf.f caller ziel)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (e : ErgExpr D Γ Λ (vertragVon D z.kopf.f).erg)
    (hperm : Λ.Perm (vertragVon D z.kopf.f).ende)
    (rest : Block D (vertragVon D z.kopf.f) l Γ Λ Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.ret e hperm) rest) k⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      GepopptG M' f (ziel (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ))
        rst z.kopf.f z.kopf.rho z.kopf.s0 z.log
        (evalErg ((M.weltVon f).lese Λ e.orte) e ((M.weltVon f).lese Λ e.orte) ρ)
        ((M.weltVon f).lese Λ e.orte) := by
  subst hz
  cases hart with
  | wie =>
    exact ⟨_, RufSchrittG.dannRet M f l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ
      _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl _ rfl, gepopptG_neu rfl rfl⟩
  | bind restb k' ρc hc he =>
    exact ⟨_, RufSchrittG.dannRetBind M f l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop
      _ _ _ _ _ restb k' ρc hc hΛ _ rfl _ rfl (M.faeden f).kopf.rho rfl _ rfl _ rfl he _ rfl,
      gepopptG_neu rfl rfl⟩

/-- `rufDann`: the caller advances to `dann rest k` and waits below the
    callee frame, which starts at the read world with the evaluated
    arguments. -/
theorem w_rufDann {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D (vertragVon D z.kopf.f) l Γ (nach D g Λ) Λ'')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ'') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons (.call g args hp hr) rest) k⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ ::
          z.stapel) g
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        ((M.weltVon f).lese Λ args.orte)
        (RufEreignisF.eintritt g
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          ((M.weltVon f).lese Λ args.orte) :: z.log)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ args.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.rufDann M f l Γ Λ Λ Λ'' g args hp hr rest k ρ hhead hΛ _ rfl _ rfl _ rfl,
    zustandG_neu rfl rfl⟩

/-- `ruf` (repaired): at `ende` position the caller advances to `ende rest`. -/
theorem w_rufEnde {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ (nach D g Λ)) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons (.call g args hp hr) rest)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩ ::
          z.stapel) g
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        ((M.weltVon f).lese Λ args.orte)
        (RufEreignisF.eintritt g
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          ((M.weltVon f).lese Λ args.orte) :: z.log)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ args.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.ruf M f l Γ Λ g args hp hr rest ρ hhead hΛ _ rfl _ rfl _ rfl,
    zustandG_neu rfl rfl⟩

/-- `dannBindCall`: the caller waits (`wartet rest k`) below the callee. -/
theorem w_bindCall {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (g : D.Fn) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) (nach D g Λ) Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.bindCall g args he hp hr rest) k⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
          z.stapel) g
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        ((M.weltVon f).lese Λ args.orte)
        (RufEreignisF.eintritt g
          (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
          ((M.weltVon f).lese Λ args.orte) :: z.log)
        (evalArgs ((M.weltVon f).lese Λ args.orte) args ((M.weltVon f).lese Λ args.orte) ρ)
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ args.orte) := by
  subst hz
  exact ⟨_, RufSchrittG.dannBindCall M f l Γ Λ Λ' Λ' τ g args he hp hr rest k ρ hhead hΛ
    _ rfl _ rfl _ rfl, zustandG_neu rfl rfl⟩

end Schritte

/-! ## 4. What a call must deliver: the callee's frame runs to its pop -/

/-- **The callee obligation.** For every admitted callee `g` whose handler
    run ends normally in `σ'` with value `v`, the machine, from the callee's
    fresh frame (entry world `σ1`, residue `ende (P.rumpf g)`) above any
    caller, runs by steps of `f` alone to the pop that resumes the caller as
    `PopArt` says, logging the return of `v` at world `σ'`, with shared
    memory `σ'.speicher` and the same held locks as at entry. Proved for the
    body-running handler by induction on the depth (`rufOk_tief`). -/
def RufOk (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (A : D.Lock → Prop)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (C : D.Fn → Prop) : Prop :=
  ∀ (g : D.Fn), C g → ∀ (σ1 σ' : World D) (rhoG : Env D (D.params g)) (v : ErgVal D (D.erg g)),
    R g σ1 rhoG = .ok σ' v →
    ∀ (M : RufMaschineG D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
      (log : List (RufEreignisF D)),
      ZustandG M f (caller :: rst) g rhoG σ1 log rhoG (.ende (P.rumpf g)) σ1 →
      ∀ (ziel : ErgVal D (D.erg g) → RufRahmenG D), PopArt g caller ziel →
      HeldGenau (Signatur.anfang D (D.signatur g)) (offen σ1.spur) → FreiA A M f →
      ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
        GepopptG M' f (ziel v) rst g rhoG σ1 (ext ++ log) v σ' ∧ offen σ'.spur = offen σ1.spur

/-- A covered leaf does not consult the call handler. -/
theorem BlattG.exec_R {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R s σ ρ = execStmt O passes keinRuf s σ ρ := by
  cases h <;> rfl

/-- The callee's entry holdings from the caller's: `RufPasst.hh`. -/
theorem heldGenau_eintritt {V : Vertrag D} {g : D.Fn} {Λ : List (Res D)} {σ : World D}
    (hp : RufPasst D V (D.signatur g) Λ) (hΛ : HeldGenau Λ (offen σ.spur))
    (os : List (D.Tab ⊕ D.Glob)) (Λ₀ : List (Res D)) :
    HeldGenau (Signatur.anfang D (D.signatur g)) (offen (σ.lese Λ₀ os).spur) :=
  heldGenau_ruf hp.hh (heldGenau_lese os hΛ)

/-- After the callee's pop the resumed caller frame IS a thread state of the
    caller's frame, whose log gained the call's events. -/
theorem gepoppt_zustand {M : RufMaschineG D} {f : Faden} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} {g : D.Fn} {rhoG : Env D (D.params g)} {s1 : World D}
    {log e2 : List (RufEreignisF D)} {e : RufEreignisF D} {v : ErgVal D (D.erg g)}
    {σ' : World D} (h : GepopptG M f caller rst g rhoG s1 (e2 ++ e :: log) v σ')
    {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D fn) l Γ Λ}
    (hc : caller = ⟨fn, rho, s0, ⟨l, Γ, Λ, ρ, r⟩⟩) :
    ZustandG M f rst fn rho s0
      ((RufEreignisF.rueck g rhoG v s1 σ' :: e2 ++ [e]) ++ log) ρ r σ' := by
  refine ⟨?_, h.2⟩
  rw [h.1, hc]
  simp


/-! ## 5. Normal completion: the machine reaches the continuation

    As `RufAdaequatG.lean` §7, for any handler `R` and fragment `C`, with a
    log that may GROW (calls log `eintritt`/`rueck` events); a call is
    discharged by the callee obligation `RufOk`. -/

section SimOk

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (A : D.Lock → Prop) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (C : D.Fn → Prop)

/-- Block simulation, normal completion: `dann b k` at `σ, ρ` runs (steps of
    `f` only) to `k` at the world and environment `execBlock` returns; the
    log grows by the events of the calls made on the way (`ext`). -/
def SimOkBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
    execBlock O passes R b σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f stapel fn rho s0 log ρ (.dann b k) σ → HeldGenau Λ (offen σ.spur) →
    FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur

/-- Statement simulation, normal completion: `dann (s; rest) k` runs to
    `dann rest k`. -/
def SimOkSR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
    execStmt O passes R s σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f stapel fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann rest k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- A covered leaf: one `dannBlatt` step. -/
theorem blattOkR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimOkSR P O passes f fn stapel rho s0 A R s := by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ _
  have hW := hZ.welt
  have herw := h.erw O passes R σ σ' ρ ρ' hex
  obtain ⟨M', hs, hZ'⟩ := w_dannBlatt (P := P) (O := O) (passes := passes) hZ.1 s rest k ρ
    h.istBlatt rfl hΛ σ' ρ' (by rw [hW, ← h.exec_R O passes R]; exact hex) (by rw [hW]; exact herw)
  exact ⟨M', [], RufLaufG.einzeln hs, hZ', herw.offen⟩

/-- A `schrumpf` layer after a sub-block: one `schrumpfVergiss` step. -/
theorem schrumpfOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {M : RufMaschineG D} {log : List (RufEreignisF D)} {k : GRest D (vertragVon D fn) l Γ Λ}
    {v : Wert D τ} {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log (.cons v ρ) (.schrumpf k) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧ ZustandG M' f stapel fn rho s0 log ρ k σ := by
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_schrumpf (P := P) (O := O) (passes := passes) hZ.1 k v ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩

variable (hRuf : RufOk P O passes f A R C)
include hRuf

-- `hRuf` discharges the calls in `stmtOkR`/`blockOkR`; `armsOkR`/`grundOkR`
-- need it only through their recursive `blockOkR` calls, which the linter
-- does not count as a use.
set_option linter.unusedSectionVars false in
mutual

theorem stmtOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtR A C mr s →
    SimOkSR P O passes f fn stapel rho s0 A R s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignDurch p t ht f' i e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignDurch _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignGlob g e hw hL)
  | _, _, _, _, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.schreibBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignVar x e)
  | _, _, _, _, _, .uebergang t f' hτ i von nach hn he hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.uebergang t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regSchreib r hk e, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.regSchreib r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.retires m s h a)
  | _, _, _, _, _, .ite c t e, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR t ht _ _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR e he _ _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onOption o p a, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR p hp _ _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hv
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR a ha _ _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, Λ₀, _, .onTag v arms, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hsim := armsOkR arms ha (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ) = w
        at hex hsim
      obtain ⟨c, b, nutz⟩ := w
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨w', hw'⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ _ hw' M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onGrund r arms, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes R arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := grundOkR arms ha _ _ _ _ _ _ hex M1 _ hZ1
        (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .call g args hp hr, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have hC := hs.call_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i σ2 v hR2
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M1, hs1, hZ1⟩ := w_rufDann (P := P) (O := O) (passes := passes) hZ.1
          g args hp hr rest k ρ rfl hΛ
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _ PopArt.wie
          (heldGenau_eintritt hp hΛ _ _) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hl2, gepoppt_zustand hG2 rfl,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
  | _, _, _, _, _, .callInd .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .locks L hr body, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hAL, hb⟩ := hs.locks_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨σ1, hb1, rfl⟩ := mapWelt_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_locks (P := P) (O := O) (passes := passes) hZ.1
        L hr body rest k ρ rfl hΛ (hA L hAL)
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR body hb _ _ _ _ _ hb1 M1 _ hZ1
        (heldGenau_locks L hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      have hW2 := hZ2.welt
      obtain ⟨M3, hs3, hZ3⟩ := w_freiGib (P := P) (O := O) (passes := passes) hZ2.1
        L (.dann rest k) ρ' rfl
      rw [hW2] at hZ3
      exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        offen_gibt_nimmt σ σ1 L ho2⟩
  | _, _, _, _, _, .breaking i body, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR body hb _ _ _ _ _ hex M1 _ hZ1
        hΛ (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩
  | _, _, _, _, _, .traverse .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .retry .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .forever .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .axiomCall .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .ret .., _ => by
      intro log σ σ' ρ ρ' hex
      simp [execStmt] at hex
  | _, _, _, _, _, .retGrund .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .leave .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .next .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])

theorem blockOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockR A C mr b →
    SimOkBR P O passes f fn stapel rho s0 A R b
  | _, _, _, _, _, .nil, _ => by
      intro log σ σ' ρ ρ' hex M k hZ _ _
      simp only [execBlock, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      have hW := hZ.welt
      obtain ⟨M1, hs1, hZ1⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ.1 k ρ rfl
      rw [hW] at hZ1
      exact ⟨M1, [], RufLaufG.einzeln hs1, hZ1, rfl⟩
  | _, _, _, _, _, .cons s rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      obtain ⟨σ1, ρ1, hs1, hr1⟩ := execBlock_cons_ok O passes R s rest hex
      obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := stmtOkR s hs _ _ _ _ _ hs1 M rest k hZ hΛ hA
      have hΛ1 := heldGenau_iff (s.held_iff) hΛ
      rw [← ho1] at hΛ1
      obtain ⟨M2, e2, hl2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hr1 M1 k hZ1 hΛ1 (hA.lauf hl1)
      exact ⟨M2, e2 ++ e1, hl1.trans hl2, by rw [List.append_assoc]; exact hZ2,
        by rw [ho2, ho1]⟩
  | _, _, _, _, _, .bind e rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨w, hw⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
        (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
      exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .bindCall g args he hp hr rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      obtain ⟨hC, hrest⟩ := hb.bindCall_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i σ2 v hR2
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_bindCall (P := P) (O := O) (passes := passes) hZ.1
          g args he hp hr rest k ρ rfl hΛ
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _
          (PopArt.bind rest k ρ rfl he) (heldGenau_eintritt hp hΛ _ _)
          (hA.lauf (RufLaufG.einzeln hs1))
        have hZ2 := gepoppt_zustand hG2 rfl
        have hΛ2 : HeldGenau (nach D g _) (offen σ2.spur) :=
          heldGenau_iff (fun L => held_nachSig_iff _ _ L)
            (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
        have hl12 := RufLaufG.schritt hs1 hl2
        obtain ⟨M3, e3, hl3, hZ3, ho3⟩ := blockOkR rest hrest _ _ _ _ _ hw M2 _ hZ2 hΛ2
          (hA.lauf hl12)
        obtain ⟨M4, hs4, hZ4⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ3
        exact ⟨M4, e3 ++ _, hl12.trans (hl3.trans (RufLaufG.einzeln hs4)),
          by rw [List.append_assoc]; exact hZ4,
          by rw [ho3, ho2, (Erw.lese _ _ _).offen]⟩
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .regLies r hk rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hzs
          obtain ⟨w, hw⟩ := schrumpf_ok hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl v (by rw [hW]; exact hv) hzs
          rw [hW] at hZ1
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
            hΛ (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
          exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
        · cases hex
      · cases hex
  | _, _, _, _, _, .regLiesElse r hk zusage sonst rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.regLiesElse_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hw0
          obtain ⟨w, hw⟩ := schrumpf_ok hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl v (by rw [hW]; exact hv)
            (by rw [hW]; exact hw0)
          rw [hW] at hZ1
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
            (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
          exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            by rw [ho2, (Erw.lese _ _ _).offen]⟩
        · exact absurd hex (zuAusgang_ne_ok _ _ _)
      · cases hex
  | _, _, _, _, _, .awaits g payload hp hL rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨w, hw'⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw' M1 _ hZ1
        (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
      exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, herw.offen]⟩
  | _, _, _, _, _, .narrow e lo' hi' sonst rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.narrow_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hin
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl hW hin
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)
  | _, _, _, _, _, .pruefung c sonst rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.pruefung_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)
  | _, _, _, _, _, .gleit op a b lo hi rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, _, _, .gleitLit q lo hi rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl v hv
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          hΛ (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
      · cases hex
  | _, _, _, _, _, .gleitVon e lo hi rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, _, _, .gleitNarrow e lo hi sonst rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitNarrow_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes)
          hZ.1 e lo hi sonst rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)

theorem armsOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsR A C mr arms → ∀ (v : Wert D (.sum cs)),
    SimOkBR P O passes f fn stapel rho s0 A R (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => by
      exact blockOkR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨⟨n + 1, _⟩, _⟩ => by
      exact armsOkR rest ha.cons_inv.2 _

theorem grundOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsR A C mr arms →
    ∀ (r : Fin n), SimOkBR P O passes f fn stapel rho s0 A R (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => by
      exact blockOkR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨k + 1, _⟩ => by
      exact grundOkR rest ha.cons_inv.2 _

end

end SimOk

/-! ## 8. Under a `locks` body nothing returns -/

section KeinRueck

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  (A : D.Lock → Prop) (C : D.Fn → Prop)

/-- A block never ends in `.zurueck`. -/
def KeinRueckBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg),
    execBlock O passes R b σ ρ ≠ .zurueck σ' v

mutual

theorem stmtKeinR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), StmtR A C false s →
    ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg),
      execStmt O passes R s σ ρ ≠ .zurueck σ' v
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      BlattG.nicht_zurueck O passes R (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignDurch p t ht f' i e hw hL, _ =>
      BlattG.nicht_zurueck O passes R (.assignDurch _ p t ht f' i e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      BlattG.nicht_zurueck O passes R (.assignGlob g e hw hL)
  | _, _, _, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _ =>
      BlattG.nicht_zurueck O passes R (.schreibBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      BlattG.nicht_zurueck O passes R (.assignVar x e)
  | _, _, _, _, .uebergang t f' hτ i von nach hn he hw hL, _ =>
      BlattG.nicht_zurueck O passes R (.uebergang t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regSchreib r hk e, _ =>
      BlattG.nicht_zurueck O passes R (.regSchreib r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      BlattG.nicht_zurueck O passes R (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      BlattG.nicht_zurueck O passes R (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      BlattG.nicht_zurueck O passes R (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      BlattG.nicht_zurueck O passes R (.retires m s h a)
  | _, _, _, _, .ite c t e, hs => by
      intro σ σ' ρ v hex
      obtain ⟨ht, he⟩ := hs.ite_inv
      simp only [execStmt] at hex
      split at hex
      · exact blockKeinR t ht _ _ _ _ hex
      · exact blockKeinR e he _ _ _ _ hex
  | _, _, _, _, .onOption o p a, hs => by
      intro σ σ' ρ v hex
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      simp only [execStmt] at hex
      split at hex
      · exact blockKeinR p hp _ _ _ _ (schrumpf_zurueck hex)
      · exact blockKeinR a ha _ _ _ _ hex
  | _, _, Λ₀, _, .onTag w arms, hs => by
      intro σ σ' ρ v hex
      have ha := hs.onTag_inv
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hk := armsKeinR arms ha (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ)
      generalize armWahlG arms (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ) = x at hex hk
      obtain ⟨c, b, nutz⟩ := x
      cases c with
      | none => exact hk _ _ _ _ hex
      | some lh => exact hk _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .onGrund r arms, hs => by
      intro σ σ' ρ v hex
      have ha := hs.onGrund_inv
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes R arms] at hex
      exact grundKeinR arms ha _ _ _ _ _ hex
  | _, _, _, _, .call g args hp hr, _ => by
      intro σ σ' ρ v hex
      simp only [execStmt] at hex
      split at hex
      · cases hex
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .locks L hr body, hs => by
      intro σ σ' ρ v hex
      obtain ⟨_, hb⟩ := hs.locks_inv
      simp only [execStmt] at hex
      obtain ⟨σ1, h1, _⟩ := mapWelt_zurueck hex
      exact blockKeinR body hb _ _ _ _ h1
  | _, _, _, _, .breaking i body, hs => by
      intro σ σ' ρ v hex
      have hb := hs.breaking_inv
      simp only [execStmt] at hex
      exact blockKeinR body hb _ _ _ _ hex
  | _, _, _, _, .traverse .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .retry .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .forever .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .ret .., hs => absurd hs.ret_inv (by decide)
  | _, _, _, _, .retGrund .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .leave .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .next .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])

theorem blockKeinR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), BlockR A C false b → KeinRueckBR O passes R b
  | _, _, _, _, .nil, _ => by
      intro σ σ' ρ v hex
      simp [execBlock] at hex
  | _, _, _, _, .cons s rest, hb => by
      intro σ σ' ρ v hex
      obtain ⟨hs, hr⟩ := hb.cons_inv
      rcases execBlock_cons_zurueck O passes R s rest hex with h | ⟨σ1, ρ1, _, h⟩
      · exact stmtKeinR s hs _ _ _ _ h
      · exact blockKeinR rest hr _ _ _ _ h
  | _, _, _, _, .bind e rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.bind_inv
      simp only [execBlock] at hex
      exact blockKeinR rest hr _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .bindCall g args he hp hr rest, hb => by
      intro σ σ' ρ v hex
      have hr' := hb.bindCall_inv.2
      simp only [execBlock] at hex
      split at hex
      · exact blockKeinR rest hr' _ _ _ _ (schrumpf_zurueck hex)
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .regLies r hk rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.regLies_inv
      simp only [execBlock] at hex
      split at hex
      · split at hex
        · exact blockKeinR rest hr _ _ _ _ (schrumpf_zurueck hex)
        · cases hex
      · cases hex
  | _, _, _, _, .regLiesElse .., hb => absurd hb.regLiesElse_inv.1 (by decide)
  | _, _, _, _, .awaits g payload hp hL rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.awaits_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKeinR rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .exchange g neuE hw hL rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.exchange_inv
      simp only [execBlock] at hex
      exact blockKeinR rest hr _ _ _ _ (schrumpf_zurueck hex)
  | _, _, _, _, .narrow .., hb => absurd hb.narrow_inv.1 (by decide)
  | _, _, _, _, .pruefung .., hb => absurd hb.pruefung_inv.1 (by decide)
  | _, _, _, _, .gleit op a b lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleit_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKeinR rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .gleitLit q lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleitLit_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKeinR rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .gleitVon e lo hi rest, hb => by
      intro σ σ' ρ v hex
      have hr := hb.gleitVon_inv
      simp only [execBlock] at hex
      split at hex
      · exact blockKeinR rest hr _ _ _ _ (schrumpf_zurueck hex)
      · cases hex
  | _, _, _, _, .gleitNarrow .., hb => absurd hb.gleitNarrow_inv.1 (by decide)

theorem armsKeinR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    ArmsR A C false arms → ∀ (v : Wert D (.sum cs)),
    KeinRueckBR O passes R (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockKeinR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsKeinR rest ha.cons_inv.2 _

theorem grundKeinR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsR A C false arms →
    ∀ (r : Fin n), KeinRueckBR O passes R (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockKeinR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundKeinR rest ha.cons_inv.2 _

end

end KeinRueck

/-! ## 9. Statements at `ende` position: `blatt`, or `endeEntf` into `dann` -/

section Ende

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (A : D.Lock → Prop) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (C : D.Fn → Prop)

/-- A covered statement at `ende (s; rest)` that ends normally runs to
    `ende rest`: a leaf by `blatt`, a call by the repaired `ruf` and the
    callee obligation, a compound by `endeEntf`, its `dann` simulation and
    `dannLeer`. -/
theorem endeConsOkR (hRuf : RufOk P O passes f A R C) {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {log : List (RufEreignisF D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (hs : StmtR A C mr s)
    (hok : SimOkSR P O passes f fn stapel rho s0 A R s)
    (σ σ' : World D) (ρ ρ' : Env D Γ)
    (hex : execStmt O passes R s σ ρ = .ok σ' ρ') (M : RufMaschineG D)
    (rest : Endblock D (vertragVon D fn) l Γ Λ')
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.ende (.cons s rest)) σ)
    (hΛ : HeldGenau Λ (offen σ.spur)) (hA : FreiA A M f) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.ende rest) σ' ∧
      offen σ'.spur = offen σ.spur := by
  have hW := hZ.welt
  have hEntf : ∀ (hent : GEntfaltbar s = true),
      ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
        ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.ende rest) σ' ∧
        offen σ'.spur = offen σ.spur := by
    intro hent
    obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes) hZ.1
      s rest ρ hent rfl
    rw [hW] at hZ1
    obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hok log σ σ' ρ ρ' hex M1 .nil (.ende rest) hZ1 hΛ
      (hA.lauf (RufLaufG.einzeln hs1))
    have hW2 := hZ2.welt
    obtain ⟨M3, hs3, hZ3⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ2.1
      (.ende rest) ρ' rfl
    rw [hW2] at hZ3
    exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
  cases hs with
  | blatt _ h =>
    have herw := h.erw O passes R σ σ' ρ ρ' hex
    obtain ⟨M1, hs1, hZ1⟩ := w_blatt (P := P) (O := O) (passes := passes) hZ.1 s rest ρ
      h.istBlatt rfl hΛ σ' ρ' (by rw [hW, ← h.exec_R O passes R]; exact hex)
      (by rw [hW]; exact herw)
    exact ⟨M1, [], RufLaufG.einzeln hs1, hZ1, herw.offen⟩
  | call s g' hg hC =>
    cases s with
    | call g args hp hr =>
      have hgg : g = g' := Option.some.inj hg
      subst hgg
      simp only [execStmt] at hex
      split at hex
      · rename_i σ2 v hR2
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M1, hs1, hZ1⟩ := w_rufEnde (P := P) (O := O) (passes := passes) hZ.1
          g args hp hr rest ρ rfl hΛ
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _ PopArt.wie
          (heldGenau_eintritt hp hΛ _ _) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hl2, gepoppt_zustand hG2 rfl,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
    | _ => simp [Stmt.rufZiel] at hg
  | ret _ _ => simp [execStmt] at hex
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onGrund => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl

end Ende

/-! ## 7. Return: the machine pops with the value `execBlock` returns

    As `RufAdaequatG.lean` §10, for any handler `R`, fragment `C` and pop mode
    `PopArt`; the conclusion also keeps the held locks (`offen`), which the
    callee obligation needs. -/

section SimRet

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (rho : Env D (D.params fn))
  (s0 : World D) (A : D.Lock → Prop)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (C : D.Fn → Prop)
  (ziel : ErgVal D (D.erg fn) → RufRahmenG D)

/-- Block simulation, return: `dann b k` pops the frame with the value and
    the world `execBlock` returns, resuming the caller as `ziel`. -/
def SimRetBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ : Env D Γ)
    (v : ErgVal D (vertragVon D fn).erg),
    execBlock O passes R b σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.dann b k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptG M' f (ziel v) rst fn rho s0 (ext ++ log) v σ' ∧ offen σ'.spur = offen σ.spur

/-- Statement simulation, return, at `dann (s; rest) k`. -/
def SimRetSR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ : Env D Γ)
    (v : ErgVal D (vertragVon D fn).erg),
    execStmt O passes R s σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptG M' f (ziel v) rst fn rho s0 (ext ++ log) v σ' ∧ offen σ'.spur = offen σ.spur

/-- End-block simulation, return, at `ende e`. -/
def SimRetER {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D (vertragVon D fn) l Γ Λ) : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ : Env D Γ)
    (v : ErgVal D (vertragVon D fn).erg),
    execEnd O passes R e σ ρ = .zurueck σ' v →
  ∀ (M : RufMaschineG D),
    ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende e) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptG M' f (ziel v) rst fn rho s0 (ext ++ log) v σ' ∧ offen σ'.spur = offen σ.spur

theorem blattRetR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimRetSR P O passes f fn caller rst rho s0 A R ziel s := by
  intro log σ σ' ρ v hex
  exact absurd hex (h.nicht_zurueck O passes R σ σ' ρ v)

/-- A call statement never returns (`execStmt` of a call is `ok`, `logik`
    or `hardware`). -/
theorem call_nicht_zurueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {g : D.Fn} {args : Args D Γ Λ (D.params g)} {hp : RufPasst D V (D.signatur g) Λ}
    {hr : D.gruende g = 0} (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg) :
    execStmt O passes R (.call (l := l) g args hp hr) σ ρ ≠ .zurueck σ' v := by
  intro hex
  simp only [execStmt] at hex
  split at hex
  · cases hex
  · exact (Fin.cast hr ‹_›).elim0
  · cases hex
  · cases hex

/-- A covered call statement never returns. -/
theorem stmtR_call_nicht_zurueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} {g : D.Fn} (hg : s.rufZiel = some g) (σ σ' : World D)
    (ρ : Env D Γ) (v : ErgVal D V.erg) : execStmt O passes R s σ ρ ≠ .zurueck σ' v := by
  cases s with
  | call => exact call_nicht_zurueck O passes R σ σ' ρ v
  | _ => simp [Stmt.rufZiel] at hg

/-- Lift a pop after one step. -/
theorem gepoppt_vorR {M M1 : RufMaschineG D} {log : List (RufEreignisF D)}
    {v : ErgVal D (D.erg fn)} {σ σ1 σ' : World D}
    (hs : RufSchrittG P O passes M f M1) (ho : offen σ1.spur = offen σ.spur)
    (h : ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M1 M' ∧
      GepopptG M' f (ziel v) rst fn rho s0 (ext ++ log) v σ' ∧ offen σ'.spur = offen σ1.spur) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptG M' f (ziel v) rst fn rho s0 (ext ++ log) v σ' ∧
      offen σ'.spur = offen σ.spur := by
  obtain ⟨M', ext, hr, hG, ho'⟩ := h
  exact ⟨M', ext, RufLaufG.schritt hs hr, hG, by rw [ho', ho]⟩

/-- Lift a pop after a run that logged `e1`. -/
theorem gepoppt_laufR {M M1 : RufMaschineG D} {log e1 : List (RufEreignisF D)}
    {v : ErgVal D (D.erg fn)} {σ σ1 σ' : World D}
    (hl : RufLaufG P O passes f M M1) (ho : offen σ1.spur = offen σ.spur)
    (h : ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M1 M' ∧
      GepopptG M' f (ziel v) rst fn rho s0 (ext ++ (e1 ++ log)) v σ' ∧
      offen σ'.spur = offen σ1.spur) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptG M' f (ziel v) rst fn rho s0 (ext ++ log) v σ' ∧
      offen σ'.spur = offen σ.spur := by
  obtain ⟨M', ext, hr, hG, ho'⟩ := h
  exact ⟨M', ext ++ e1, hl.trans hr, by rw [List.append_assoc]; exact hG, by rw [ho', ho]⟩

/-- A statement at `ende (s; rest)` that returns: `rueckCons` (or its bind
    form) for `ret`, `endeEntf` and the `dann` simulation for a compound. -/
theorem endeConsRetR (hart : PopArt fn caller ziel) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {log : List (RufEreignisF D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (hs : StmtR A C true s)
    (hret : SimRetSR P O passes f fn caller rst rho s0 A R ziel s)
    (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D (vertragVon D fn).erg)
    (hex : execStmt O passes R s σ ρ = .zurueck σ' v) (M : RufMaschineG D)
    (rest : Endblock D (vertragVon D fn) l Γ Λ')
    (hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende (.cons s rest)) σ)
    (hΛ : HeldGenau Λ (offen σ.spur)) (hA : FreiA A M f) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      GepopptG M' f (ziel v) rst fn rho s0 (ext ++ log) v σ' ∧
      offen σ'.spur = offen σ.spur := by
  have hW := hZ.welt
  have hEntf : ∀ (hent : GEntfaltbar s = true),
      ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
        GepopptG M' f (ziel v) rst fn rho s0 (ext ++ log) v σ' ∧
        offen σ'.spur = offen σ.spur := by
    intro hent
    obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := P) (O := O) (passes := passes) hZ.1
      s rest ρ hent rfl
    rw [hW] at hZ1
    exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 rfl
      (hret log σ σ' ρ v hex M1 .nil (.ende rest) hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  cases hs with
  | blatt _ h => exact absurd hex (h.nicht_zurueck O passes R σ σ' ρ v)
  | call _ g hg _ => exact absurd hex (stmtR_call_nicht_zurueck O passes R hg σ σ' ρ v)
  | ret e hperm =>
    simp only [execStmt, Ausgang.zurueck.injEq] at hex
    obtain ⟨rfl, rfl⟩ := hex
    obtain ⟨M1, hs1, hG⟩ := w_rueckConsP (P := P) (O := O) (passes := passes) hZ.1
      caller rst rfl hart e hperm rest ρ rfl hΛ
    rw [hW] at hG
    exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩
  | ite => exact hEntf rfl
  | onOption => exact hEntf rfl
  | onTag => exact hEntf rfl
  | onGrund => exact hEntf rfl
  | breaking => exact hEntf rfl
  | locks => exact hEntf rfl

variable (hart : PopArt fn caller ziel) (hRuf : RufOk P O passes f A R C)
include hart hRuf

-- `hart`/`hRuf` are used at returns and calls; the arm recursions reach them
-- only through `blockRetR`, which the linter does not count as a use.
set_option linter.unusedSectionVars false in
mutual

theorem stmtRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtR A C true s →
    SimRetSR P O passes f fn caller rst rho s0 A R ziel s
  | _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.assignSlot t f' i e hw hL)
  | _, _, _, _, .assignDurch p t ht f' i e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.assignDurch _ p t ht f' i e hw hL)
  | _, _, _, _, .assignGlob g e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.assignGlob g e hw hL)
  | _, _, _, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel
        (.schreibBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, .assignVar x e, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.assignVar x e)
  | _, _, _, _, .uebergang t f' hτ i von nach hn he hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel
        (.uebergang t f' hτ i von nach hn he hw hL)
  | _, _, _, _, .regSchreib r hk e, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.regSchreib r hk e)
  | _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.transition r hk m hm hl maske bits)
  | _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.publish g e payload hp hw hL)
  | _, _, _, _, .advances m a h hs, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.advances m a h hs)
  | _, _, _, _, .retires m s h a, _ =>
      blattRetR P O passes f fn caller rst rho s0 A R ziel (.retires m s h a)
  | _, _, _, _, .ite c t e, hs => by
      intro log σ σ' ρ v hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR t ht _ _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR e he _ _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .onOption o p a, hs => by
      intro log σ σ' ρ v hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR p hp _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hw
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR a ha _ _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, Λ₀, _, .onTag w arms, hs => by
      intro log σ σ' ρ v hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hsim := armsRetR arms ha (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ w.orte) w (σ.lese Λ₀ w.orte) ρ) = x
        at hex hsim
      obtain ⟨c, b, nutz⟩ := x
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          w arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (hsim _ _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          w arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (hsim _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .onGrund r arms, hs => by
      intro log σ σ' ρ v hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes R arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
        (grundRetR arms ha _ _ _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .call g args hp hr, _ => by
      intro log σ σ' ρ v hex
      exact absurd hex (call_nicht_zurueck O passes R σ σ' ρ v)
  | _, _, _, _, .callInd .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .locks L hr body, hs => by
      intro log σ σ' ρ v hex
      obtain ⟨_, hb⟩ := hs.locks_inv
      simp only [execStmt] at hex
      obtain ⟨σ1, h1, _⟩ := mapWelt_zurueck hex
      exact absurd h1 (blockKeinR O passes R A C body hb _ _ _ _)
  | _, _, _, _, .breaking i body, hs => by
      intro log σ σ' ρ v hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 rfl
        (blockRetR body hb _ _ _ _ _ hex M1 _ hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .traverse .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .retry .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .forever .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .axiomCall .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .ret e hperm, _ => by
      intro log σ σ' ρ v hex M _ rest k hZ hΛ _
      have hW := hZ.welt
      simp only [execStmt, Ausgang.zurueck.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      obtain ⟨M1, hs1, hG⟩ := w_dannRetP (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl hart e hperm rest k ρ rfl hΛ
      rw [hW] at hG
      exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩
  | _, _, _, _, .retGrund .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .leave .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, .next .., hs => absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])

theorem blockRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockR A C true b →
    SimRetBR P O passes f fn caller rst rho s0 A R ziel b
  | _, _, _, _, .nil, _ => by
      intro log σ σ' ρ v hex
      simp [execBlock] at hex
  | _, _, _, _, .cons s rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      rcases execBlock_cons_zurueck O passes R s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact stmtRetR s hs _ _ _ _ _ h M rest k hZ hΛ hA
      · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := stmtOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf
          s hs _ _ _ _ _ h1 M rest k hZ hΛ hA
        have hΛ1 := heldGenau_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel hl1 ho1
          (blockRetR rest hr _ _ _ _ _ h2 M1 k hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, _, .bind e rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
        (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .bindCall g args he hp hr rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨hC, hrest⟩ := hb.bindCall_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i σ2 w hR2
        obtain ⟨M1, hs1, hZ1⟩ := w_bindCall (P := P) (O := O) (passes := passes) hZ.1
          g args he hp hr rest k ρ rfl hΛ
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf g hC _ _ _ _ hR2 M1 _ (caller :: rst) _ hZ1 _
          (PopArt.bind rest k ρ rfl he) (heldGenau_eintritt hp hΛ _ _)
          (hA.lauf (RufLaufG.einzeln hs1))
        have hZ2 := gepoppt_zustand hG2 rfl
        have hΛ2 : HeldGenau (nach D g _) (offen σ2.spur) :=
          heldGenau_iff (fun L => held_nachSig_iff _ _ L)
            (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
        have hl12 := RufLaufG.schritt hs1 hl2
        have ho12 : offen σ2.spur = offen σ.spur := by rw [ho2, (Erw.lese _ _ _).offen]
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel hl12 ho12
          (blockRetR rest hrest _ _ _ _ _ (schrumpf_zurueck hex) M2 _ hZ2 hΛ2 (hA.lauf hl12))
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
  | _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, .regLies r hk rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        split at hex
        · rename_i hzs
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl w (by rw [hW]; exact hw) hzs
          rw [hW] at hZ1
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 rfl
            (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 hΛ
              (hA.lauf (RufLaufG.einzeln hs1)))
        · cases hex
      · cases hex
  | _, _, _, _, .regLiesElse r hk zusage sonst rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.regLiesElse_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        split at hex
        · rename_i hw0
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl w (by rw [hW]; exact hw)
            (by rw [hW]; exact hw0)
          rw [hW] at hZ1
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
            (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
              (hA.lauf (RufLaufG.einzeln hs1)))
        · rename_i hw0
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseFalsch (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl w (by rw [hW]; exact hw)
            (by rw [hW]; simpa using hw0)
          rw [hW] at hZ1
          exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
            (endRetR sonst hs _ _ _ _ _ (zuAusgang_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
              (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .awaits g payload hp hL rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 herw.offen
        (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1
          (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .narrow e lo' hi' sonst rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hin
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl hW hin
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hin
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowElse (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl (by rw [hW]; exact hin)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (endRetR sonst hs _ _ _ _ _ (zuAusgang_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .pruefung c sonst rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ _ hex M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefFalsch (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (endRetR sonst hs _ _ _ _ _ (zuAusgang_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
  | _, _, _, _, .gleit op a b lo hi rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .gleitLit q lo hi rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl w hw
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 rfl
          (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 hΛ
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .gleitVon e lo hi rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · cases hex
  | _, _, _, _, .gleitNarrow e lo hi sonst rest, hb => by
      intro log σ σ' ρ v hex M k hZ hΛ hA
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i w hw
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes) hZ.1
          e lo hi sonst rest k ρ rfl w (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (blockRetR rest hr _ _ _ _ _ (schrumpf_zurueck hex) M1 _ hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))
      · rename_i hn
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowElse (P := P) (O := O) (passes := passes) hZ.1
          e lo hi sonst rest k ρ rfl (by rw [hW]; exact hn)
        rw [hW] at hZ1
        exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
          (endRetR sonst hs _ _ _ _ _ (zuAusgang_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
            (hA.lauf (RufLaufG.einzeln hs1)))

theorem endRetR : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D (vertragVon D fn) l Γ Λ), EndR A C e →
    SimRetER P O passes f fn caller rst rho s0 A R ziel e
  | _, _, _, .ret e hperm, he => by
      intro log σ σ' ρ v hex M hZ hΛ _
      have hW := hZ.welt
      simp only [execEnd, EndAusgang.zurueck.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      obtain ⟨M1, hs1, hG⟩ := w_rueckP (P := P) (O := O) (passes := passes) hZ.1
        caller rst rfl hart e hperm ρ rfl hΛ
      rw [hW] at hG
      exact ⟨M1, [], RufLaufG.einzeln hs1, hG, (Erw.lese _ _ _).offen⟩
  | _, _, _, .retGrund .., he => by cases he
  | _, _, _, .leave .., he => by cases he
  | _, _, _, .next .., he => by cases he
  | _, _, _, .cons s rest, he => by
      intro log σ σ' ρ v hex M hZ hΛ hA
      obtain ⟨hs, hr, _⟩ := he.cons_inv
      rcases execEnd_cons_zurueck O passes R s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact endeConsRetR P O passes f fn caller rst rho s0 A R C ziel hart hs (stmtRetR s hs)
          σ σ' ρ v h M rest hZ hΛ hA
      · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := endeConsOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf
          hs (stmtOkR P O passes f fn (caller :: rst) rho s0 A R C hRuf s hs) σ σ1 ρ ρ1 h1 M rest
          hZ hΛ hA
        have hΛ1 := heldGenau_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        exact gepoppt_laufR P O passes f fn rst rho s0 ziel hl1 ho1
          (endRetR rest hr _ _ _ _ _ h2 M1 hZ1 hΛ1 (hA.lauf hl1))
  | _, _, _, .bind e rest, he => by
      intro log σ σ' ρ v hex M hZ hΛ hA
      have hr := he.bind_inv
      have hW := hZ.welt
      simp only [execEnd] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_endeBind (P := P) (O := O) (passes := passes) hZ.1
        e rest ρ rfl
      rw [hW] at hZ1
      exact gepoppt_vorR P O passes f fn rst rho s0 ziel hs1 (Erw.lese _ _ _).offen
        (endRetR rest hr _ _ _ _ _ (endSchrumpf_zurueck hex) M1 hZ1 (heldGenau_lese _ hΛ)
          (hA.lauf (RufLaufG.einzeln hs1)))

theorem armsRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsR A C true arms → ∀ (v : Wert D (.sum cs)),
    SimRetBR P O passes f fn caller rst rho s0 A R ziel (armWahlG arms v).2.1
  | _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => blockRetR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨⟨_ + 1, _⟩, _⟩ => armsRetR rest ha.cons_inv.2 _

theorem grundRetR : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsR A C true arms →
    ∀ (r : Fin n), SimRetBR P O passes f fn caller rst rho s0 A R ziel (grundWahlG arms r)
  | _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => blockRetR b ha.cons_inv.1
  | _, _, _, _, _, .cons _ rest, ha, ⟨_ + 1, _⟩ => grundRetR rest ha.cons_inv.2 _

end

end SimRet


/-! ## 8. The depth induction and TARGET 4 -/

/-- The fragment by nesting depth: at depth `n + 1` a callee `g` is admitted
    if its body is covered with callees admitted at depth `n`; at depth `0`
    no callee is admitted (the handler of depth `0` never returns). A fact
    about the concrete program's bodies, decidable for a finite program. -/
def Tief (P : Programm D) (A : D.Lock → Prop) : Nat → D.Fn → Prop
  | 0, _ => False
  | n + 1, g => EndR A (Tief P A n) (P.rumpf g)

/-- **The callee obligation holds for the body-running handler**, at every
    depth: the handler of depth `n + 1` runs a covered callee body with
    handler depth `n`, and `endRetR` (with the obligation of depth `n`, by
    induction) realises that run on the machine, popping into whatever
    caller frame `PopArt` names. -/
theorem rufOk_tief (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden)
    (A : D.Lock → Prop) : ∀ n, RufOk P O passes f A (rufRumpf P O passes n) (Tief P A n)
  | 0 => by
      intro g hC
      exact (hC : False).elim
  | n + 1 => by
      intro g hC σ1 σ' rhoG v hR M caller rst log hZ ziel hart hΛ hA
      exact endRetR P O passes f g caller rst rhoG σ1 A (rufRumpf P O passes n) (Tief P A n)
        ziel hart (rufOk_tief P O passes f A n) (P.rumpf g) hC log σ1 σ' rhoG v
        (rufRumpf_ok hR) M hZ hΛ hA

/-- **TARGET 4 -- adequacy of the call machine G for bodies WITH calls.**
    Thread `f` of `M` runs a frame of `fn` above a caller frame, with residue
    `.ende b` for an end block `b` in the fragment extended by calls
    (`call` in block and `ende` position, `let x = g(…)`), whose callees are
    admitted at nesting depth `n` (`Tief P A n`: their bodies are in the
    fragment with callees at depth `n - 1`, and so on); its holdings `Λ` name
    exactly the locks its trace holds; no other thread holds a lock the run
    may take (`A`). If the sequential semantics, run with the handler
    `rufRumpf P O passes n` that executes each callee's BODY, started at the
    thread's current world, returns `v` in world `σ'`, then steps of thread
    `f` alone reach a machine `M'` that has popped the frame -- after
    running every call on the machine (push, callee steps, pop) and
    continuing each caller PAST its call -- and logged `rueck fn rho v s0 σ'`
    with THE SAME value `v`, on top of the old log extended by the calls'
    events; its shared memory is `σ'.speicher`, and other threads are
    untouched. -/
theorem rufG_adaequat_ruf (P : Programm D) (O : Orakel D) (passes : Nat) (n : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (spur : List (Ereignis D)) (log : List (RufEreignisF D)) {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (b : Endblock D (vertragVon D fn) false Γ Λ)
    (A : D.Lock → Prop) (hb : EndR A (Tief P A n) b)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (hΛ : HeldGenau Λ (offen spur))
    (hfrei : ∀ L, A L → RufFreiG M f L)
    (σ' : World D) (v : ErgVal D (vertragVon D fn).erg)
    (hexec : execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ = .zurueck σ' v) :
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      M'.faeden f = ⟨rst, caller, σ'.spur, RufEreignisF.rueck fn rho v s0 σ' :: (ext ++ log)⟩ ∧
      M'.speicher = σ'.speicher ∧
      (∀ g, g ≠ f → M'.faeden g = M.faeden g) := by
  have hsp : (M.weltVon f).spur = spur := by
    show (M.faeden f).spur = spur
    rw [hM]
  have hZ : ZustandG M f (caller :: rst) fn rho s0 log ρ (.ende b) (M.weltVon f) :=
    ⟨by rw [hsp]; exact hM, rfl⟩
  obtain ⟨M', ext, hl, hG, _⟩ := endRetR P O passes f fn caller rst rho s0 A
    (rufRumpf P O passes n) (Tief P A n) (fun _ => caller) PopArt.wie (rufOk_tief P O passes f A n)
    b hb log (M.weltVon f) σ' ρ v hexec M hZ (by rw [hsp]; exact hΛ) hfrei
  exact ⟨M', ext, hl, hG.1, hG.2, rufLaufG_fremd hl⟩

/-! ### The old fragment embeds: a call-free body is covered at every depth -/

mutual

theorem stmtG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'},
    StmtG A mr s → StmtR A C mr s
  | _, _, _, _, _, _, .blatt s h => .blatt s h
  | _, _, _, _, _, _, .ite c t e ht he => .ite c t e (blockG_R ht) (blockG_R he)
  | _, _, _, _, _, _, .onOption o p a hp ha => .onOption o p a (blockG_R hp) (blockG_R ha)
  | _, _, _, _, _, _, .onTag v arms ha => .onTag v arms (armsG_R ha)
  | _, _, _, _, _, _, .onGrund r arms ha => .onGrund r arms (grundG_R ha)
  | _, _, _, _, _, _, .breaking i body hb => .breaking i body (blockG_R hb)
  | _, _, _, _, _, _, .locks L hr body hA hb => .locks L hr body hA (blockG_R hb)
  | _, _, _, _, _, _, .ret e hΛ => .ret e hΛ

theorem blockG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'},
    BlockG A mr b → BlockR A C mr b
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons s rest hs hr => .cons s rest (stmtG_R hs) (blockG_R hr)
  | _, _, _, _, _, _, .bind e rest hr => .bind e rest (blockG_R hr)
  | _, _, _, _, _, _, .regLies r hk rest hr => .regLies r hk rest (blockG_R hr)
  | _, _, _, _, _, _, .regLiesElse r hk z sonst rest hs hr =>
      .regLiesElse r hk z sonst rest (endG_R hs) (blockG_R hr)
  | _, _, _, _, _, _, .awaits g payload hp hL rest hr => .awaits g payload hp hL rest (blockG_R hr)
  | _, _, _, _, _, _, .exchange g neu hw hL rest hr => .exchange g neu hw hL rest (blockG_R hr)
  | _, _, _, _, _, _, .narrow e lo hi sonst rest hs hr =>
      .narrow e lo hi sonst rest (endG_R hs) (blockG_R hr)
  | _, _, _, _, _, _, .pruefung c sonst rest hs hr =>
      .pruefung c sonst rest (endG_R hs) (blockG_R hr)
  | _, _, _, _, _, _, .gleit op a b lo hi rest hr => .gleit op a b lo hi rest (blockG_R hr)
  | _, _, _, _, _, _, .gleitLit q lo hi rest hr => .gleitLit q lo hi rest (blockG_R hr)
  | _, _, _, _, _, _, .gleitVon e lo hi rest hr => .gleitVon e lo hi rest (blockG_R hr)
  | _, _, _, _, _, _, .gleitNarrow e lo hi sonst rest hs hr =>
      .gleitNarrow e lo hi sonst rest (endG_R hs) (blockG_R hr)

theorem endG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ},
    EndG A e → EndR A C e
  | _, _, _, _, .ret e hΛ => .ret e hΛ
  | _, _, _, _, .cons s rest hs hr => .cons s rest (stmtG_R hs) (endG_R hr)
  | _, _, _, _, .bind e rest hr => .bind e rest (endG_R hr)

theorem armsG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {arms : Arms D V l Γ Λ Λ' cs}, ArmsG A mr arms → ArmsR A C mr arms
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons b rest hb hr => .cons b rest (blockG_R hb) (armsG_R hr)

theorem grundG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} :
    ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    {arms : GrundArms D V l Γ Λ Λ' n}, GrundArmsG A mr arms → GrundArmsR A C mr arms
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons b rest hb hr => .cons b rest (blockG_R hb) (grundG_R hr)

end

/-- A call-free covered body is covered by the extended fragment at every
    depth; `rufG_adaequat_ruf` therefore contains `rufG_adaequat` for the
    body-running handler. -/
theorem endG_tief (P : Programm D) (A : D.Lock → Prop) (n : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ} (h : EndG A e) :
    EndR A (Tief P A n) e :=
  endG_R h



/-! ## 9. Witness: a caller that continues after the call

    `t4D` has one table `konto` (2 slots, one `.int 0 100` field, unguarded
    and unshared), no locks, and three functions over `Fin 3` with one
    signature (no parameters, returns `.int 0 100`, may write `konto`):

        fn 0 (the callee):   konto[0] := 5; return 3
        fn 1 (plain call):   g(); konto[1] := 7; return 9
        fn 2 (bind-call):    if true { let x = g(); konto[1] := x } else { }; return 9

    `fn 1` is exactly the shape the old `ruf` got wrong: the call stands at
    `ende` position and the caller has an observable statement AFTER it. -/

def t4Sig : Signatur Unit Empty Empty Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def t4D : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Fin 3
  sig := fun _ => 0
  sigNr := fun _ => t4Sig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => absurd h (by decide)
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The callee, the plain caller, the bind caller. -/
def t4G : t4D.Fn := show Fin 3 from 0
def t4F : t4D.Fn := show Fin 3 from 1
def t4B : t4D.Fn := show Fin 3 from 2

theorem t4Darf : darf t4D () [] := fun _ h => absurd h List.not_mem_nil

def t4Idx0 : Expr t4D [] [] (.index (t4D.count ())) := .weiter (by decide) (by decide) (.lit 0)
def t4Idx1 : Expr t4D [] [] (.index (t4D.count ())) := .weiter (by decide) (by decide) (.lit 1)
def t4Idx1x : Expr t4D [.int 0 100] [] (.index (t4D.count ())) :=
  .weiter (by decide) (by decide) (.lit 1)
def t4Lit (k : Int) (h0 : 0 ≤ k) (h1 : k ≤ 100) : Expr t4D [] [] (t4D.typ () ()) :=
  .weiter h0 h1 (.lit k)

/-- The callee body: `konto[0] := 5; return 3`. -/
def t4GRumpf : Endblock t4D (vertragVon t4D t4G) false [] [] :=
  .cons (.assignSlot () () t4Idx0 (t4Lit 5 (by decide) (by decide)) rfl t4Darf)
    (.ret (.wert (t4Lit 3 (by decide) (by decide))) List.Perm.nil)

/-- Every caller passes the callee's contract: it may write what the callee
    writes, and there are no locks or marks. -/
theorem t4Hp (fn : t4D.Fn) : RufPasst t4D (vertragVon t4D fn) (t4D.signatur t4G) [] where
  hw := fun _ _ => rfl
  hg := fun g _ => nomatch g
  hk := ⟨[], List.Perm.nil, List.Sublist.slnil⟩
  hh := fun L => nomatch L

/-- The plain caller: `g(); konto[1] := 7; return 9`. -/
def t4FRumpf : Endblock t4D (vertragVon t4D t4F) false [] [] :=
  .cons (.call t4G .nil (t4Hp t4F) rfl)
    (.cons (.assignSlot () () t4Idx1 (t4Lit 7 (by decide) (by decide)) rfl t4Darf)
      (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil))

/-- The bind block: `let x = g(); konto[1] := x`. -/
def t4BindBlock : Block t4D (vertragVon t4D t4B) false [] [] [] :=
  .bindCall t4G .nil rfl (t4Hp t4B) rfl
    (.cons (.assignSlot () () t4Idx1x (.var .hier) rfl t4Darf) .nil)

/-- The bind caller: `if true { let x = g(); konto[1] := x } else { }; return 9`. -/
def t4BRumpf : Endblock t4D (vertragVon t4D t4B) false [] [] :=
  .cons (.ite .wahr t4BindBlock .nil)
    (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil)

def t4P : Programm t4D where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf := fun (f : Fin 3) => match f with
    | 0 => t4GRumpf
    | 1 => t4FRumpf
    | 2 => t4BRumpf

def t4O : Orakel t4D where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- Start memory: every slot reads `0`. -/
def t4Sp : Speicher t4D :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- The frame below the caller (any frame will do: it is only resumed). -/
def t4Unten : RufRahmenG t4D :=
  ⟨t4F, Env.nil, t4Sp.welt [], ⟨false, [], [], Env.nil,
    .ende (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil)⟩⟩

/-- A machine whose threads all run the frame of `fn` with body `b` above
    `t4Unten`, with empty trace and log. -/
def t4M (fn : t4D.Fn) (b : Endblock t4D (vertragVon t4D fn) false [] []) : RufMaschineG t4D :=
  ⟨t4Sp, fun _ => ⟨[t4Unten], ⟨fn, Env.nil, t4Sp.welt [], ⟨false, [], [], Env.nil, .ende b⟩⟩,
    [], []⟩, [], t4Sp.welt []⟩

/-- The callee body is covered with no further calls: depth 1 admits it. -/
theorem t4G_tief (A : t4D.Lock → Prop) : Tief t4P A 1 t4G :=
  show EndR A (Tief t4P A 0) t4GRumpf from EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)

theorem t4FRumpf_R (A : t4D.Lock → Prop) : EndR A (Tief t4P A 1) t4FRumpf :=
  EndR.cons _ _ (StmtR.call _ t4G rfl (t4G_tief A))
    (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _))

theorem t4BRumpf_R (A : t4D.Lock → Prop) : EndR A (Tief t4P A 1) t4BRumpf :=
  EndR.cons _ _
    (StmtR.ite _ _ _
      (BlockR.bindCall _ _ _ _ _ _ (t4G_tief A)
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
      BlockR.nil)
    (EndR.ret _ _)

theorem t4_frei (fn : t4D.Fn) (b : Endblock t4D (vertragVon t4D fn) false [] []) :
    ∀ L : t4D.Lock, (fun _ => False) L → RufFreiG (t4M fn b) 0 L := fun L => nomatch L

theorem t4_held : HeldGenau ([] : List (Res t4D)) (offen ([] : List (Ereignis t4D))) :=
  fun L => nomatch L

/-- The sequential run of the plain caller with the body-running handler:
    the callee writes slot 0, the caller then writes slot 1 and returns 9. -/
theorem t4F_exec : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
    execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 7 ∧ (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- The sequential run of the bind caller: the callee writes slot 0 and
    returns 3, the caller binds it and writes it to slot 1, then returns 9. -/
theorem t4B_exec : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
    execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
      .zurueck σ' v ∧
    (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 3 ∧ (show Zahl 0 100 from v).n = 9 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- **Witness for `rufG_adaequat_ruf`** (plain call at `ende` position).
    Every premise is instantiated jointly on the non-degenerate program
    above at depth `1`: the caller's body calls a callee that WRITES the
    table, and after the call the caller writes a second slot and returns
    a value. The sequential semantics with the body-running handler ends
    with slot 0 moved `0 -> 5` (the callee), slot 1 moved `0 -> 7` (the
    caller, AFTER the call) and value `9`; the machine, by steps of thread 0
    alone, pops the caller's frame logging that same `9` and that same
    world, and its memory holds both moved slots. The old `ruf` rule could
    never reach the write to slot 1. -/
theorem rufG_adaequat_ruf_zeuge :
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      (((t4M t4F t4FRumpf).weltVon 0).slots () 0 ()).n = 0 ∧
      (((t4M t4F t4FRumpf).weltVon 0).slots () 1 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 7 ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4P t4O 0 0 (t4M t4F t4FRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4F Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        M'.speicher = σ'.speicher ∧ (M'.speicher.slots () 0 ()).n = 5 ∧
        (M'.speicher.slots () 1 ()).n = 7 ∧
        (∀ g, g ≠ 0 → M'.faeden g = (t4M t4F t4FRumpf).faeden g) := by
  obtain ⟨σ', v, hex, h5, h7, h9⟩ := t4F_exec
  obtain ⟨M', ext, hl, hf, hsp, hfr⟩ := rufG_adaequat_ruf t4P t4O 0 1 (t4M t4F t4FRumpf) 0 t4F
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4FRumpf (fun _ => False)
    (t4FRumpf_R _) rfl t4_held (t4_frei t4F t4FRumpf) σ' v hex
  refine ⟨σ', v, hex, rfl, rfl, h5, h7, h9, M', ext, hl, hf, hsp, ?_, ?_, hfr⟩
  · rw [hsp]; exact h5
  · rw [hsp]; exact h7

/-- **Witness for `rufG_adaequat_ruf`** (bind-call in block position, under
    an `if`): the callee writes slot 0 and returns `3`; the caller binds
    `x = 3` and writes it to slot 1. The machine pops the caller's frame
    with the same value `9` and a memory holding `5` and `3` -- the bound
    value travelled through the machine's `rueckBind`. -/
theorem rufG_adaequat_ruf_zeuge_bind :
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      (σ'.slots () 0 ()).n = 5 ∧ (σ'.slots () 1 ()).n = 3 ∧ (show Zahl 0 100 from v).n = 9 ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4P t4O 0 0 (t4M t4B t4BRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4B Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ ∧
        (M'.speicher.slots () 0 ()).n = 5 ∧ (M'.speicher.slots () 1 ()).n = 3 := by
  obtain ⟨σ', v, hex, h5, h3, h9⟩ := t4B_exec
  obtain ⟨M', ext, hl, hf, hsp, _⟩ := rufG_adaequat_ruf t4P t4O 0 1 (t4M t4B t4BRumpf) 0 t4B
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4BRumpf (fun _ => False)
    (t4BRumpf_R _) rfl t4_held (t4_frei t4B t4BRumpf) σ' v hex
  refine ⟨σ', v, hex, h5, h3, h9, M', ext, hl, hf, ?_, ?_⟩
  · rw [hsp]; exact h5
  · rw [hsp]; exact h3



/-! ## 10. FINDING: a verbatim pop into a waiting bind-caller deadlocks

    `rueck`, `rueckCons` and `dannRet` pop the callee frame and restore the
    caller frame VERBATIM. When the caller waits for a bound value (residue
    `wartet rest k`, pushed by `dannBindCall`/`dannBindCallInd`/
    `dannBindCallElse`), the restored head is `wartet …`, for which NO rule
    exists: the thread is stuck for good (`wartet_steht`), while the
    sequential semantics binds the value and continues. The binding pops
    (`rueckBind`, and the new `rueckConsBind`/`dannRetBind`) exist beside
    the verbatim ones, so the machine HAS the right run (that is what
    `rufG_adaequat_ruf_zeuge_bind` uses) -- but it also has this wrong one.
    Excluding it would need a premise "the caller does not wait" on the three
    verbatim pops, which changes the statement of `rufG_adaequat`
    (`RufAdaequatG.lean`, any caller frame) -- so it is reported, not
    repaired. Machine-checked on the bind witness: -/

/-- At a head `wartet rest k` every step of `f` is a bare lock step. -/
theorem wartet_steht {P : Programm D} {O : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (rest : Block D (vertragVon D z.kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D z.kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, .wartet rest k⟩) :
    ∃ sp, M'.faeden f = ⟨z.stapel, z.kopf, sp, z.log⟩ := by
  subst hz
  cases hs with
  | blatt _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | nimmt => exact ⟨_, rufUpdateG_self _ _ _⟩
  | gibt => exact ⟨_, rufUpdateG_self _ _ _⟩
  | ruf _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueck _ _ hpop _ _ _ _ _ hhead => kopfweg
  | endeEntf _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBlatt _ _ _ _ _ _ _ _ _ hleaf hhead _ _ _ _ hstep => kopfweg
  | dannLeer _ _ _ _ _ hhead => kopfweg
  | dannIteWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannIteFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannOnOptionSome _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnOptionNone _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannOnTagSome _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ _ _ hw => kopfweg
  | dannOnTagNone _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ _ hw => kopfweg
  | dannOnGrund _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ _ hw => kopfweg
  | endeBind _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBind _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannPruefWahr _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannPruefFalsch _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannBreaking _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLocks _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | freiGib _ _ _ _ _ _ hhead => kopfweg
  | schrumpfVergiss _ _ _ _ _ _ _ hhead => kopfweg
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travNext _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | travDone _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederUeber _ _ _ _ _ _ _ _ hhead => kopfweg
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead _ hs₁ hw => kopfweg
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufDann _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | rueckBind _ _ hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep _ _ _ hs₁ hw => kopfweg
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hstep => kopfweg
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelDannNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => kopfweg
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRet _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckCons _ _ hpop _ _ _ _ _ _ hhead => kopfweg
  | dannRetBind _ _ _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | rueckConsBind _ _ _ _ _ _ _ hhead _ _ hpop => kopfweg
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead _ _ _ hs₁ hw => kopfweg
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ hhead _ _ hs₁ => kopfweg
  | dannExchange _ _ _ _ _ _ hw _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitLit _ _ _ _ _ _ _ _ _ _ hhead => kopfweg
  | dannGleitVon _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowOk _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannGleitNarrowElse _ _ _ _ _ _ _ _ _ _ _ _ _ hhead _ hs₁ => kopfweg
  | dannBindAxiom _ _ _ _ _ _ _ _ hw _ _ _ _ _ _ hhead _ hs₁ => kopfweg

/-- A thread whose head waits stays so, and logs nothing, along any run. -/
theorem wartet_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M')
    (stapel : List (RufRahmenG D)) (kopf : RufRahmenG D) (log : List (RufEreignisF D))
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (rest : Block D (vertragVon D kopf.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hR : kopf.rest = ⟨l, Γ, Λ, ρ, .wartet rest k⟩) :
    ∀ sp0, M.faeden f = ⟨stapel, kopf, sp0, log⟩ →
      ∃ sp, M'.faeden f = ⟨stapel, kopf, sp, log⟩ := by
  induction hl with
  | refl => intro sp0 h; exact ⟨sp0, h⟩
  | schritt hs _ ih =>
    intro sp0 h
    obtain ⟨sp, e⟩ := wartet_steht hs _ h rest k ρ hR
    exact ih sp e

/-- The function an event belongs to. -/
def RufEreignisF.fnVon : RufEreignisF D → D.Fn
  | .eintritt f .. => f
  | .rueck f .. => f

/-- The bind witness: the frame of `t4B` after `endeEntf`, `dannIteWahr`,
    `dannBindCall`, the callee's writing leaf, and a VERBATIM `rueck`. -/
theorem befund_wartet :
    (∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 9) ∧
    ∃ M5 : RufMaschineG t4D, RufLaufG t4P t4O 0 0 (t4M t4B t4BRumpf) M5 ∧
      ∀ M' : RufMaschineG t4D, RufLaufG t4P t4O 0 0 M5 M' →
        (M'.faeden 0).log = (M5.faeden 0).log ∧ (M'.faeden 0).kopf = (M5.faeden 0).kopf ∧
        ∀ (w : ErgVal t4D (t4D.erg t4B)) (s1 : World t4D),
          RufEreignisF.rueck t4B Env.nil w (t4Sp.welt []) s1 ∉ (M'.faeden 0).log := by
  refine ⟨⟨_, _, rfl, rfl⟩, ?_⟩
  have hZ0 : ZustandG (t4M t4B t4BRumpf) 0 [t4Unten] t4B Env.nil (t4Sp.welt []) []
      (Env.nil : Env t4D []) (.ende t4BRumpf) ((t4M t4B t4BRumpf).weltVon 0) := ⟨rfl, rfl⟩
  obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := t4P) (O := t4O) (passes := 0) hZ0.1
    (.ite .wahr t4BindBlock .nil) (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil)
    Env.nil rfl rfl
  obtain ⟨M2, hs2, hZ2⟩ := w_iteWahr (P := t4P) (O := t4O) (passes := 0) hZ1.1
    .wahr t4BindBlock .nil .nil
    (.ende (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil)) Env.nil rfl rfl
  obtain ⟨M3, hs3, hZ3⟩ := w_bindCall (P := t4P) (O := t4O) (passes := 0) hZ2.1
    t4G .nil rfl (t4Hp t4B) rfl (.cons (.assignSlot () () t4Idx1x (.var .hier) rfl t4Darf) .nil)
    (.dann .nil (.ende (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil))) Env.nil
    rfl (fun L => nomatch L)
  have hleaf : ∃ σ4, execStmt t4O 0 keinRuf
      (Stmt.assignSlot (V := vertragVon t4D t4G) (l := false) () () t4Idx0
        (t4Lit 5 (by decide) (by decide)) rfl t4Darf) (M3.weltVon 0) Env.nil = .ok σ4 Env.nil :=
    ⟨_, rfl⟩
  obtain ⟨σ4, h4⟩ := hleaf
  obtain ⟨M4, hs4, hZ4⟩ := w_blatt (P := t4P) (O := t4O) (passes := 0) hZ3.1
    (Stmt.assignSlot () () t4Idx0 (t4Lit 5 (by decide) (by decide)) rfl t4Darf)
    (.ret (.wert (t4Lit 3 (by decide) (by decide))) List.Perm.nil) Env.nil rfl rfl
    (fun L => nomatch L) σ4 Env.nil h4
    (by
      have e := BlattG.erw t4O 0 keinRuf (BlattG.assignSlot (l := false) (V := vertragVon t4D t4G)
        () () t4Idx0 (t4Lit 5 (by decide) (by decide)) rfl t4Darf) _ _ _ _ h4
      exact e)
  obtain ⟨M5, hs5, hG⟩ := w_rueck (P := t4P) (O := t4O) (passes := 0) hZ4.1 _ [t4Unten] rfl
    (.wert (t4Lit 3 (by decide) (by decide))) List.Perm.nil Env.nil rfl (fun L => nomatch L)
  refine ⟨M5, RufLaufG.schritt hs1 (RufLaufG.schritt hs2 (RufLaufG.schritt hs3
    (RufLaufG.schritt hs4 (RufLaufG.einzeln hs5)))), ?_⟩
  intro M' hl
  obtain ⟨sp, e⟩ := wartet_lauf hl (M5.faeden 0).stapel (M5.faeden 0).kopf (M5.faeden 0).log
    (.cons (.assignSlot () () t4Idx1x (.var .hier) rfl t4Darf) .nil)
    (.dann .nil (.ende (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil))) Env.nil
    (by rw [hG.1]; rfl) (M5.faeden 0).spur rfl
  refine ⟨by rw [e], by rw [e], ?_⟩
  intro w s1 hm
  rw [e, hG.1] at hm
  have hf := List.mem_map_of_mem (f := RufEreignisF.fnVon) hm
  simp only [RufEreignisF.fnVon, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, or_self] at hf
  exact absurd (congrArg Fin.val hf) (by decide)

/-! ## 11. NOTE: the machine realises `rufRumpf`, not `rufAt`

    The program semantics `exec` calls through `rufAt`, which checks the
    callee's `requires` (and `ensures`, and the owed invariants) and READS
    their places. The machine checks no contract (booked in
    `RufMaschineG.lean`'s CUTS). So G agrees with `exec` only where every
    contract holds and reads nothing -- a design cut of G, not a defect of
    its steps, shown here on the plain witness with `requires false`. -/

/-- The plain witness program with every `requires` false. -/
def t4Pk : Programm t4D :=
  { t4P with requires := fun _ => .falsch }

theorem befund_vertrag :
    execEnd t4O 0 (rufAt t4Pk t4O 0 2) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
      .logik (.vorbedingung t4G) ∧
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4Pk t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4Pk t4O 0 0 (t4M t4F t4FRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4F Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ := by
  refine ⟨rfl, ?_⟩
  have hex : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4Pk t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v := ⟨_, _, rfl⟩
  obtain ⟨σ', v, hex⟩ := hex
  have hG : Tief t4Pk (fun _ => False) 1 t4G :=
    show EndR (fun _ => False) (Tief t4Pk (fun _ => False) 0) t4GRumpf from
      EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)
  have hb : EndR (fun _ => False) (Tief t4Pk (fun _ => False) 1) t4FRumpf :=
    EndR.cons _ _ (StmtR.call _ t4G rfl hG)
      (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _))
  obtain ⟨M', ext, hl, hf, _, _⟩ := rufG_adaequat_ruf t4Pk t4O 0 1 (t4M t4F t4FRumpf) 0 t4F
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4FRumpf (fun _ => False) hb rfl t4_held
    (t4_frei t4F t4FRumpf) σ' v hex
  exact ⟨σ', v, hex, M', ext, hl, hf⟩


/-! ## CUTS:
  What is proved: TARGET 4 (`rufG_adaequat_ruf`) -- for a body in the
  fragment `EndR`/`StmtR`/`BlockR` (the covered fragment of
  `RufAdaequatG.lean` plus direct `call` in block and `ende` position and
  `let x = g(…)` in block position), whose callees are admitted at nesting
  depth `n` (`Tief`), the machine realises `execEnd` with the body-running
  handler `rufRumpf n`, by induction on `n` (`rufOk_tief`); the call-free
  fragment embeds at every depth (`endG_tief`). Joint witnesses on a
  non-degenerate program (`rufG_adaequat_ruf_zeuge`: a call at `ende`
  position followed by a write and a return; `rufG_adaequat_ruf_zeuge_bind`:
  a bind-call whose value is written). A FINDING (`befund_wartet`) and a
  NOTE (`befund_vertrag`). What is NOT proved:

  - Indirect calls (`callInd`, `bindCallInd`): the callee is the pointer's
    VALUE, so the admission would be a premise over every function of the
    signature; the machine rules (`rufCallInd`, `dannCallInd`,
    `dannBindCallInd`) have the same shape as the direct ones and would go
    through the same `RufOk`, not done.
  - `bindCallElse`: its grund path has no machine rule (G's CUTS); its ok
    path is like `bindCall`, not done.
  - `retGrund` in a callee (no grund machinery in G), and every form
    `RufAdaequatG.lean`'s CUTS excludes (loops, `leave`/`next`, axioms,
    `ret` under `locks`).
  - Contracts: `rufRumpf` checks no `requires`/`ensures`/invariant and the
    machine neither; `exec` (through `rufAt`) does, and reads their places.
    So the adequacy is against `rufRumpf`, not `rufAt` (`befund_vertrag`).
  - Adequacy is existential (SOME f-only run realises the result): G also
    has the deadlocking run of `befund_wartet`, so no statement about ALL
    maximal runs holds for bind-calls.
  - The log is described only as `rueck … :: (ext ++ log)`: the calls'
    events `ext` are not characterised (they are balanced
    `eintritt`/`rueck` pairs by `rufG_treu`'s invariant).
  - Depth: `Tief P A n` admits callees by depth; recursion deeper than `n`
    is `logik (abstieg f)` sequentially and no claim is made.
-/

#print axioms Gabbro.Grammatik.rufOk_tief
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf
#print axioms Gabbro.Grammatik.endG_tief
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_zeuge
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_zeuge_bind
#print axioms Gabbro.Grammatik.befund_wartet
#print axioms Gabbro.Grammatik.befund_vertrag
#print axioms Gabbro.Grammatik.stmtOkR
#print axioms Gabbro.Grammatik.endRetR

end Gabbro.Grammatik
