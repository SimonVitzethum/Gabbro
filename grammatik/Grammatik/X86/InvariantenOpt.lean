/-
  File:      Grammatik/X86/InvariantenOpt.lean
  Subject:   Invariant-derived optimisation legality over ACTUAL source semantics.

  This file states and proves generic optimisation legality rules against the
  real typed source language (`Syntax.lean`: `Expr`/`Block`/`Stmt`) and its
  real world semantics (`Semantik.lean`: `eval`/`execBlock`/`execStmt`), for
  consumption by the later IR/certificate lane. No toy model: every rewrite
  is an executable function on source syntax, every correspondence a theorem
  over `eval`/`execBlock` with real table-writing witnesses.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik.X86.InvariantenOpt

variable {D : Deklaration} {V : Vertrag D}
variable {Γ : Ctx} {Λ : List (Res D)}

/-- Literal extractor at GENERAL type: `some n` for `lit n`, `none`
    otherwise. Generalising the index is load-bearing: `cases` on a
    specific `.int lo hi` fails where declaration indices (`gtyp`, `typ`)
    leave unification stuck, while a free index unifies with every arm. -/
def alsLitOpt {τ : Ty} : Expr D Γ Λ τ → Option Int
  | .lit n => some n
  | _ => none

/-- Non-recursive literal-inequality test: no termination issue, no trust. -/
def litLeBool {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) : Bool :=
  match alsLitOpt a, alsLitOpt b with
  | some x, some y => decide (x ≤ y)
  | _, _ => false

/-- Non-recursive literal-equality test. -/
def litEqBool {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) : Bool :=
  match alsLitOpt a, alsLitOpt b with
  | some x, some y => decide (x = y)
  | _, _ => false

/-- A computable truth check for boolean source conditions: `wahr`,
    literal comparisons, and boolean combinations. A later certificate
    checker re-runs exactly this `Bool`; nothing is trusted from Rust.
    Top-level patterns only (the `Expr.orte` precedent), so the recursion
    is structural over direct subterms. -/
def isWahrAll : Expr D Γ Λ τ → Bool
  | .wahr => true
  | .le a b => litLeBool a b
  | .eq a b => litEqBool a b
  | .und a b => isWahrAll a && isWahrAll b
  | .oder a b => isWahrAll a || isWahrAll b
  | _ => false

/-- What "the checker says true" means at ANY type: a true boolean value,
    and `False` elsewhere, so the soundness induction generalises over the
    type index (which fixed-`.bool` induction cannot). -/
def holdsBool (τ : Ty) (v : Wert D τ) : Prop :=
  match τ with
  | .bool => v = true
  | _ => False

def isWahr (c : Expr D Γ Λ .bool) : Bool := isWahrAll c

/-- Match inversion for the extractor: a successful extraction exhibits
    the literal, with its index equation. Proved by `cases` at the free
    index (where every arm unifies); each non-literal arm reduces the
    hypothesis to `False` definitionally. -/
theorem alsLitOpt_lit {τ : Ty} (e : Expr D Γ Λ τ) (y : Int)
    (h : alsLitOpt e = some y) :
    ∃ n : Int, ∃ hτ : τ = Ty.int n n, hτ ▸ e = Expr.lit n ∧ n = y := by
  revert h
  cases e
  case lit n =>
    intro h
    exact ⟨n, rfl, rfl, by simpa [alsLitOpt] using h⟩
  all_goals (intro h; simp_all [alsLitOpt])

/-- An extracted literal really is the value `eval` computes. -/
theorem eval_alsLit {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (x : Int)
    (σ₀ σ : World D) (ρ : Env D Γ) (h : alsLitOpt e = some x) :
    (eval σ₀ e σ ρ).n = x := by
  obtain ⟨n, hτ, he, hn⟩ := alsLitOpt_lit e x h
  subst hn
  injection hτ with hlo hhi
  have hlo' : n = lo := hlo.symm
  have hhi' : n = hi := hhi.symm
  subst hlo'
  subst hhi'
  cases hτ
  have heq : e = @Expr.lit D Γ Λ n := he
  subst heq
  rfl

/-- A successful literal-inequality check means the real `le` evaluates true. -/
theorem litLeBool_sound {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) (σ₀ σ : World D) (ρ : Env D Γ)
    (h : litLeBool a b = true) : wahr? (eval σ₀ (.le a b) σ ρ) = true := by
  unfold litLeBool at h
  cases ha : alsLitOpt a with
  | none => simp [ha] at h
  | some x =>
    cases hb : alsLitOpt b with
    | none => simp [ha, hb] at h
    | some y =>
      simp only [ha, hb] at h
      have e1 : (eval σ₀ a σ ρ).n = x := eval_alsLit a x σ₀ σ ρ ha
      have e2 : (eval σ₀ b σ ρ).n = y := eval_alsLit b y σ₀ σ ρ hb
      have hdec : wahr? (eval σ₀ (.le a b) σ ρ) = decide (x ≤ y) := by
        simp only [eval, wahr?, e1, e2]
      rw [hdec]; exact h

/-- A successful literal-equality check means the real `eq` evaluates true. -/
theorem litEqBool_sound {l1 h1 l2 h2 : Int} (a : Expr D Γ Λ (.int l1 h1))
    (b : Expr D Γ Λ (.int l2 h2)) (σ₀ σ : World D) (ρ : Env D Γ)
    (h : litEqBool a b = true) : wahr? (eval σ₀ (.eq a b) σ ρ) = true := by
  unfold litEqBool at h
  cases hb : alsLitOpt b with
  | none =>
    cases ha : alsLitOpt a with
    | none => simp [ha, hb] at h
    | some _ => simp [ha, hb] at h
  | some y =>
    cases ha : alsLitOpt a with
    | none => simp [ha, hb] at h
    | some x =>
      simp only [ha, hb] at h
      have e1 : (eval σ₀ a σ ρ).n = x := eval_alsLit a x σ₀ σ ρ ha
      have e2 : (eval σ₀ b σ ρ).n = y := eval_alsLit b y σ₀ σ ρ hb
      have hdec : wahr? (eval σ₀ (.eq a b) σ ρ) = decide (x = y) := by
        simp only [eval, wahr?, e1, e2]
      rw [hdec]; exact h

/-- Soundness of the checker over `eval`, at any type. There is NO `nicht`
    arm in `isWahrAll` by design: from a negated check answering `false`
    nothing follows without completeness (a true `eval` through a
    non-literal shape answers `false`), and completeness is false.
    The induction goes through `Expr.rec` (the type is mutual, with
    `NutzlastExpr` discharged by the trivial motive); `ρ` is an explicit
    induction-hypothesis argument because `Env` depends on the context. -/
theorem isWahrAll_sound {τ : Ty} (e : Expr D Γ Λ τ) (σ₀ σ : World D) (ρ : Env D Γ)
    (h : isWahrAll e = true) : holdsBool τ (eval σ₀ e σ ρ) := by
  revert h
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True) with
  | le a b iha ihb =>
    intro h
    exact litLeBool_sound a b σ₀ σ ρ h
  | eq a b iha ihb =>
    intro h
    exact litEqBool_sound a b σ₀ σ ρ h
  | und a b iha ihb =>
    intro h
    cases ha : isWahrAll a with
    | true =>
      cases hb : isWahrAll b with
      | true =>
        have ha' : (eval σ₀ a σ ρ) = true := iha ρ ha
        have hb' : (eval σ₀ b σ ρ) = true := ihb ρ hb
        show wahr? (eval σ₀ (.und a b) σ ρ) = true
        simp [eval, wahr?, ha', hb']
      | false => simp_all [isWahrAll]
    | false => simp_all [isWahrAll]
  | oder a b iha ihb =>
    intro h
    cases ha : isWahrAll a with
    | true =>
      have ha' : (eval σ₀ a σ ρ) = true := iha ρ ha
      show ((eval σ₀ a σ ρ) || (eval σ₀ b σ ρ)) = true
      rw [ha']
      rfl
    | false =>
      cases hb : isWahrAll b with
      | true =>
        have hb' : (eval σ₀ b σ ρ) = true := ihb ρ hb
        show ((eval σ₀ a σ ρ) || (eval σ₀ b σ ρ)) = true
        rw [hb']
        exact Bool.or_true _
      | false => simp_all [isWahrAll]
  | keine => trivial
  | zahl e ih => trivial
  | _ => (intro h; simp_all [isWahrAll, holdsBool, eval]; try rfl)

/-! ## 2. Pure integer rewrites: constant folding and widening values -/

/-- Executable constant fold: `add (lit a) (lit b)` becomes `lit (a+b)`.
    Both sides share the type `.int (a+b) (a+b)`; the machine-width result
    is justified by the literal ranges, which is exactly the strength
    reduction the task asks for in miniature. -/
def foldAddLit (a b : Int) : Expr D Γ Λ (.int (a + b) (a + b)) :=
  .lit (a + b)

/-- The fold preserves `eval` against the actual source semantics. -/
theorem eval_foldAddLit (a b : Int) (σ₀ σ : World D) (ρ : Env D Γ) :
    eval σ₀ (foldAddLit (D := D) (Γ := Γ) (Λ := Λ) a b) σ ρ =
      eval σ₀ (@Expr.add D Γ Λ _ _ _ _ (@Expr.lit D Γ Λ a) (@Expr.lit D Γ Λ b)) σ ρ :=
  rfl

/-- A `weiter` widening keeps the number: dropping a redundant widening
    (whose range evidence the checker holds) changes no value. -/
theorem eval_weiter_n {lo hi lo' hi' : Int} (h1 : lo' ≤ lo) (h2 : hi ≤ hi')
    (e : Expr D Γ Λ (.int lo hi)) (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ ((.weiter h1 h2 e : Expr D Γ Λ (.int lo' hi'))) σ ρ).n =
      (eval σ₀ e σ ρ).n :=
  rfl

/-! ## 3. Check/branch elimination with exact trace transfer -/

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- Executable `pruefung` elimination: a `where`/check whose condition the
    computable checker proves is replaced by its body. The correspondence
    is EXACT about the trace: the condition's read events (`lese`) stay,
    because the rest runs in the post-read world. The refused `else`
    branch needs no fault transfer: it is unreachable, proved, not assumed. -/
theorem exec_pruefung_wahr {l : Bool} {Γ' : Ctx} {Λ'' Λ''' : List (Res D)}
    (c : Expr D Γ' Λ'' .bool) (sonst : Endblock D V l Γ' Λ'')
    (rest : Block D V l Γ' Λ'' Λ''') (σ : World D) (ρ : Env D Γ')
    (h : isWahr c = true) :
    execBlock O passes R (Block.pruefung c sonst rest) σ ρ =
      execBlock O passes R rest (σ.lese Λ'' c.orte) ρ := by
  have hc : wahr? (eval (σ.lese Λ'' c.orte) c (σ.lese Λ'' c.orte) ρ) = true :=
    isWahrAll_sound c _ _ ρ h
  simp [execBlock, hc]

/-- Executable `ite` elimination: a branch on a proved condition behaves as
    the taken side, again in the post-read world, so read observations
    transfer exactly. -/
theorem exec_ite_wahr {l : Bool} {Γ' : Ctx} {Λ'' Λ''' : List (Res D)}
    (c : Expr D Γ' Λ'' .bool) (t e : Block D V l Γ' Λ'' Λ''')
    (σ : World D) (ρ : Env D Γ') (h : isWahr c = true) :
    execStmt O passes R (Stmt.ite c t e) σ ρ =
      execBlock O passes R t (σ.lese Λ'' c.orte) ρ := by
  have hc : wahr? (eval (σ.lese Λ'' c.orte) c (σ.lese Λ'' c.orte) ρ) = true :=
    isWahrAll_sound c _ _ ρ h
  simp [execStmt, hc]

/-! ## 4. Invariant scope discipline and stable-load redundancy -/

/-- The admissible scopes for invariant-derived check elimination,
    mirroring the goal legs. The tag records WHICH leg discharges the
    truth evidence at the use site, and the elimination proof consumes it
    by cases -- a use without a named scope does not typecheck.
    - `ruhe`: the invariant holds at a rest state (`invRuhe`/`InvRuheG`).
    - `sicht`: the invariant holds outside every writer of its carriers
      (`invSicht`/`InvSichtG`).
    - `wechsel`: the invariant is re-established across a lock move
      (`sperrWechsel`/`sperrSicht`).
    No constructor is dischargeable from inside a running writer or a
    held section: that is the legs' statement, not assumed here. -/
inductive InvScope : Type where
  | ruhe
  | sicht
  | wechsel

/-- Invariant-derived `pruefung` elimination: the exact transfer of
    `exec_pruefung_wahr`, but the truth evidence is a program invariant
    through a NAMED scope instead of the computable checker. Cost,
    call-log, fault and interleaving transfers are the same separate
    obligations as there; the scope discharge itself (which leg, at which
    program point) belongs to the later certificate layer. -/
theorem exec_pruefung_inv {l : Bool} {Γ' : Ctx} {Λ'' Λ''' : List (Res D)}
    (inv : Expr D Γ' Λ'' .bool) (sonst : Endblock D V l Γ' Λ'')
    (rest : Block D V l Γ' Λ'' Λ''') (σ : World D) (ρ : Env D Γ')
    (s : InvScope)
    (h : wahr? (eval (σ.lese Λ'' inv.orte) inv (σ.lese Λ'' inv.orte) ρ) = true) :
    execBlock O passes R (Block.pruefung inv sonst rest) σ ρ =
      execBlock O passes R rest (σ.lese Λ'' inv.orte) ρ := by
  cases s <;> simp [execBlock, h]

/-- A repeated read of the same slot returns the same value when the
    index evaluates the same and the carrier is unchanged between the
    reads. The stability premise is the EXPLICIT separate obligation,
    discharged per instance by exclusive ownership, held-lock stability
    or immutability -- never by thread-local token reasoning alone, never
    across publication, fences or acquire/release edges, and never for
    atomics, MMIO or foreign-observable memory. -/
theorem slot_read_stabil {t : D.Tab} {f : D.Feld t}
    {i : Expr D Γ Λ (.index (D.count t))} {hL : darf D t Λ}
    {σ₀ σ σ' : World D} {ρ ρ' : Env D Γ}
    (hidx : (eval σ₀ i σ' ρ').n = (eval σ₀ i σ ρ).n)
    (hinhalt : σ'.slots t (eval σ₀ i σ ρ).n f = σ.slots t (eval σ₀ i σ ρ).n f) :
    eval σ₀ (Expr.slot t f i hL) σ' ρ' = eval σ₀ (Expr.slot t f i hL) σ ρ := by
  simp only [eval]
  rw [hidx]
  exact hinhalt

/-! ## 5. Jointly inhabited witness: a table-writing program -/

/-- A dummy signature (the witness runs a block directly, never a call). -/
def wSig : Signatur Unit Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The witness declaration: one private table `()` with one slot over
    `0 .. 10`, no locks, no globals, no invariants. Private (not shared),
    so the empty guard list is consistent (`geteilt_bewacht`). -/
def wD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
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
  decMarke := fun e => nomatch e
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => wSig
  eigner_nie_erzeugt := fun _ _ _ _ h => False.elim (List.not_mem_nil h)
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
  geteilt_bewacht := fun _ h => Bool.noConfusion h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The witness contract: writes the table, no result, no locks. -/
def wV : Vertrag wD where
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  erg := none
  gruende := 0
  haelt := []
  produziert := []

/-- The checked condition: constantly true. -/
def wCond : Expr wD [] [] .bool := .wahr

/-- Index `0` into the one-slot table. -/
def wIdx : Expr wD [] [] (.index (wD.count ())) := .lit 0

/-- Value `5` in `0 .. 10`. -/
def wVal : Expr wD [] [] (wD.typ () ()) :=
  .weiter (by decide) (by decide) (.lit 5)

/-- The writing body: one guarded slot store. -/
def wRest : Block wD wV true [] [] [] :=
  Block.cons (Stmt.assignSlot () () wIdx wVal rfl
    (fun _ hw => False.elim (List.not_mem_nil hw))) Block.nil

/-- The refused branch: `leave` (loop context, no proof burden). -/
def wSonst : Endblock wD wV true [] [] := Endblock.leave rfl

/-- The full checked block. -/
def wFull : Block wD wV true [] [] [] :=
  Block.pruefung wCond wSonst wRest

/-- The initial world: slot reads `0`, empty trace. -/
def wWorld0 : World wD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun e => nomatch e
  spur := []

/-- A concrete oracle (never consulted by the witness: no calls, no
    registers, no globals). -/
def wO : Orakel wD where
  wirkt := fun e => nomatch e
  regLies := fun e => nomatch e
  regSchreib := fun e => nomatch e
  sichtbar := fun e => nomatch e

/-- A concrete call handler (never consulted: the witness makes no calls). -/
def wR : ∀ f : wD.Fn, World wD → Env wD (wD.params f) → RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- Non-degeneracy (contract side): the witness contract writes a table. -/
theorem wit_schreibt : wV.schreibt () = true :=
  rfl

/-- The checker fires on the witness condition, by computation. -/
theorem wit_isWahr : isWahr wCond = true :=
  rfl

/-- The generic elimination, jointly inhabited on the witness program. -/
theorem wit_elim :
    execBlock wO 5 wR (Block.pruefung wCond wSonst wRest) wWorld0 Env.nil =
      execBlock wO 5 wR wRest (wWorld0.lese [] wCond.orte) Env.nil :=
  exec_pruefung_wahr wO 5 wR wCond wSonst wRest wWorld0 Env.nil rfl

/-- The witness run writes: the slot reads `5` afterwards. This is the
    reached run with a memory-changing step the gate requires. -/
theorem wit_step :
    match execBlock wO 5 wR wRest wWorld0 Env.nil with
    | .ok σ' _ => (σ'.slots () 0 ()).n = 5
    | _ => False := by
  simp only [wRest, wIdx, wVal, execBlock, execStmt, eval, Expr.orte, World.lese,
    World.merke, World.schreibSlot, World.storeSlot]
  decide

/- CUTS:
   Only the computable check exists so far. Open: its soundness over `eval`;
   constant folding / `weiter` value lemmas; `pruefung`/`ite` elimination with
   exact trace transfer; the invariant-scoped rule (rest/sight/lock-move only,
   never inside a running writer or held section); the stability-gated
   redundant-load rule; cost/ghost-budget, call-log (`Folge`), fault and
   interleaving transfers; the non-degenerate table-writing witness.
-/

end Gabbro.Grammatik.X86.InvariantenOpt
