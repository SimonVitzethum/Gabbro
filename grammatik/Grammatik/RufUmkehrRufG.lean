/-
  File:      Grammatik/RufUmkehrRufG.lean
  Subject:   THE CONVERSE FOR BODIES WITH CALLS -- every run of one thread of
             the call machine G that pops a frame logs exactly the value the
             sequential semantics (with the body-running handler `rufRumpf`)
             returns, for bodies with direct calls and bind-calls.

  Why: `RufAdaequatG.lean` proves the converse (`rufG_adaequat_umkehr`) for
  call-free bodies; `RufAdaequatRufG.lean` proves the forward direction
  with calls (`rufG_adaequat_ruf`). Here the converse is extended by calls:
  while the frame of `fn` is on the stack, the frames above it form a
  pending call chain; each callee's frame result is DEMANDED by the frames
  below it (`Anspruch`), and every machine step keeps the demand of the top
  frame (`schrittErhaltK`, `invK_schritt`). When the run pops the frame of
  `fn` for the first time, its logged value is the sequential one
  (`rufG_adaequat_ruf_umkehr`).

  The fragment is the call-free, oracle-free fragment of the G converse
  plus `call` (block and `ende` position) and `let x = g(…)`: `StmtR`/
  `BlockR`/`EndR` restricted by the syntactic check `kOk` (no loops, no
  `leave`/`next`, no error channel, no indirect call, no oracle form). The
  depth `n` is any depth at which the body is covered (`TiefK P A n`),
  i.e. at least the nesting depth of the calls; nothing else bounds the run.
-/
import Grammatik.RufAdaequatRufG

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The fragment of the converse -/

mutual

/-- The statement is in the fragment of the converse: no loop, no abrupt
    exit, no error channel, no indirect call, no axiom. -/
def Stmt.kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.kOk && e.kOk
  | .onOption _ p a => p.kOk && a.kOk
  | .onTag _ arms => arms.kOk
  | .onGrund _ arms => arms.kOk
  | .locks _ _ body => body.kOk
  | .breaking _ body => body.kOk
  | .traverse .. => false
  | .retry .. => false
  | .forever .. => false
  | .axiomCall .. => false
  | .retGrund .. => false
  | .leave .. => false
  | .next .. => false
  | .callInd .. => false
  | _ => true

def Block.kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.kOk && rest.kOk
  | .bind _ rest => rest.kOk
  | .bindCall _ _ _ _ _ rest => rest.kOk
  | .bindCallInd .. => false
  | .bindCallElse .. => false
  | .bindAxiom .. => false
  | .regLies .. => false
  | .regLiesElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.kOk
  | .narrow _ _ _ sonst rest => sonst.kOk && rest.kOk
  | .pruefung _ sonst rest => sonst.kOk && rest.kOk
  | .gleit _ _ _ _ _ rest => rest.kOk
  | .gleitLit _ _ _ rest => rest.kOk
  | .gleitVon _ _ _ rest => rest.kOk
  | .gleitNarrow _ _ _ sonst rest => sonst.kOk && rest.kOk

def Endblock.kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => false
  | .leave .. => false
  | .next .. => false
  | .cons s rest => s.kOk && rest.kOk
  | .bind _ rest => rest.kOk

def Arms.kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.kOk && rest.kOk

def GrundArms.kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.kOk && rest.kOk

end

theorem armWahlG_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    arms.kOk = true → (armWahlG arms v).2.1.kOk = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => by
      simp only [Arms.kOk, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => by
      simp only [Arms.kOk, Bool.and_eq_true] at h
      exact armWahlG_kOk rest _ h.2

theorem grundWahlG_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    arms.kOk = true → (grundWahlG arms r).kOk = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => by
      simp only [GrundArms.kOk, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => by
      simp only [GrundArms.kOk, Bool.and_eq_true] at h
      exact grundWahlG_kOk rest _ h.2

theorem armWahlG_kOk' {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option (Int × Int)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : arms.kOk = true) :
    b.kOk = true := by
  have h0 := armWahlG_kOk arms v h
  rw [hw] at h0
  exact h0

theorem armWahlG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    ArmsR A C mr arms → BlockR A C mr (armWahlG arms v).2.1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => h.cons_inv.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => armWahlG_R rest _ h.cons_inv.2

theorem armWahlG_R' {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) {c : Option (Int × Int)}
    {b : Block D V l (ArmCtx Γ c) Λ Λ'} {nutz : Nutzlast c} (hw : armWahlG arms v = ⟨c, b, nutz⟩)
    (h : ArmsR A C mr arms) : BlockR A C mr b := by
  have h1 := armWahlG_R arms v h
  rw [hw] at h1
  exact h1

theorem grundWahlG_R {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} {mr l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    GrundArmsR A C mr arms → BlockR A C mr (grundWahlG arms r)
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => h.cons_inv.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => grundWahlG_R rest _ h.cons_inv.2

/-- The fragment of the converse by nesting depth: at depth `n + 1` a callee
    is admitted if its body is covered with callees at depth `n` and is in
    the fragment (`kOk`); at depth `0` no callee is admitted. A fact about
    the concrete program's bodies. -/
def TiefK (P : Programm D) (A : D.Lock → Prop) : Nat → D.Fn → Prop
  | 0, _ => False
  | n + 1, g => EndR A (TiefK P A n) (P.rumpf g) ∧ (P.rumpf g).kOk = true

/-- The residues the converse follows: covered blocks in the fragment in
    `dann` position, covered end blocks, `schrumpf` and `frei` layers. -/
inductive RestK {V : Vertrag D} (A : D.Lock → Prop) (C : D.Fn → Prop) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop where
  | ende {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ)
      (he : EndR A C e) (ho : e.kOk = true) : RestK A C (.ende e)
  | dann {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ')
      (k : GRest D V l Γ Λ') (hb : BlockR A C mr b) (ho : b.kOk = true)
      (hk : RestK A C k) : RestK A C (.dann b k)
  | schrumpf {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ)
      (hk : RestK A C k) : RestK A C (.schrumpf (τ := τ) k)
  | frei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ)
      (hk : RestK A C k) : RestK A C (.frei L k)

section RestKInv

variable {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop} {l : Bool} {Γ : Ctx}

theorem RestK.ende_inv {Λ : List (Res D)} {e : Endblock D V l Γ Λ}
    (h : RestK A C (.ende e)) : EndR A C e ∧ e.kOk = true := by
  cases h with
  | ende _ he ho => exact ⟨he, ho⟩

theorem RestK.dann_inv {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'}
    {k : GRest D V l Γ Λ'} (h : RestK A C (.dann b k)) :
    (∃ mr, BlockR A C mr b) ∧ b.kOk = true ∧ RestK A C k := by
  cases h with
  | dann _ _ hb ho hk => exact ⟨⟨_, hb⟩, ho, hk⟩

theorem RestK.schrumpf_inv {Λ : List (Res D)} {τ : Ty} {k : GRest D V l Γ Λ}
    (h : RestK A C (.schrumpf (τ := τ) k)) : RestK A C k := by
  cases h with
  | schrumpf _ hk => exact hk

theorem RestK.frei_inv {Λ : List (Res D)} {L : D.Lock} {k : GRest D V l Γ Λ}
    (h : RestK A C (.frei L k)) : RestK A C k := by
  cases h with
  | frei _ _ hk => exact hk

/-- The head statement of a covered `dann` block is in the fragment. -/
theorem RestK.dann_cons_kOk {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : RestK A C (.dann (.cons s rest) k)) : s.kOk = true := by
  obtain ⟨_, ho, _⟩ := h.dann_inv
  simp only [Block.kOk, Bool.and_eq_true] at ho
  exact ho.1

theorem RestK.ende_cons_kOk {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : RestK A C (.ende (.cons s rest))) : s.kOk = true := by
  obtain ⟨_, ho⟩ := h.ende_inv
  simp only [Endblock.kOk, Bool.and_eq_true] at ho
  exact ho.1

theorem RestK.dann_kOk {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'}
    {k : GRest D V l Γ Λ'} (h : RestK A C (.dann b k)) : b.kOk = true :=
  h.dann_inv.2.1

theorem RestK.ende_kOk {Λ : List (Res D)} {e : Endblock D V l Γ Λ}
    (h : RestK A C (.ende e)) : e.kOk = true :=
  h.ende_inv.2

end RestKInv

/-! ## 2. The frame semantics with a call handler

    As `semR` (`RufAdaequatG.lean` §15), for any call handler `R`: a residue
    runs sequentially, and only a return counts. -/

section SemK

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

def semK : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → World D →
    Env D Γ → REnde V
  | _, _, _, .ende e, σ, ρ => endErg (execEnd O passes R e σ ρ)
  | _, _, _, .dann b k, σ, ρ =>
      match execBlock O passes R b σ ρ with
      | .ok σ' ρ' => semK k σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | _ => .sonst
  | _, _, _, .schrumpf k, σ, ρ => semK k σ ρ.tail
  | _, _, _, .frei L k, σ, ρ => semK k (σ.gibt L) ρ
  | _, _, _, .trav .., _, _ => .sonst
  | _, _, _, .travRest .., _, _ => .sonst
  | _, _, _, .wieder .., _, _ => .sonst
  | _, _, _, .wiederRest .., _, _ => .sonst
  | _, _, _, .ewig .., _, _ => .sonst
  | _, _, _, .ewigRest .., _, _ => .sonst
  | _, _, _, .wartet .., _, _ => .sonst
  | _, _, _, .wartetSonst .., _, _ => .sonst

/-- Continue with `k` after an outcome. -/
def nachK {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (o : Ausgang V l Γ)
    (k : GRest D V l Γ Λ) : REnde V :=
  match o with
  | .ok σ ρ => semK O passes R k σ ρ
  | .zurueck σ v => .zurueck σ v
  | _ => .sonst

variable {l : Bool} {Γ : Ctx}

theorem semK_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann b k) σ ρ = nachK O passes R (execBlock O passes R b σ ρ) k := by
  simp only [semK, nachK]

theorem nachK_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    nachK O passes R (execBlock O passes R (.cons s rest) σ ρ) k =
      nachK O passes R (execStmt O passes R s σ ρ) (.dann rest k) := by
  simp only [execBlock]
  generalize execStmt O passes R s σ ρ = o
  cases o <;> simp only [nachK, semK_dann]

theorem nachK_schrumpf {τ : Ty} {Λ : List (Res D)} (o : Ausgang V l (τ :: Γ))
    (k : GRest D V l Γ Λ) :
    nachK O passes R o.schrumpf k = nachK O passes R o (.schrumpf k) := by
  cases o <;> simp only [Ausgang.schrumpf, nachK, semK]

theorem nachK_zuAusgang {Λ : List (Res D)} (o : EndAusgang V l Γ) (k : GRest D V l Γ Λ) :
    nachK O passes R o.zuAusgang k = endErg o := by
  cases o <;> rfl

theorem endErgK_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    endErg (execEnd O passes R (.cons s rest) σ ρ) =
      nachK O passes R (execStmt O passes R s σ ρ) (.dann .nil (.ende rest)) := by
  simp only [execEnd]
  generalize execStmt O passes R s σ ρ = o
  cases o <;> simp only [endErg, nachK, semK, execBlock]

theorem nachK_frei {Λ : List (Res D)} (o : Ausgang V l Γ) (L : D.Lock)
    (k : GRest D V l Γ Λ) :
    (nachK O passes R o (.frei L k)).gleich (nachK O passes R (o.mapWelt (·.gibt L)) k) := by
  cases o with
  | ok σ ρ => exact REnde.gleich_refl _
  | zurueck σ v => exact ⟨⟨rfl, rfl⟩, rfl⟩
  | _ => trivial

end SemK

/-! ## 3. The sequential semantics does not see the trace, with calls

    As `RufAdaequatG.lean` §14, for the fragment of the converse and a call
    handler that agrees up to the trace on the admitted callees (`RufSG`);
    the body-running handler does, by induction on the depth
    (`rufRumpf_SG`). -/

theorem SG.evalArgs {σ σ' : World D} (h : SG σ σ') {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {τs : List Ty} (args : Args D Γ Λ τs) (ρ : Env D Γ),
      evalArgs σ args σ ρ = evalArgs σ' args σ' ρ
  | _, .nil, _ => rfl
  | _, .cons e rest, ρ => by
      show Env.cons (Gabbro.Grammatik.eval σ e σ ρ) (Gabbro.Grammatik.evalArgs σ rest σ ρ) =
        Env.cons (Gabbro.Grammatik.eval σ' e σ' ρ) (Gabbro.Grammatik.evalArgs σ' rest σ' ρ)
      rw [h.eval e ρ, SG.evalArgs h rest ρ]

/-- Call outcomes that agree up to the trace. -/
def RufAusSG {g : D.Fn} : RufAusgang g → RufAusgang g → Prop
  | .ok σ v, .ok σ' v' => SG σ σ' ∧ v = v'
  | .ok .., _ => False
  | _, .ok .. => False
  | _, _ => True

/-- The handler agrees up to the trace on the admitted callees. -/
def RufSG (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (C : D.Fn → Prop) : Prop :=
  ∀ (g : D.Fn), C g → ∀ (σ σ' : World D) (ρ : Env D (D.params g)), SG σ σ' →
    RufAusSG (R g σ ρ) (R g σ' ρ)

/-- The `narrow` step of `execBlock` with the narrowed value abstracted, for
    any handler. -/
def narrowWeiterK (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int}
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (sonst : Endblock D V l Γ Λ)
    (ρ : Env D Γ) (v : Zahl lo hi) (σ₁ : World D) : Ausgang V l Γ :=
  if h : lo' ≤ v.n ∧ v.n ≤ hi' then
    (execBlock O passes R rest σ₁ (.cons (τ := .int lo' hi') ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
  else (execEnd O passes R sonst σ₁ ρ).zuAusgang

theorem execBlock_narrowK (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (.narrow e lo' hi' sonst rest) σ ρ =
      narrowWeiterK O passes R rest sonst ρ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)
        (σ.lese Λ e.orte) := rfl

section SpurK

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  (A : D.Lock → Prop) (C : D.Fn → Prop) (hR : RufSG R C)
include hR

/-- A block's outcome agrees, up to the trace, from worlds with one memory. -/
def SGBK {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
    AusSG (execBlock O passes R b σ ρ) (execBlock O passes R b σ' ρ)

set_option linter.unusedSectionVars false in
mutual

theorem stmtSGK : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), StmtR A C mr s → s.kOk = true →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      AusSG (execStmt O passes R s σ ρ) (execStmt O passes R s σ' ρ)
  | _, _, _, Λ₀, _, .assignSlot t f' i e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .assignDurch p t ht f' i e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .assignGlob g e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1.schreibGlob _ _ _, rfl⟩
  | _, _, _, Λ₀, _, .schreibBytes t f' hf n i hlo hhi e hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (i.orte ++ e.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.eval e]
      exact ⟨SG.schreibBytes _ _ _ _ _ _ _ _ h1, rfl⟩
  | _, _, _, Λ₀, _, .assignVar x e, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1, rfl⟩
  | _, _, _, Λ₀, _, .uebergang t f' hτ i von nach hn he hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ (.inl t :: i.orte)
      simp only [execStmt]
      rw [h1.eval i, h1.1]
      split
      · exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
      · trivial
  | _, _, _, _, _, .regSchreib r hk e, _, _ => by
      intro σ σ' ρ h
      simp only [execStmt]
      exact ⟨h.lese _ _, rfl⟩
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _, _ => by
      intro σ σ' ρ h
      simp only [execStmt]
      exact ⟨h, rfl⟩
  | _, _, _, Λ₀, _, .publish g e payload hp hw hL, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      rw [h1.eval e]
      exact ⟨h1.schreibGlob _ _ _, rfl⟩
  | _, _, _, _, _, .advances m a h hs, _, _ => by
      intro σ σ' ρ h'
      simp only [execStmt]
      exact ⟨h', rfl⟩
  | _, _, _, _, _, .retires m s h a, _, _ => by
      intro σ σ' ρ h'
      simp only [execStmt]
      exact ⟨h', rfl⟩
  | _, _, _, Λ₀, _, .ite c t e, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨ht, he⟩ := hs.ite_inv
      simp only [Stmt.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ c.orte
      simp only [execStmt]
      rw [h1.eval c]
      split
      · exact blockSGK t ht ho.1 _ _ _ h1
      · exact blockSGK e he ho.2 _ _ _ h1
  | _, _, _, Λ₀, _, .onOption o p a, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      simp only [Stmt.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ o.orte
      simp only [execStmt]
      rw [h1.eval o]
      split
      · exact AusSG.schrumpf (blockSGK p hp ho.1 _ _ _ h1)
      · exact blockSGK a ha ho.2 _ _ _ h1
  | _, _, _, Λ₀, _, .onTag w arms, hs, ho => by
      intro σ σ' ρ h
      have ha := hs.onTag_inv
      simp only [Stmt.kOk] at ho
      have h1 := h.lese Λ₀ w.orte
      simp only [execStmt]
      rw [execArms_wahl, execArms_wahl, h1.eval w]
      exact AusSG.schrumpfArm _ (armsSGK arms ha ho _ _ _ _ h1)
  | _, _, _, Λ₀, _, .onGrund r arms, hs, ho => by
      intro σ σ' ρ h
      have ha := hs.onGrund_inv
      simp only [Stmt.kOk] at ho
      have h1 := h.lese Λ₀ r.orte
      simp only [execStmt]
      rw [execGrund_wahlW O passes R arms, execGrund_wahlW O passes R arms, h1.eval r]
      exact grundSGK arms ha ho _ _ _ _ h1
  | _, _, _, Λ₀, _, .call g args hp hr, hs, _ => by
      intro σ σ' ρ h
      have hC := hs.call_inv
      have h1 := h.lese Λ₀ args.orte
      simp only [execStmt]
      rw [h1.evalArgs args ρ]
      have hRg := hR g hC _ _ (evalArgs (σ'.lese Λ₀ args.orte) args (σ'.lese Λ₀ args.orte) ρ) h1
      generalize R g (σ.lese Λ₀ args.orte) _ = o at hRg ⊢
      generalize R g (σ'.lese Λ₀ args.orte) _ = o' at hRg ⊢
      cases o with
      | ok σ1 v1 =>
        cases o' with
        | ok σ2 v2 => exact ⟨hRg.1, rfl⟩
        | _ => exact hRg.elim
      | grund _ r => exact (Fin.cast hr r).elim0
      | logik e =>
        cases o' with
        | ok => exact hRg.elim
        | grund _ r => exact (Fin.cast hr r).elim0
        | _ => trivial
      | hardware e =>
        cases o' with
        | ok => exact hRg.elim
        | grund _ r => exact (Fin.cast hr r).elim0
        | _ => trivial
  | _, _, _, _, _, .callInd .., _, ho => by simp [Stmt.kOk] at ho
  | _, _, _, _, _, .locks L hr body, hs, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hb, _⟩ := hs.locks_inv
      simp only [Stmt.kOk] at ho
      simp only [execStmt]
      exact AusSG.gibt (blockSGK body hb ho _ _ _ (h.nimmt L)) L
  | _, _, _, _, _, .breaking i body, hs, ho => by
      intro σ σ' ρ h
      have hb := hs.breaking_inv
      simp only [Stmt.kOk] at ho
      simp only [execStmt]
      exact blockSGK body hb ho _ _ _ h
  | _, _, _, _, _, .traverse .., _, ho => by simp [Stmt.kOk] at ho
  | _, _, _, _, _, .retry .., _, ho => by simp [Stmt.kOk] at ho
  | _, _, _, _, _, .forever .., _, ho => by simp [Stmt.kOk] at ho
  | _, _, _, _, _, .axiomCall .., _, ho => by simp [Stmt.kOk] at ho
  | _, _, _, Λ₀, _, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execStmt]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, _, _, .retGrund .., _, ho => by simp [Stmt.kOk] at ho
  | _, _, _, _, _, .leave .., _, ho => by simp [Stmt.kOk] at ho
  | _, _, _, _, _, .next .., _, ho => by simp [Stmt.kOk] at ho

theorem blockSGK : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), BlockR A C mr b → b.kOk = true → SGBK O passes R b
  | _, _, _, _, _, .nil, _, _ => by
      intro σ σ' ρ h
      exact ⟨h, rfl⟩
  | _, _, _, _, _, .cons s rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨hs, hr⟩ := hb.cons_inv
      simp only [Block.kOk, Bool.and_eq_true] at ho
      have h1 := stmtSGK s hs ho.1 _ _ ρ h
      simp only [execBlock]
      generalize execStmt O passes R s σ ρ = o at h1 ⊢
      generalize execStmt O passes R s σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | (obtain ⟨hs1, rfl⟩ := h1; exact blockSGK rest hr ho.2 _ _ _ hs1)
  | _, _, _, Λ₀, _, .bind e rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.bind_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ h1)
  | _, _, _, Λ₀, _, .bindCall g args he hp hr rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨hC, hrest⟩ := hb.bindCall_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ args.orte
      simp only [execBlock]
      rw [h1.evalArgs args ρ]
      have hRg := hR g hC _ _ (evalArgs (σ'.lese Λ₀ args.orte) args (σ'.lese Λ₀ args.orte) ρ) h1
      generalize R g (σ.lese Λ₀ args.orte) _ = o at hRg ⊢
      generalize R g (σ'.lese Λ₀ args.orte) _ = o' at hRg ⊢
      cases o with
      | ok σ1 v1 =>
        cases o' with
        | ok σ2 v2 =>
          obtain ⟨hs2, rfl⟩ := hRg
          exact AusSG.schrumpf (blockSGK rest hrest ho _ _ _ hs2)
        | _ => exact hRg.elim
      | grund _ r => exact (Fin.cast hr r).elim0
      | logik e =>
        cases o' with
        | ok => exact hRg.elim
        | grund _ r => exact (Fin.cast hr r).elim0
        | _ => trivial
      | hardware e =>
        cases o' with
        | ok => exact hRg.elim
        | grund _ r => exact (Fin.cast hr r).elim0
        | _ => trivial
  | _, _, _, _, _, .bindCallInd .., _, ho => by simp [Block.kOk] at ho
  | _, _, _, _, _, .bindCallElse .., _, ho => by simp [Block.kOk] at ho
  | _, _, _, _, _, .bindAxiom .., _, ho => by simp [Block.kOk] at ho
  | _, _, _, _, _, .regLies .., _, ho => by simp [Block.kOk] at ho
  | _, _, _, _, _, .regLiesElse .., _, ho => by simp [Block.kOk] at ho
  | _, _, _, _, _, .awaits .., _, ho => by simp [Block.kOk] at ho
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.exchange_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ (.inr g :: neuE.orte)
      simp only [execBlock]
      have hg : (σ.lese Λ₀ (.inr g :: neuE.orte)).globs g =
          (σ'.lese Λ₀ (.inr g :: neuE.orte)).globs g := by rw [h1.2]
      rw [hg, h1.eval neuE]
      exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ (h1.schreibGlob _ _ _))
  | _, _, _, Λ₀, _, .narrow e lo' hi' sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
      simp only [Block.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ e.orte
      rw [execBlock_narrowK, execBlock_narrowK, h1.eval e]
      unfold narrowWeiterK
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho.2 _ _ _ h1)
      · exact EndSG.zuAusgang (endSGK sonst hs ho.1 _ _ _ h1)
  | _, _, _, Λ₀, _, .pruefung c sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
      simp only [Block.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ c.orte
      simp only [execBlock]
      rw [h1.eval c]
      split
      · exact blockSGK rest hr ho.2 _ _ _ h1
      · exact EndSG.zuAusgang (endSGK sonst hs ho.1 _ _ _ h1)
  | _, _, _, Λ₀, _, .gleit op a b lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleit_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ (a.orte ++ b.orte)
      simp only [execBlock]
      rw [h1.eval a, h1.eval b]
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ h1)
      · trivial
  | _, _, _, _, _, .gleitLit q lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleitLit_inv
      simp only [Block.kOk] at ho
      simp only [execBlock]
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ h)
      · trivial
  | _, _, _, Λ₀, _, .gleitVon e lo hi rest, hb, ho => by
      intro σ σ' ρ h
      have hr := hb.gleitVon_inv
      simp only [Block.kOk] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho _ _ _ h1)
      · trivial
  | _, _, _, Λ₀, _, .gleitNarrow e lo hi sonst rest, hb, ho => by
      intro σ σ' ρ h
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      simp only [Block.kOk, Bool.and_eq_true] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execBlock]
      rw [h1.eval e]
      split
      · exact AusSG.schrumpf (blockSGK rest hr ho.2 _ _ _ h1)
      · exact EndSG.zuAusgang (endSGK sonst hs ho.1 _ _ _ h1)

theorem endSGK : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), EndR A C e → e.kOk = true →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      EndSG (execEnd O passes R e σ ρ) (execEnd O passes R e σ' ρ)
  | _, _, Λ₀, .ret e hperm, _, _ => by
      intro σ σ' ρ h
      have h1 := h.lese Λ₀ e.orte
      simp only [execEnd]
      exact ⟨h1, h1.evalErg e ρ⟩
  | _, _, _, .retGrund .., _, ho => by simp [Endblock.kOk] at ho
  | _, _, _, .leave .., _, ho => by simp [Endblock.kOk] at ho
  | _, _, _, .next .., _, ho => by simp [Endblock.kOk] at ho
  | _, _, _, .cons s rest, he, ho => by
      intro σ σ' ρ h
      obtain ⟨hs, hr, _⟩ := he.cons_inv
      simp only [Endblock.kOk, Bool.and_eq_true] at ho
      have h1 := stmtSGK s hs ho.1 _ _ ρ h
      simp only [execEnd]
      generalize execStmt O passes R s σ ρ = o at h1 ⊢
      generalize execStmt O passes R s σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact endSGK rest hr ho.2 _ _ _ hs1)
  | _, _, Λ₀, .bind e rest, he, ho => by
      intro σ σ' ρ h
      have hr := he.bind_inv
      simp only [Endblock.kOk] at ho
      have h1 := h.lese Λ₀ e.orte
      simp only [execEnd]
      rw [h1.eval e]
      exact EndSG.schrumpf (endSGK rest hr ho _ _ _ h1)

theorem armsSGK : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    ArmsR A C mr arms → arms.kOk = true → ∀ (v : Wert D (.sum cs)),
    SGBK O passes R (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ho, ⟨⟨0, _⟩, _⟩ => by
      simp only [Arms.kOk, Bool.and_eq_true] at ho
      exact blockSGK b ha.cons_inv.1 ho.1
  | _, _, _, _, _, _, .cons _ rest, ha, ho, ⟨⟨_ + 1, _⟩, _⟩ => by
      simp only [Arms.kOk, Bool.and_eq_true] at ho
      exact armsSGK rest ha.cons_inv.2 ho.2 _

theorem grundSGK : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), GrundArmsR A C mr arms → arms.kOk = true →
    ∀ (r : Fin n), SGBK O passes R (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ho, ⟨0, _⟩ => by
      simp only [GrundArms.kOk, Bool.and_eq_true] at ho
      exact blockSGK b ha.cons_inv.1 ho.1
  | _, _, _, _, _, _, .cons _ rest, ha, ho, ⟨_ + 1, _⟩ => by
      simp only [GrundArms.kOk, Bool.and_eq_true] at ho
      exact grundSGK rest ha.cons_inv.2 ho.2 _

end

/-- Frame results do not see the trace (covered residues of the converse). -/
theorem semK_SG : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ), RestK A C r →
    ∀ (σ σ' : World D) (ρ : Env D Γ), SG σ σ' →
      (semK O passes R r σ ρ).gleich (semK O passes R r σ' ρ)
  | _, _, _, .ende e, hr => by
      intro σ σ' ρ h
      obtain ⟨he, ho⟩ := hr.ende_inv
      exact endErg_SG (endSGK O passes R A C hR e he ho σ σ' ρ h)
  | _, _, _, .dann b k, hr => by
      intro σ σ' ρ h
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hr.dann_inv
      have h1 := blockSGK O passes R A C hR b hb ho σ σ' ρ h
      rw [semK_dann, semK_dann]
      generalize execBlock O passes R b σ ρ = o at h1 ⊢
      generalize execBlock O passes R b σ' ρ = o' at h1 ⊢
      cases o <;> cases o' <;>
        first
        | exact False.elim h1
        | exact h1
        | trivial
        | (obtain ⟨hs1, rfl⟩ := h1; exact semK_SG k hk _ _ _ hs1)
  | _, _, _, .schrumpf k, hr => by
      intro σ σ' ρ h
      exact semK_SG k hr.schrumpf_inv σ σ' ρ.tail h
  | _, _, _, .frei L k, hr => by
      intro σ σ' ρ h
      exact semK_SG k hr.frei_inv (σ.gibt L) (σ'.gibt L) ρ (h.gibt L)
  | _, _, _, .trav .., hr => by cases hr
  | _, _, _, .travRest .., hr => by cases hr
  | _, _, _, .wieder .., hr => by cases hr
  | _, _, _, .wiederRest .., hr => by cases hr
  | _, _, _, .ewig .., hr => by cases hr
  | _, _, _, .ewigRest .., hr => by cases hr
  | _, _, _, .wartet .., hr => by cases hr
  | _, _, _, .wartetSonst .., hr => by cases hr

end SpurK

/-- **The body-running handler does not see the trace** on the callees the
    converse admits, at every depth. -/
theorem rufRumpf_SG (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) :
    ∀ d, RufSG (rufRumpf P O passes d) (TiefK P A d)
  | 0 => fun _ hC => (hC : False).elim
  | d + 1 => by
      intro g hC σ σ' ρ h
      obtain ⟨he, ho⟩ := hC
      have h1 := endSGK O passes (rufRumpf P O passes d) A (TiefK P A d) (rufRumpf_SG P O passes A d)
        (P.rumpf g) he ho σ σ' ρ h
      simp only [rufRumpf]
      generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes d) (P.rumpf g) σ ρ = o
        at h1 ⊢
      generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes d) (P.rumpf g) σ' ρ = o'
        at h1 ⊢
      cases o with
      | zurueck σ1 v1 =>
        cases o' with
        | zurueck σ2 v2 => exact h1
        | leave h' => exact absurd h' (by decide)
        | next h' => exact absurd h' (by decide)
        | _ => exact h1.elim
      | leave h' => exact absurd h' (by decide)
      | next h' => exact absurd h' (by decide)
      | _ =>
        cases o' with
        | zurueck => exact h1.elim
        | leave h' => exact absurd h' (by decide)
        | next h' => exact absurd h' (by decide)
        | _ => trivial

/-! ## 4. Each machine step keeps the frame semantics, with calls -/

section SemSchrittK

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
  {Γ : Ctx}

theorem semK_blatt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (σ σ' : World D) (ρ ρ' : Env D Γ) (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semK O passes R (.ende rest) σ' ρ' = semK O passes R (.ende (.cons s rest)) σ ρ := by
  simp only [semK, execEnd, h]

theorem semK_dannBlatt {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semK O passes R (.dann rest k) σ' ρ' = semK O passes R (.dann (.cons s rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons s rest), nachK_cons, h]
  rfl

theorem semK_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann (.cons s .nil) (.ende rest)) σ ρ =
      semK O passes R (.ende (.cons s rest)) σ ρ := by
  rw [semK_dann, nachK_cons]
  exact (endErgK_cons O passes R s rest σ ρ).symm

theorem semK_iteWahr {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semK O passes R (.dann t (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semK O passes R (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt, hw, if_true]

theorem semK_iteFalsch {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semK O passes R (.dann e (.dann rest k)) (σ.lese Λ c.orte) ρ =
      semK O passes R (.dann (.cons (.ite c t e) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt, hw, Bool.false_eq_true, if_false]

theorem semK_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semK O passes R (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) =
      semK O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt, hv]
  rw [nachK_schrumpf]

theorem semK_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semK O passes R (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ =
      semK O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt, hv]

theorem semK_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semK O passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semK O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact (semK_dann O passes R b _ _ _).trans (nachK_schrumpf O passes R _ _).symm

theorem semK_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semK O passes R (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semK O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact semK_dann O passes R b _ _ _

theorem semK_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.grund n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ =
      semK O passes R (.dann (.cons (.onGrund r arms) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt]
  rw [execGrund_wahlW O passes R arms]

theorem semK_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann body (.dann rest k)) σ ρ =
      semK O passes R (.dann (.cons (.breaking i body) rest) k) σ ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt]

theorem semK_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    (semK O passes R (.dann body (.frei L (.dann rest k))) (σ.nimmt L) ρ).gleich
      (semK O passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ) := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons, semK_dann]
  simp only [execStmt]
  exact nachK_frei O passes R _ L _

theorem semK_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semK O passes R (.ende (.bind e rest)) σ ρ := by
  simp only [semK, execEnd]
  rw [endErg_schrumpf]

theorem semK_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semK O passes R (.dann (.bind e rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock]
  rw [nachK_schrumpf]

theorem semK_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) =
      semK O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semK_dann O passes R (.narrow e lo' hi' sonst rest), execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_pos h, nachK_schrumpf, semK_dann]

theorem semK_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    semK O passes R (.ende sonst) (σ.lese Λ e.orte) ρ =
      semK O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semK_dann O passes R (.narrow e lo' hi' sonst rest), execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_neg h, nachK_zuAusgang]
  rfl

theorem semK_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semK O passes R (.dann rest k) (σ.lese Λ c.orte) ρ =
      semK O passes R (.dann (.pruefung c sonst rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hw, if_true]

theorem semK_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semK O passes R (.ende sonst) (σ.lese Λ c.orte) ρ =
      semK O passes R (.dann (.pruefung c sonst rest) k) σ ρ := by
  rw [semK_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  rw [nachK_zuAusgang]
  rfl

theorem semK_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
      semK O passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock]
  rw [nachK_schrumpf]

theorem semK_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) =
      semK O passes R (.dann (.gleit op a b lo hi rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hv]
  rw [nachK_schrumpf]

theorem semK_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semK O passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) =
      semK O passes R (.dann (.gleitLit q lo hi rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hv]
  rw [nachK_schrumpf]

theorem semK_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (Float.ofInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semK O passes R (.dann (.gleitVon e lo hi rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hv]
  rw [nachK_schrumpf]

theorem semK_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semK O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semK O passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semK_dann, semK_dann]
  simp only [execBlock, hv]
  rw [nachK_schrumpf]

theorem semK_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    semK O passes R (.ende sonst) (σ.lese Λ e.orte) ρ =
      semK O passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semK_dann]
  simp only [execBlock, hn]
  rw [nachK_zuAusgang]
  rfl

theorem semK_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.ende (.ret (l := l) e hperm)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := rfl

theorem semK_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.ende (.cons (.ret e hperm) rest)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  simp only [semK, execEnd, execStmt, endErg]

theorem semK_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semK O passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  rw [semK_dann, nachK_cons]
  rfl

end SemSchrittK

section RufSemK

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
  {Γ : Ctx}

/-- A call in block position, when the handler answers normally, continues
    with the rest. -/
theorem semK_rufDann {Λ Λ'' : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l Γ (nach D g Λ) Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semK O passes R (.dann (.cons (.call g args hp hr) rest) k) σ ρ =
      semK O passes R (.dann rest k) σ1 ρ := by
  rw [semK_dann O passes R (.cons _ rest), nachK_cons]
  simp only [execStmt, h]
  rfl

/-- A call at `ende` position, when the handler answers normally. -/
theorem semK_ruf {Λ : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D V l Γ (nach D g Λ)) (σ : World D) (ρ : Env D Γ)
    (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semK O passes R (.ende (.cons (.call g args hp hr) rest)) σ ρ =
      semK O passes R (.ende rest) σ1 ρ := by
  simp only [semK, execEnd, execStmt, h]

/-- A bind-call, when the handler answers normally, binds the value. -/
theorem semK_bindCall {Λ Λ' : List (Res D)} {τ : Ty} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l (τ :: Γ) (nach D g Λ) Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semK O passes R (.dann (.bindCall g args he hp hr rest) k) σ ρ =
      semK O passes R (.dann rest (.schrumpf k)) σ1 (.cons (ergWert he v1) ρ) := by
  rw [semK_dann]
  simp only [execBlock, h]
  rw [nachK_schrumpf, semK_dann]

end RufSemK

/-- A leaf does not consult the call handler. -/
theorem istBlatt_R (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (h : s.istBlatt = true)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R s σ ρ = execStmt O passes keinRuf s σ ρ := by
  cases s <;> first | rfl | simp [Stmt.istBlatt] at h

/-- How the machine resumes a caller when the callee `g` returns `v`: the
    caller itself (it did not wait), or its waiting continuation with `v`
    bound (a `let x = g(…)`, with or without an else block). -/
inductive Wiederauf (g : D.Fn) (caller : RufRahmenG D) (v : ErgVal D (D.erg g)) :
    RufRahmenG D → Prop where
  | wie (hnw : caller.wartend = false) : Wiederauf g caller v caller
  | bind {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
      (hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) (he : D.erg g = some τ) :
      Wiederauf g caller v ⟨caller.f, caller.rho, caller.s0,
        ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩
  | bindSonst {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.grund n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
      (hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) (he : D.erg g = some τ) :
      Wiederauf g caller v ⟨caller.f, caller.rho, caller.s0,
        ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩

/-- The frame a call leaves below its callee, and how the caller's frame
    result `S0` continues from the callee's normal answer: plainly (the
    caller advanced past the call), or with the answer bound (`wartet`). -/
def WarteK (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (A : D.Lock → Prop)
    (C : D.Fn → Prop) (T : RufRahmenG D) (g : D.Fn) (rhoG : Env D (D.params g))
    (σc : World D) (Fw : RufRahmenG D) (S0 : REnde (vertragVon D T.f)) : Prop :=
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' : List (Res D)) (ρ' : Env D Γ')
      (rw : GRest D (vertragVon D T.f) l' Γ' Λ'),
      Fw = ⟨T.f, T.rho, T.s0, ⟨l', Γ', Λ', ρ', rw⟩⟩ ∧ rw.wartend = false ∧ RestK A C rw ∧
      ∀ σ1 v1, R g σc rhoG = .ok σ1 v1 → S0 = semK O passes R rw σ1 ρ') ∨
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' Λ'' : List (Res D)) (τ : Ty) (ρ' : Env D Γ')
      (restb : Block D (vertragVon D T.f) l' (τ :: Γ') Λ' Λ'')
      (k : GRest D (vertragVon D T.f) l' Γ' Λ'') (he : D.erg g = some τ),
      Fw = ⟨T.f, T.rho, T.s0, ⟨l', Γ', Λ', ρ', .wartet restb k⟩⟩ ∧
      RestK A C (.dann restb (.schrumpf k)) ∧
      ∀ σ1 v1, R g σc rhoG = .ok σ1 v1 →
        S0 = semK O passes R (.dann restb (.schrumpf k)) σ1 (.cons (ergWert he v1) ρ'))

/-- What one step of thread `f` does to a covered top frame: it stays on
    top with a covered residue and the same frame result (up to the trace);
    or it pops, logging a `rueck` whose world and value ARE the frame result
    (up to the trace), and resumes the caller; or it pushes an admitted
    callee's fresh frame above the caller's waiting frame. -/
def ErhaltK (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (A : D.Lock → Prop)
    (C : D.Fn → Prop) (M M' : RufMaschineG D) (f : Faden) (z : RufFadenG D) {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ) :
    Prop :=
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' : List (Res D)) (ρ' : Env D Γ')
      (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (sp : List (Ereignis D)),
      M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, sp, z.log⟩ ∧
      RestK A C r' ∧
      (semK O passes R r' (M'.weltVon f) ρ').gleich (semK O passes R r (M.weltVon f) ρ)) ∨
  (∃ (v : ErgVal D (D.erg z.kopf.f)) (s1 : World D) (caller neu : RufRahmenG D)
      (rst : List (RufRahmenG D)),
      z.stapel = caller :: rst ∧ Wiederauf z.kopf.f caller v neu ∧
      M'.faeden f = ⟨rst, neu, s1.spur,
        RufEreignisF.rueck z.kopf.f z.kopf.rho v z.kopf.s0 s1 :: z.log⟩ ∧
      M'.speicher = s1.speicher ∧
      (semK O passes R r (M.weltVon f) ρ).gleich (.zurueck s1 v)) ∨
  (∃ (g : D.Fn) (rhoG : Env D (D.params g)) (σc : World D) (Fw : RufRahmenG D),
      C g ∧
      M'.faeden f = ⟨Fw :: z.stapel, ⟨g, rhoG, σc, ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rhoG, .ende (P.rumpf g)⟩⟩, σc.spur,
        RufEreignisF.eintritt g rhoG σc :: z.log⟩ ∧
      M'.speicher = σc.speicher ∧
      WarteK O passes R A C z.kopf g rhoG σc Fw (semK O passes R r (M.weltVon f) ρ))

set_option hygiene false in
/-- Refute a step whose head shape the covered residue cannot have. -/
macro "widerlegeK" h:ident : tactic => `(tactic| (
  rw [hR] at $h:ident
  cases $h:ident
  first
  | exact absurd hcov.dann_cons_kOk (by simp [Stmt.kOk])
  | exact absurd hcov.ende_cons_kOk (by simp [Stmt.kOk])
  | exact absurd hcov.dann_kOk (by simp [Block.kOk])
  | exact absurd hcov.ende_kOk (by simp [Endblock.kOk])
  | cases hcov))

set_option linter.unusedSimpArgs false in
/-- **Each step keeps the frame semantics, with calls.** The top frame of a
    covered residue either stays (same frame result), pops (logged value =
    frame result), or pushes an admitted callee above the frame it leaves
    waiting (`ErhaltK`). `hRSG`: the handler does not see the trace on the
    admitted callees (the trace may differ; the bare lock steps that
    changed only the trace were removed from G on 2026-09-13). -/
theorem schrittErhaltK {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {A : D.Lock → Prop}
    {C : D.Fn → Prop} (hRSG : RufSG R C)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hcov : RestK A C r) :
    ErhaltK P O passes R A C M M' f z ρ r := by
  subst hz
  unfold ErhaltK
  cases hs with
  | blatt l2 Γ2 Λ2 Λ2' s rest ρ2 hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨_, hr, _⟩ := he.cons_inv
    simp only [Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestK.ende rest hr ho.2, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_blatt O passes R s rest _ _ _ ρ' (by rw [istBlatt_R O passes R hleaf]; exact hstep))
  | ruf l2 Γ2 Λ2 g args hp hr rest ρ2 hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs0 hrho
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨hst, hr', _⟩ := he.cons_inv
    have hC := hst.call_inv
    simp only [Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inr (Or.inr ⟨g, _, _, _, hC, rufUpdateG_self _ _ _, rfl,
      Or.inl ⟨_, _, _, _, .ende rest, rfl, rfl, RestK.ende rest hr' ho.2, ?_⟩⟩)
    intro σ1 v1 hR1
    exact semK_ruf O passes R g args hp hr rest _ _ σ1 v1 hR1
  | rueck caller rst hpop Γ2 Λ2 e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr (Or.inl ⟨_, _, caller, caller, rst, hpop, Wiederauf.wie hnw, ?_, rfl,
      REnde.gleich_of_eq (semK_rueck O passes R e hperm _ _)⟩)
    rw [faeden_upd, hrho]
    rfl
  | endeEntf l2 Γ2 Λ2 Λ2' s rest ρ2 hent hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨hs, hr, _⟩ := he.cons_inv
    simp only [Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann (.cons s .nil) (.ende rest), _, rufUpdateG_self _ _ _, RestK.dann _ _ (BlockR.cons s .nil hs BlockR.nil) (by simp [Block.kOk, ho.1]) (RestK.ende rest hr ho.2), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeEntf O passes R s rest _ _)
  | dannBlatt l2 Γ2 Λ2 Λ2' Λ2'' s rest k ρ2 hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest k, _, rufUpdateG_self _ _ _, RestK.dann _ _ hr ho.2 hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_dannBlatt O passes R s rest k _ _ _ ρ' (by rw [istBlatt_R O passes R hleaf]; exact hstep))
  | dannLeer l2 Γ2 Λ2 k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | dannIteWahr l2 Γ2 Λ2 Λ2' Λ2'' c t e rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨ht, he⟩ := hst.ite_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann t (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ ht ho.1.1 (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_iteWahr O passes R c t e rest k _ _ hw)
  | dannIteFalsch l2 Γ2 Λ2 Λ2' Λ2'' c t e rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨ht, he⟩ := hst.ite_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann e (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ he ho.1.2 (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_iteFalsch O passes R c t e rest k _ _ hw)
  | dannOnOptionSome l2 Γ2 Λ2 Λ2' Λ2'' n o p a rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨hp, ha⟩ := hst.onOption_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann p (.schrumpf (.dann rest k)), _, rufUpdateG_self _ _ _, RestK.dann _ _ hp ho.1.1 (RestK.schrumpf _ (RestK.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_optSome O passes R o p a rest k _ _ v hv)
  | dannOnOptionNone l2 Γ2 Λ2 Λ2' Λ2'' n o p a rest k ρ2 hhead σ₁ hs₁ hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨hp, ha⟩ := hst.onOption_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann a (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ ha ho.1.2 (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_optNone O passes R o p a rest k _ _ hv)
  | dannOnTagSome l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ lo hi b nutz hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onTag_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    have hbb := armWahlG_R' arms _ hw ha
    have hbo := armWahlG_kOk' arms _ hw ho.1
    refine Or.inl ⟨_, _, _, _, .dann b (.schrumpf (.dann rest k)), _, rufUpdateG_self _ _ _, RestK.dann _ _ hbb hbo (RestK.schrumpf _ (RestK.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_tagSome O passes R v arms rest k _ _ lo hi b nutz hw)
  | dannOnTagNone l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ b nutz hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onTag_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    have hbb := armWahlG_R' arms _ hw ha
    have hbo := armWahlG_kOk' arms _ hw ho.1
    refine Or.inl ⟨_, _, _, _, .dann b (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hbb hbo (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_tagNone O passes R v arms rest k _ _ b nutz hw)
  | dannOnGrund l2 Γ2 Λ2 Λ2' Λ2'' n rg arms rest k ρ2 hhead σ₁ hs₁ b hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁ hw
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onGrund_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, _, _, rufUpdateG_self _ _ _, RestK.dann _ _ (grundWahlG_R arms _ ha) (grundWahlG_kOk arms _ ho.1) (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_grund O passes R rg arms rest k _ _)
  | endeBind l2 Γ2 Λ2 τ e rest ρ2 hhead σ₁ hs₁ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨he, ho⟩ := hcov.ende_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestK.ende rest he.bind_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeBind O passes R e rest (M.weltVon f) ρ)
  | dannBind l2 Γ2 Λ2 Λ2' Λ2'' τ e rest k ρ2 hhead σ₁ hs₁ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.bind_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_dannBind O passes R e rest k (M.weltVon f) ρ)
  | dannNarrowOk l2 Γ2 Λ2 Λ2' Λ2'' lo hi lo' hi' e sonst rest k ρ2 hhead σ₁ hs₁ h neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hr ho.2 (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_narrowOk O passes R e lo' hi' sonst rest k _ _ h)
  | dannNarrowElse l2 Γ2 Λ2 Λ2' Λ2'' lo hi lo' hi' e sonst rest k ρ2 hhead σ₁ hs₁ h neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende sonst, _, rufUpdateG_self _ _ _, RestK.ende sonst hs ho.1, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_narrowElse O passes R e lo' hi' sonst rest k _ _ h)
  | dannPruefWahr l2 Γ2 Λ2 Λ2' Λ2'' c sonst rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest k, _, rufUpdateG_self _ _ _, RestK.dann _ _ hr ho.2 hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_pruefWahr O passes R c sonst rest k _ _ hw)
  | dannPruefFalsch l2 Γ2 Λ2 Λ2' Λ2'' c sonst rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende sonst, _, rufUpdateG_self _ _ _, RestK.ende sonst hs ho.1, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_pruefFalsch O passes R c sonst rest k _ _ hw)
  | dannBreaking l2 Γ2 Λ2 Λ2' Λ2'' i body rest k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have hbd := hst.breaking_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann body (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hbd ho.1 (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_breaking O passes R i body rest k _ _)
  | dannLocks l2 Γ2 Λ2 Λ2'' L hrg body rest k ρ2 hhead hself hrang hfrei =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨_, hbd, _⟩ := hst.locks_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann body (.frei L (.dann rest k)), _, rufUpdateG_self _ _ _, RestK.dann _ _ hbd ho.1 (RestK.frei _ _ (RestK.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact semK_locks O passes R L hrg body rest k (M.weltVon f) ρ
  | freiGib l2 Γ2 Λ2 L k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hcov.frei_inv, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | schrumpfVergiss l2 Γ2 Λ2 τ k v ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hcov.schrumpf_inv, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | travNext _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | travDone _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | wiederUeber _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | rufDann l2 Γ2 Λ2 Λ2' Λ2'' g args hp hr rest k ρ2 hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs0 hrho
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr'⟩ := hb.cons_inv
    have hC := hst.call_inv
    simp only [Block.kOk, Bool.and_eq_true] at ho
    refine Or.inr (Or.inr ⟨g, _, _, _, hC, rufUpdateG_self _ _ _, rfl,
      Or.inl ⟨_, _, _, _, .dann rest k, rfl, rfl, RestK.dann rest k hr' ho.2 hk, ?_⟩⟩)
    intro σ1 v1 hR1
    exact semK_rufDann O passes R g args hp hr rest k _ _ σ1 v1 hR1
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannBindCall l2 Γ2 Λ2 Λ2' Λ2'' τ g args he hp hr rest k ρ2 hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs0 hrho
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hC, hrest⟩ := hb.bindCall_inv
    simp only [Block.kOk] at ho
    refine Or.inr (Or.inr ⟨g, _, _, _, hC, rufUpdateG_self _ _ _, rfl,
      Or.inr ⟨_, _, _, _, _, _, rest, k, he, rfl,
        RestK.dann rest (.schrumpf k) hrest ho (RestK.schrumpf k hk), ?_⟩⟩)
    intro σ1 v1 hR1
    exact semK_bindCall O passes R g args he hp hr rest k _ _ σ1 v1 hR1
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | rueckBind caller rst hpop l2 Γ2 Λ2 Λ2' τ restb k ρc hcaller Γc Λc e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    rcases hcaller with hc | ⟨n, err, hc⟩
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop, Wiederauf.bind restb k ρc hc he, ?_, rfl,
        REnde.gleich_of_eq (semK_rueck O passes R e hperm _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop,
        Wiederauf.bindSonst n err restb k ρc hc he, ?_, rfl, REnde.gleich_of_eq (semK_rueck O passes R e hperm _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelDannNext _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannRet l2 Γ2 Λ2 Λ2'' e hperm rest k ρ2 hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu
      hnw =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr (Or.inl ⟨_, _, caller, caller, rst, hpop, Wiederauf.wie hnw, ?_, rfl,
      REnde.gleich_of_eq (semK_dannRet O passes R e hperm rest k _ _)⟩)
    rw [faeden_upd, hrho]
    rfl
  | rueckCons caller rst hpop Γ2 Λ2 e hperm rest ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr (Or.inl ⟨_, _, caller, caller, rst, hpop, Wiederauf.wie hnw, ?_, rfl,
      REnde.gleich_of_eq (semK_rueckCons O passes R e hperm rest _ _)⟩)
    rw [faeden_upd, hrho]
    rfl
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ2 hhead caller rst hpop l2 Γ2 Λ2 Λ2' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    rcases hcaller with hc | ⟨n, err, hc⟩
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop, Wiederauf.bind restb k ρc hc he, ?_, rfl,
        REnde.gleich_of_eq (semK_dannRet O passes R e hperm restk kk _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop,
        Wiederauf.bindSonst n err restb k ρc hc he, ?_, rfl, REnde.gleich_of_eq (semK_dannRet O passes R e hperm restk kk _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
  | rueckConsBind lk Γk Λk e hperm restk ρ2 hhead caller rst hpop l2 Γ2 Λ2 Λ2' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    rcases hcaller with hc | ⟨n, err, hc⟩
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop, Wiederauf.bind restb k ρc hc he, ?_, rfl,
        REnde.gleich_of_eq (semK_rueckCons O passes R e hperm restk _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop,
        Wiederauf.bindSonst n err restb k ρc hc he, ?_, rfl, REnde.gleich_of_eq (semK_rueckCons O passes R e hperm restk _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannExchange l2 Γ2 Λ2 Λ2' g neuE hw hL rest k ρ2 hhead σ₁ hs₁ σ₂ hs₂ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    subst hs₂
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.exchange_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_exchange O passes R g neuE hw hL rest k (M.weltVon f) ρ)
  | dannGleit l2 Γ2 Λ2 Λ2' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.gleit_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleit O passes R op a b lo hi rest k _ _ v hv)
  | dannGleitLit l2 Γ2 Λ2 Λ2' q lo hi rest k ρ2 hhead v hv =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.gleitLit_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleitLit O passes R q lo hi rest k _ _ v hv)
  | dannGleitVon l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.gleitVon_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleitVon O passes R e lo hi rest k _ _ v hv)
  | dannGleitNarrowOk l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi sonst rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hr ho.2 (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleitNarrowOk O passes R e lo hi sonst rest k _ _ v hv)
  | dannGleitNarrowElse l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi sonst rest k ρ2 hhead σ₁ hs₁ hn neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende sonst, _, rufUpdateG_self _ _ _, RestK.ende sonst hs ho.1, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleitNarrowElse O passes R e lo hi sonst rest k _ _ hn)
  | dannBindAxiom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | rueckGrund _ _ _ hhead => widerlegeK hhead
  | rueckConsGrund _ _ _ _ hhead => widerlegeK hhead
  | dannRetGrund _ _ _ _ _ hhead => widerlegeK hhead


/-! ## 5. The pending call chain

    While the frame of `fn` is on the stack, the frames above it are its
    callees, their callees, and so on; each waits in the frame below it.
    The frame at position `i` above the frame of `fn` runs at depth `n - i`
    (its calls go through `rufRumpf (n - i)`). A returning frame's result is
    DEMANDED by the chain below it (`Anspruch`): a normal answer must make
    the frame below -- resumed as the machine resumes it -- end with the
    demand of ITS chain, down to the frame of `fn`, whose result must agree
    with `S` (the sequential result). A frame that does not answer normally
    (`sonst`) is never popped (`schrittErhaltK`), so it is demanded nothing. -/

section Kette

variable (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (n : Nat)
  (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D) (S : REnde (vertragVon D fn))

theorem wartend_of_wartet {F : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    {restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ'} {k : GRest D (vertragVon D F.f) l Γ Λ'}
    {ρc : Env D Γ} (hc : F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) : F.wartend = true := by
  unfold RufRahmenG.wartend
  rw [hc]
  rfl

/-- The demand the pending call chain `unten` (top first, ending with the
    frame of `fn`) makes on the result of a frame of `g` directly above it. -/
inductive Anspruch : List (RufRahmenG D) → (g : D.Fn) → REnde (vertragVon D g) → Prop
  | basis (res : REnde (vertragVon D fn)) (h : res.gleich S) : Anspruch [] fn res
  | sonst (unten : List (RufRahmenG D)) (g : D.Fn) : Anspruch unten g .sonst
  | wie (F : RufRahmenG D) (unten : List (RufRahmenG D)) (g : D.Fn) (σ1 : World D)
      (v1 : ErgVal D (D.erg g)) (hnw : F.wartend = false)
      (h : Anspruch unten F.f (semK O passes (rufRumpf P O passes (n - unten.length))
        F.rest.2.2.2.2 σ1 F.rest.2.2.2.1)) :
      Anspruch (F :: unten) g (.zurueck σ1 v1)
  | bind (F : RufRahmenG D) (unten : List (RufRahmenG D)) (g : D.Fn) (σ1 : World D)
      (v1 : ErgVal D (D.erg g)) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ)
      (hc : F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) (he : D.erg g = some τ)
      (h : Anspruch unten F.f (semK O passes (rufRumpf P O passes (n - unten.length))
        (.dann restb (.schrumpf k)) σ1 (.cons (ergWert he v1) ρc))) :
      Anspruch (F :: unten) g (.zurueck σ1 v1)

/-- A frame waiting in the chain, covered at its depth `d`: plainly (it
    advanced past the call) or waiting for a bound value. -/
def FrameK (d : Nat) (F : RufRahmenG D) : Prop :=
  (F.wartend = false ∧ RestK A (TiefK P A d) F.rest.2.2.2.2) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
      F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∧ RestK A (TiefK P A d) (.dann restb (.schrumpf k)))

/-- The chain below the top: every frame covered at its depth; the bottom
    one is the frame of `fn` (its key). -/
inductive KetteOk : List (RufRahmenG D) → Prop
  | nil : KetteOk []
  | cons (F : RufRahmenG D) (unten : List (RufRahmenG D))
      (hF : FrameK P A (n - unten.length) F)
      (hkey : unten = [] → RufSchluesselG F = ⟨fn, rho, s0⟩) (h : KetteOk unten) :
      KetteOk (F :: unten)

/-- The top frame: covered at its depth, its frame result meets the demand
    of the chain below, and it is the frame of `fn` if the chain is empty. -/
def TopOk (unten : List (RufRahmenG D)) (T : RufRahmenG D) (σ : World D) : Prop :=
  RestK A (TiefK P A (n - unten.length)) T.rest.2.2.2.2 ∧
  Anspruch P O passes n fn S unten T.f
    (semK O passes (rufRumpf P O passes (n - unten.length)) T.rest.2.2.2.2 σ T.rest.2.2.2.1) ∧
  (unten = [] → RufSchluesselG T = ⟨fn, rho, s0⟩)

/-- **The run invariant of the converse with calls**: the frame of `fn` is on
    the stack of thread `f` above `caller :: rst`, the frames above it form
    a well-formed pending call chain, and the log grew from `log`. -/
def InvK (f : Faden) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (log : List (RufEreignisF D)) (M : RufMaschineG D) : Prop :=
  ∃ (unten : List (RufRahmenG D)) (ext : List (RufEreignisF D)),
    (M.faeden f).stapel = unten ++ caller :: rst ∧ (M.faeden f).log = ext ++ log ∧
    KetteOk P A n fn rho s0 unten ∧ TopOk P O passes A n fn rho s0 S unten (M.faeden f).kopf (M.weltVon f)

/-- The demand only sees results up to the trace. -/
theorem anspruch_gleich : ∀ {unten : List (RufRahmenG D)} {g : D.Fn} {res res' : REnde (vertragVon D g)},
    KetteOk P A n fn rho s0 unten → Anspruch P O passes n fn S unten g res → res.gleich res' →
    Anspruch P O passes n fn S unten g res' := by
  intro unten g res res' hK h hg
  induction h with
  | basis res hS =>
    exact Anspruch.basis res' (REnde.gleich_trans (REnde.gleich_symm hg) hS)
  | sonst unten g =>
    cases res' with
    | sonst => exact Anspruch.sonst unten g
    | zurueck => exact hg.elim
  | wie F unten g σ1 v1 hnw h ih =>
    cases res' with
    | sonst => exact hg.elim
    | zurueck σ2 v2 =>
      obtain ⟨hs, rfl⟩ := hg
      cases hK with
      | cons _ _ hF hkey hK' =>
        rcases hF with ⟨_, hcov⟩ | ⟨_, _, _, _, _, _, _, _, hc, _⟩
        · refine Anspruch.wie F unten g σ2 v1 hnw (ih hK' ?_)
          exact semK_SG O passes _ A (TiefK P A (n - unten.length))
            (rufRumpf_SG P O passes A _) _ hcov σ1 σ2 _ hs
        · rw [wartend_of_wartet hc] at hnw
          cases hnw
  | bind F unten g σ1 v1 restb k ρc hc he h ih =>
    cases res' with
    | sonst => exact hg.elim
    | zurueck σ2 v2 =>
      obtain ⟨hs, rfl⟩ := hg
      cases hK with
      | cons _ _ hF hkey hK' =>
        rcases hF with ⟨hnw, _⟩ | ⟨_, _, _, _, _, restb', k', ρc', hc', hcov⟩
        · rw [wartend_of_wartet hc] at hnw
          cases hnw
        · rw [hc] at hc'
          cases hc'
          refine Anspruch.bind F unten g σ2 v1 restb k ρc hc he (ih hK' ?_)
          exact semK_SG O passes _ A (TiefK P A (n - unten.length))
            (rufRumpf_SG P O passes A _) _ hcov σ1 σ2 _ hs

/-- The demand at the bottom: agreement with `S`. -/
theorem anspruch_nil {g : D.Fn} {res : REnde (vertragVon D g)}
    (h : Anspruch P O passes n fn S [] g res) :
    res = .sonst ∨ ∃ hg : g = fn, (hg ▸ res).gleich S := by
  cases h with
  | basis _ hS => exact Or.inr ⟨rfl, hS⟩
  | sonst => exact Or.inl rfl

/-- The demand on a return, one frame up: how the frame below resumes. -/
theorem anspruch_cons {F : RufRahmenG D} {unten : List (RufRahmenG D)} {g : D.Fn}
    {σ1 : World D} {v1 : ErgVal D (D.erg g)}
    (h : Anspruch P O passes n fn S (F :: unten) g (.zurueck σ1 v1)) :
    (F.wartend = false ∧ Anspruch P O passes n fn S unten F.f
      (semK O passes (rufRumpf P O passes (n - unten.length)) F.rest.2.2.2.2 σ1
        F.rest.2.2.2.1)) ∨
    (∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ)
      (_ : F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩) (he : D.erg g = some τ),
      Anspruch P O passes n fn S unten F.f
        (semK O passes (rufRumpf P O passes (n - unten.length)) (.dann restb (.schrumpf k)) σ1
          (.cons (ergWert he v1) ρc))) := by
  cases h with
  | wie _ _ _ _ _ hnw h => exact Or.inl ⟨hnw, h⟩
  | bind _ _ _ _ _ restb k ρc hc he h => exact Or.inr ⟨_, _, _, _, _, restb, k, ρc, hc, he, h⟩

/-- The bottom frame pops: its logged value agrees with `S`. -/
theorem schluss_basis {T : RufRahmenG D} (hkey : RufSchluesselG T = ⟨fn, rho, s0⟩)
    {res : REnde (vertragVon D T.f)} (han : Anspruch P O passes n fn S [] T.f res)
    (v : ErgVal D (D.erg T.f)) (s1 : World D) (hg : res.gleich (.zurueck s1 v)) :
    ∃ v' : ErgVal D (D.erg fn), RufEreignisF.rueck T.f T.rho v T.s0 s1 =
      RufEreignisF.rueck fn rho v' s0 s1 ∧ (REnde.zurueck (V := vertragVon D fn) s1 v').gleich S := by
  obtain ⟨Tf, Trho, Ts0, Trest⟩ := T
  simp only [RufSchluesselG, Sigma.mk.injEq] at hkey
  obtain ⟨rfl, h2⟩ := hkey
  have h3 : (Trho, Ts0) = (rho, s0) := eq_of_heq h2
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hres := anspruch_gleich P O passes (fun _ => True) n Tf Trho Ts0 S KetteOk.nil han hg
  rcases anspruch_nil P O passes n Tf S hres with h | ⟨_, hS⟩
  · cases h
  · exact ⟨v, rfl, hS⟩

end Kette

/-! ## 6. Every step keeps the chain; the first pop of the frame -/

section Lauf

variable (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (n : Nat)
  (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D) (S : REnde (vertragVon D fn))
  (f : Faden) (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (log : List (RufEreignisF D))

/-- The frame of `fn` has been popped: thread `f` is back at the caller's
    stack `rst`, and its log carries the frame's return with a value and a
    world that agree with `S`. -/
def GepopptK (M : RufMaschineG D) : Prop :=
  ∃ (v : ErgVal D (D.erg fn)) (s1 : World D) (ext : List (RufEreignisF D)),
    (M.faeden f).stapel = rst ∧
    (M.faeden f).log = RufEreignisF.rueck fn rho v s0 s1 :: (ext ++ log) ∧
    (REnde.zurueck (V := vertragVon D fn) s1 v).gleich S

/-- **One step keeps the pending call chain**, or it is the pop of the frame
    of `fn` itself -- with the value `S` demands. -/
theorem invK_schritt {M M' : RufMaschineG D} (hs : RufSchrittG P O passes M f M')
    (h : InvK P O passes A n fn rho s0 S f caller rst log M) :
    InvK P O passes A n fn rho s0 S f caller rst log M' ∨ GepopptK fn rho s0 S f rst log M' := by
  obtain ⟨unten, ext, hst, hlog, hK, hcovT, hanT, hkeyT⟩ := h
  rcases hT : (M.faeden f).kopf.rest with ⟨lT, ΓT, ΛT, ρT, rT⟩
  rw [hT] at hcovT hanT
  rcases schrittErhaltK (rufRumpf_SG P O passes A (n - unten.length)) hs (M.faeden f) rfl ρT rT hT
      hcovT with
    ⟨l', Γ', Λ', ρ', r', sp, hM', hcov', hsem⟩ |
    ⟨v, s1, caller', neu, rst', hpop, hwa, hM', hsp', hsem⟩ |
    ⟨g, rhoG, σc, Fw, hC, hM', hsp', hwk⟩
  · -- the frame stays on top
    left
    refine ⟨unten, ext, by rw [hM']; exact hst, by rw [hM']; exact hlog, hK, ?_, ?_, ?_⟩
    · rw [hM']
      exact hcov'
    · rw [hM']
      exact anspruch_gleich P O passes A n fn rho s0 S hK hanT (REnde.gleich_symm hsem)
    · intro hu
      rw [hM']
      exact hkeyT hu
  · -- a pop
    have hW' : M'.weltVon f = s1 := by
      unfold RufMaschineG.weltVon
      rw [hsp', hM']
      exact Speicher.welt_speicher s1
    cases unten with
    | nil =>
      right
      rw [hst] at hpop
      simp only [List.nil_append, List.cons.injEq] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      obtain ⟨v', he, hS⟩ := schluss_basis P O passes n fn rho s0 S (hkeyT rfl) hanT v s1 hsem
      refine ⟨v', s1, ext, by rw [hM'], ?_, hS⟩
      rw [hM', hlog, he]
    | cons F unten' =>
      left
      rw [hst] at hpop
      simp only [List.cons_append, List.cons.injEq] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      cases hK with
      | cons _ _ hF hkey hK' =>
      have hres := anspruch_gleich P O passes A n fn rho s0 S (KetteOk.cons F unten' hF hkey hK')
        hanT hsem
      refine ⟨unten', RufEreignisF.rueck _ _ v _ s1 :: ext, by rw [hM'],
        by rw [hM', hlog]; rfl, hK', ?_⟩
      rcases anspruch_cons P O passes n fn S hres with
        ⟨hnw, han'⟩ | ⟨l, Γ, Λ, Λ', τ, restb, k, ρc, hc, he, han'⟩
      · cases hwa with
        | wie _ =>
          refine ⟨?_, ?_, ?_⟩
          · rw [hM']
            rcases hF with ⟨_, hcov⟩ | ⟨_, _, _, _, _, _, _, _, hc0, _⟩
            · exact hcov
            · rw [wartend_of_wartet hc0] at hnw
              cases hnw
          · rw [hM', hW']
            exact han'
          · intro hu
            rw [hM']
            exact hkey hu
        | bind restb' k' ρc' hc' he' =>
          rw [wartend_of_wartet hc'] at hnw
          cases hnw
        | bindSonst n' err restb' k' ρc' hc' he' =>
          have hw1 : F.wartend = true := by
            unfold RufRahmenG.wartend
            rw [hc']
            rfl
          rw [hw1] at hnw
          cases hnw
      · cases hwa with
        | wie hnw' =>
          rw [wartend_of_wartet hc] at hnw'
          cases hnw'
        | bind restb' k' ρc' hc' he' =>
          rw [hc] at hc'
          cases hc'
          refine ⟨?_, ?_, ?_⟩
          · rw [hM']
            rcases hF with ⟨hnw0, _⟩ | ⟨_, _, _, _, _, restb0, k0, ρc0, hc0, hcov0⟩
            · rw [wartend_of_wartet hc] at hnw0
              cases hnw0
            · rw [hc] at hc0
              cases hc0
              exact hcov0
          · rw [hM', hW']
            exact han'
          · intro hu
            rw [hM']
            exact hkey hu
        | bindSonst n' err restb' k' ρc' hc' he' =>
          rw [hc] at hc'
          cases hc'
  · -- a push
    left
    have hW' : M'.weltVon f = σc := by
      unfold RufMaschineG.weltVon
      rw [hsp', hM']
      exact Speicher.welt_speicher σc
    have hd : ∃ d', n - unten.length = d' + 1 := by
      cases hdd : n - unten.length with
      | zero =>
        rw [hdd] at hC
        exact hC.elim
      | succ d' => exact ⟨d', rfl⟩
    obtain ⟨d', hd⟩ := hd
    have hC' : TiefK P A (d' + 1) g := by rw [← hd]; exact hC
    obtain ⟨hbody, hko⟩ := hC'
    have hlen : n - (Fw :: unten).length = d' := by
      simp only [List.length_cons]
      omega
    have hFrame : FrameK P A (n - unten.length) Fw := by
      rcases hwk with ⟨l', Γ', Λ', ρ', rw, hFw, hnw, hcovw, _⟩ |
        ⟨l', Γ', Λ', Λ'', τ, ρ', restb, k, he, hFw, hcovw, _⟩
      · subst hFw
        exact Or.inl ⟨hnw, hcovw⟩
      · subst hFw
        exact Or.inr ⟨_, _, _, _, _, restb, k, ρ', rfl, hcovw⟩
    have hkeyW : unten = [] → RufSchluesselG Fw = ⟨fn, rho, s0⟩ := by
      intro hu
      rcases hwk with ⟨_, _, _, _, _, hFw, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hFw, _⟩ <;>
        (subst hFw; exact hkeyT hu)
    refine ⟨Fw :: unten, RufEreignisF.eintritt g rhoG σc :: ext, by rw [hM', hst]; rfl,
      by rw [hM', hlog]; rfl, KetteOk.cons Fw unten hFrame hkeyW hK, ?_, ?_, ?_⟩
    · rw [hM', hlen]
      exact RestK.ende _ hbody hko
    · rw [hM', hlen, hW']
      show Anspruch P O passes n fn S (Fw :: unten) g
        (endErg (execEnd O passes (rufRumpf P O passes d') (P.rumpf g) σc rhoG))
      cases hx : execEnd O passes (rufRumpf P O passes d') (P.rumpf g) σc rhoG with
      | zurueck σ1 v1 =>
        have hR1 : rufRumpf P O passes (n - unten.length) g σc rhoG = .ok σ1 v1 := by
          rw [hd]
          simp only [rufRumpf, hx]
        rcases hwk with ⟨l', Γ', Λ', ρ', rw, hFw, hnw, _, hsemw⟩ |
          ⟨l', Γ', Λ', Λ'', τ, ρ', restb, k, he, hFw, _, hsemw⟩
        · subst hFw
          refine Anspruch.wie _ unten g σ1 v1 hnw ?_
          rw [← hsemw σ1 v1 hR1]
          exact hanT
        · subst hFw
          refine Anspruch.bind _ unten g σ1 v1 restb k ρ' rfl he ?_
          rw [← hsemw σ1 v1 hR1]
          exact hanT
      | grund => exact Anspruch.sonst _ _
      | leave h' => exact absurd h' (by decide)
      | next h' => exact absurd h' (by decide)
      | logik => exact Anspruch.sonst _ _
      | hardware => exact Anspruch.sonst _ _
    · intro hu
      cases hu

end Lauf

/-- A run of thread `f` during which the stack of `f` stays longer than
    `lo` in every state that steps: with `lo` the length of the caller's
    stack, a run up to (at most) the FIRST pop of the frame above it. -/
inductive RufLaufUeber (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (lo : Nat) :
    RufMaschineG D → RufMaschineG D → Prop where
  | refl (M : RufMaschineG D) : RufLaufUeber P O passes f lo M M
  | schritt {M M' M'' : RufMaschineG D} (hh : lo < (M.faeden f).stapel.length)
      (h : RufSchrittG P O passes M f M') (hr : RufLaufUeber P O passes f lo M' M'') :
      RufLaufUeber P O passes f lo M M''

/-- Such a run is a run of thread `f`. -/
theorem RufLaufUeber.lauf {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden} {lo : Nat}
    {M M'' : RufMaschineG D} (h : RufLaufUeber P O passes f lo M M'') :
    RufLaufG P O passes f M M'' := by
  induction h with
  | refl => exact RufLaufG.refl _
  | schritt _ hs _ ih => exact RufLaufG.schritt hs ih

/-- Along a run up to the first pop, the chain is kept; at a machine whose
    stack is no longer than the caller's, the frame has been popped. -/
theorem invK_lauf (P : Programm D) (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (n : Nat)
    (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D) (S : REnde (vertragVon D fn))
    (f : Faden) (caller : RufRahmenG D) (rst : List (RufRahmenG D))
    (log : List (RufEreignisF D)) {M M'' : RufMaschineG D}
    (hl : RufLaufUeber P O passes f rst.length M M'') :
    InvK P O passes A n fn rho s0 S f caller rst log M →
    (M''.faeden f).stapel.length ≤ rst.length → GepopptK fn rho s0 S f rst log M'' := by
  induction hl with
  | refl M =>
    intro h hpop
    obtain ⟨unten, _, hst, _⟩ := h
    rw [hst] at hpop
    simp only [List.length_append, List.length_cons] at hpop
    omega
  | schritt hh hs hr ih =>
    intro h hpop
    rcases invK_schritt P O passes A n fn rho s0 S f caller rst log hs h with h' | hG
    · exact ih h' hpop
    · cases hr with
      | refl => exact hG
      | schritt hh' _ _ =>
        obtain ⟨_, _, _, hst', _⟩ := hG
        rw [hst'] at hh'
        exact absurd hh' (Nat.lt_irrefl _)

/-- **The converse with calls.** Thread `f` of `M` runs a frame of `fn`
    (parameters `rho`, entry world `s0`) above `caller :: rst`, with residue
    `.ende b` for an end block `b` covered at depth `n` by the fragment of
    the converse (calls and bind-calls, callees admitted by `TiefK P A n`:
    their bodies covered one level down, and so on). If ANY run of thread
    `f` alone leads from `M` to a machine
    whose stack of `f` is no longer than the caller's, every state before
    it keeping the frame on the stack (a run up to the FIRST pop of the
    frame, `RufLaufUeber`), then the log of that machine is the old log,
    extended by the events of the calls made on the way, topped by the
    frame's return `rueck fn rho v s0 s1`; and the sequential semantics
    with the body-running handler of depth `n`, started at the thread's
    world, returns THE SAME value `v`, in a world with the memory of `s1`.

    The depth: `n` is any depth at which `b` is covered (`TiefK`), i.e. at
    least the nesting depth of the calls; the run itself is not bounded. -/
theorem rufG_adaequat_ruf_umkehr (P : Programm D) (O : Orakel D) (passes : Nat) (n : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn)) (s0 : World D)
    (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (spur : List (Ereignis D))
    (log : List (RufEreignisF D)) {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (b : Endblock D (vertragVon D fn) false Γ Λ) (A : D.Lock → Prop)
    (hb : EndR A (TiefK P A n) b) (hko : b.kOk = true)
    (hM : M.faeden f = ⟨caller :: rst, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (M'' : RufMaschineG D) (hl : RufLaufUeber P O passes f rst.length M M'')
    (hpop : (M''.faeden f).stapel.length ≤ rst.length) :
    ∃ (v : ErgVal D (D.erg fn)) (s1 : World D) (ext : List (RufEreignisF D)) (σ' : World D),
      (M''.faeden f).log = RufEreignisF.rueck fn rho v s0 s1 :: (ext ++ log) ∧
      execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ = .zurueck σ' v ∧
      σ'.speicher = s1.speicher := by
  have h0 : InvK P O passes A n fn rho s0
      (endErg (execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ)) f caller rst log M := by
    refine ⟨[], [], by rw [hM]; rfl, by rw [hM]; rfl, KetteOk.nil, ?_, ?_, ?_⟩
    · rw [hM]
      exact RestK.ende b hb hko
    · rw [hM]
      exact Anspruch.basis _ (REnde.gleich_refl _)
    · intro _
      rw [hM]
      rfl
  obtain ⟨v, s1, ext, _, hlog, hS⟩ := invK_lauf P O passes A n fn rho s0 _ f caller rst log hl h0
    hpop
  revert hS
  cases hx : execEnd O passes (rufRumpf P O passes n) b (M.weltVon f) ρ with
  | zurueck σ' w =>
    intro hS
    obtain ⟨hsg, hvw⟩ := hS
    subst hvw
    exact ⟨v, s1, ext, σ', hlog, rfl, hsg.speicher.symm⟩
  | _ => intro hS; exact absurd hS id



/-! ## 7. Runs up to the first pop, and the witnesses -/

theorem RufLaufUeber.trans {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden}
    {lo : Nat} {M M' M'' : RufMaschineG D} (h1 : RufLaufUeber P O passes f lo M M')
    (h2 : RufLaufUeber P O passes f lo M' M'') : RufLaufUeber P O passes f lo M M'' := by
  induction h1 with
  | refl => exact h2
  | schritt hh hs _ ih => exact RufLaufUeber.schritt hh hs (ih h2)

/-- Every run of thread `f` that ends with a stack no longer than `lo`
    passes through a FIRST such machine: its prefix up to there keeps the
    stack longer than `lo` in every state that steps. -/
theorem rufLaufG_erster {P : Programm D} {O : Orakel D} {passes : Nat} {f : Faden} (lo : Nat)
    {M M'' : RufMaschineG D} (hl : RufLaufG P O passes f M M'')
    (hpop : (M''.faeden f).stapel.length ≤ lo) :
    ∃ M1, RufLaufUeber P O passes f lo M M1 ∧ (M1.faeden f).stapel.length ≤ lo ∧
      RufLaufG P O passes f M1 M'' := by
  induction hl with
  | refl M => exact ⟨M, RufLaufUeber.refl M, hpop, RufLaufG.refl M⟩
  | @schritt M M' M2 hs hr ih =>
    by_cases hM : (M.faeden f).stapel.length ≤ lo
    · exact ⟨M, RufLaufUeber.refl M, hM, RufLaufG.schritt hs hr⟩
    · obtain ⟨M1, h1, h2, h3⟩ := ih hpop
      exact ⟨M1, RufLaufUeber.schritt (by omega) hs h1, h2, h3⟩

/-- The callee of the bind witness is covered by the converse at depth 1. -/
theorem t4G_tiefK (A : t4D.Lock → Prop) : TiefK t4P A 1 t4G :=
  ⟨show EndR A (TiefK t4P A 0) t4GRumpf from
    EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _), rfl⟩

/-- The bind caller is covered by the converse at depth 1. -/
theorem t4BRumpf_K (A : t4D.Lock → Prop) : EndR A (TiefK t4P A 1) t4BRumpf :=
  EndR.cons _ _
    (StmtR.ite _ _ _
      (BlockR.bindCall _ _ _ _ _ _ (t4G_tiefK A)
        (BlockR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) BlockR.nil))
      BlockR.nil)
    (EndR.ret _ _)

theorem t4BRumpf_kOk : t4BRumpf.kOk = true := rfl

/-- **Witness for `rufG_adaequat_ruf_umkehr`.** All premises jointly, on the
    bind-caller program at depth 1: the machine `t4M t4B t4BRumpf`, the
    covered body (a bind-call of the writing callee under an `if`, the
    bound value written), and the run `rufG_adaequat_ruf` produces, cut at
    its FIRST pop of the caller's frame (`rufLaufG_erster`) -- a real run
    of the machine through the push, the callee's writing leaf, the binding
    pop, the caller's writing leaf and the final pop. From the MACHINE's
    log alone the converse recovers that the sequential semantics returns
    the logged value `9`, in a world with the logged memory (slot 0 moved
    to 5 by the callee, slot 1 to 3 by the caller). -/
theorem rufG_adaequat_ruf_umkehr_zeuge :
    ∃ (M1 : RufMaschineG t4D) (v : ErgVal t4D (t4D.erg t4B)) (s1 : World t4D)
      (ext : List (RufEreignisF t4D)),
      RufLaufUeber t4P t4O 0 0 0 (t4M t4B t4BRumpf) M1 ∧ (M1.faeden 0).stapel = [] ∧
      (M1.faeden 0).log = RufEreignisF.rueck t4B Env.nil v (t4Sp.welt []) s1 :: (ext ++ []) ∧
      (s1.slots () 0 ()).n = 5 ∧ (s1.slots () 1 ()).n = 3 ∧
      ∃ σ', execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0)
          Env.nil = .zurueck σ' v ∧
        σ'.speicher = s1.speicher ∧ (show Zahl 0 100 from v).n = 9 := by
  obtain ⟨σ', v, hex, h5, h3, h9, M', ext', hl, hf, _, _⟩ := rufG_adaequat_ruf_zeuge_bind
  have hpop' : (M'.faeden 0).stapel.length ≤ ([] : List (RufRahmenG t4D)).length := by
    rw [hf]
    exact Nat.le_refl 0
  obtain ⟨M1, hu, hpop1, _⟩ := rufLaufG_erster 0 hl hpop'
  obtain ⟨v1, s1, ext, σ1, hlog, hex1, hsp⟩ := rufG_adaequat_ruf_umkehr t4P t4O 0 1
    (t4M t4B t4BRumpf) 0 t4B Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4BRumpf
    (fun _ => False) (t4BRumpf_K _) t4BRumpf_kOk rfl M1 hu hpop1
  cases hex.symm.trans hex1
  have hst : (M1.faeden 0).stapel = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hs1 : s1.slots = σ'.slots := by
    have := congrArg Speicher.slots hsp
    exact this.symm
  refine ⟨M1, v, s1, ext, hu, hst, hlog, ?_, ?_, σ', hex, hsp, h9⟩
  · rw [hs1]; exact h5
  · rw [hs1]; exact h3

/-- The bind witness up to its waiting state, as a run up to the first pop:
    `endeEntf`, `dannIteWahr`, `dannBindCall`. -/
theorem t4B_wartet_ueber :
    ∃ M3 : RufMaschineG t4D, RufLaufUeber t4P t4O 0 0 0 (t4M t4B t4BRumpf) M3 ∧
      ∃ caller : RufRahmenG t4D, (M3.faeden 0).stapel = [caller, t4Unten] ∧
        caller.f = t4B ∧ caller.wartend = true ∧ (M3.faeden 0).kopf.f = t4G := by
  have hZ0 : ZustandG (t4M t4B t4BRumpf) 0 [t4Unten] t4B Env.nil (t4Sp.welt []) []
      (Env.nil : Env t4D []) (.ende t4BRumpf) ((t4M t4B t4BRumpf).weltVon 0) := ⟨rfl, rfl⟩
  obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := t4P) (O := t4O) (passes := 0) hZ0.1
    (.ite .wahr t4BindBlock .nil) (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil)
    Env.nil rfl rfl
  obtain ⟨M2, hs2, hZ2⟩ := w_iteWahr (P := t4P) (O := t4O) (passes := 0) hZ1.1
    .wahr t4BindBlock .nil .nil
    (.ende (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil)) Env.nil rfl rfl
    (fun L => nomatch L)
  obtain ⟨M3, hs3, hZ3⟩ := w_bindCall (P := t4P) (O := t4O) (passes := 0) hZ2.1
    t4G .nil rfl (t4Hp t4B) rfl (.cons (.assignSlot () () t4Idx1x (.var .hier) rfl t4Darf) .nil)
    (.dann .nil (.ende (.ret (.wert (t4Lit 9 (by decide) (by decide))) List.Perm.nil))) Env.nil
    rfl (fun L => nomatch L)
  have h0 : 0 < ((t4M t4B t4BRumpf).faeden 0).stapel.length := Nat.zero_lt_succ _
  have h1 : 0 < (M1.faeden 0).stapel.length := by rw [hZ1.1]; exact Nat.zero_lt_succ _
  have h2 : 0 < (M2.faeden 0).stapel.length := by rw [hZ2.1]; exact Nat.zero_lt_succ _
  refine ⟨M3, RufLaufUeber.schritt h0 hs1 (RufLaufUeber.schritt h1 hs2
    (RufLaufUeber.schritt h2 hs3 (RufLaufUeber.refl M3))), _, by rw [hZ3.1], rfl, rfl,
    by rw [hZ3.1]⟩

/-- **AGREEMENT on the bind witness, both halves** (the former finding
    `befund_wartet`). From the state in which the caller of `t4B` WAITS
    below the callee, along every run of the thread up to the first pop of
    the caller's frame: no head of any thread waits (the verbatim pops can
    no longer restore the waiting caller), and if the run pops the
    caller's frame, the logged return value is the sequential one, `9`. -/
theorem wartet_einig_voll :
    (∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 9) ∧
    ∃ M3 : RufMaschineG t4D, RufLaufUeber t4P t4O 0 0 0 (t4M t4B t4BRumpf) M3 ∧
      (∃ caller : RufRahmenG t4D, (M3.faeden 0).stapel = [caller, t4Unten] ∧
        caller.f = t4B ∧ caller.wartend = true) ∧
      ∀ M' : RufMaschineG t4D, RufLaufUeber t4P t4O 0 0 0 M3 M' →
        (∀ g, (M'.faeden g).kopf.wartend = false) ∧
        ((M'.faeden 0).stapel.length ≤ 0 →
          ∃ (v : ErgVal t4D (t4D.erg t4B)) (s1 : World t4D) (ext : List (RufEreignisF t4D)),
            (M'.faeden 0).log = RufEreignisF.rueck t4B Env.nil v (t4Sp.welt []) s1 :: ext ∧
            (show Zahl 0 100 from v).n = 9) := by
  obtain ⟨σ0, v0, hex0, h50, h30, h90⟩ := t4B_exec
  refine ⟨⟨σ0, v0, hex0, h90⟩, ?_⟩
  obtain ⟨M3, hu3, caller, hst, hf, hw, _⟩ := t4B_wartet_ueber
  refine ⟨M3, hu3, ⟨caller, hst, hf, hw⟩, ?_⟩
  intro M' hu'
  refine ⟨fun g => (rufLaufG_sauber (hu3.trans hu').lauf (t4M_sauber t4B t4BRumpf) g).kopf_wartend,
    ?_⟩
  intro hpop
  obtain ⟨v1, s1, ext, σ1, hlog, hex1, _⟩ := rufG_adaequat_ruf_umkehr t4P t4O 0 1
    (t4M t4B t4BRumpf) 0 t4B Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4BRumpf
    (fun _ => False) (t4BRumpf_K _) t4BRumpf_kOk rfl M' (hu3.trans hu') hpop
  cases hex0.symm.trans hex1
  exact ⟨v0, s1, ext ++ [], hlog, h90⟩

/-! ## CUTS:
  What is proved: the converse with calls (`rufG_adaequat_ruf_umkehr`) --
  for a frame whose body is covered at depth `n` by the fragment of the
  converse, every run of its thread up to the first pop of the frame
  logs the value the sequential semantics with the
  body-running handler `rufRumpf n` returns, in a world with the logged
  memory. Proved through a pending call chain invariant (`InvK`: the top
  frame's result meets the demand `Anspruch` of the frames below it) that
  every step keeps (`invK_schritt`, from the one-frame step lemma
  `schrittErhaltK`: stay / pop / push), and the trace-insensitivity of the
  sequential semantics with calls (`rufRumpf_SG`, by depth). Joint witness
  on the bind program (`rufG_adaequat_ruf_umkehr_zeuge`), and the full
  agreement on the former deadlock finding (`wartet_einig_voll`).
  What is NOT proved:

  - The fragment of the converse (`kOk`) excludes loops (`traverse`,
    `retry`, `forever`), `leave`/`next`, the error channel (`retGrund`,
    `let … else`), indirect calls, axioms and the oracle forms (`regLies`,
    `regLiesElse`, `awaits`). The frame semantics `semK` gives the loop
    shims and waiting residues no meaning (`sonst`); following a loop
    would need its residues (`trav`/`wieder`/`ewig` and their `Rest`
    shims) in `semK` with `traverseLauf`/`retryLauf`/`foreverLauf` as their
    meaning, and the error channel a second demand (`grund`) in
    `Anspruch`. The oracle forms stay out for the reason of the G converse:
    the oracle sees the whole world, trace included (the bare lock steps
    that changed the trace are gone since 2026-09-13, but a run from a
    world with a different trace still meets a trace-reading oracle).
  - The run is cut at the FIRST pop of the frame (`RufLaufUeber`): after
    the pop the caller may call `fn` again, and a later `rueck fn …` belongs
    to another frame. `rufLaufG_erster` finds the first pop on any run.
  - The depth `n` is any depth at which the body is covered (`TiefK`); the
    statement is about THAT `n` (a deeper `n` covers the same body and
    gives the same result, by determinism of the witness, not proved in
    general).
  - As in the G converse, `s1` agrees with the sequential world in memory,
    not in trace.
-/

#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_umkehr
#print axioms Gabbro.Grammatik.rufG_adaequat_ruf_umkehr_zeuge
#print axioms Gabbro.Grammatik.wartet_einig_voll
#print axioms Gabbro.Grammatik.invK_schritt
#print axioms Gabbro.Grammatik.schrittErhaltK
#print axioms Gabbro.Grammatik.rufRumpf_SG
#print axioms Gabbro.Grammatik.rufLaufG_erster

end Gabbro.Grammatik
