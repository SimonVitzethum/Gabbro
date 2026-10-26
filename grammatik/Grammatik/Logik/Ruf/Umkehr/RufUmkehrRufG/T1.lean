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
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG

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
  | .onWhy _ arms => arms.kOk
  | .locks _ _ body => body.kOk
  | .breaking _ body => body.kOk
  | .traverse .. => false
  | .retry .. => false
  | .forever .. => false
  | .axiomCall .. => false
  | .retWhy .. => false
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
  | .bindAxiomElse .. => false
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.kOk
  | .narrow _ _ _ sonst rest => sonst.kOk && rest.kOk
  | .check _ sonst rest => sonst.kOk && rest.kOk
  | .float _ _ _ _ _ rest => rest.kOk
  | .floatLit _ _ _ rest => rest.kOk
  | .floatOf _ _ _ rest => rest.kOk
  | .floatNarrow _ _ _ sonst rest => sonst.kOk && rest.kOk

def Endblock.kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => false
  | .leave .. => false
  | .next .. => false
  | .cons s rest => s.kOk && rest.kOk
  | .bind _ rest => rest.kOk
  | .bindCall _ _ _ _ _ rest => rest.kOk
  | .bindCallElse .. => false
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .narrow _ _ _ sonst rest => sonst.kOk && rest.kOk
  | .exchange _ _ _ _ rest => rest.kOk
  | .ite _ t e => t.kOk && e.kOk

  | .regRead .. => false

  | .regReadElse .. => false

  | .awaits .. => false

  | .bindCallInd .. => false

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
  | abbruch {l : Bool} {Γ : Ctx} {Λ Λk : List (Res D)} (k : GRest D V l Γ Λk)
      (hk : RestK A C k) : RestK A C (.abbruch (Λ := Λ) k)

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
  | _, _, _, .abbruch .., _, _ => .sonst
  | _, _, _, .leer, _, _ => .sonst

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


end Gabbro.Grammatik
